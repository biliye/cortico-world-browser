/**
 * Browser World：把本机 web-access 的 CDP proxy 接成一个浏览器。
 *
 * 环境是操作员日常用的那个浏览器（带着他所有网站的登录态）。这个类做三件事：
 * 管 proxy 的起停、把工具调用翻译成 HTTP 调用、把浏览器里他自己的动向报成事件。
 *
 * 起停沿用 SenseVoice 那一套：先探活，通了就复用（他自己或 coding agent 已经在跑的情况下
 * 不重复拉起），探不通才 spawn，`stop()` 只关自己拉起的那个。起不来不抛错——投一条
 * `browser.down`，让工具去报失败，这样 bot 知道「手现在不能用」，而不是这个 World 整个消失。
 */
import { existsSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import type {
  ToolCallContext,
  ToolDef,
  ToolOutcome,
  ToolSpec,
  World,
  WorldWebUiDecl,
  WorldHost,
  WorldLamp,
} from 'cortico/core/types.ts';
import { nowIso } from 'cortico/core/util.ts';
import { CdpRelay, RelayError, classifyRelayError, runFindUrl, type EvalResult, type PageTarget, type RelayFailureKind, type RelayHealth } from './cdp-client.ts';
import { BilibiliSession, isBilibili } from './video/session.ts';
import { VIDEO_DEFAULTS } from './video/config.ts';
import { BrowserSearchService, BROWSER_FETCH_TOOL, type SearchServiceOptions } from './search-service.ts';
import { BROWSER_CONFIG_GROUP, type BrowserConfigSection } from './config.ts';
import { OwnBrowser, createWindow, showTarget } from './own-browser.ts';
import { raiseSentence, type RaiseResult } from './window-raise.ts';
import { readExpression, typeExpression } from './page-scripts.ts';
import {
  SEARCH_COUNT_DEFAULT,
  SEARCH_COUNT_MAX,
  clampCount,
  normalizeHarvest,
  renderSearch,
  searchExpression,
  searchUrl,
  type SearchEngineId,
} from './search.ts';

const ENV_PROMPT_FILE = fileURLToPath(new URL('./ENV_PROMPT.md', import.meta.url));

/** 开页时顺手读回的正文上限：够看清这个页面在讲什么，又不把上下文塞满。 */
const OPEN_TEXT_MAX = 4000;
/** `browser_read` 的默认值与上限。 */
const READ_TEXT_DEFAULT = 8000;
const READ_TEXT_MAX = 40000;
/** 回执里列几条链接。 */
const LINKS_SHOWN = 20;
/** `browser_js` 回执里值序列化之后的上限。 */
const JS_VALUE_MAX = 30000;
/** `browser_tabs` 的变化段最多列几条。 */
const CHANGES_MAX = 12;
/** 等就绪的轮询间隔。 */
const READY_POLL_MS = 1000;
/**
 * 已就绪之后的复检间隔。连接可能在两次调用之间静默失效：半开 socket 不会发 close 事件，
 * 上游 `/health` 仍然报 `connected: true`。30 秒内最多复检一次，正常路径上只是一个
 * 时间戳比较，不给每次工具调用加一次 HTTP 往返。
 */
const READY_RECHECK_MS = 30_000;
/** 复检用的探活超时：比普通调用短，别让"确认它已经死了"本身又拖 30 秒。 */
const READY_RECHECK_TIMEOUT_MS = 8000;
/** `find-url.mjs` 跑一次的上限：它要开本机的 sqlite 历史库。 */
const FIND_URL_TIMEOUT_MS = 20000;
/**
 * 导航那一段的下限超时。普通调用超时（`requestTimeoutMs`）默认 30 秒，而站点打不通时上游的
 * `Page.navigate` 正好要等它自己的 30 秒 CDP 超时才回话——客户端若也卡在 30 秒，拿到的只是本地
 * 那句 `aborted due to timeout`，真话被挡在外面。宽这 5 秒是为了拿到**上游自己的回答**。
 */
const NAV_TIMEOUT_MIN_MS = 35_000;
/** 导航没成之后，再试读一次那块内容用的短超时：页面那一侧可能还卡着，别把调用再拖长一轮。 */
const NAV_FAILED_DUMP_MS = 5000;

/**
 * 这一类失败（导航没在窗口内完成）要说的话。
 *
 * 关键是**别让她以为浏览器坏了**：2026-09-30 那天她连着三次 `browser_open example.com` 拿到
 * 「连不上 cdp-proxy + 去开远程调试」，顺手把「browser 别再试了」写进了自己的笔记——而浏览器
 * 与 proxy 全程都是好的，打不开的是那个域名。
 */
const NAV_UNANSWERED_HINT =
  '（proxy 与浏览器都是通的：多半是那个地址在这台机器上打不开、或者页面太慢。' +
  '先确认这个站点连得上，或换个地址再试——不是浏览器坏了。）';

/** 「连上了但不答」时补给人看的一句：这跟远程调试开关无关。 */
const RELAY_HALF_DEAD_HINT =
  '（代理与浏览器都还在，是连接层不再应答——不是远程调试开关的问题。' +
  '下一次调用会尝试重新连接；仍然不行就重启 cdp-proxy，再不行重启 Coopanion。）';

/** 这一类失败（命令发出去没回话）要说的话。 */
const COMMAND_TIMEOUT_HINT =
  '（proxy 与浏览器都是通的：是这一发命令没回话，多半那个页面自己卡着。换个页面或过一会儿再试。）';

/** 失败归类在回执里的说法。 */
const FAILURE_LABEL: Record<RelayFailureKind | 'nav', string> = {
  unreachable: '连不上 proxy',
  'not-connected': '浏览器没连上',
  'command-timeout': '命令没回话',
  nav: '页面没打开',
  relay: 'proxy 报错',
};

/** 浏览器的内部页面不进变化段：那不是「他去了哪儿」。 */
const INTERNAL_URL = /^(chrome|edge|brave|about|devtools|chrome-extension|extension|chrome-untrusted):/i;

const KIND_VERB: Record<PageChange['kind'], string> = { opened: '打开', moved: '转到', closed: '关掉' };

/** 两次查看之间，一个页面发生的变化。 */
interface PageChange {
  kind: 'opened' | 'moved' | 'closed';
  label: string;
}

interface SeenPage {
  url: string;
  title: string;
}

/** `browser_read` 读回来的页面。 */
interface PageDump {
  title: string;
  url: string;
  ready: string;
  text: string;
  links: Array<{ text: string; url: string }>;
  truncated: boolean;
  error?: string;
}

export interface BrowserWorldOptions {
  /** `worlds.browser` 的活引用。 */
  cfg: BrowserConfigSection;
  timezone: string;
  secret?: SearchServiceOptions['secret'];
  storeSecret?: SearchServiceOptions['storeSecret'];
  request?: typeof fetch;
}

/**
 * 全部工具的静态声明：`tools()` 与定义里的 describe 都取它。
 * 实例只补 handler，不改这里的字。工具是否**能用**按配置变（专属实例、bringToFront），
 * 名字与声明不随配置变。
 */
export const BROWSER_OPEN_TOOL: ToolSpec = {
  name: 'browser_open',
  description:
    'Open a page in a new background tab in the operator\'s own browser and return what the page shows: ' +
    'title, URL, its readable text and its links. The tab carries the operator\'s login state. ' +
    'Use the returned `target` value for every later call on that page. ' +
    'A URL written without a scheme gets https:// in front of it.',
  tags: ['act', 'snapshot'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      url: { type: 'string', description: 'Address to open, for example `example.com/report`.' },
    },
    required: ['url'],
  },
};

export const BROWSER_SEARCH_TOOL: ToolSpec = {
  name: 'browser_search',
  description:
    'Search the web through DeepSeek, Tavily or a browser search page. Returns titles, URLs, summaries and the actual engine. ' +
    'Uses user-configured order, enabled engines and optional failure fallback. An explicit engine selects only that provider. ' +
    'Successful empty results do not trigger fallback. DeepSeek query limit is 128 Unicode characters. ' +
    'API search creates no tab; browser engines return a target you can read or close. Use browser_fetch for public article content, or browser_open for interactive pages.',
  // 网页引擎会创建页面，因此工具保留 act 标签。
  tags: ['act', 'snapshot'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      query: { type: 'string', description: 'What to search for, words as a person would type them.' },
      engine: { type: 'string', enum: ['deepseek', 'tavily', 'bing', 'sogou', 'baidu'], description: 'Optional explicit engine; otherwise follows Browser search settings.' },
      count: { type: 'integer', description: `How many results to return; default ${SEARCH_COUNT_DEFAULT}, max ${SEARCH_COUNT_MAX}.` },
    },
    required: ['query'],
  },
};

export const BROWSER_READ_TOOL: ToolSpec = {
  name: 'browser_read',
  description:
    'Read the readable text and links of a page you already opened, by `target`. ' +
    'Pass `selector` to read one part of the page instead of the whole document. ' +
    'Text reaching the limit is cut and flagged. `ready` is the document readyState, not proof the ' +
    'content you want has appeared.',
  tags: ['read', 'snapshot'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      target: { type: 'string', description: 'Target id returned by browser_open or browser_tabs.' },
      selector: { type: 'string', description: 'CSS selector to read inside, for example `main article`.' },
      maxChars: { type: 'integer', description: `How much text to return; default ${READ_TEXT_DEFAULT}, max ${READ_TEXT_MAX}.` },
    },
    required: ['target'],
  },
};

export const BROWSER_JS_TOOL: ToolSpec = {
  name: 'browser_js',
  description:
    'Evaluate one JavaScript expression inside the page and return its value. This is the escape hatch when ' +
    'the other tools do not cover what the page needs. Expressions only: to run several statements, wrap them ' +
    'yourself as `(async () => { ... })()` and return a value. A thrown error comes back as a failed receipt. ' +
    'The value must be JSON-serializable; DOM nodes and functions come back as their names.',
  tags: ['act'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      target: { type: 'string', description: 'Target id returned by browser_open or browser_tabs.' },
      expression: { type: 'string', description: 'JavaScript expression, for example `document.querySelectorAll("a").length`.' },
    },
    required: ['target', 'expression'],
  },
};

export const BROWSER_CLICK_TOOL: ToolSpec = {
  name: 'browser_click',
  description:
    'Click the first element matching a CSS selector. Default is a JS click, which covers most cases. ' +
    '`native: true` sends a real mouse event at the element\'s centre: use it when the page ignores a JS click, ' +
    'when the click should count as a user gesture, or when it should open a file dialog. ' +
    'A link that opens a new tab (`target=_blank`, which is what search result links are) opens **only** with ' +
    '`native: true` — a JS click on it does nothing at all. When a click does open a new page, the receipt ' +
    'names it, with its target id. ' +
    'Returns what was clicked and the page\'s title and URL right after.',
  tags: ['act'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      target: { type: 'string', description: 'Target id returned by browser_open or browser_tabs.' },
      selector: { type: 'string', description: 'CSS selector of the element to click.' },
      native: { type: 'boolean', description: 'Send a real mouse event instead of `el.click()`.' },
    },
    required: ['target', 'selector'],
  },
};

export const BROWSER_TYPE_TOOL: ToolSpec = {
  name: 'browser_type',
  description:
    'Type a value into an input, textarea, select or contenteditable element, then fire input and change events ' +
    'so frameworks notice. `submit: true` sends the value and submits: the containing form when there is one, ' +
    'otherwise an Enter key press on the element.',
  tags: ['act'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      target: { type: 'string', description: 'Target id returned by browser_open or browser_tabs.' },
      selector: { type: 'string', description: 'CSS selector of the field.' },
      value: { type: 'string', description: 'Text to put in, or the option of a select.' },
      submit: { type: 'boolean', description: 'Submit after typing.' },
    },
    required: ['target', 'selector', 'value'],
  },
};

export const BROWSER_UPLOAD_TOOL: ToolSpec = {
  name: 'browser_upload',
  description:
    'Attach local files to a page\'s file input, bypassing the file dialog. ' +
    '`files` are absolute paths on this machine — a file in your own workspace is one.',
  tags: ['act'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      target: { type: 'string', description: 'Target id returned by browser_open or browser_tabs.' },
      selector: { type: 'string', description: 'CSS selector of the `input[type=file]`.' },
      files: { type: 'array', items: { type: 'string' }, description: 'Absolute paths to attach.' },
    },
    required: ['target', 'selector', 'files'],
  },
};

export const BROWSER_SCROLL_TOOL: ToolSpec = {
  name: 'browser_scroll',
  description:
    'Scroll the page. `to: bottom` is the usual one: it loads lazy content, so images and later sections ' +
    'exist in the DOM afterwards. `y` is the distance for `down` and `up`.',
  tags: ['act'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      target: { type: 'string', description: 'Target id returned by browser_open or browser_tabs.' },
      to: { type: 'string', enum: ['down', 'up', 'top', 'bottom'], description: 'Where to scroll; default `down`.' },
      y: { type: 'integer', description: 'Pixels for `down` / `up`; default 3000.' },
    },
    required: ['target'],
  },
};

export const BROWSER_SHOT_TOOL: ToolSpec = {
  name: 'browser_shot',
  description:
    'Capture one screenshot of the page and attach it to the receipt. The image is the viewport, not the whole ' +
    'document. Use it when the content is in images, canvas or video, where the readable text comes back empty ' +
    'or thin — and scroll first if the part you need is further down.',
  tags: ['read'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      target: { type: 'string', description: 'Target id returned by browser_open or browser_tabs.' },
    },
    required: ['target'],
  },
};

export const BROWSER_NAVIGATE_TOOL: ToolSpec = {
  name: 'browser_navigate',
  description:
    'Move an existing tab to another address, or go back one entry. Use `browser_open` instead when you want ' +
    'a second page at the same time. A URL without a scheme gets https:// in front of it.',
  tags: ['act', 'snapshot'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      target: { type: 'string', description: 'Target id returned by browser_open or browser_tabs.' },
      url: { type: 'string', description: 'Address to move to.' },
      back: { type: 'boolean', description: 'Go back one entry in this tab\'s history instead.' },
    },
    required: ['target'],
  },
};

export const BROWSER_TABS_TOOL: ToolSpec = {
  name: 'browser_tabs',
  description:
    'List the pages open in the browser right now, each with its target id. ' +
    'Entries are marked `mine: true` when you opened them — those are the only ones `browser_close` accepts. ' +
    'When the browser is the operator\'s own, this also reports what changed since the previous call: the pages ' +
    'he opened, moved or closed in between, as a net difference (a page he opened and closed in between leaves ' +
    'no trace, and the browser\'s own pages never appear). ' +
    'When it is your own instance, there is nobody else browsing in it, so no change section is reported.',
  tags: ['read', 'snapshot'],
  parameters: { type: 'object', additionalProperties: false, properties: {} },
};

export const BROWSER_FOCUS_TOOL: ToolSpec = {
  name: 'browser_focus',
  description:
    'Bring one of your pages into the operator\'s view: its window is restored if it is minimized or hidden, moved back on screen, and raised above ' +
    'whatever he is using. Use it when you actually want him to look at something. This is the only tool ' +
    'that takes over his screen, so reach for it deliberately — your pages work fine, media included, while ' +
    'they stay off screen, and this interrupts whatever he is doing (his keyboard focus usually stays where ' +
    'it was, but that is not guaranteed). The receipt tells you the page\'s document.visibilityState ' +
    'afterwards, which window it raised, and what (if anything) is sitting on top of it — only if that last ' +
    'part says nothing is in the way can he really see it. When something is in the way (a topmost window ' +
    'cannot be covered at all) or no window could be identified, do not retry in a loop: browser_shot is the ' +
    'reliable way to show him instead.',
  tags: ['act'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      target: { type: 'string', description: 'Target id returned by browser_open or browser_tabs.' },
    },
    required: ['target'],
  },
};

export const BROWSER_CLOSE_TOOL: ToolSpec = {
  name: 'browser_close',
  description:
    'Close a page you opened. Pages the operator opened are refused on purpose: closing one loses his state. ' +
    'Your pages are also closed automatically when they sit idle, so this is for tidying up sooner than that.',
  tags: ['act'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      target: { type: 'string', description: 'Target id of a page you opened.' },
    },
    required: ['target'],
  },
};

export const BROWSER_FIND_URL_TOOL: ToolSpec = {
  name: 'browser_find_url',
  description:
    'Search this machine\'s browser bookmarks and history for a URL. Use it when the target is something the ' +
    'operator has visited — a page he mentions by name, an internal system no search engine can reach. ' +
    'Keywords are AND-ed and match title and URL. Returns the tool\'s own listing text.',
  tags: ['read', 'snapshot'],
  parameters: {
    type: 'object',
    additionalProperties: false,
    properties: {
      keywords: { type: 'array', items: { type: 'string' }, description: 'Words to match, all of them.' },
      only: { type: 'string', enum: ['bookmarks', 'history'], description: 'Search one source only.' },
      browser: { type: 'string', enum: ['chrome', 'edge'], description: 'Limit to one browser\'s data.' },
      limit: { type: 'integer', description: 'How many results; default 20 in the tool itself.' },
      since: { type: 'string', description: 'History only: `1d`, `7h`, `30m` or `YYYY-MM-DD`.' },
      sort: { type: 'string', enum: ['recent', 'visits'], description: 'History only: by last visit or by visit count.' },
    },
    required: [],
  },
};

export class BrowserWorld implements World {
  readonly id = 'browser';

  private readonly relay: CdpRelay;
  private readonly video: BilibiliSession;
  private readonly directPages = new Set<string>();
  private readonly proxyTouchedAt = new Map<string, number>();
  /**
   * 配了专属实例时才有：她的浏览器由本 World 起停，并且我们还要直接对它说一句 CDP
   * （`Target.activateTarget`，上游没有这个端点）。没配时为 null，一切照旧。
   */
  private readonly own: OwnBrowser | null;
  private host: WorldHost | null = null;
  private running = false;
  private state: 'idle' | 'starting' | 'ready' | 'failed' = 'idle';
  private lastError = '';
  /** proxy 报的浏览器名，没有时为配置里的那个。 */
  private browserLabel = '';
  /** 自己开的页面：targetId → 最后一次用到它的时刻。只有这些允许关，也只有这些会被闲置回收。 */
  private readonly mine = new Map<string, number>();
  /**
   * 上一次 `browser_tabs` 看到的页面：targetId → 页面，加一个看的时间。
   * 只在被她问的时候更新——这个 World 自己不定时看任何东西。
   */
  private readonly seen = new Map<string, SeenPage>();
  private seenAt = 0;
  /** proxy 掉了之后补拉过一次就不再试了。 */
  private recoveryTried = false;
  /** 上一次 ready 复检的时刻；0 表示还没复检过。 */
  private readyProbedAt = 0;

  private readonly searchService: BrowserSearchService;

  constructor(private readonly opts: BrowserWorldOptions) {
    this.searchService = new BrowserSearchService(opts);
    const cfg = opts.cfg;
    cfg.video ??= structuredClone(VIDEO_DEFAULTS);
    this.own = cfg.ownBrowser
      ? new OwnBrowser({
          exePath: cfg.ownBrowserExe.trim(),
          home: cfg.ownBrowserHome.trim(),
          cdpPort: cfg.ownBrowserPort,
        })
      : null;
    this.relay = new CdpRelay({
      skillDir: cfg.skillDir.trim(),
      browser: cfg.browser.trim(),
      port: cfg.port,
      tabIdleMinutes: cfg.tabIdleMinutes,
      // 专属实例那一路：把"家"当 LOCALAPPDATA 交给 proxy，上游据此发现她那个实例。
      localAppDataRoot: this.own ? cfg.ownBrowserHome.trim() : undefined,
    });
    this.video = new BilibiliSession({
      cfg: cfg.video, timezone: opts.timezone,
      acquire: requested => this.acquireVideoPage(requested),
      touch: target => this.touch(target),
      present: this.own ? async (target, by) => {
        const outcome = await this.focus({ target }, by === 'operator');
        if (typeof outcome === 'string') return outcome;
        if (outcome.failed) throw new Error(outcome.text);
        return outcome.text;
      } : undefined,
      close: async target => {
        if (!this.mine.has(target)) throw new Error('这个页面不是 Browser 开的，请手动关闭；已经停止观看。');
        await this.relay.close(target, this.timeout());
        this.mine.delete(target); this.directPages.delete(target); this.seen.delete(target);
      },
    });
  }

  /** 模板里的占位符：她操作的是哪个浏览器、是不是她自己的那个、页面在她自己的窗口里还是他的浏览器里。 */
  envPromptVars(): Record<string, string> {
    const own = this.own !== null;
    return {
      ...this.video.envPromptVars(),
      'browser.videoEnabled': this.opts.cfg.video.enabled ? '已启用' : '已禁用，browser_video_* 工具不可用',
      'browser.label': displayBrowser(this.opts.cfg.browser),
      'browser.kind': own
        ? '你自己那个专属实例（独立 profile 与调试端口，不带操作员的登录态）'
        : '操作员日常用的那个浏览器（带着他所有网站的登录态）',
      'browser.front': own
        ? '你开出来的每个页面都在它自己的窗口里，那个窗口停在屏幕外——媒体照样能播，但操作员看不见它'
        : '你开出来的页面是后台 tab，不打扰他',
    };
  }

  webUi(): WorldWebUiDecl {
    const cfg = this.opts.cfg;
    const video = this.video.webUi();
    const search = this.searchService.webUi();
    return {
      panels: [...(search.panels ?? []), ...(cfg.video.enabled ? video.panels ?? [] : [])],
      invoke: (panel, method, args) => panel === 'search' ? search.invoke!(panel, method, args) : video.invoke!(panel, method, args),
      lamps: [this.lamp(), ...(cfg.video.enabled ? video.lamps ?? [] : [])],
      badges: [
        { label: '浏览器', value: this.browserLabel || displayBrowser(cfg.browser) || '未配置', tone: 'plain' },
        ...(this.own
          ? [{ label: '她的浏览器', value: `127.0.0.1:${cfg.ownBrowserPort}`, tone: 'plain' as const }]
          : []),
        { label: 'proxy', value: `127.0.0.1:${cfg.port}`, tone: 'plain' },
        { label: '她开的页', value: this.mine.size, tone: 'plain' },
      ],
      config: [BROWSER_CONFIG_GROUP, ...(search.config ?? []), ...(video.config ?? [])],
      promptDocs: [
        {
          key: 'worlds.browser.envPrompt',
          title: 'Browser · 环境提示词',
          description: '这个浏览器这一段进 system 前缀的说明；留空则该 World 不进入前缀。',
          path: ENV_PROMPT_FILE,
          role: 'envPrompt',
          vars: [
            { name: 'browser.label', description: '当前配置要操作的浏览器。' },
            { name: 'browser.front', description: '页面所在窗口与可见性。' },
            { name: 'bilibiliVideo.identity', description: '共享 profile 的 B 站身份。' },
            { name: 'bilibiliVideo.state', description: '绑定视频页与播放状态。' },
            { name: 'bilibiliVideo.intervalSec', description: '最短观察间隔，秒。' },
            { name: 'bilibiliVideo.stallSec', description: '卡顿判据，秒。' },
            { name: 'browser.videoEnabled', description: 'B 站视频模块是否启用。' },
            { name: 'browser.kind', description: '那是她自己的实例，还是操作员日常那个。' },
          ],
        },
      ],
    };
  }

  async start(host: WorldHost): Promise<void> {
    this.searchService.start();
    this.host = host;
    this.running = true;
    if (this.opts.cfg.video.enabled) await this.video.start(host);
    const log = host.log.child(this.id);
    try {
      // 配了专属实例：先保证它在跑，并把发现文件写出来——上游的 proxy 就是靠那个文件认出它的。
      if (this.own) {
        const ownProblem = await this.own.ensure(log, this.opts.cfg.readyTimeoutMs);
        if (ownProblem) {
          this.state = 'failed';
          this.lastError = ownProblem;
          log.warn('她自己的浏览器起不来', { error: ownProblem });
          await this.emit(
            'browser.down',
            `浏览器起不来：${ownProblem}。（看 worlds.browser.ownBrowserExe 与 ownBrowserHome 配得对不对。）`,
          );
          return;
        }
      }

      const health = await this.relay.probe();
      if (health) {
        this.browserLabel = health.browserLabel || health.browserId;
        if (await this.relay.reachable()) {
          const wrongTarget = await this.ownTargetProblem(health);
          if (wrongTarget) {
            this.state = 'failed';
            this.lastError = wrongTarget;
            log.warn('proxy 连的不是她那个实例', { error: wrongTarget });
            await this.emit('browser.down', `浏览器不可用：${wrongTarget}`);
            return;
          }
          this.state = 'ready';
          log.info('复用已在运行的 cdp-proxy', { endpoint: this.relay.endpoint(), browser: this.browserLabel });
          await this.emit(
            'browser.ready',
            `浏览器已就绪（复用了已在运行的 proxy，${this.relay.endpoint()}，${this.browserLabel || '浏览器未识别'}）。`,
          );
          return;
        }
        // 端口上已经有 proxy 了，但浏览器没接上。不再拉起一个去抢端口。
        this.state = 'failed';
        this.lastError = '已经有一个 proxy 在跑，但它没连上浏览器';
        log.warn('复用的 proxy 没连上浏览器');
        await this.emit('browser.down', `浏览器不可用：${this.lastError}。${this.connectHint()}`);
        return;
      }

      this.state = 'starting';
      const portProblem = await this.relay.checkPort();
      if (portProblem) {
        this.state = 'failed';
        this.lastError = portProblem;
        log.warn('这个端口用不了，不拉了', { error: portProblem });
        await this.emit('browser.down', `浏览器起不来：${portProblem}${this.connectHint()}`);
        return;
      }
      if (!this.relay.spawnProxy(log)) {
        this.state = 'failed';
        this.lastError = this.relay.failure;
        await this.emit('browser.down', `浏览器起不来：${this.lastError}。${this.connectHint()}`);
        return;
      }
      if (!(await this.waitReady(this.opts.cfg.readyTimeoutMs))) {
        this.state = 'failed';
        this.lastError = this.relay.failure || '等它连上浏览器超时';
        log.warn('cdp-proxy 没能连上浏览器', { error: this.lastError });
        await this.emit('browser.down', `浏览器没能就绪：${this.lastError}。${this.connectHint()}`);
        return;
      }
      const wrongTarget = await this.ownTargetProblem();
      if (wrongTarget) {
        this.state = 'failed';
        this.lastError = wrongTarget;
        log.warn('proxy 连的不是她那个实例', { error: wrongTarget });
        await this.emit('browser.down', `浏览器不可用：${wrongTarget}`);
        return;
      }
      this.state = 'ready';
      log.info('浏览器已就绪', { endpoint: this.relay.endpoint(), browser: this.browserLabel });
      await this.emit('browser.ready', `浏览器已就绪（${this.relay.endpoint()}，${this.browserLabel || displayBrowser(this.opts.cfg.browser)}）。`);
    } catch (err) {
      this.state = 'failed';
      this.lastError = describe(err);
      log.error('启动 Browser World 时出错', err);
    }
  }

  async stop(): Promise<void> {
    this.searchService.stop();
    this.running = false;
    await this.video.stop();
    await this.relay.stop(); // 只关自己拉起的那个
    this.own?.stop(); // 同理：复用的那个实例不动它
    this.state = 'idle';
    this.host = null;
    this.seen.clear();
    this.seenAt = 0;
    this.recoveryTried = false;
  }

  /**
   * 配了专属实例时，核对 proxy 连的**确实是那个实例**。
   *
   * 会走神的情形：他刚把 `ownBrowser` 打开，而端口上还挂着一个老的 proxy（连着他日常那个 Edge）。
   * 那种情况下这个 World 会静默地去操作他的浏览器——正是我们想离开的东西，必须当场说清。
   * 拿不到 `/health` 时不算这里的问题：工具那条路自己会报。
   */
  private async ownTargetProblem(health?: RelayHealth | null): Promise<string | null> {
    if (!this.own) return null;
    const info = health ?? (await this.relay.probe());
    if (!info) return null;
    if (info.chromePort > 0 && info.chromePort !== this.opts.cfg.ownBrowserPort) {
      const who = info.browserLabel || info.browserId || '未识别';
      const flag = info.browserId ? `--browser ${info.browserId}` : '--browser …';
      return (
        `proxy 连的是端口 ${info.chromePort} 上的浏览器（${who}），不是她自己的那个（${this.opts.cfg.ownBrowserPort}）。` +
        `多半是端口 ${this.opts.cfg.port} 上还挂着一个上一次运行留下的 cdp-proxy（它的命令行里带 \`${flag}\`）：` +
        '把那个 node 进程停掉就行——停掉之后这个 World 下次工具调用会自己把 proxy 补拉回来，不必再重启。' +
        '（如果那是操作员或他的 coding agent 自己起的 proxy，就别动它：把 worlds.browser.port 换一个。）'
      );
    }
    return null;
  }

  // ——— 状态与轮询 ———

  private async waitReady(timeoutMs: number): Promise<boolean> {
    const deadline = Date.now() + Math.max(1000, timeoutMs);
    while (Date.now() < deadline) {
      if (await this.relay.reachable(READY_POLL_MS * 2)) return true;
      if (!this.running) return false;
      await sleep(READY_POLL_MS);
    }
    return false;
  }

  /**
   * 与她上次问的时候比：他新开了、转到、关掉了哪些页面。
   *
   * 这个 World 自己**不定时看任何东西**——她想知道他在干什么，调一次 `browser_tabs` 就是问一次。
   * 因此报的是「自你上次看以来」的净变化：中间开了又关的页面看不见，那不是做不到，是没在采样。
   */
  private collectChanges(targets: readonly PageTarget[]): { changes: PageChange[]; sinceMs: number } {
    const first = this.seenAt === 0;
    const changes: PageChange[] = [];
    const present = new Set<string>();
    for (const target of targets) {
      present.add(target.targetId);
      const previous = this.seen.get(target.targetId);
      if (previous && previous.url === target.url && previous.title === target.title) continue;
      this.seen.set(target.targetId, { url: target.url, title: target.title });
      // 第一次看没有可比的东西；她自己开的页面不是他的动向。
      if (first || this.mine.has(target.targetId) || INTERNAL_URL.test(target.url)) continue;
      changes.push({ kind: previous ? 'moved' : 'opened', label: labelOf({ url: target.url, title: target.title }) });
    }
    for (const [targetId, page] of [...this.seen]) {
      if (present.has(targetId)) continue;
      this.seen.delete(targetId);
      if (first || this.mine.has(targetId) || INTERNAL_URL.test(page.url)) continue;
      changes.push({ kind: 'closed', label: labelOf(page) });
    }
    const sinceMs = this.seenAt === 0 ? 0 : Date.now() - this.seenAt;
    this.seenAt = Date.now();
    return { changes, sinceMs };
  }

  /** proxy 死了不会自己回来，而没有定时器在替我们看着。整场只补拉一次。 */
  private async tryRelaunch(): Promise<void> {
    const host = this.host;
    if (!host || this.recoveryTried || this.relay.owned || !this.opts.cfg.skillDir.trim()) return;
    this.recoveryTried = true;
    const log = host.log.child(this.id);
    const portProblem = await this.relay.checkPort();
    if (portProblem) {
      log.warn('端口用不了，不补拉了', { error: portProblem });
      return;
    }
    log.info('proxy 不在了，补拉一次');
    if (!this.relay.spawnProxy(log)) return;
    // 这是在一次工具调用里等，别把调用本身拖到超时。
    if (!(await this.waitReady(Math.min(4000, this.opts.cfg.readyTimeoutMs)))) {
      log.warn('补拉的 proxy 也没能连上浏览器');
    }
  }

  private lamp(): WorldLamp {
    switch (this.state) {
      case 'ready':
        return { label: '浏览器', state: 'online', hint: `${this.browserLabel || displayBrowser(this.opts.cfg.browser)} · ${this.relay.endpoint()}` };
      case 'starting':
        return { label: '浏览器', state: 'loading', hint: `${this.relay.endpoint()} · 等它连上浏览器` };
      case 'failed':
        return { label: '浏览器', state: 'error', hint: this.lastError || '连不上浏览器' };
      default:
        return { label: '浏览器', state: 'offline', hint: `${this.relay.endpoint()} · 未启动` };
    }
  }

  private async emit(type: string, text: string): Promise<void> {
    const host = this.host;
    if (!host) return;
    try {
      await host.pushEvent({
        type,
        ts: nowIso(this.opts.timezone),
        source: this.id,
        origin: 'internal',
        senderKey: this.id,
        text,
      });
    } catch {
      // 投递失败不该把 World 自己带崩
    }
  }

  private connectHint(): string {
    if (/CDP 命令超时|不回话|连接.*失效/.test(this.lastError)) {
      return '（这不是调试开关的问题：连接曾经建立过，是浏览器那一侧不再应答。' +
        '先按「连接层半死」处理：重启 cdp-proxy，仍然不行再重启 Coopanion。）';
    }
    if (/端口/.test(this.lastError)) {
      return '（换一个没被占用的 worlds.browser.port：Windows 保留的端口段会报 EACCES。）';
    }
    if (this.own) {
      return (
        '（这是她自己那个实例，不是操作员日常的浏览器：看 ownBrowserExe / ownBrowserHome 配得对不对，' +
        `或它是不是被关掉了、端口 ${this.opts.cfg.ownBrowserPort} 上有没有别的东西。）`
      );
    }
    const browser = this.opts.cfg.browser.trim() || 'chrome';
    return (
      `（要在${displayBrowser(browser)}的地址栏打开 ${browser}://inspect/#remote-debugging，` +
      '勾选「Allow remote debugging for this browser instance」。）'
    );
  }

  /**
   * 把一个 tab 搬到操作员眼前（窗口搬回屏幕内 + 激活）。只在有专属实例时做：
   * 那时候带上来的是**她自己的窗口**；借他日常那个浏览器时不给这个能力（那会抢他正在用的窗口）。
   *
   * 这是"她想让他看"的动作，不是默认行为——平时她的窗口在屏幕外，媒体照样播、也不打扰他。
   */
  private async show(targetId: string): Promise<{ visibility: string; raise: RaiseResult } | { error: string } | null> {
    if (!this.own) return null;
    try {
      return await showTarget(this.opts.cfg.ownBrowserPort, targetId, Math.min(5000, this.timeout()));
    } catch (err) {
      return { error: describe(err) };
    }
  }

  /**
   * 专属模式下开页：建**一个她自己的窗口**装这一页（不激活、屏幕外）。
   *
   * 为什么不用上游的 `/new`：它建的是后台 tab，而量到过——后台 tab 里页面是 `hidden`、媒体**根本不加载**。
   * 页面在一个自己窗口里就足以让它是 `visible`、媒体照播，而且不抬窗口、不抢焦点。
   * 建不成时退回 `/new`（她仍然能读页，只是媒体播不了），并在回执里说明——别让一次失败变成没手可用。
   */
  private async newPage(
    url: string,
    timeoutMs: number,
    ctx: ToolCallContext,
  ): Promise<{ targetId: string; note: string }> {
    if (this.own) {
      try {
        const { targetId } = await createWindow(this.opts.cfg.ownBrowserPort, url, Math.min(timeoutMs, 5000));
        return { targetId, note: '' };
      } catch (err) {
        const targetId = await this.relay.openBlank(timeoutMs, ctx.signal);
        return {
          targetId,
          note: `（这次没能给她开独立窗口：${describe(err)}。退回了后台 tab —— 页面能读，但**媒体播不了**。）`,
        };
      }
    }
    return { targetId: await this.relay.openBlank(timeoutMs, ctx.signal), note: '' };
  }

  /** 任何带 `target` 的调用都记一笔"刚用过"，闲置回收靠这个时间戳。 */
  private async acquireVideoPage(requested?: string): Promise<{targetId: string; browserURL: string}> {
    const problem = await this.ensureReady();
    if (problem) throw new Error(problem);
    const health = await this.relay.probe();
    const port = health?.chromePort;
    if (!port || (this.own && port !== this.opts.cfg.ownBrowserPort)) throw new Error('proxy 未提供可核验的浏览器调试端口');
    let targetId = requested;
    if (targetId) {
      const page = (await this.relay.targets(this.timeout())).find(p => p.targetId === targetId);
      if (!page || !isBilibili(page.url)) throw new Error('指定 target 不存在或不是 B 站页面');
    } else {
      const created = await createWindow(port, 'about:blank', this.timeout());
      targetId = created.targetId;
      this.mine.set(targetId, Date.now());
      this.directPages.add(targetId);
    }
    return {targetId, browserURL: 'http://127.0.0.1:' + port};
  }

  private touch(targetId: string): void {
    if (!this.mine.has(targetId)) return;
    const now = Date.now();
    this.mine.set(targetId, now);
    // Borrowed-browser pages created by the proxy have a second idle clock there.
    if (!this.own && !this.directPages.has(targetId) && now - (this.proxyTouchedAt.get(targetId) ?? 0) >= 30_000) {
      this.proxyTouchedAt.set(targetId, now);
      void this.relay.info(targetId, 5000).catch(() => {});
    }
  }

  /**
   * 闲置回收：自己开的页面闲置超过 `tabIdleMinutes` 就关掉。
   *
   * 借他那个浏览器时这件事是上游 proxy 干的（它的 `managedTabs` + 每分钟扫一次）。但她的窗口是
   * **我们直连 CDP 建的**，上游不认识它们——不自己收就会一直堆着，所以这里补一份。
   * 走的是"每次工具调用顺便扫一眼"，不挂定时器（与这个 World「不定时看任何东西」一致）。
   */
  private sweepIdle(): void {
    const limit = Math.max(1, Math.round(this.opts.cfg.tabIdleMinutes * 60_000));
    const now = Date.now();
    for (const [target, usedAt] of [...this.mine]) {
      if (!this.own && !this.directPages.has(target)) continue;
      if (this.video.protects(target) || now - usedAt < limit) continue;
      this.mine.delete(target);
      this.directPages.delete(target);
      this.seen.delete(target);
      void this.video.mutateTarget(target, () => this.relay.close(target, 5000)).catch(() => {
        // 关不成就算了：下次调用还会再试一遍
      });
    }
  }

  private timeout(): number {
    return Math.max(3000, this.opts.cfg.requestTimeoutMs);
  }

  /** 导航那一段单独的超时：见 `NAV_TIMEOUT_MIN_MS` 的注释。 */
  private navTimeout(): number {
    return Math.max(this.timeout(), NAV_TIMEOUT_MIN_MS);
  }

  /**
   * 工具调用前的现查：状态可能是陈旧的，先探一次；还是不通就顺手补拉一次 proxy，
   * 再不通才报不可用。没有定时器在替她看着，所以补拉挂在这一条路上。
   *
   * **每一次转成 ready 都要过 `ownTargetProblem()`**（不只是 `start()` 那一次）：端口上挂着一个
   * 连别处的旧 proxy 时，它是**活的**，`/targets` 答得出来——只探活不看连的是谁，就会把它当成就绪，
   * 然后静默地去操作操作员的浏览器。这正是要防的那件事。
   */
  private async ensureReady(): Promise<string | null> {
    this.sweepIdle(); // 顺手把她闲置的窗口收掉（不挂定时器）；注意要在"已就绪就早退"之前
    if (this.state === 'ready') {
      // 已就绪 ≠ 还活着。连接层没有心跳（上游 send 超时只 reject、不改状态），
      // 半开的 socket 会让 /health 一直报 connected。这里带缓存复检一次，失败就退回 failed，
      // 让下面那条补拉路径（以及下一次调用的重连）有机会真正跑起来。
      if (Date.now() - this.readyProbedAt < READY_RECHECK_MS) return null;
      this.readyProbedAt = Date.now();
      if (await this.relay.reachable(Math.min(READY_RECHECK_TIMEOUT_MS, this.timeout()))) return null;
      this.state = 'failed';
      this.lastError = '连接在上一次调用之后失效了（浏览器不再应答）';
    }
    const settle = async (): Promise<string | null> => {
      const wrong = await this.ownTargetProblem();
      if (wrong) {
        this.state = 'failed';
        this.lastError = wrong;
        return `浏览器不可用：${wrong}`;
      }
      this.state = 'ready';
      this.lastError = '';
      this.readyProbedAt = Date.now();
      // 恢复成功就把"本场只补拉一次"的额度还回去：下次再断还能再试一次，
      // 不至于一次失败之后整场都失去补拉能力。
      this.recoveryTried = false;
      return null;
    };
    if (await this.relay.reachable(this.timeout())) return settle();
    await this.tryRelaunch();
    if (await this.relay.reachable(this.timeout())) return settle();
    const port = this.relay.endpoint();
    const reason = this.lastError || this.relay.failure || '没连上浏览器';
    return `浏览器不可用（${port}）：${reason}。${this.connectHint()}`;
  }

  // ——— 工具 ———

  tools(): ToolDef[] {
    const defs: ToolDef[] = [
      this.openTool(),
      this.searchTool(),
      { ...BROWSER_FETCH_TOOL, handler: (args, ctx) => this.searchService.fetchPage(args, ctx) },
      this.readTool(),
      this.jsTool(),
      this.clickTool(),
      this.typeTool(),
      this.uploadTool(),
      this.scrollTool(),
      this.shotTool(),
      this.navigateTool(),
      this.tabsTool(),
      this.focusTool(),
      this.closeTool(),
      this.findUrlTool(),
    ];
    // 一处挂钩：任何带 target 的调用都算"刚用过这个页面"。闲置回收（sweepIdle）靠这个时间戳，
    // 因为她的窗口是我们直连 CDP 建的、上游 proxy 不认识它们。
    if (this.opts.cfg.video.enabled) defs.push(...this.video.tools());
    return defs.map((def) => ({
      ...def,
      handler: async (args, ctx) => {
        try {
          const target = str(args.target);
          if (target) this.touch(target);
          if (target && (def.name === 'browser_navigate' || def.name === 'browser_close')) {
            if (def.name === 'browser_close' && !this.mine.has(target)) return await def.handler(args, ctx);
            return await this.video.mutateTarget(target, () => def.handler(args, ctx));
          }
          return await def.handler(args, ctx);
        } catch (err) {
          throw this.noteRelayFailure(err) ?? err;
        }
      },
    }));
  }

  /**
   * 把「连上了但不答」记成 failed，并给回执补一句人话。
   *
   * 上游 `send()` 超时只 reject 那一条命令、不改连接状态，所以这里看到的是
   * 「每次调用都卡 30 秒然后报 CDP 命令超时」，而 `state` 仍然是 ready。
   * 不在这里降级，`ensureReady()` 下次还会把它当成就绪，永远走不到补拉那一步。
   * 返回替换后的错误（调用方 throw 它）；不是这一类失败就返回 null。
   */
  private noteRelayFailure(err: unknown): Error | null {
    if (!(err instanceof RelayError)) return null;
    if (!/CDP 命令超时/.test(err.message)) return null;
    this.state = 'failed';
    this.lastError = `浏览器连着但不回话（${err.message}）`;
    return new RelayError(`${err.message}${RELAY_HALF_DEAD_HINT}`, err.status);
  }

  private openTool(): ToolDef {
    return { ...BROWSER_OPEN_TOOL, handler: async (args, ctx) => this.open(args, ctx) };
  }

  /**
   * 搜索：把关键词变成一批**地址**。
   *
   * 2026-10-12 加这一条，起因是她的原话：「浏览器给我的是打开这个地址、读正文，没有『搜』这一步，
   * 主题一模糊我就只剩猜域名、翻站内导航两条路。」所以这个工具回的不是一个页面正文，
   * 而是**能继续开的候选地址**——她拿到地址就用 `browser_open` 开，不点结果页上的链接。
   * 为什么不点：结果链接都是 `target=_blank`，程序化点击（`browser_click` 默认那条）开不出新页面，
   * 6 里量到过「JS 点击 → 新页面 0 个，真鼠标 → 1 个」；按地址开没有这一层。
   */
  private searchTool(): ToolDef {
    return { ...BROWSER_SEARCH_TOOL, handler: async (args, ctx) => this.search(args, ctx) };
  }

  private readTool(): ToolDef {
    return { ...BROWSER_READ_TOOL, handler: async (args, ctx) => this.read(args, ctx) };
  }

  private jsTool(): ToolDef {
    return { ...BROWSER_JS_TOOL, handler: async (args, ctx) => this.js(args, ctx) };
  }

  private clickTool(): ToolDef {
    return { ...BROWSER_CLICK_TOOL, handler: async (args, ctx) => this.click(args, ctx) };
  }

  private typeTool(): ToolDef {
    return { ...BROWSER_TYPE_TOOL, handler: async (args, ctx) => this.type(args, ctx) };
  }

  private uploadTool(): ToolDef {
    return { ...BROWSER_UPLOAD_TOOL, handler: async (args, ctx) => this.upload(args, ctx) };
  }

  private scrollTool(): ToolDef {
    return { ...BROWSER_SCROLL_TOOL, handler: async (args, ctx) => this.scroll(args, ctx) };
  }

  private shotTool(): ToolDef {
    return { ...BROWSER_SHOT_TOOL, handler: async (args, ctx) => this.shot(args, ctx) };
  }

  private navigateTool(): ToolDef {
    return { ...BROWSER_NAVIGATE_TOOL, handler: async (args, ctx) => this.navigate(args, ctx) };
  }

  private tabsTool(): ToolDef {
    return { ...BROWSER_TABS_TOOL, handler: async () => this.tabs() };
  }

  /**
   * 把一个页面**搬到操作员眼前**（窗口从屏幕外搬回来 + 激活 + 抬到别人窗口之上）。
   *
   * 这不是"让页面能播"——量到过：页面在她自己的窗口里就是可见的、媒体照播，**不需要抬窗口、也不需要
   * 抢焦点**。它的语义是"她想让操作员看某样东西"，所以只在真的想让他看时用：它会把他的屏幕占住。
   * 回执里带**抬完之后量到的真实相对位置**：抬不成、或被独占全屏的程序挡着时会直说，别让她以为
   * "搬过去了"就等于"他看见了"（2026-10-01 之前就是这么栽的）。
   */
  private focusTool(): ToolDef {
    return { ...BROWSER_FOCUS_TOOL, handler: async (args) => this.focus(args) };
  }

  private closeTool(): ToolDef {
    return { ...BROWSER_CLOSE_TOOL, handler: async (args, ctx) => this.close(args, ctx) };
  }

  private findUrlTool(): ToolDef {
    return { ...BROWSER_FIND_URL_TOOL, handler: async (args, ctx) => this.findUrl(args, ctx) };
  }

  // ——— 工具实现 ———

  private async open(args: Record<string, unknown>, ctx: ToolCallContext): Promise<ToolOutcome> {
    const raw = str(args.url);
    if (!raw) return fail('url 是空的：给一个要打开的地址。');
    const notReady = await this.ensureReady();
    if (notReady) return fail(notReady);

    // ① 先建一个空白页，**拿到 id 就先认下来**——后面无论导航成不成，这个页面都认得出、关得掉，
    //    不会再留孤儿。专属模式下建的是"一个她自己的窗口"（不激活、屏幕外：媒体能播、不打扰他），
    //    借他日常那个浏览器时仍是后台 tab。
    let targetId: string;
    let openNote = '';
    try {
      const created = await this.newPage('about:blank', this.timeout(), ctx);
      targetId = created.targetId;
      openNote = created.note;
    } catch (err) {
      return fail(this.explain(err, 'open'));
    }
    this.mine.set(targetId, Date.now());

    // ② 再单独导航。这一段走 navTimeout()，比普通调用宽：站点打不通时上游要等它自己的 30 秒
    //    CDP 超时才回话，客户端卡在 30 秒上只会把真话挡在外面。
    try {
      await this.relay.navigate(targetId, withScheme(raw), this.navTimeout(), ctx.signal);
    } catch (err) {
      const told = this.explain(err, '导航', 'nav');
      const page = await this.dump(targetId, null, OPEN_TEXT_MAX, ctx, NAV_FAILED_DUMP_MS);
      return fail(
        `${told}\n` +
          `target: ${targetId} 这个页面还开着（多半是那个站点的问题）：你稍后可以再 browser_read 一次，或 browser_close 关掉它。` +
          (page.ok ? `\n它此刻显示的是：\n${renderPage(page.page, OPEN_TEXT_MAX)}` : ''),
      );
    }

    const page = await this.dump(targetId, null, OPEN_TEXT_MAX, ctx);
    if (!page.ok) return fail(`页面已打开（target ${targetId}），但没能读回内容：${page.text}`);
    return {
      text: [`已打开（target ${targetId}）。`, openNote, renderPage(page.page, OPEN_TEXT_MAX)]
        .filter((part) => part !== '')
        .join('\n'),
    };
  }

  /**
   * 搜索的实现：开结果页（和 `open` 同一条路：先建页认下来，再导航），
   * 然后注入抽取函数，把结果整理成一批地址。抽不到就把整页正文交回去——别让她空手。
   */
  private async search(args: Record<string, unknown>, ctx: ToolCallContext): Promise<ToolOutcome> {
    return this.searchService.search(args, ctx, (engine, searchCtx) => this.searchPage(args, engine, searchCtx));
  }

  private async searchPage(args: Record<string, unknown>, engine: SearchEngineId, ctx: ToolCallContext): Promise<ToolOutcome> {
    const query = str(args.query);
    const count = clampCount(typeof args.count === 'number' ? args.count : undefined);
    const notReady = await this.ensureReady();
    if (notReady) return fail(notReady);

    // 与 browser_open 同一套：先建空白页拿到 id（“认下来”），失败也不会留孤儿页面。
    let targetId: string;
    let openNote = '';
    try {
      const created = await this.newPage('about:blank', this.timeout(), ctx);
      targetId = created.targetId;
      openNote = created.note;
    } catch (err) {
      return fail(this.explain(err, '搜索'));
    }
    this.mine.set(targetId, Date.now());

    try {
      await this.relay.navigate(targetId, searchUrl(engine, query), this.navTimeout(), ctx.signal);
    } catch (err) {
      return fail(
        `${this.explain(err, '打开搜索结果页', 'nav')}\n` +
          `target: ${targetId} 这个页面还开着：你可以稍后 browser_read 一次，或 browser_close 关掉它。`,
      );
    }

    let harvested: unknown = null;
    try {
      const result = await this.relay.evaluate(targetId, searchExpression(engine, count), this.timeout(), ctx.signal);
      harvested = result.ok ? result.value : null;
    } catch {
      // 抽取这一发没回话不算失败：下面会退回整页正文。
      harvested = null;
    }
    const harvest = normalizeHarvest(harvested, engine);

    if (harvest && harvest.hits.length > 0) {
      return {
        text: [renderSearch(engine, query, harvest, { target: targetId }), openNote]
          .filter((part) => part !== '')
          .join('\n'),
      };
    }

    // 抽取没命中（引擎换了结构、或者它给了验证页）：退回整页正文，并说明这是退路。
    const empty = harvest ?? { anchors: 0, hits: [], title: '', url: searchUrl(engine, query) };
    const page = await this.dump(targetId, null, OPEN_TEXT_MAX, ctx);
    return {
      text: [
        renderSearch(engine, query, empty, { target: targetId, fallbackText: page.ok ? page.page.text : '' }),
        openNote,
      ]
        .filter((part) => part !== '')
        .join('\n'),
    };
  }

  private async read(args: Record<string, unknown>, ctx: ToolCallContext): Promise<ToolOutcome> {
    const target = str(args.target);
    if (!target) return fail('target 是空的：给 browser_open 或 browser_tabs 回的那个 target。');
    const notReady = await this.ensureReady();
    if (notReady) return fail(notReady);

    const selector = str(args.selector) || null;
    const maxChars = clampInt(args.maxChars, READ_TEXT_DEFAULT, 200, READ_TEXT_MAX);
    const page = await this.dump(target, selector, maxChars, ctx);
    if (!page.ok) return fail(page.text);
    return { text: renderPage(page.page, maxChars) };
  }

  private async js(args: Record<string, unknown>, ctx: ToolCallContext): Promise<ToolOutcome> {
    const target = str(args.target);
    const expression = str(args.expression);
    if (!target) return fail('target 是空的：给 browser_open 或 browser_tabs 回的那个 target。');
    if (!expression) return fail('expression 是空的：给一段要在页面里求值的 JS 表达式。');
    const notReady = await this.ensureReady();
    if (notReady) return fail(notReady);

    let result: EvalResult;
    try {
      result = await this.relay.evaluate(target, expression, this.timeout(), ctx.signal);
    } catch (err) {
      return fail(this.explain(err, 'eval'));
    }
    if (!result.ok) return fail(`页面里那句 JS 抛了错：\n${truncate(result.error, 2000)}`);
    return { text: `页面里求值的结果：\n${renderValue(result.value, JS_VALUE_MAX)}` };
  }

  private async click(args: Record<string, unknown>, ctx: ToolCallContext): Promise<ToolOutcome> {
    const target = str(args.target);
    const selector = str(args.selector);
    if (!target) return fail('target 是空的：给 browser_open 或 browser_tabs 回的那个 target。');
    if (!selector) return fail('selector 是空的：给一个 CSS 选择器。');
    const notReady = await this.ensureReady();
    if (notReady) return fail(notReady);

    const native = args.native === true;
    // 点之前先记一眼页面表。结果页上的链接是 `target=_blank`，点下去新页面开在**别处**，
    // 而这个回执从前只说原页面「点击后此刻」——开出来那张她既看不见、也关不掉（不在她的页面表里）。
    // 2026-10-12 量到：JS 点击开不出新页，真鼠标那一下会开出来。
    const before = await this.relay.targets(this.timeout()).catch(() => null);
    try {
      const clicked = await this.relay.click(target, selector, native, this.timeout(), ctx.signal);
      const info = await this.relay.info(target, this.timeout(), ctx.signal).catch(() => null);
      const head = `已点击 ${native ? '（真实鼠标）' : ''}：${clicked.tag}${clicked.text ? ` 「${truncate(clicked.text, 80)}」` : ''}`;
      const tail = info ? `点击后此刻：${info.title || '(无标题)'} · ${info.url}（${info.ready}）` : null;
      const opened = await this.openedByClick(before);
      return { text: [head, tail, ...opened].filter((line): line is string => line !== null).join('\n') };
    } catch (err) {
      return fail(this.explain(err, 'click'));
    }
  }

  /**
   * 这次点击新开出来的页面，写进回执；有专属实例时**顺手登记成她的页**。
   *
   * 为什么登记要看 `ownBrowser`：借操作员日常那个浏览器时，两次快照之间也可能出现**他自己**开的
   * 页面，认成她的就等于将来替她把它关掉。专属实例里没有别人，那条一定成立。
   */
  private async openedByClick(before: readonly PageTarget[] | null): Promise<string[]> {
    if (!before) return [];
    const after = await this.relay.targets(this.timeout()).catch(() => null);
    if (!after) return [];
    const known = new Set(before.map((page) => page.targetId));
    const fresh = after.filter((page) => !known.has(page.targetId) && !INTERNAL_URL.test(page.url));
    const lines: string[] = [];
    for (const page of fresh) {
      if (this.own) this.mine.set(page.targetId, Date.now());
      const label = `${page.title || '(无标题)'} · ${page.url}\ntarget: ${page.targetId}`;
      lines.push(`点击开出了一张新页面（${label}）`);
    }
    if (lines.length === 0) return lines;
    lines.push(
      this.own
        ? '（那是你自己那个实例里的窗口，已经记成我开的：能 browser_read、能 browser_close，闲置也会被收掉。）'
        : '（他那个浏览器里新开的页面没有登记成我开的：不动它——两次快照之间也可能有他自己开的东西。' +
          '要读它就用 browser_open 按地址打开。）',
    );
    return lines;
  }

  private async type(args: Record<string, unknown>, ctx: ToolCallContext): Promise<ToolOutcome> {
    const target = str(args.target);
    const selector = str(args.selector);
    const value = typeof args.value === 'string' ? args.value : '';
    if (!target) return fail('target 是空的：给 browser_open 或 browser_tabs 回的那个 target。');
    if (!selector) return fail('selector 是空的：给一个 CSS 选择器。');
    const notReady = await this.ensureReady();
    if (notReady) return fail(notReady);

    let result: EvalResult;
    try {
      result = await this.relay.evaluate(
        target,
        typeExpression(selector, value, args.submit === true),
        this.timeout(),
        ctx.signal,
      );
    } catch (err) {
      return fail(this.explain(err, 'type'));
    }
    if (!result.ok) return fail(`页面里那句 JS 抛了错：\n${truncate(result.error, 2000)}`);
    const outcome = result.value as { ok?: unknown; error?: unknown; applied?: unknown; value?: unknown; submitted?: unknown };
    if (!outcome || outcome.ok !== true) {
      return fail(`没填进去：${typeof outcome?.error === 'string' ? outcome.error : '页面上没有这个元素'}`);
    }
    const applied = typeof outcome.applied === 'string' ? outcome.applied : '';
    const current = typeof outcome.value === 'string' ? outcome.value : '';
    const submitted = typeof outcome.submitted === 'string' ? `，已提交（${outcome.submitted}）` : '';
    return { text: `已填入（${applied}）：${truncate(current, 200)}${submitted}` };
  }

  private async upload(args: Record<string, unknown>, ctx: ToolCallContext): Promise<ToolOutcome> {
    const target = str(args.target);
    const selector = str(args.selector);
    const files = Array.isArray(args.files) ? args.files.filter((item): item is string => typeof item === 'string' && item.trim() !== '') : [];
    if (!target) return fail('target 是空的：给 browser_open 或 browser_tabs 回的那个 target。');
    if (!selector) return fail('selector 是空的：给 file input 的 CSS 选择器。');
    if (files.length === 0) return fail('files 是空的：给要上传的文件的绝对路径。');
    const notReady = await this.ensureReady();
    if (notReady) return fail(notReady);

    try {
      const count = await this.relay.setFiles(target, selector, files, this.timeout(), ctx.signal);
      return { text: `已给 ${selector} 挂上 ${count} 个文件：${files.join('、')}` };
    } catch (err) {
      return fail(this.explain(err, 'upload'));
    }
  }

  private async scroll(args: Record<string, unknown>, ctx: ToolCallContext): Promise<ToolOutcome> {
    const target = str(args.target);
    if (!target) return fail('target 是空的：给 browser_open 或 browser_tabs 回的那个 target。');
    const notReady = await this.ensureReady();
    if (notReady) return fail(notReady);

    const to = ['down', 'up', 'top', 'bottom'].includes(str(args.to)) ? str(args.to) : 'down';
    const y = clampInt(args.y, 3000, 0, 1_000_000);
    try {
      const said = await this.relay.scroll(target, { direction: to, y }, this.timeout(), ctx.signal);
      return { text: said || `已滚动（${to}）` };
    } catch (err) {
      return fail(this.explain(err, 'scroll'));
    }
  }

  private async shot(args: Record<string, unknown>, ctx: ToolCallContext): Promise<ToolOutcome> {
    const target = str(args.target);
    if (!target) return fail('target 是空的：给 browser_open 或 browser_tabs 回的那个 target。');
    const notReady = await this.ensureReady();
    if (notReady) return fail(notReady);

    try {
      const bytes = await this.relay.screenshot(target, this.timeout(), ctx.signal);
      const info = await this.relay.info(target, this.timeout(), ctx.signal).catch(() => null);
      const where = info ? `${info.title || '(无标题)'} · ${info.url}` : `target ${target}`;
      return {
        text: `截图：${where}\n这是视口那一屏，不是整页；要看更下面的内容先 browser_scroll。`,
        blobs: [
          {
            bytes,
            mime: 'image/png',
            name: 'screenshot.png',
            fallbackText: '页面截图（视口）',
          },
        ],
      };
    } catch (err) {
      return fail(this.explain(err, 'screenshot'));
    }
  }

  private async navigate(args: Record<string, unknown>, ctx: ToolCallContext): Promise<ToolOutcome> {
    const target = str(args.target);
    if (!target) return fail('target 是空的：给 browser_open 或 browser_tabs 回的那个 target。');
    const back = args.back === true;
    const url = str(args.url);
    if (!back && !url) return fail('url 是空的：给一个要去的地址，或把 back 设成 true。');
    const notReady = await this.ensureReady();
    if (notReady) return fail(notReady);

    try {
      if (back) await this.relay.back(target, this.navTimeout(), ctx.signal);
      else await this.relay.navigate(target, withScheme(url), this.navTimeout(), ctx.signal);
      const info = await this.relay.info(target, this.timeout(), ctx.signal).catch(() => null);
      const where = info ? `${info.title || '(无标题)'} · ${info.url}（${info.ready}）` : '页面已响应';
      return { text: `${back ? '已后退' : '已导航'}：${where}` };
    } catch (err) {
      return fail(this.explain(err, '导航', 'nav'));
    }
  }

  private async tabs(): Promise<ToolOutcome> {
    const notReady = await this.ensureReady();
    if (notReady) return fail(notReady);
    let targets: PageTarget[];
    try {
      targets = await this.relay.targets(this.timeout());
    } catch (err) {
      return fail(this.explain(err, 'tabs'));
    }
    const { changes, sinceMs } = this.collectChanges(targets);
    // 专属实例里没有"别人"在浏览：变化段报的是她自己的页面，没有意义，索性不报。
    const own = this.own !== null;
    const head = targets.length === 0
      ? own
        ? '你自己的浏览器里现在没有打开的页面。'
        : '浏览器里现在没有打开的页面。'
      : own
        ? `你自己的浏览器里现在有 ${targets.length} 个页面：`
        : `浏览器里现在有 ${targets.length} 个页面：`;
    const lines = targets.map((target) => {
      const mine = this.mine.has(target.targetId) ? '（我开的）' : '';
      return `- ${target.title || '(无标题)'}${mine}\n  ${target.url}\n  target: ${target.targetId}`;
    });
    return {
      text: [head, ...lines, own ? '' : renderChanges(changes, sinceMs)]
        .filter((part) => part !== '')
        .join('\n'),
    };
  }

  private async close(args: Record<string, unknown>, ctx: ToolCallContext): Promise<ToolOutcome> {
    const target = str(args.target);
    if (!target) return fail('target 是空的：给 browser_open 回的那个 target。');
    if (!this.mine.has(target)) {
      return fail(
        `这个页面不是我开的，不关：${target}。` +
          '他自己开的页面里可能有没保存的东西。要我关请先用 browser_open 打开它。',
      );
    }
    const notReady = await this.ensureReady();
    if (notReady) return fail(notReady);

    try {
      await this.relay.close(target, this.timeout(), ctx.signal);
    } catch (err) {
      return fail(this.explain(err, 'close'));
    }
    this.mine.delete(target);
    this.seen.delete(target);
    return { text: `已关闭 ${target}。` };
  }

  private async focus(args: Record<string, unknown>, operator = false): Promise<ToolOutcome> {
    const target = str(args.target);
    if (!target) return fail('target 是空的：给 browser_open 或 browser_tabs 回的那个 target。');
    if (!this.own) {
      return fail(
        '这个 World 借的是操作员日常那个浏览器，不能把页面搬到他眼前：那会抢他正在用的窗口。' +
          '要这个能力，得给她配一个她自己的浏览器实例（worlds.browser.ownBrowser）。',
      );
    }
    if (!operator && !this.opts.cfg.bringToFront) {
      return fail('worlds.browser.bringToFront 关着：操作员不想被打断，页面留在屏幕外。');
    }
    const result = await this.show(target);
    if (result === null) return fail('没能把它搬到他眼前。');
    if ('error' in result) {
      return fail(
        `把它搬到他眼前没成功：${result.error}。` +
          '如果是刚开出来的页面，多半是那个 target 已经不在了——用 browser_tabs 看一眼现在有哪些。',
      );
    }
    return {
      text:
        `已把 ${target} 搬到操作员眼前（document.visibilityState = ${result.visibility || '未知'}）。` +
        raiseSentence(result.raise),
    };
  }

  private async findUrl(args: Record<string, unknown>, ctx: ToolCallContext): Promise<ToolOutcome> {
    const skillDir = this.opts.cfg.skillDir.trim();
    if (!skillDir) return fail('worlds.browser.skillDir 没配：找不到 find-url.mjs。');
    if (!existsSync(join(skillDir, 'scripts', 'find-url.mjs'))) {
      return fail(`${skillDir}\\scripts 里没有 find-url.mjs：这个工具要 web-access 2.5.0 起才带。`);
    }
    const argv: string[] = [];
    if (Array.isArray(args.keywords)) {
      for (const word of args.keywords) {
        if (typeof word === 'string' && word.trim() !== '') argv.push(word.trim());
      }
    }
    const only = str(args.only);
    if (only === 'bookmarks' || only === 'history') argv.push('--only', only);
    const browser = str(args.browser);
    if (browser === 'chrome' || browser === 'edge') argv.push('--browser', browser);
    if (typeof args.limit === 'number' && Number.isFinite(args.limit)) argv.push('--limit', String(Math.round(args.limit)));
    const since = str(args.since);
    if (since) argv.push('--since', since);
    const sort = str(args.sort);
    if (sort === 'recent' || sort === 'visits') argv.push('--sort', sort);

    // 这个脚本要看他的书签库与历史库，跟页面无关，所以不走 proxy 的请求超时。
    ctx.signal?.throwIfAborted();
    const result = await runFindUrl(skillDir, argv, FIND_URL_TIMEOUT_MS);
    if (!result.ok) return fail(`书签历史检索没成功：\n${truncate(result.output, 2000)}`);
    return { text: result.output.trim() || '没有匹配的书签或历史记录。' };
  }

  // ——— 读页 ———

  /** 读一个页面。失败时给出一句能放进回执的话。 */
  private async dump(
    target: string,
    selector: string | null,
    maxChars: number,
    ctx: ToolCallContext,
    timeoutMs = this.timeout(),
  ): Promise<{ ok: true; page: PageDump } | { ok: false; text: string }> {
    let result: EvalResult;
    try {
      result = await this.relay.evaluate(target, readExpression(selector, maxChars), timeoutMs, ctx.signal);
    } catch (err) {
      return { ok: false, text: this.explain(err, 'read') };
    }
    if (!result.ok) return { ok: false, text: `读这个页面时页面里抛了错：\n${truncate(result.error, 2000)}` };
    const page = result.value as Partial<PageDump> | null;
    if (!page || typeof page !== 'object') return { ok: false, text: '读回来的不是页面内容。' };
    if (typeof page.error === 'string') return { ok: false, text: `没读到：${page.error}` };
    return {
      ok: true,
      page: {
        title: typeof page.title === 'string' ? page.title : '',
        url: typeof page.url === 'string' ? page.url : '',
        ready: typeof page.ready === 'string' ? page.ready : '',
        text: typeof page.text === 'string' ? page.text : '',
        links: Array.isArray(page.links) ? page.links.filter(isLink) : [],
        truncated: page.truncated === true,
      },
    };
  }

  /**
   * 一句话解释失败，并按**哪一类**失败决定贴哪段话。
   *
   * 教训（2026-09-30）：那段「去开远程调试」原先无条件贴（`status === 0` 就贴），于是「站点打不开」
   * 被念成「浏览器没连上」——bot 照着自己手里 `browser_tabs` 列得出 25 个页面这一点就矛盾了。
   * 现在只有「连不上 proxy」与「proxy 说浏览器没连上」才贴它；导航那一段（`step: 'nav'`）另有说法。
   */
  private explain(err: unknown, what: string, step: 'plain' | 'nav' = 'plain'): string {
    if (!(err instanceof RelayError)) return `${what} 没成功：${describe(err)}`;
    const kind: RelayFailureKind | 'nav' = step === 'nav' ? 'nav' : classifyRelayError(err);
    const tail =
      kind === 'unreachable' || kind === 'not-connected'
        ? ` ${this.connectHint()}`
        : kind === 'nav'
          ? ` ${NAV_UNANSWERED_HINT}`
          : kind === 'command-timeout'
            ? ` ${COMMAND_TIMEOUT_HINT}`
            : '';
    return `${what} 没成功（${FAILURE_LABEL[kind]}）：${err.message}${tail}`;
  }
}

// ——— 模块级小工具 ———

function renderPage(page: PageDump, maxChars: number): string {
  const head = `页面：${page.title || '(无标题)'}\n地址：${page.url}（${page.ready}）`;
  const body = page.text
    ? `正文${page.truncated ? `（被截到 ${maxChars} 字，要更多就再读一次并指定选择器）` : ''}：\n${page.text}`
    : '正文是空的：这一页的内容大概都在图片、画布或视频里，用 browser_shot 看一眼。';
  const links = page.links.length > 0
    ? `链接（${page.links.length} 条）：\n${page.links
        .slice(0, LINKS_SHOWN)
        .map((link) => `- ${truncate(link.text, 60)} → ${link.url}`)
        .join('\n')}`
    : '';
  return [head, body, links].filter((part) => part !== '').join('\n');
}

/** 变化那一段：只在他真的动了页面时出现，并且说清是「自你上次看以来」。 */
function renderChanges(changes: readonly PageChange[], sinceMs: number): string {
  if (changes.length === 0) return '';
  const shown = changes.slice(-CHANGES_MAX);
  const lines = shown.map((change) => `  ${KIND_VERB[change.kind]} ${change.label}`);
  const when = sinceMs > 0 ? `距你上次看约${elapsedText(sinceMs)}` : '自你上次看';
  const tail = changes.length > shown.length ? `  （另有 ${changes.length - shown.length} 条更早的）` : null;
  return [`[变化] ${when}：`, ...lines, tail].filter((line): line is string => line !== null).join('\n');
}

function elapsedText(ms: number): string {
  const minutes = Math.round(ms / 60_000);
  if (minutes < 1) return '不到一分钟';
  if (minutes < 60) return `${minutes} 分钟`;
  const hours = Math.round(minutes / 60);
  return hours < 24 ? `${hours} 小时` : `${Math.round(hours / 24)} 天`;
}

function renderValue(value: unknown, maxChars: number): string {
  if (typeof value === 'string') return truncate(value, maxChars);
  if (value === undefined) return '(undefined)';
  try {
    return truncate(JSON.stringify(value, null, 2) ?? String(value), maxChars);
  } catch {
    return truncate(String(value), maxChars);
  }
}

function isLink(item: unknown): item is { text: string; url: string } {
  return typeof item === 'object' && item !== null
    && typeof (item as { url?: unknown }).url === 'string';
}

/** 域名 + 标题，给变化那一段用。都不存在时退到 URL 本身。 */
function labelOf(page: SeenPage): string {
  const site = siteOf(page.url);
  const title = page.title.trim();
  if (site && title) return truncate(`${site}「${title}」`, 100);
  return truncate(title || site || page.url, 100);
}

function siteOf(url: string): string {
  try {
    const parsed = new URL(url);
    return parsed.host || parsed.protocol.replace(':', '');
  } catch {
    return url.slice(0, 60);
  }
}

/** 没写协议的补 https://：不然浏览器拿到的是相对地址。 */
function withScheme(url: string): string {
  return /^[a-z][a-z0-9+.-]*:/i.test(url) ? url : `https://${url}`;
}

function displayBrowser(id: string): string {
  switch (id.trim().toLowerCase()) {
    case 'chrome':
      return 'Chrome';
    case 'edge':
      return 'Edge';
    case 'chromium':
      return 'Chromium';
    default:
      return id.trim();
  }
}

function str(value: unknown): string {
  return typeof value === 'string' ? value.trim() : '';
}

function clampInt(value: unknown, fallback: number, min: number, max: number): number {
  if (typeof value !== 'number' || !Number.isFinite(value)) return fallback;
  return Math.min(max, Math.max(min, Math.round(value)));
}

function truncate(value: string, maxChars: number): string {
  if (value.length <= maxChars) return value;
  return `${value.slice(0, maxChars)}\n…（还有 ${value.length - maxChars} 字没显示）`;
}

function fail(message: string): ToolOutcome {
  return { text: `[browser] ${message}`, failed: true };
}

function describe(err: unknown): string {
  return err instanceof Error ? err.message : String(err);
}

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}
