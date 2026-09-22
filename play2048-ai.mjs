#!/usr/bin/env node
/**
 * play2048-ai.mjs —— 用 expectimax AI 自动操作 2048.html，一路玩到 2048 获胜
 * =============================================================================
 * 零依赖：只用 Node 内置模块 + 系统已安装的 Edge/Chrome（通过 DevTools 协议驱动）。
 *
 * 用法：
 *   node play2048-ai.mjs                 # 打开 2048.html，AI 自动玩到获胜
 *   node play2048-ai.mjs --sim           # 不开浏览器，直接驱动页面脚本（受限环境可用）
 *   node play2048-ai.mjs --head          # 显示浏览器窗口（默认无头）
 *   node play2048-ai.mjs --fast          # 加速模式：压缩动画等待，约 5 倍速
 *   node play2048-ai.mjs --bench 20      # 纯自我对弈 20 局，输出胜率与平均分
 *   node play2048-ai.mjs --selftest      # 校验 AI 走子模型与真实游戏规则一致
 *
 * 工作原理：
 *   1. 启动浏览器 → 用 CDP 打开 2048.html；
 *   2. 从 DOM 读取棋盘（每个 .tile 的 --x/--y 与文本值）；
 *   3. expectimax 搜索（含“随机生成方块”的概率节点）选出最优方向；
 *   4. 用 CDP Input.dispatchKeyEvent 发送真实方向键操作游戏；
 *   5. 出现 2048 即获胜；若这局走死了就自动重开，直到赢下为止。
 * =============================================================================
 */

import { spawn, spawnSync } from 'node:child_process';
import { existsSync, readFileSync, readdirSync, rmSync, mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const HERE = dirname(fileURLToPath(import.meta.url));
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const readdirSafe = (dir) => { try { return readdirSync(dir); } catch (e) { return []; } };

/* ===========================================================================
   1. 2048 核心模型
   ---------------------------------------------------------------------------
   棋盘用长度 16 的 Uint8Array 表示，每格存“指数”：0=空格，1=2，2=4 … 11=2048。
   指数编码让“数值翻倍”等于“指数 +1”，启发式函数里也天然是对数尺度。
   =========================================================================== */

const CELLS = 16;
const WIN_EXP = 11;          // 2^11 = 2048

/* --- 行查找表：把 4 格一行压成 16bit 键，预计算“向左合并”的结果与得分 ------ */
const ROW_LUT = new Uint16Array(65536);    // 键 -> 左移后的行
const ROW_GAIN = new Float64Array(65536);  // 键 -> 本次合并得分

(function buildRowLut() {
  for (let key = 0; key < 65536; key++) {
    const src = [key & 15, (key >> 4) & 15, (key >> 8) & 15, (key >> 12) & 15];
    const out = [];
    let gain = 0;
    let i = 0;
    while (i < 4) {
      const v = src[i];
      if (v === 0) { i++; continue; }        // 空格跳过
      let j = i + 1;
      while (j < 4 && src[j] === 0) j++;     // 找下一个非空格
      if (j < 4 && src[j] === v) {
        const nv = v + 1;                    // 数值翻倍 = 指数 +1
        out.push(nv);
        gain += Math.pow(2, nv);
        i = j + 1;                           // 同一个方块本回合不再参与合并
      } else {
        out.push(v);
        i = j;
      }
    }
    while (out.length < 4) out.push(0);
    ROW_LUT[key] = out[0] | (out[1] << 4) | (out[2] << 8) | (out[3] << 12);
    ROW_GAIN[key] = gain;
  }
})();

/** 第 line 条线（行或列）上、沿 dir 方向第 k 个格子的下标 */
function lineOrder(dir, line, k) {
  switch (dir) {
    case 0: return line * 4 + k;               // 左：从最左开始
    case 1: return line * 4 + (3 - k);         // 右：从最右开始
    case 2: return k * 4 + line;               // 上：从最上开始
    default: return (3 - k) * 4 + line;        // 下：从最下开始
  }
}

/**
 * 沿某个方向移动棋盘。
 * @param {Uint8Array} g   当前棋盘（只读，不会被修改）
 * @param {number} dir     0=左 1=右 2=上 3=下
 * @param {Uint8Array} out 结果写入这里（避免搜索时频繁分配内存）
 * @returns {number} 合并得分；若该方向没有任何方块移动则返回 -1（非法走法）
 */
function moveGrid(g, dir, out) {
  let gained = 0;
  let moved = false;
  for (let line = 0; line < 4; line++) {
    // 按“前进方向”取出这一行/列的 4 个格号，index 0 是移动的目标端
    const i0 = lineOrder(dir, line, 0);
    const i1 = lineOrder(dir, line, 1);
    const i2 = lineOrder(dir, line, 2);
    const i3 = lineOrder(dir, line, 3);
    const key = g[i0] | (g[i1] << 4) | (g[i2] << 8) | (g[i3] << 12);
    const packed = ROW_LUT[key];
    gained += ROW_GAIN[key];
    if (packed !== key) moved = true;
    out[i0] = packed & 15;
    out[i1] = (packed >> 4) & 15;
    out[i2] = (packed >> 8) & 15;
    out[i3] = (packed >> 12) & 15;
  }
  return moved ? gained : -1;
}

const DIR_NAMES = ['left', 'right', 'up', 'down'];
const DIR_KEYS = { left: 'ArrowLeft', right: 'ArrowRight', up: 'ArrowUp', down: 'ArrowDown' };

function emptyCellsOf(g, arr) {
  let n = 0;
  for (let i = 0; i < CELLS; i++) if (g[i] === 0) arr[n++] = i;
  return n;
}

function maxExp(g) {
  let m = 0;
  for (let i = 0; i < CELLS; i++) if (g[i] > m) m = g[i];
  return m;
}

function countEmpty(g) {
  let n = 0;
  for (let i = 0; i < CELLS; i++) if (g[i] === 0) n++;
  return n;
}

/** 随机生成一个新方块：90% 出 2，10% 出 4（与游戏内实现一致） */
function spawnTile(g, rnd) {
  const free = [];
  for (let i = 0; i < CELLS; i++) if (g[i] === 0) free.push(i);
  if (!free.length) return false;
  const spot = free[Math.floor(rnd() * free.length)];
  g[spot] = rnd() < 0.9 ? 1 : 2;
  return true;
}

/* ===========================================================================
   2. 启发式评估函数
   ---------------------------------------------------------------------------
   几个经典维度，越高越好：
     empty   空格数        —— 留出腾挪空间，是最重要的生存指标
     mono    单调性        —— 行列数值尽量单向递增/递减，便于把大数挤到一角
     smooth  平滑度        —— 相邻数值差越小越好，便于将来合并
     merges  可合并对数    —— 相邻同值对数，直接奖励“马上能合”的局面
     maxE    最大方块指数  —— 鼓励养大数字
   另外给“最大块贴角”额外奖励，这是 2048 能长期活下去的关键。
   =========================================================================== */

// 权重可用环境变量覆盖，便于调参与消融实验
const envNum = (name, def) => (process.env[name] !== undefined ? Number(process.env[name]) : def);
const W_EMPTY = envNum('AI_W_EMPTY', 2.7);
const W_MONO = envNum('AI_W_MONO', 1.0);
const W_SMOOTH = envNum('AI_W_SMOOTH', 0.1);
const W_MERGES = envNum('AI_W_MERGES', 0.5);
const W_MAX = envNum('AI_W_MAX', 1.0);
const W_CORNER = envNum('AI_W_CORNER', 0.6);
const DEAD_PENALTY = -1e6;

function heuristic(g) {
  let empty = 0;
  let maxE = 0;
  for (let i = 0; i < CELLS; i++) {
    const e = g[i];
    if (e === 0) empty++;
    else if (e > maxE) maxE = e;
  }

  // 平滑度 + 可合并对数：只遍历“右”和“下”两个方向即可覆盖所有相邻对
  let smooth = 0;
  let merges = 0;
  for (let y = 0; y < 4; y++) {
    for (let x = 0; x < 4; x++) {
      const i = y * 4 + x;
      const e = g[i];
      if (!e) continue;
      if (x < 3 && g[i + 1]) {
        smooth -= Math.abs(e - g[i + 1]);
        if (e === g[i + 1]) merges++;
      }
      if (y < 3 && g[i + 4]) {
        smooth -= Math.abs(e - g[i + 4]);
        if (e === g[i + 4]) merges++;
      }
    }
  }

  // 单调性：分别统计横向/纵向两个方向各自的“逆序程度”，各取较好的那个
  let hDown = 0, hUp = 0, vDown = 0, vUp = 0;
  for (let y = 0; y < 4; y++) {
    for (let x = 0; x < 3; x++) {
      const a = g[y * 4 + x], b = g[y * 4 + x + 1];
      if (a > b) hDown += b - a; else hUp += a - b;
    }
  }
  for (let x = 0; x < 4; x++) {
    for (let y = 0; y < 3; y++) {
      const a = g[y * 4 + x], b = g[(y + 1) * 4 + x];
      if (a > b) vDown += b - a; else vUp += a - b;
    }
  }
  const mono = Math.max(hDown, hUp) + Math.max(vDown, vUp);

  // 最大方块是否待在四角
  const corner = Math.max(g[0], g[3], g[12], g[15]);
  const cornerBonus = (corner === maxE && maxE > 0) ? W_CORNER * maxE : 0;

  return W_EMPTY * empty + W_MONO * mono + W_SMOOTH * smooth +
         W_MERGES * merges + W_MAX * maxE + cornerBonus;
}

/* ===========================================================================
   3. Expectimax 搜索
   ---------------------------------------------------------------------------
   两类节点交替：
     max 节点（玩家）：在 4 个方向里选期望值最高的；
     chance 节点（游戏）：枚举“在哪个空格生成 2 还是 4”的所有可能，
                          按 0.9 / 0.1 的概率加权求平均。
   depth 只统计“玩家层”（每走一步减 1），chance 层不消耗深度。
   搜索缓冲区按层号复用，chance 层原地改格再还原，全程零分配。
   =========================================================================== */
const SCRATCH = Array.from({ length: 16 }, () => new Uint8Array(CELLS));
const ROOT_BUF = new Uint8Array(CELLS);   // 根节点专用，避免与搜索缓冲区互相覆盖
const EMPTY_BUF = new Int32Array(CELLS);
const PROB_CUTOFF = envNum('AI_PROB_CUTOFF', 1e-4);   // 概率太低的枝杈直接剪掉
const CHANCE_LIMIT = envNum('AI_CHANCE_LIMIT', 6);    // chance 节点最多枚举几个空格

/**
 * 自适应搜索深度：棋盘越挤越危险（也越容易死），但此时空格少、分支也少，
 * 加深深度的代价很低；棋盘很空时局面安全，浅一层即可。
 */
const ADAPTIVE = envNum('AI_ADAPTIVE', 1) !== 0;
const DEEP_AT = envNum('AI_DEEP_AT', 5);      // 空格 <= 5：深度 +1
const DEEPER_AT = envNum('AI_DEEPER_AT', 2);  // 空格 <= 2：深度 +2

function depthFor(g, base) {
  if (!ADAPTIVE) return base;
  const e = countEmpty(g);
  if (e <= DEEPER_AT) return base + 2;
  if (e <= DEEP_AT) return base + 1;
  return base;
}

function expectimax(g, depth, isPlayer, prob, level) {
  if (depth <= 0 || prob < PROB_CUTOFF) return heuristic(g);

  if (isPlayer) {
    const out = SCRATCH[level];
    let best = -Infinity;
    let any = false;
    for (let d = 0; d < 4; d++) {
      const gained = moveGrid(g, d, out);
      if (gained < 0) continue;                 // 该方向走不动
      any = true;
      const v = expectimax(out, depth - 1, false, prob, level + 1);
      if (v > best) best = v;
    }
    // 四个方向都走不动 = 死局
    return any ? best : DEAD_PENALTY;
  }

  // ---- chance 节点：枚举随机生成 ----
  const n = emptyCellsOf(g, EMPTY_BUF);
  if (n === 0) return heuristic(g);

  // 空格很多时按步长抽样，把分支数从 2n 压到 2*CHANCE_LIMIT。
  // 棋盘越空越安全，此时精确枚举收益很低；棋盘拥挤时 n 本来就不大，会全量枚举。
  const stride = Math.max(1, Math.ceil(n / CHANCE_LIMIT));
  let considered = 0;
  let sum = 0;
  for (let k = 0; k < n; k += stride) {
    const idx = EMPTY_BUF[k];
    const saved = g[idx];
    considered++;
    g[idx] = 1;                                  // 生成 2
    sum += 0.9 * expectimax(g, depth, true, prob * 0.9, level);
    g[idx] = 2;                                  // 生成 4
    sum += 0.1 * expectimax(g, depth, true, prob * 0.1, level);
    g[idx] = saved;                              // 还原，零分配
  }
  return sum / considered;
}

/**
 * 选出最优方向。并列最优时随机挑一个，避免固定套路走进死循环。
 * @returns {string|null} 'left' | 'right' | 'up' | 'down' | null(无路可走)
 */
function bestMove(g, depth, rnd = Math.random) {
  const d = depthFor(g, depth);        // 同一根节点下所有分支用同一深度，保证可比
  let best = -Infinity;
  const bestDirs = [];
  for (let dd = 0; dd < 4; dd++) {
    const gained = moveGrid(g, dd, ROOT_BUF);    // moveGrid 会原地覆盖 ROOT_BUF
    if (gained < 0) continue;                    // 该方向走不动
    const v = expectimax(ROOT_BUF, d, false, 1.0, 0);
    if (v > best + 1e-9) { best = v; bestDirs.length = 0; bestDirs.push(dd); }
    else if (v > best - 1e-9) bestDirs.push(dd);
  }
  if (!bestDirs.length) return null;
  return DIR_NAMES[bestDirs[Math.floor(rnd() * bestDirs.length)]];
}

/* ===========================================================================
   4. 纯模拟自我对弈（用来测胜率）
   =========================================================================== */
function playGame(depth, rnd = Math.random, maxMoves = 20000) {
  const g = new Uint8Array(CELLS);
  spawnTile(g, rnd);
  spawnTile(g, rnd);
  let score = 0;
  let moves = 0;
  const buf = new Uint8Array(CELLS);

  while (moves < maxMoves) {
    const dir = bestMove(g, depth, rnd);
    if (!dir) return { won: false, dead: true, score, moves, max: maxExp(g) };
    const gained = moveGrid(g, DIR_NAMES.indexOf(dir), buf);
    if (gained < 0) return { won: false, dead: true, score, moves, max: maxExp(g) };
    score += gained;
    g.set(buf);
    moves++;
    if (maxExp(g) >= WIN_EXP) return { won: true, dead: false, score, moves, max: maxExp(g) };
    spawnTile(g, rnd);
    if (maxExp(g) >= WIN_EXP) return { won: true, dead: false, score, moves, max: maxExp(g) };
  }
  return { won: false, dead: false, timeout: true, score, moves, max: maxExp(g) };
}

/* ===========================================================================
   5. 自我校验：确认 AI 的走子模型与真实游戏规则完全一致
   （用例来自对 2048.html 实际行为的实测回归）
   =========================================================================== */
function selfTest() {
  const cases = [
    // name,                    棋盘(指数),       方向,     期望结果（null = 该方向走不动）
    ['两格合并', [[1, 1, 0, 0]], 'left', [[2, 0, 0, 0]]],
    ['两组分别合并', [[1, 1, 2, 2]], 'left', [[2, 3, 0, 0]]],
    ['四个相同两两合并', [[1, 1, 1, 1]], 'left', [[2, 2, 0, 0]]],
    ['禁止连锁合并 [2,2,4]', [[1, 1, 2, 0]], 'left', [[2, 2, 0, 0]]],
    ['大数不连锁 [4,4,4,4]', [[2, 2, 2, 2]], 'left', [[3, 3, 0, 0]]],
    ['向右合并 [4,2,2]', [[2, 1, 1, 0]], 'right', [[0, 0, 2, 2]]],
    ['已满且相邻不等则走不动', [[1, 2, 1, 2]], 'right', null],
  ];
  let pass = 0, fail = 0;

  for (const [name, rows, dir, expect] of cases) {
    const g = new Uint8Array(CELLS);
    rows.forEach((row, y) => row.forEach((v, x) => { g[y * 4 + x] = v; }));
    const out = new Uint8Array(CELLS);
    const gained = moveGrid(g, DIR_NAMES.indexOf(dir), out);
    const got = [[out[0], out[1], out[2], out[3]]];
    const ok = expect === null
      ? gained < 0
      : (gained >= 0 && JSON.stringify(got) === JSON.stringify(expect));
    ok ? pass++ : fail++;
    const shown = gained < 0 ? '无移动(-1)' : JSON.stringify(got);
    console.log(`${ok ? '通过' : '失败'}  ${name} (${dir})  得到 ${shown}` +
      (ok ? '' : `  期望 ${expect === null ? '无移动(-1)' : JSON.stringify(expect)}`));
  }

  const vertical = [
    ['纵向向上', [1, 1, 2, 2], 'up', [2, 3, 0, 0]],
    ['纵向向下', [1, 1, 2, 2], 'down', [0, 0, 2, 3]],
    ['纵向下禁止连锁 [4,4,2]', [2, 2, 1, 0], 'down', [0, 0, 3, 1]],
  ];
  for (const [name, col, dir, want] of vertical) {
    const g = new Uint8Array(CELLS);
    col.forEach((v, y) => { g[y * 4] = v; });
    const out = new Uint8Array(CELLS);
    const gained = moveGrid(g, DIR_NAMES.indexOf(dir), out);
    const got = [out[0], out[4], out[8], out[12]];
    const ok = gained >= 0 && JSON.stringify(got) === JSON.stringify(want);
    ok ? pass++ : fail++;
    console.log(`${ok ? '通过' : '失败'}  ${name} (${dir})  得到 ${JSON.stringify(got)}` +
      (ok ? '' : `  期望 ${JSON.stringify(want)}`));
  }

  console.log(`\n自检结果：${pass} 通过 / ${fail} 失败`);
  return fail === 0;
}

/* ===========================================================================
   6. 浏览器自动化（DevTools 协议）
   =========================================================================== */
const BROWSER_CANDIDATES = [
  process.env.CHROME_PATH,
  process.env.EDGE_PATH,
  'C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe',
  'C:\\Program Files\\Microsoft\\Edge\\Application\\msedge.exe',
  'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe',
  'C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe',
  process.env.LOCALAPPDATA ? join(process.env.LOCALAPPDATA, 'Google/Chrome/Application/chrome.exe') : null,
  '/usr/bin/google-chrome', '/usr/bin/chromium', '/usr/bin/chromium-browser',
  '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
].filter(Boolean);

function findBrowser(explicit) {
  if (explicit) {
    if (!existsSync(explicit)) throw new Error('指定的浏览器不存在：' + explicit);
    return explicit;
  }
  for (const p of BROWSER_CANDIDATES) if (p && existsSync(p)) return p;
  throw new Error('未找到 Edge/Chrome，请用 --executable 指定浏览器路径');
}

/** 极简 CDP 客户端 */
class CDP {
  constructor(ws) {
    this.ws = ws;
    this.id = 0;
    this.pending = new Map();
    this.handlers = new Map();
    ws.addEventListener('message', (ev) => {
      const m = JSON.parse(ev.data);
      if (m.id && this.pending.has(m.id)) {
        const p = this.pending.get(m.id);
        this.pending.delete(m.id);
        m.error ? p.rej(new Error(JSON.stringify(m.error))) : p.res(m.result);
      } else if (m.method && this.handlers.has(m.method)) {
        this.handlers.get(m.method)(m.params);
      }
    });
  }
  send(method, params) {
    const id = ++this.id;
    return new Promise((res, rej) => {
      this.pending.set(id, { res, rej });
      this.ws.send(JSON.stringify({ id, method, params: params || {} }));
    });
  }
  once(method) {
    return new Promise((res) => {
      this.handlers.set(method, (p) => { this.handlers.delete(method); res(p); });
    });
  }
}

/** 读取页面里的棋盘状态（正在消失的方块不算） */
const STATE_EXPR = `(function () {
  var list = document.querySelectorAll('.tile');
  var tiles = [];
  for (var i = 0; i < list.length; i++) {
    var t = list[i];
    if (t.getAttribute('data-dead') === '1') continue;
    tiles.push([+t.style.getPropertyValue('--x'), +t.style.getPropertyValue('--y'), +t.textContent]);
  }
  var ov = document.getElementById('overlay');
  var card = document.getElementById('card');
  return JSON.stringify({
    tiles: tiles,
    score: +document.getElementById('scoreEl').textContent,
    modal: (ov && ov.classList.contains('show')) ? card.innerText.replace(/\\s+/g, ' ').trim() : null
  });
})()`;

const KEY_CODES = { ArrowLeft: 37, ArrowUp: 38, ArrowRight: 39, ArrowDown: 40 };

/** 用真实按键事件操作游戏 */
async function pressKey(cdp, dir) {
  const key = DIR_KEYS[dir];
  const vk = KEY_CODES[key];
  const base = { key, code: key, windowsVirtualKeyCode: vk, nativeVirtualKeyCode: vk };
  await cdp.send('Input.dispatchKeyEvent', { ...base, type: 'rawKeyDown' });
  await cdp.send('Input.dispatchKeyEvent', { ...base, type: 'keyUp' });
}

function gridFromTiles(tiles) {
  const g = new Uint8Array(CELLS);
  for (const [x, y, v] of tiles) {
    if (x >= 0 && x < 4 && y >= 0 && y < 4 && v > 0) g[y * 4 + x] = Math.round(Math.log2(v));
  }
  return g;
}

function renderGrid(g) {
  const lines = [];
  for (let y = 0; y < 4; y++) {
    const row = [];
    for (let x = 0; x < 4; x++) {
      const e = g[y * 4 + x];
      row.push(e ? String(2 ** e).padStart(4) : '   .');
    }
    lines.push('  ' + row.join(' '));
  }
  return lines.join('\n');
}

/* ===========================================================================
   6.5 无浏览器模式：把 2048.html 里的真实脚本装进一个最小 DOM 里直接驱动
   ---------------------------------------------------------------------------
   不重新实现游戏，而是把 2048.html 内联 <script> 原样取出执行，
   再通过它自己的 keydown 监听器“按键”操作 —— 跑的就是页面里那份真实逻辑。
   适用于无法启动浏览器的受限环境（CI / 沙箱）。
   =========================================================================== */
class StubEl {
  constructor(tag) {
    this.tagName = tag;
    this.children = [];
    this.parent = null;
    this.dataset = {};
    this._cls = new Set();
    this._text = '';
    this._html = '';
    this._fc = null;
    this._ev = {};
    this.offsetWidth = 0;
    this.onclick = null;
    const self = this;
    this.style = {
      _p: {},
      setProperty(k, v) { self.style._p[k] = String(v); },
      getPropertyValue(k) { return k in self.style._p ? self.style._p[k] : ''; },
      get fontSize() { return self.style._p.fontSize || ''; },
      set fontSize(v) { self.style._p.fontSize = v; },
    };
  }
  get className() { return [...this._cls].join(' '); }
  set className(v) { this._cls = new Set(String(v).split(/\s+/).filter(Boolean)); }
  get classList() {
    const s = this._cls;
    return {
      add: (...c) => c.forEach((x) => s.add(x)),
      remove: (...c) => c.forEach((x) => s.delete(x)),
      contains: (c) => s.has(c),
    };
  }
  get textContent() {
    if (this.children.length) return this.children.map((c) => c.textContent).join('');
    return this._text;
  }
  set textContent(v) { this._text = String(v); this.children = []; this._fc = null; }
  get innerText() { return this._html.replace(/<[^>]*>/g, ' ').replace(/\s+/g, ' ').trim(); }
  get innerHTML() { return this._html; }
  set innerHTML(v) {
    this._html = String(v);
    this.children = [];
    this._fc = null;
    if (v === '') return;
    // 游戏只会给方块写这一种结构，其余（弹窗）保留为文本即可
    const m = /^<div class="([^"]+)"><\/div>$/.exec(v);
    if (m) {
      const c = new StubEl('div');
      c.className = m[1];
      c.parent = this;
      this.children = [c];
      this._fc = c;
    }
  }
  get firstChild() { return this._fc || this.children[0] || null; }
  appendChild(c) {
    c.parent = this;
    this.children.push(c);
    if (!this._fc) this._fc = c;
    return c;
  }
  remove() {
    if (!this.parent) return;
    const i = this.parent.children.indexOf(this);
    if (i >= 0) this.parent.children.splice(i, 1);
    if (this.parent._fc === this) this.parent._fc = this.parent.children[0] || null;
  }
  setAttribute() {}
  addEventListener(type, fn) { this._ev[type] = fn; }
  querySelector(sel) { return findIn(this, sel) || new StubEl('div'); }
  querySelectorAll(sel) { const r = []; collectIn(this, sel, r); return r; }
}

function matches(el, sel) {
  if (sel.startsWith('.')) return el._cls.has(sel.slice(1));
  const m = /^\[data-act="([^"]+)"\]$/.exec(sel);
  if (m) return el.dataset.act === m[1];
  return false;
}
function findIn(root, sel) {
  for (const c of root.children) {
    if (matches(c, sel)) return c;
    const r = findIn(c, sel);
    if (r) return r;
  }
  return null;
}
function collectIn(root, sel, out) {
  for (const c of root.children) {
    if (matches(c, sel)) out.push(c);
    collectIn(c, sel, out);
  }
}

function makeStubDom() {
  const byId = new Map();
  const handlers = {};
  const store = new Map();

  const document = {
    documentElement: new StubEl('html'),
    createElement: (tag) => new StubEl(tag),
    getElementById(id) {
      if (!byId.has(id)) byId.set(id, new StubEl('div'));
      return byId.get(id);
    },
    querySelector: () => null,
    addEventListener(type, fn) { handlers[type] = fn; },
  };
  // 页面启动时会用到这些容器
  ['board', 'cells', 'tiles', 'scoreEl', 'bestEl', 'gamesEl', 'scoreBox',
   'overlay', 'card', 'themeBtn', 'newBtn', 'resetBtn', 'historyBtn']
    .forEach((id) => byId.set(id, new StubEl('div')));

  const window = { matchMedia: () => ({ matches: false }), addEventListener() {} };
  const localStorage = {
    getItem: (k) => (store.has(k) ? store.get(k) : null),
    setItem: (k, v) => { store.set(k, String(v)); },
  };
  return { document, window, localStorage, handlers, byId };
}

async function runSim(opts) {
  const gamePath = resolve(opts.file);
  if (!existsSync(gamePath)) throw new Error('找不到游戏文件：' + gamePath);
  const html = readFileSync(gamePath, 'utf8');
  const m = html.match(/<script>([\s\S]*?)<\/script>/);
  if (!m) throw new Error('2048.html 里找不到 <script> 段');

  console.log('游戏页 : ' + gamePath + '（无浏览器模式：直接执行页面脚本）');
  console.log('搜索深度: ' + opts.depth + (ADAPTIVE ? '（自适应：拥挤时自动加深）' : '') + '\n');

  const dom = makeStubDom();
  // setTimeout 同步执行：游戏每步的“结算”是 move() 的最后一句，
  // 同步跑掉它不改变任何逻辑，但省去了等待动画的 110ms。
  const setTimeoutSync = (fn) => { if (typeof fn === 'function') fn(); return 0; };

  const run = new Function(
    'document', 'window', 'localStorage', 'setTimeout', 'clearTimeout', m[1]
  );
  run(dom.document, dom.window, dom.localStorage, setTimeoutSync, () => {});

  const onKey = dom.handlers.keydown;
  if (typeof onKey !== 'function') throw new Error('页面脚本没有注册 keydown 监听，无法操作');

  const tilesEl = dom.byId.get('tiles');
  const cardEl = dom.byId.get('card');
  const scoreEl = dom.byId.get('scoreEl');
  const newBtn = dom.byId.get('newBtn');

  const readTiles = () => tilesEl.children
    .filter((t) => t.dataset.dead !== '1')
    .map((t) => [+t.style.getPropertyValue('--x'), +t.style.getPropertyValue('--y'), +t.textContent]);

  const t0 = Date.now();
  const games = [];

  for (let gameNo = 1; gameNo <= opts.maxGames; gameNo++) {
    if (gameNo > 1 && newBtn._ev.click) newBtn._ev.click();   // 点“新游戏”重开

    let moves = 0;
    let score = 0;
    let won = false;

    for (; moves < opts.maxMoves; moves++) {
      const g = gridFromTiles(readTiles());
      const best = maxExp(g);
      score = Number(scoreEl.textContent) || 0;

      if (best >= WIN_EXP) { won = true; break; }
      if (cardEl.innerText.includes('Game Over')) break;

      const dir = bestMove(g, opts.depth);
      if (!dir) break;

      // 像真人一样“按下方向键”，走页面自己的 keydown 处理流程
      onKey({ key: DIR_KEYS[dir], preventDefault() {}, metaKey: false, ctrlKey: false, altKey: false });
    }

    const maxNow = 2 ** maxExp(gridFromTiles(readTiles()));
    games.push({ game: gameNo, score, moves, won, max: maxNow });

    if (won) {
      return { won: true, moves, score, elapsed: Date.now() - t0, games,
               grid: gridFromTiles(readTiles()), modal: cardEl.innerText, max: maxNow };
    }
    console.log(`  第 ${gameNo} 局失败：得分 ${score}，最大 ${maxNow}，${moves} 步 —— 自动重开继续挑战`);
  }

  return { won: false, exhausted: true, games, moves: 0, score: 0, elapsed: Date.now() - t0, grid: null };
}

/* ===========================================================================
   7. 主流程：启动浏览器 → 自动操作 → 直到胜利
   =========================================================================== */

/**
 * 用一组启动参数尝试拉起浏览器，拿到 DevTools 端口就返回 { child, port }，否则返回 null。
 * 端口写成 0 表示让浏览器自选空闲端口，并把结果写进 profile 下的 DevToolsActivePort。
 */
async function tryLaunch(exe, flags, commonArgs, profile) {
  try { rmSync(profile, { recursive: true, force: true }); } catch (e) {}
  try { mkdirSync(profile, { recursive: true }); } catch (e) {}

  const child = spawn(exe, [...flags, ...commonArgs, 'about:blank'], { stdio: 'ignore' });
  let dead = false;
  child.on('exit', () => { dead = true; });
  child.on('error', () => { dead = true; });

  const portFile = join(profile, 'DevToolsActivePort');
  for (let i = 0; i < 40; i++) {
    if (existsSync(portFile)) {
      const first = readFileSync(portFile, 'utf8').split('\n')[0].trim();
      if (Number(first) > 0) return { child, port: Number(first) };
    }
    if (dead) break;
    await sleep(150);
  }
  try { killTree(child); } catch (e) {}
  await sleep(250);
  return null;
}

/**
 * Chromium 是多进程架构，child.kill() 只杀得掉主进程，渲染/GPU 等子进程会留下来
 * 占着 profile 目录。Windows 上用 taskkill /T 整棵树一起收掉。
 */
function killTree(child) {
  if (!child || !child.pid) return;
  if (process.platform === 'win32') {
    try { spawnSync('taskkill', ['/pid', String(child.pid), '/T', '/F'], { stdio: 'ignore' }); } catch (e) {}
  }
  try { child.kill('SIGKILL'); } catch (e) {}
}

async function runBrowser(opts) {
  const gamePath = resolve(opts.file);
  if (!existsSync(gamePath)) throw new Error('找不到游戏文件：' + gamePath);
  const gameUrl = 'file:///' + gamePath.replace(/\\/g, '/');

  const browserPath = findBrowser(opts.executable);
  // 每次用一个独立的 profile 目录：即使上一次异常退出、目录还被子进程锁着，
  // 也不会因为删不掉而启动失败。启动时顺手尽力清掉历史残留。
  const profile = join(HERE, `.ai2048-profile-${process.pid}`);
  try { rmSync(profile, { recursive: true, force: true }); } catch (e) { /* 锁着就换新的 */ }
  try { mkdirSync(profile, { recursive: true }); } catch (e) {}
  for (const name of readdirSafe(HERE)) {
    if (name.startsWith('.ai2048-profile') && name !== `.ai2048-profile-${process.pid}`) {
      try { rmSync(join(HERE, name), { recursive: true, force: true }); } catch (e) {}
    }
  }

  console.log('浏览器 : ' + browserPath);
  console.log('游戏页 : ' + gameUrl);
  console.log('搜索深度: ' + opts.depth + (ADAPTIVE ? '（自适应：拥挤时自动加深）' : '') +
    '   模式: ' + (opts.fast ? '加速' : '实时'));
  console.log('');

  const commonArgs = [
    '--remote-debugging-port=0',
    '--user-data-dir=' + profile,
    '--no-first-run', '--no-default-browser-check', '--disable-extensions',
    '--disable-background-networking', '--disable-sync', '--disable-crash-reporter',
    '--disable-features=Translate,MediaRouter', '--hide-scrollbars',
    '--window-size=520,940', '--disable-gpu',
  ];

  // 浏览器启动方式按顺序尝试：
  // 某些受限环境（沙箱 / CI）禁止创建命名管道，而 Chromium 的多进程 IPC 依赖命名管道，
  // 此时 --headless=new 会静默崩溃；退回“旧版无头 + 单进程”即可绕开。
  const strategies = opts.head
    ? [
        { label: '显示窗口', flags: ['--new-window'] },
        { label: '显示窗口 + 单进程', flags: ['--new-window', '--single-process'] },
      ]
    : [
        { label: '现代无头 --headless=new', flags: ['--headless=new'] },
        { label: '旧版无头 + 单进程', flags: ['--headless=old', '--single-process'] },
        { label: '现代无头 + 单进程', flags: ['--headless=new', '--single-process'] },
        { label: '现代无头 + 关闭沙箱', flags: ['--headless=new', '--no-sandbox'] },
      ];

  let child = null;
  let cdp = null;
  const killBrowser = () => killTree(child);
  process.on('SIGINT', () => { killBrowser(); process.exit(130); });

  try {
    // ---- 逐个尝试启动方式，直到拿到 DevTools 端口 ----
    let port = null;
    for (const s of strategies) {
      process.stdout.write('  启动浏览器：' + s.label + ' ... ');
      const r = await tryLaunch(browserPath, s.flags, commonArgs, profile);
      if (r) { child = r.child; port = r.port; console.log('成功'); break; }
      console.log('失败');
    }
    if (!port) {
      throw new Error('浏览器无法启动。可尝试 --head 显示窗口运行，或改用 --sim 无浏览器模式');
    }

    let wsUrl = null;
    for (let i = 0; i < 60 && !wsUrl; i++) {
      try {
        const res = await fetch(`http://127.0.0.1:${port}/json/list`);
        const list = await res.json();
        const page = list.find((t) => t.type === 'page');
        if (page && page.webSocketDebuggerUrl) wsUrl = page.webSocketDebuggerUrl;
      } catch (e) { /* 还没起来 */ }
      if (!wsUrl) await sleep(125);
    }
    if (!wsUrl) throw new Error('未能连接到浏览器页面');

    const ws = new WebSocket(wsUrl);
    await new Promise((res, rej) => {
      ws.addEventListener('open', res);
      ws.addEventListener('error', () => rej(new Error('WebSocket 连接失败')));
    });
    cdp = new CDP(ws);

    await cdp.send('Page.enable');
    await cdp.send('Runtime.enable');

    // 加速模式：把页面的 setTimeout 钳到 12ms 以内。
    // 只加快动画/结算的节奏，不改变任何游戏规则与 AI 拿到的信息。
    if (opts.fast) {
      await cdp.send('Page.addScriptToEvaluateOnNewDocument', {
        source: '(function(){var o=window.setTimeout;window.setTimeout=function(f,ms){' +
                'var a=[].slice.call(arguments,2);' +
                'return o.apply(window,[f,Math.min(ms||0,12)].concat(a));};})();'
      });
    }

    // ---- 反复开局，直到赢下一局为止 ----
    const games = [];
    let lastShot = null;

    for (let gameNo = 1; gameNo <= opts.maxGames; gameNo++) {
      const loaded = cdp.once('Page.loadEventFired');
      await cdp.send('Page.navigate', { url: gameUrl });
      await loaded;
      await sleep(opts.fast ? 200 : 500);

      // 页面自检：确认游戏真的加载出来了
      const probe = JSON.parse((await cdp.send('Runtime.evaluate', { expression: STATE_EXPR, returnByValue: true })).result.value);
      if (!probe.tiles.length) throw new Error('页面已打开但读不到任何方块，游戏可能没有正常加载');

      const r = await playOneBrowserGame(cdp, opts, gameNo);
      if (r.shot) lastShot = r.shot;
      games.push({ game: gameNo, score: r.score, moves: r.moves, won: !!r.won, max: r.max });
      if (r.won) return { ...r, games, shot: lastShot };
      if (r.stuck) return { ...r, games };

      console.log(`  第 ${gameNo} 局失败：得分 ${r.score}，最大 ${r.max}，${r.moves} 步 —— 自动重开继续挑战`);
    }

    return { won: false, exhausted: true, games, moves: 0, score: 0, elapsed: 0, grid: null };
  } finally {
    if (cdp) { try { cdp.ws.close(); } catch (e) {} }
    killBrowser();
    // Chromium 是多进程的，杀掉主进程后子进程可能还攥着 profile 里的文件，
    // 所以等一会儿再删，并且删不掉就重试几次，免得在工作目录里留下一大堆缓存。
    await sleep(400);
    for (let i = 0; i < 6; i++) {
      try { rmSync(profile, { recursive: true, force: true }); break; }
      catch (e) { await sleep(350); }
    }
  }
}

/** 在已打开的页面里玩一局，直到获胜 / 无路可走 / 步数上限 */
async function playOneBrowserGame(cdp, opts, gameNo) {
  const settle = opts.fast ? 26 : 150;
  const t0 = Date.now();
  let moves = 0;
  let score = 0;
  let stall = 0;
  let bestSeen = 0;      // 记录本局见过的最大方块，便于超时后如实汇报
  let lastShotAt = Date.now();

  for (; moves < opts.maxMoves; moves++) {
    const raw = await cdp.send('Runtime.evaluate', { expression: STATE_EXPR, returnByValue: true });
    if (typeof raw.result.value !== 'string') throw new Error('读取棋盘失败，页面结构可能已变化');
    const st = JSON.parse(raw.result.value);
    score = st.score;

    const g = gridFromTiles(st.tiles);
    const best = maxExp(g);
    if (best > bestSeen) bestSeen = best;

    // 胜利判定：棋盘上出现 2048
    if (best >= WIN_EXP) {
      await sleep(opts.fast ? 80 : 400);   // 等庆祝弹窗和动画播完
      let shot = null;
      if (opts.shots) {
        try {
          mkdirSync(opts.shots, { recursive: true });
          const cap = await cdp.send('Page.captureScreenshot', { format: 'png' });
          shot = join(opts.shots, `victory-${new Date().toISOString().replace(/[:.]/g, '-')}.png`);
          writeFileSync(shot, Buffer.from(cap.data, 'base64'));
        } catch (e) { shot = null; }
      }
      const raw2 = await cdp.send('Runtime.evaluate', { expression: STATE_EXPR, returnByValue: true });
      const st2 = JSON.parse(raw2.result.value);
      return { won: true, moves, score: st2.score, elapsed: Date.now() - t0, max: 2 ** WIN_EXP,
               grid: gridFromTiles(st2.tiles), modal: st2.modal, shot };
    }

    // 结束判定：游戏结束弹窗
    if (st.modal && /Game Over/i.test(st.modal)) {
      return { won: false, over: true, moves, score, elapsed: Date.now() - t0, grid: g, max: 2 ** best };
    }

    const dir = bestMove(g, opts.depth);
    if (!dir) {
      if (++stall > 40) return { won: false, stuck: true, moves, score, elapsed: Date.now() - t0, grid: g, max: 2 ** best };
      await sleep(settle);
      continue;
    }
    stall = 0;

    await pressKey(cdp, dir);
    await sleep(settle);

    if (moves % 25 === 0 || moves < 3) {
      const secs = ((Date.now() - t0) / 1000).toFixed(0);
      process.stdout.write(`\r  第 ${gameNo} 局 · 第 ${String(moves).padStart(4)} 步 | 得分 ${String(score).padStart(6)} | ` +
        `最大 ${2 ** best} | 空格 ${countEmpty(g)} | ${secs}s `);
    }

    // 演示用：每隔 --every 秒抓一张棋盘截图，方便回看 AI 的推进过程
    if (opts.every && Date.now() - lastShotAt >= opts.every * 1000) {
      lastShotAt = Date.now();
      try {
        mkdirSync(opts.shots, { recursive: true });
        const cap = await cdp.send('Page.captureScreenshot', { format: 'png' });
        const f = join(opts.shots, `frame-g${gameNo}-${String(moves).padStart(4, '0')}.png`);
        writeFileSync(f, Buffer.from(cap.data, 'base64'));
        process.stdout.write(`\n  [截图] 第 ${moves} 步 · 最大 ${2 ** best} · 得分 ${score} -> ${f}\n`);
      } catch (e) { /* 截图失败不影响对局 */ }
    }
  }

  return { won: false, timeout: true, moves, score, elapsed: Date.now() - t0, grid: null, max: 2 ** bestSeen };
}

/* ===========================================================================
   8. 命令行入口
   =========================================================================== */
function help() {
  console.log(`
用 expectimax AI 自动操作 2048，输了自动重开，直到赢下 2048。

  node play2048-ai.mjs [选项]

选项：
  --file <路径>       游戏 HTML（默认同目录 2048.html）
  --depth <n>         搜索深度（玩家层数），默认 3；越大越强也越慢
  --sim               无浏览器模式：直接执行 2048.html 的脚本并“按键”驱动
  --fast              加速模式：压缩游戏动画等待，约 5 倍（默认实时）
  --head              显示浏览器窗口（默认无头运行）
  --max-moves <n>     单局步数上限，默认 6000
  --max-games <n>     最多尝试几局（输了自动重开），默认 20
  --shots <目录>      截图保存目录，默认 ai-shots
  --every <秒>        每隔这么多秒抓一张棋盘截图（演示 / 延时摄影用，默认关闭）
  --executable <路径> 指定 Edge/Chrome 可执行文件
  --bench <n>         纯自我对弈 n 局，输出胜率与平均分（不打开游戏页面）
  --selftest          校验 AI 走子模型与真实游戏规则是否一致
  -h, --help          显示帮助

环境变量：AI_W_EMPTY / AI_W_MONO / AI_W_SMOOTH / AI_W_MERGES / AI_W_MAX / AI_W_CORNER
          AI_CHANCE_LIMIT / AI_ADAPTIVE / AI_DEEP_AT / AI_DEEPER_AT
          AI_DEBUG=1 打印错误堆栈
`);
}

function parseArgs(argv) {
  const o = {
    file: join(HERE, '2048.html'), depth: 3, fast: false, head: false, sim: false,
    maxMoves: 6000, maxGames: 20, shots: join(HERE, 'ai-shots'), executable: null,
    every: 0, bench: 0, selftest: false,
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--file') o.file = argv[++i];
    else if (a === '--depth') o.depth = Number(argv[++i]);
    else if (a === '--fast') o.fast = true;
    else if (a === '--sim') o.sim = true;
    else if (a === '--head') o.head = true;
    else if (a === '--max-moves') o.maxMoves = Number(argv[++i]);
    else if (a === '--max-games') o.maxGames = Number(argv[++i]);
    else if (a === '--shots') o.shots = argv[++i];
    else if (a === '--every') o.every = Number(argv[++i]);
    else if (a === '--no-shots') o.shots = null;
    else if (a === '--executable') o.executable = argv[++i];
    else if (a === '--bench') o.bench = Number(argv[++i] || 10);
    else if (a === '--selftest') o.selftest = true;
    else if (a === '-h' || a === '--help') { help(); process.exit(0); }
    else { console.error('未知参数：' + a); help(); process.exit(2); }
  }
  return o;
}

function reportGames(games) {
  if (games && games.length) {
    console.log('  对战记录：' + games.map((g) =>
      `第${g.game}局 ${g.score}分/最大${g.max}${g.won ? '(胜)' : ''}`).join('  '));
  }
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));

  if (opts.selftest) process.exit(selfTest() ? 0 : 1);

  if (opts.bench > 0) {
    console.log(`纯自我对弈基准：${opts.bench} 局，搜索深度 ${opts.depth}\n`);
    let wins = 0, totalScore = 0, totalMoves = 0;
    const t0 = Date.now();
    for (let i = 0; i < opts.bench; i++) {
      const r = playGame(opts.depth);
      if (r.won) wins++;
      totalScore += r.score;
      totalMoves += r.moves;
      console.log(`  第 ${String(i + 1).padStart(2)} 局：${r.won ? '达成 2048 成功' : '未达成'}  ` +
        `得分 ${String(r.score).padStart(6)}  最大 ${2 ** r.max}  ${r.moves} 步`);
    }
    const secs = (Date.now() - t0) / 1000;
    console.log(`\n胜率 ${wins}/${opts.bench} = ${(wins / opts.bench * 100).toFixed(1)}%   ` +
      `平均得分 ${(totalScore / opts.bench).toFixed(0)}   平均 ${(totalMoves / opts.bench).toFixed(0)} 步   ` +
      `耗时 ${secs.toFixed(1)}s（${(totalMoves / secs).toFixed(0)} 步/秒）`);
    process.exit(wins === opts.bench ? 0 : 1);
  }

  let result = null;
  try {
    result = opts.sim ? await runSim(opts) : await runBrowser(opts);
  } catch (err) {
    console.error('\n运行失败：' + err.message);
    if (process.env.AI_DEBUG) console.error(err.stack);
    if (!opts.sim) console.error('（若当前环境禁止浏览器启动，可改用：node play2048-ai.mjs --sim）');
    process.exit(1);
  }

  const secs = (result.elapsed / 1000).toFixed(1);
  console.log('\n');
  if (result.grid) console.log(renderGrid(result.grid) + '\n');

  if (result.won) {
    const n = result.games.length;
    console.log(`胜利！AI 成功合成 2048${n > 1 ? `（第 ${n} 局终于赢下）` : ''}`);
    console.log(`   本局步数 ${result.moves} | 得分 ${result.score} | 总耗时 ${secs}s`);
    reportGames(result.games);
    if (result.modal) console.log('   页面弹窗：' + result.modal);
    if (result.shot) console.log('   截图已保存：' + result.shot);
    process.exit(0);
  }

  if (result.exhausted) {
    console.log(`连输 ${result.games.length} 局仍未达成 2048（可用 --depth 4 提高棋力，或加大 --max-games）`);
    reportGames(result.games);
    process.exit(1);
  }
  if (result.over) { console.log('意外：AI 在获胜前已无路可走。' + (result.modal || '')); process.exit(1); }
  if (result.stuck) { console.log('意外：读取不到有效棋盘状态（页面结构可能变了）。'); process.exit(1); }
  console.log(`达到步数上限 ${opts.maxMoves} 仍未获胜，得分 ${result.score}。`);
  process.exit(1);
}

main();
