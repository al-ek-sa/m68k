const D = SCHEMA;
const FONT = '"IBM Plex Sans", "Segoe UI", Roboto, Helvetica, Arial, sans-serif';
const MONO = '"IBM Plex Mono", ui-monospace, Menlo, Consolas, monospace';
const COL = { data: "#7a1f45", addr: "#5b2a6e", ctrl: "#c2577f", stat: "#9a5a48" };
const PINK = ["#8c2350", "#55112e", "#2e0718"];
const CUC = ["#4a0d28", "#2a0616", "#2e0718"];
const INK = "#2a0f20";
const LIGHT = "#fde7f1";
const SIG = ["#f9d6e3", "#e591b2", "#b23a68"];
const STAT = ["#f6dcd5", "#5a2a24"];
const GLOW = "#ff4f9a";
const SEL = "#7b3fa0";
const BIT = { fill: "#fff0f6", stroke: "#c2185b", text: "#7a0f3d" };
const MBIT = { fill: "#f3e3fa", stroke: "#7b3fa0", text: "#4a1d66" };
const SPEED = 340;

const canvas = document.getElementById("c");
const ctx = canvas.getContext("2d");
const pctEl = document.getElementById("pct");
const stageEl = document.getElementById("stage");
const tipEl = document.getElementById("tip");
let scale = 1, ox = 0, oy = 0, dpr = 1, vw = 0, vh = 0, queued = false;
const MIN = 0.2, MAX = 8;

const BLOCK = Object.fromEntries(D.blocks.map(b => [b.id, b]));
const OUT_EDGES = {};
D.edges.forEach((e, i) => { (OUT_EDGES[e.s] = OUT_EDGES[e.s] || []).push(i); });
const SIG_EDGE = {};
D.edges.forEach((e, i) => { if (e.s.startsWith("s_")) SIG_EDGE[e.s] = i; });

const BASE = {
  PC: 0x100, MAR: 0, MDR: 0, TMP: 0, IR: "—", SR: "0000", OUT: "—", IN: "—", uPC: "fetch0",
  D0: 0, D1: 0, D2: 0, D3: 0, D4: 0, D5: 0, D6: 0, D7: 0,
  A0: 0, A1: 0, A2: 0, A3: 0, A4: 0, A5: 0, A6: 0, A7: 0x3f0
};
let state = { ...BASE };
const flash = {};

let prog = null, stepIdx = -1, phaseIdx = 0, phaseT = 0, phaseDur = 0, tracks = [];
let playing = false, running = false, speedMul = 1, lastTs = 0, pauseUntil = 0, finished = false;
let noteText = "";
let selected = null;

function hex(v, n) { return "0x" + (v >>> 0).toString(16).toUpperCase().padStart(n || 3, "0"); }
function fmtVal(k, v) {
  if (typeof v === "string") return v;
  if (k === "PC" || k === "MAR" || /^A\d$/.test(k)) return hex(v);
  if (/^D\d$/.test(k)) return Math.abs(v | 0) < 1000 ? String(v | 0) : hex(v);
  return (v >>> 0) >= 0x80 ? hex(v) : String(v);
}

function resize() {
  dpr = window.devicePixelRatio || 1;
  const r = canvas.getBoundingClientRect();
  vw = r.width; vh = r.height;
  canvas.width = Math.round(vw * dpr);
  canvas.height = Math.round(vh * dpr);
  draw();
}

function fit() {
  const pad = 16;
  const availH = vh - pad * 2;
  const s = Math.min((vw - pad * 2) / D.W, availH / D.H);
  scale = Math.max(MIN, Math.min(MAX, s));
  ox = (vw - D.W * scale) / 2;
  oy = pad + Math.max(0, (availH - D.H * scale) / 2);
  draw();
}

function zoomAt(f, cx, cy) {
  const ns = Math.max(MIN, Math.min(MAX, scale * f));
  const k = ns / scale;
  ox = cx - (cx - ox) * k;
  oy = cy - (cy - oy) * k;
  scale = ns;
  draw();
}

function draw() {
  if (queued) return;
  queued = true;
  requestAnimationFrame(render);
}

function grad(x, y, h, c) {
  const g = ctx.createLinearGradient(0, y, 0, y + h);
  g.addColorStop(0, c[0]);
  g.addColorStop(1, c[1]);
  return g;
}

function rrect(x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r);
  ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r);
  ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}

function text(lines, cx, cy, size, opts) {
  const o = opts || {};
  ctx.fillStyle = o.color || INK;
  ctx.font = (o.italic ? "italic " : "") + (o.bold ? "600 " : "400 ") + size + "px " + (o.mono ? MONO : FONT);
  ctx.textAlign = o.align || "center";
  ctx.textBaseline = "middle";
  const lh = size * 1.2;
  const y0 = cy - (lh * (lines.length - 1)) / 2;
  lines.forEach((l, i) => ctx.fillText(l, cx, y0 + i * lh));
}

function insideCU(b) {
  const cu = BLOCK.CU;
  return cu && b.kind !== "cu" && b.x >= cu.x && b.y >= cu.y && b.x + b.w <= cu.x + cu.w && b.y + b.h <= cu.y + cu.h;
}

function glowFor(id) {
  let g = 0;
  if (activeBlocks.has(id)) g = 1;
  const f = flash[id];
  if (f) {
    const age = (performance.now() - f) / 1400;
    if (age < 1) g = Math.max(g, 1 - age);
  }
  return g;
}

function box(b, c, radius, glowId) {
  const g = glowId ? glowFor(glowId) : 0;
  if (g > 0) {
    ctx.save();
    ctx.shadowColor = GLOW;
    ctx.shadowBlur = 18 * g;
  }
  ctx.fillStyle = grad(b.x, b.y, b.h, c);
  if (radius) rrect(b.x, b.y, b.w, b.h, radius); else { ctx.beginPath(); ctx.rect(b.x, b.y, b.w, b.h); }
  ctx.fill();
  if (g > 0) ctx.restore();
  ctx.lineWidth = g > 0 ? 1.2 + 1.3 * g : 1.2;
  ctx.strokeStyle = g > 0 ? GLOW : (c === PINK && insideCU(b) ? "#c45c8a" : c[2]);
  ctx.stroke();
}

const SIZE = { reg: 12, mem: 12, mux: 10, unit: 10, const: 9, sig: 10, status: 10 };
const VALUE_OF = { PC: "PC", MAR: "MAR", MDR: "MDR", TMP: "TMP" };

function drawBlock(b) {
  const k = b.kind;
  if (k === "junction") {
    ctx.fillStyle = activeBlocks.has(b.id) ? GLOW : "#8c2350";
    ctx.beginPath();
    ctx.arc(b.x + b.w / 2, b.y + b.h / 2, b.w / 2, 0, Math.PI * 2);
    ctx.fill();
    return;
  }
  if (k === "alu") {
    const g = glowFor("ALU");
    const ins = 0.2 * b.w;
    ctx.beginPath();
    ctx.moveTo(b.x, b.y);
    ctx.lineTo(b.x + b.w, b.y);
    ctx.lineTo(b.x + b.w - ins, b.y + b.h);
    ctx.lineTo(b.x + ins, b.y + b.h);
    ctx.closePath();
    ctx.save();
    if (g > 0) { ctx.shadowColor = GLOW; ctx.shadowBlur = 22 * g; }
    ctx.fillStyle = grad(b.x, b.y, b.h, PINK);
    ctx.fill();
    ctx.restore();
    ctx.lineWidth = g > 0 ? 2.5 : 1.4;
    ctx.strokeStyle = g > 0 ? GLOW : PINK[2];
    ctx.stroke();
    const op = currentAluOp();
    text(["ALU"], b.x + b.w / 2, b.y + b.h / 2 - (op ? 8 : 0), 16, { bold: true, color: LIGHT });
    if (op) text([op], b.x + b.w / 2, b.y + b.h / 2 + 14, 10, { color: "#ffb3d4", mono: true });
    return;
  }
  if (k === "cu") {
    box(b, CUC, 0);
    text(["Control Unit (microprogrammed)"], b.x + 8, b.y + 14, 12, { bold: true, align: "left", color: LIGHT });
    return;
  }
  if (k === "rf") {
    box(b, PINK, 0, "RF");
    text(["Register File"], b.x + b.w / 2, b.y + 18, 12, { bold: true, color: LIGHT });
    return;
  }
  if (k === "status") {
    const on = activeBlocks.has(b.id);
    ctx.fillStyle = on ? "#ffd1e4" : STAT[0];
    ctx.fillRect(b.x, b.y, b.w, b.h);
    if (on) { ctx.lineWidth = 1.5; ctx.strokeStyle = GLOW; ctx.strokeRect(b.x, b.y, b.w, b.h); }
    text(b.label.split("\n"), b.x + b.w / 2, b.y + b.h / 2, 10, { italic: true, color: STAT[1] });
    return;
  }
  if (k === "sig") {
    const on = activeSigs.has(b.label);
    if (on) {
      ctx.save();
      ctx.shadowColor = GLOW;
      ctx.shadowBlur = 14;
      ctx.fillStyle = "#ff7eb3";
      ctx.fillRect(b.x, b.y, b.w, b.h);
      ctx.restore();
      ctx.lineWidth = 1.5;
      ctx.strokeStyle = "#8a0f45";
      ctx.strokeRect(b.x, b.y, b.w, b.h);
      text([b.label], b.x + b.w / 2, b.y + b.h / 2, 10, { italic: true, bold: true, color: "#3a0018" });
    } else {
      ctx.globalAlpha = prog ? 0.55 : 1;
      box(b, SIG, 0);
      text([b.label], b.x + b.w / 2, b.y + b.h / 2, 10, { italic: true });
      ctx.globalAlpha = 1;
    }
    return;
  }
  box(b, PINK, k === "mux" ? 7 : 0, b.id);
  const cx = b.x + b.w / 2, cy = b.y + b.h / 2;
  if (b.id === "IR") {
    text(["IR"], cx, b.y + 15, 12, { bold: true, color: LIGHT });
    if (state.IR !== "—") text([state.IR], cx, b.y + 35, 9, { color: "#ffd1e4", mono: true });
    else text(["opcode · mode · src · dst · idx"], cx, b.y + 36, 8, { color: LIGHT });
    return;
  }
  if (VALUE_OF[b.id]) {
    text([b.label], cx, cy - 7, b.id === "TMP" ? 10 : 12, { bold: true, color: LIGHT });
    text([fmtVal(b.id, state[b.id])], cx, cy + 9, 9, { color: "#ffd1e4", mono: true });
    return;
  }
  if (b.id === "SR") {
    text(["SR  N Z V C"], cx, cy - 8, 10, { bold: true, color: LIGHT });
    text([state.SR.split("").join("   ")], cx + 14, cy + 9, 10, { color: "#ffd1e4", mono: true });
    return;
  }
  if (b.id === "UPC") {
    text(["μPC"], cx, cy - 6, 10, { bold: true, color: LIGHT });
    text([state.uPC], cx, cy + 7, 8, { color: "#ffd1e4", mono: true });
    return;
  }
  if (b.id === "OUT" || b.id === "IN") {
    const v = state[b.id];
    text(b.label.split("\n"), cx, cy - (v !== "—" ? 8 : 0), 12, { color: LIGHT });
    if (v !== "—") text(["= " + v], cx, cy + 16, 11, { color: "#ffd1e4", mono: true, bold: true });
    return;
  }
  text(b.label.split("\n"), cx, cy, SIZE[k] || 10, { bold: k === "reg", color: LIGHT });
}

function drawEdge(e, idx) {
  const lit = idx !== undefined && activeEdges.has(idx);
  const sel = idx !== undefined && !lit && selected && selected.edges.has(idx);
  const col = lit ? GLOW : sel ? SEL : COL[e.kind];
  const thick = e.kind === "data" || e.kind === "addr";
  const r = 5;
  ctx.globalAlpha = prog && !lit && !sel && idx !== undefined ? 0.35 : 1;
  ctx.strokeStyle = col;
  ctx.lineWidth = (thick ? 1.5 : 1) + (lit || sel ? 1.2 : 0);
  ctx.setLineDash(thick ? [] : [4, 3]);
  if ((lit || sel) && !thick) ctx.lineDashOffset = -performance.now() / 40;
  ctx.beginPath();
  ctx.moveTo(e.pts[0][0], e.pts[0][1]);
  for (let i = 0; i < e.pts.length - 1; i++) {
    const a = e.pts[i], b = e.pts[i + 1];
    const horiz = a[1] === b[1];
    const dir = horiz ? Math.sign(b[0] - a[0]) : Math.sign(b[1] - a[1]);
    const hops = (e.hops[i] || []).slice().sort((p, q) => horiz ? (p[0] - q[0]) * dir : (p[1] - q[1]) * dir);
    for (const [hx, hy] of hops) {
      if (horiz) {
        ctx.lineTo(hx - dir * r, hy);
        ctx.arc(hx, hy, r, dir > 0 ? Math.PI : 0, dir > 0 ? 0 : Math.PI, dir < 0);
      } else {
        ctx.lineTo(hx, hy - dir * r);
        ctx.arc(hx, hy, r, dir > 0 ? -Math.PI / 2 : Math.PI / 2, dir > 0 ? Math.PI / 2 : -Math.PI / 2, dir < 0);
      }
    }
    ctx.lineTo(b[0], b[1]);
  }
  ctx.stroke();
  ctx.setLineDash([]);
  ctx.lineDashOffset = 0;
  if (!e.toJ) {
    const a = e.pts[e.pts.length - 2], b = e.pts[e.pts.length - 1];
    const dx = b[0] - a[0], dy = b[1] - a[1];
    const L = Math.hypot(dx, dy) || 1;
    const ux = dx / L, uy = dy / L, s = lit || sel ? 5.5 : 4.5;
    const p1 = [b[0] - ux * s * 1.4 - uy * s * 0.6, b[1] - uy * s * 1.4 + ux * s * 0.6];
    const p2 = [b[0] - ux * s * 1.4 + uy * s * 0.6, b[1] - uy * s * 1.4 - ux * s * 0.6];
    ctx.beginPath();
    ctx.moveTo(p1[0], p1[1]);
    ctx.lineTo(b[0], b[1]);
    ctx.lineTo(p2[0], p2[1]);
    if (thick) { ctx.closePath(); ctx.fillStyle = col; ctx.fill(); } else { ctx.lineWidth = 1; ctx.stroke(); }
  }
  ctx.globalAlpha = 1;
}

function legend() {
  text(["m68k-neumann-microcode — RTL, multi-cycle"], 20, 20, 12, { bold: true, align: "left" });
  const items = [["data", "шина данных"], ["addr", "шина адреса"], ["ctrl", "сигнал CU"], ["stat", "статус в CU"]];
  items.forEach(([k, t], i) => {
    const y = 40 + i * 16;
    drawEdge({ kind: k, pts: [[24, y], [70, y]], hops: [[]], toJ: false });
    text([t], 78, y, 10, { align: "left" });
  });
  text(["нажми на блок или провод — появится подсказка"], 20, 108, 9, { align: "left", color: "#9a6a82", italic: true });
}

function findRoute(from, to) {
  const prev = { [from]: null };
  const queue = [from];
  while (queue.length) {
    const n = queue.shift();
    if (n === to) break;
    if (n !== from && BLOCK[n] && BLOCK[n].kind !== "junction") continue;
    for (const ei of OUT_EDGES[n] || []) {
      const t = D.edges[ei].d;
      if (t in prev) continue;
      prev[t] = ei;
      queue.push(t);
    }
  }
  if (!(to in prev)) { console.warn("нет пути", from, to); return []; }
  const out = [];
  let n = to;
  while (prev[n] !== null) { out.unshift(prev[n]); n = D.edges[prev[n]].s; }
  return out;
}

function buildTrack(nodes, kind) {
  const edges = [];
  for (let i = 0; i < nodes.length - 1; i++) edges.push(...findRoute(nodes[i], nodes[i + 1]));
  const pts = [];
  edges.forEach(ei => {
    D.edges[ei].pts.forEach((p, j) => { if (j > 0 || pts.length === 0) pts.push(p); });
  });
  const cum = [0];
  for (let i = 1; i < pts.length; i++) cum.push(cum[i - 1] + Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]));
  return { edges, pts, cum, len: cum[cum.length - 1] || 0, kind, nodes };
}

const MOUSE = new Image();
MOUSE.onload = draw;
MOUSE.src = "img/mouse.png";
const MW = 46;

function posDir(tr, d) {
  const dd = Math.max(0, Math.min(tr.len, d));
  let i = 1;
  while (i < tr.pts.length - 1 && tr.cum[i] < dd) i++;
  const a = tr.pts[i - 1], b = tr.pts[i];
  const segLen = tr.cum[i] - tr.cum[i - 1] || 1;
  const t = (dd - tr.cum[i - 1]) / segLen;
  return [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, Math.sign(b[0] - a[0]), Math.sign(b[1] - a[1])];
}

function drawMouse(tr, dist, n) {
  if (!MOUSE.complete || !MOUSE.naturalWidth || tr.len === 0) return;
  const [x, y, dx, dy] = posDir(tr, dist);
  const k = tr.kind === "micro" ? 0.75 : 1;
  const w = MW * k, h = w * MOUSE.naturalHeight / MOUSE.naturalWidth;
  const moving = dist < tr.len;
  const bob = moving ? Math.sin(performance.now() / 45 + n) * 1.4 : 0;
  ctx.save();
  ctx.translate(x, y);
  if (dx < 0) ctx.scale(-1, 1);
  else if (dy > 0) ctx.rotate(Math.PI / 2);
  else if (dy < 0) ctx.rotate(-Math.PI / 2);
  ctx.shadowColor = tr.kind === "micro" ? "rgba(123, 63, 160, 0.55)" : "rgba(255, 79, 154, 0.6)";
  ctx.shadowBlur = 10;
  ctx.drawImage(MOUSE, -w * 0.94, -h * 0.62 + bob, w, h);
  ctx.restore();
  const label = tr.label;
  if (!label) return;
  ctx.font = "600 8px " + MONO;
  const tw = ctx.measureText(label).width + 8;
  const c = tr.kind === "micro" ? MBIT : BIT;
  const ty = y - h * 0.62 - 9;
  ctx.fillStyle = c.fill;
  rrect(x - tw / 2, ty - 6, tw, 12, 6);
  ctx.fill();
  ctx.lineWidth = 1;
  ctx.strokeStyle = c.stroke;
  ctx.stroke();
  ctx.fillStyle = c.text;
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  ctx.fillText(label, x, ty + 0.5);
}

let activeEdges = new Set(), activeBlocks = new Set(), activeSigs = new Set();

function sigName(s) { return s.split("=")[0]; }

function currentAluOp() {
  if (!prog || stepIdx < 0) return "";
  const st = prog.steps[stepIdx];
  if (!st) return "";
  const s = st.sig.find(x => x.startsWith("alu_op="));
  return s ? s.split("=")[1] : "";
}

function microTracks(step) {
  const base = [["UPC", "UROM", "U_SIG"]];
  const j = step.jump;
  if (j === "+1") base.push(["UPC", "INC", "MUX_UPC", "UPC"]);
  if (j === "map") base.push(["IR", "MAP", "MUX_UPC", "UPC"]);
  if (j === "next") base.push(["U_NXT", "MUX_UPC", "UPC"]);
  if (j === "cond") base.push(["U_CND", "MUX_COND"], ["st_cu", "MUX_COND", "SEQ", "MUX_UPC", "UPC"]);
  return base;
}

function stepLabel(step) {
  if (step.label !== undefined) return step.label;
  const nums = Object.values(step.set || {}).filter(v => typeof v === "number");
  const v = nums.length ? nums[0] : state.MDR;
  return (v >>> 0) >= 0x80 ? hex(v) : String(v);
}

function phasesOf(step) {
  const ph = step.flow.map(p => p.slice());
  const micro = microTracks(step);
  return ph.map((p, i) => {
    const list = p.map(nodes => ({ nodes, kind: "data" }));
    if (i === 0) list.push({ nodes: micro[0], kind: "micro" });
    if (i === ph.length - 1) micro.slice(1).forEach(n => list.push({ nodes: n, kind: "micro" }));
    return list;
  });
}

function startPhase() {
  const step = prog.steps[stepIdx];
  const phases = phasesOf(step);
  const label = stepLabel(step);
  tracks = phases[phaseIdx].map(p => buildTrack(p.nodes, p.kind));
  tracks.forEach(t => { t.label = t.kind === "micro" ? step.mu : label; });
  phaseT = 0;
  const maxLen = Math.max(...tracks.map(t => t.len), 60);
  phaseDur = maxLen / SPEED + 0.35;
  activeEdges = new Set();
  activeBlocks = new Set();
  tracks.forEach(t => { t.edges.forEach(e => activeEdges.add(e)); t.nodes.forEach(n => activeBlocks.add(n)); t.edges.forEach(e => { activeBlocks.add(D.edges[e].s); activeBlocks.add(D.edges[e].d); }); });
  activeSigs = new Set(step.sig.map(sigName));
  step.sig.forEach(s => { const ei = SIG_EDGE["s_" + sigName(s)]; if (ei !== undefined) activeEdges.add(ei); });
  running = true;
  updatePanel();
}

function startStep(i) {
  stepIdx = i;
  phaseIdx = 0;
  noteText = "";
  startPhase();
}

function finishStep() {
  const step = prog.steps[stepIdx];
  const now = performance.now();
  Object.entries(step.set || {}).forEach(([k, v]) => {
    state[k] = v;
    if (/^[DA]\d$/.test(k)) flash["RF"] = now, flash["cell_" + k] = now;
    else if (k === "uPC") flash["UPC"] = now;
    else flash[k] = now;
  });
  const next = prog.steps[stepIdx + 1];
  state.uPC = next ? next.mu : (step.after || "fetch0");
  flash["UPC"] = now;
  noteText = step.note || "";
  running = false;
  tracks = [];
  activeEdges = new Set();
  activeBlocks = new Set();
  if (!next) {
    finished = true;
    playing = false;
  } else if (playing) {
    pauseUntil = now + 300 / speedMul;
  }
  updatePanel();
}

function tick(ts) {
  const dt = lastTs ? Math.min(0.05, (ts - lastTs) / 1000) : 0;
  lastTs = ts;
  if (prog) {
    if (running) {
      phaseT += dt * speedMul;
      if (phaseT >= phaseDur) {
        const phases = phasesOf(prog.steps[stepIdx]);
        if (phaseIdx < phases.length - 1) { phaseIdx++; startPhase(); }
        else finishStep();
      }
    } else if (playing && !finished && ts >= pauseUntil) {
      startStep(stepIdx + 1);
    }
  }
  const anyFlash = Object.values(flash).some(t => ts - t < 1400);
  if (running || anyFlash || activeSigs.size || selected) draw();
  requestAnimationFrame(tick);
}

function drawSelection() {
  if (!selected || !selected.box) return;
  const b = selected.box;
  ctx.save();
  ctx.setLineDash([5, 3]);
  ctx.lineDashOffset = -performance.now() / 60;
  ctx.lineWidth = 2.2;
  ctx.strokeStyle = SEL;
  rrect(b.x - 4, b.y - 4, b.w + 8, b.h + 8, 6);
  ctx.stroke();
  ctx.restore();
}

function render() {
  queued = false;
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, vw, vh);
  ctx.setTransform(dpr * scale, 0, 0, dpr * scale, dpr * ox, dpr * oy);
  ctx.fillStyle = "#fff5fa";
  ctx.shadowColor = "rgba(90, 30, 60, 0.18)";
  ctx.shadowBlur = 24;
  ctx.fillRect(0, 0, D.W, D.H);
  ctx.shadowBlur = 0;
  ctx.shadowColor = "transparent";
  drawBlock(BLOCK.CU);
  const isSel = i => selected && selected.edges.has(i);
  D.edges.forEach((e, i) => { if (!activeEdges.has(i) && !isSel(i)) drawEdge(e, i); });
  D.edges.forEach((e, i) => { if (!activeEdges.has(i) && isSel(i)) drawEdge(e, i); });
  D.edges.forEach((e, i) => { if (activeEdges.has(i)) drawEdge(e, i); });
  D.blocks.forEach(b => { if (b.kind !== "cu") drawBlock(b); });
  D.cells.forEach(c => {
    const name = c.t.split(" ")[0];
    const g = glowFor("cell_" + name);
    if (g > 0) { ctx.save(); ctx.shadowColor = GLOW; ctx.shadowBlur = 16 * g; }
    box(c, c.sp ? SIG : PINK, 0);
    if (g > 0) { ctx.restore(); ctx.lineWidth = 2; ctx.strokeStyle = GLOW; ctx.strokeRect(c.x, c.y, c.w, c.h); }
    const v = state[name];
    let shown = prog || v !== BASE[name] ? c.t.replace(" (SP)", "") + " = " + fmtVal(name, v) : c.t;
    let size = prog ? 9 : 10;
    if (shown.length > 12) { shown = shown.replace(" = ", "="); size = 8; }
    text([shown], c.x + c.w / 2, c.y + c.h / 2, size, { color: c.sp ? INK : LIGHT, mono: !!prog || shown !== c.t });
  });
  D.texts.forEach(t => {
    const cu = BLOCK.CU;
    const inCU = t.x > cu.x && t.x < cu.x + cu.w && t.y > cu.y && t.y < cu.y + cu.h;
    const base = t.c === "#1f4e9e" ? COL.addr : t.c === "#5b6b80" ? COL.ctrl : INK;
    text([t.t], t.x, t.y, t.s, { align: "left", color: inCU ? LIGHT : base });
  });
  legend();
  drawSelection();
  if (running) {
    const dist = phaseT * SPEED;
    tracks.forEach((tr, n) => drawMouse(tr, dist, n));
  }
  pctEl.textContent = Math.round(scale * 100) + "%";
}

function esc(s) { return String(s).replace(/[&<>"]/g, ch => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[ch]); }

const JUNCTION_BUS = {
  PC: ["PC", "J_PC", "J_PC2"],
  addr: ["MAR", "J_ADDR"],
  MDR: ["MDR", "J_M1", "J_M2", "J_M3", "J_M4", "J_MA", "J_MB"],
  ALU_out: ["J_ALU", "J_R", "J_WB", "J_MDRB", "J_PCB"],
  TMP: ["TMP", "J_T"],
  src: ["J_S", "J_S2"],
  dst: ["J_D1", "J_D2"]
};
const SOURCE_BUS = Object.fromEntries(Object.entries(JUNCTION_BUS).flatMap(([k, ids]) => ids.map(id => [id, k])));
const PAIR_BUS = {
  "ADD>MUX_PC": "PCn", "RAM>MUX_MEM": "mem_data", "IN>MUX_MEM": "in_data", "J_M5>RAM": "wr_data", "J_M5>OUT": "wr_data",
  "J_M4>J_M5": "wr_data", "SEXT>MUX_B": "sext", "CONST>MUX_B": "const", "ALU>J_ALU": "ALU_out", "ALU>SR": "flags",
  "RF>MUX_A": "rdata1", "RF>MUX_B": "rdata2", "MUX_WB>RF": "wdata", "IR>J_S": "src", "IR>J_D1": "dst", "IR>MUX_R2": "idx",
  "IR>MAP": "opcode", "A7a>MUX_R1": "a7", "A7b>MUX_WR": "a7", "MUX_R1>RF": "rnum1", "MUX_R2>RF": "rnum2", "MUX_WR>RF": "wnum",
  "MUX_MAR>MAR": "mux_mar", "MUX_MEM>MUX_MDR": "mem_in", "MUX_MDR>MDR": "mdr_in", "MUX_PC>PC": "pc_in", "MUX_A>ALU": "opA",
  "MUX_B>ALU": "opB", "MAP>MUX_UPC": "uaddr", "MUX_UPC>UPC": "upc_in", "UPC>UROM": "upc", "UPC>INC": "upc", "INC>MUX_UPC": "upc1",
  "UROM>U_SIG": "uir", "U_NXT>MUX_UPC": "next", "U_JT>SEQ": "jump", "U_CND>MUX_COND": "condsel", "MUX_COND>SEQ": "cond",
  "SEQ>MUX_UPC": "sel_upc", "CMP>st_cmp": "st_cmp", "SR>st_sr": "st_sr", "st_cu>MUX_COND": "st_cu"
};

function busKey(i) {
  const e = D.edges[i];
  if (e.s.startsWith("s_")) return "sig:" + e.s;
  return PAIR_BUS[e.s + ">" + e.d] || SOURCE_BUS[e.s] || "edge:" + i;
}

function edgesOfBus(key) {
  return new Set(D.edges.map((e, i) => i).filter(i => busKey(i) === key));
}

function card(kind, title, rows, textBody, now) {
  const dl = rows.filter(([, v]) => v && v !== "—").map(([k, v]) => "<dt>" + esc(k) + "</dt><dd>" + esc(v) + "</dd>").join("");
  return '<div class="tip-head"><span class="tip-kind">' + esc(kind) + '</span><button class="tip-x" type="button" aria-label="Закрыть">✕</button></div>' +
    '<div class="tip-title">' + esc(title) + "</div>" +
    (dl ? '<dl class="tip-rows">' + dl + "</dl>" : "") +
    (textBody ? '<p class="tip-text">' + esc(textBody) + "</p>" : "") +
    (now ? '<div class="tip-now">' + esc(now) + "</div>" : "");
}

const NOW_OF = { PC: "PC", MAR: "MAR", MDR: "MDR", TMP: "TMP", IR: "IR", SR: "SR", UPC: "uPC", IN: "IN", OUT: "OUT" };

function sigNow(label) {
  if (!prog || stepIdx < 0 || !prog.steps[stepIdx]) return "";
  const s = prog.steps[stepIdx].sig.find(x => sigName(x) === label);
  return s ? "в этом такте: " + s : "в этом такте не активен";
}

function blockCard(b) {
  if (b.kind === "sig") {
    const si = SIGNAL_INFO[b.label] || {};
    return card("управляющий сигнал", b.label, [["Куда", si.b], ["Значения", si.v], ["Действие", si.a]], "Выставляется полем μIR.signals текущей микрокоманды.", sigNow(b.label));
  }
  const info = BLOCK_INFO[b.id] || { t: b.label || b.id };
  const nowKey = NOW_OF[b.id];
  const now = nowKey ? "сейчас: " + (b.id === "SR" ? "N Z V C = " + state.SR.split("").join(" ") : fmtVal(nowKey, state[nowKey])) : (activeBlocks.has(b.id) ? "работает в текущем такте" : "");
  return card(info.k || "блок", info.t, [["Сигнал", info.s], ["Входы", info.i], ["Выходы", info.o], ["Назначение", info.r]], info.d, now);
}

function regCard(name) {
  const info = name === "A7" ? REG_INFO.A7 : REG_INFO[name[0]];
  const title = name === "A7" ? "A7 (SP)" : name;
  return card(info.k, title, [["Назначение", info.r]], info.d, "сейчас: " + fmtVal(name, state[name]));
}

function busCard(key, edges) {
  if (key.startsWith("sig:")) return blockCard(BLOCK[key.slice(4)]);
  const info = BUS_INFO[key] || { t: "Связь", d: "" };
  const live = [...edges].some(i => activeEdges.has(i));
  return card("шина / связь", info.t, [], info.d, live ? "по ней сейчас бегут мыши" : "");
}

function hitTest(x, y) {
  const inBox = (b, pad) => x >= b.x - pad && x <= b.x + b.w + pad && y >= b.y - pad && y <= b.y + b.h + pad;
  const pad = 2 / scale;
  for (const b of D.blocks) {
    if (b.kind === "junction" && inBox(b, 5 / scale)) return { kind: "junction", id: b.id };
    if ((b.kind === "sig" || b.kind === "status" || b.kind === "const") && inBox(b, pad)) return { kind: "block", id: b.id };
  }
  for (const c of D.cells) if (inBox(c, 0)) return { kind: "cell", id: c.t.split(" ")[0], box: c };
  for (const b of D.blocks) {
    if (["junction", "sig", "status", "const", "rf", "cu"].includes(b.kind)) continue;
    if (inBox(b, pad)) return { kind: "block", id: b.id };
  }
  const tol = Math.max(4, 7 / scale);
  let best = -1, bd = tol;
  D.edges.forEach((e, i) => {
    for (let k = 0; k < e.pts.length - 1; k++) {
      const [ax, ay] = e.pts[k], [bx, by] = e.pts[k + 1];
      const L = (bx - ax) ** 2 + (by - ay) ** 2 || 1;
      const t = Math.max(0, Math.min(1, ((x - ax) * (bx - ax) + (y - ay) * (by - ay)) / L));
      const d = Math.hypot(x - (ax + t * (bx - ax)), y - (ay + t * (by - ay)));
      if (d < bd) { bd = d; best = i; }
    }
  });
  if (best >= 0) return { kind: "edge", idx: best };
  if (inBox(BLOCK.RF, 0)) return { kind: "block", id: "RF" };
  if (inBox(BLOCK.CU, 0)) return { kind: "block", id: "CU" };
  return null;
}

function showInfo(hit, cx, cy) {
  let html = "", boxOf = null, edges = new Set();
  if (hit.kind === "cell") {
    html = regCard(hit.id);
    boxOf = hit.box;
  } else if (hit.kind === "block") {
    const b = BLOCK[hit.id];
    html = blockCard(b);
    boxOf = b;
    if (b.kind === "sig" && SIG_EDGE[b.id] !== undefined) edges.add(SIG_EDGE[b.id]);
  } else {
    const idx = hit.kind === "edge" ? hit.idx : (OUT_EDGES[hit.id] || [])[0];
    if (idx === undefined) return closeTip();
    const key = busKey(idx);
    edges = key.startsWith("edge:") ? new Set([idx]) : edgesOfBus(key);
    html = busCard(key, edges);
    if (key.startsWith("sig:")) boxOf = BLOCK[key.slice(4)];
  }
  selected = { box: boxOf, edges };
  tipEl.innerHTML = html;
  tipEl.hidden = false;
  placeTip(cx, cy);
  draw();
}

function placeTip(cx, cy) {
  const r = stageEl.getBoundingClientRect();
  if (r.width < 560) {
    tipEl.classList.add("sheet");
    tipEl.style.left = "";
    tipEl.style.top = "";
    return;
  }
  tipEl.classList.remove("sheet");
  const w = tipEl.offsetWidth, h = tipEl.offsetHeight;
  let x = cx - r.left + 16, y = cy - r.top + 16;
  if (x + w > r.width - 8) x = cx - r.left - w - 16;
  if (y + h > r.height - 8) y = r.height - h - 8;
  tipEl.style.left = Math.max(8, x) + "px";
  tipEl.style.top = Math.max(8, y) + "px";
}

function closeTip() {
  tipEl.hidden = true;
  selected = null;
  draw();
}

tipEl.addEventListener("click", e => { if (e.target.closest(".tip-x")) closeTip(); });

function handleClick(clientX, clientY) {
  const r = canvas.getBoundingClientRect();
  const x = (clientX - r.left - ox) / scale, y = (clientY - r.top - oy) / scale;
  const hit = hitTest(x, y);
  if (hit) showInfo(hit, clientX, clientY); else closeTip();
}

const chipsEl = document.getElementById("cmds");
const filterEl = document.getElementById("filter");
const infoEl = document.getElementById("info");
const playBtn = document.getElementById("play");

function buildList() {
  const q = filterEl.value.trim().toLowerCase();
  chipsEl.innerHTML = "";
  let group = null, shown = 0;
  PROGRAMS.forEach((p, i) => {
    if (q && !(p.name.toLowerCase().includes(q) || p.about.toLowerCase().includes(q) || p.group.toLowerCase().includes(q))) return;
    if (p.group !== group) {
      group = p.group;
      const g = document.createElement("div");
      g.className = "grp";
      g.textContent = group;
      chipsEl.appendChild(g);
    }
    const b = document.createElement("button");
    b.className = "cmd" + (prog === p ? " on" : "");
    b.type = "button";
    b.dataset.idx = i;
    b.innerHTML = '<span class="cname">' + esc(p.name) + '</span><span class="cabout">' + esc(p.about) + "</span>";
    b.onclick = () => selectProgram(i, true);
    chipsEl.appendChild(b);
    shown++;
  });
  if (!shown) chipsEl.innerHTML = '<div class="idle">Ничего не нашлось.</div>';
}

filterEl.addEventListener("input", buildList);

function markActive() {
  chipsEl.querySelectorAll(".cmd").forEach(c => {
    const on = prog && PROGRAMS[+c.dataset.idx] === prog;
    c.classList.toggle("on", !!on);
    if (on) c.scrollIntoView({ block: "nearest" });
  });
}

function selectProgram(i, autoplay) {
  prog = PROGRAMS[i];
  state = { ...BASE, ...prog.init };
  Object.keys(flash).forEach(k => delete flash[k]);
  stepIdx = -1;
  finished = false;
  running = false;
  tracks = [];
  activeEdges = new Set();
  activeBlocks = new Set();
  activeSigs = new Set();
  noteText = "";
  playing = !!autoplay;
  pauseUntil = performance.now() + 250;
  markActive();
  updatePanel();
  draw();
}

function exitProgram() {
  prog = null;
  playing = false;
  running = false;
  state = { ...BASE };
  markActive();
  activeEdges = new Set();
  activeBlocks = new Set();
  activeSigs = new Set();
  updatePanel();
  draw();
}

function updatePanel() {
  playBtn.textContent = playing ? "❚❚" : "▶";
  playBtn.setAttribute("aria-label", playing ? "Пауза" : "Запуск");
  if (!prog) {
    infoEl.innerHTML = '<div class="idle">Нажми на команду — мыши пробегут весь цикл её исполнения: fetch, потом микропрограмма. Сколько путей в такте, столько и мышей. Нажми на любой блок или провод схемы — появится подсказка.</div>';
    return;
  }
  const total = prog.steps.length;
  const st = stepIdx >= 0 ? prog.steps[stepIdx] : null;
  const head = '<div class="row1"><span class="pname">' + esc(prog.name) + '</span><span class="cnt">такт ' + Math.max(0, stepIdx + 1) + " / " + total + "</span></div>";
  if (!st) {
    infoEl.innerHTML = head + '<div class="about">' + esc(prog.about) + "</div>";
    return;
  }
  const sigs = st.sig.length ? st.sig.map(s => '<span class="sg">' + esc(s) + "</span>").join("") : '<span class="nosig">сигналов тракта нет — работает только блок управления</span>';
  const jt = st.jumpText || (st.jump === "+1" ? "μPC + 1" : st.jump);
  infoEl.innerHTML = head +
    '<div class="rtl">' + esc(st.rtl) + "</div>" +
    '<div class="mu"><span>μ: <b>' + esc(st.mu) + "</b></span><span>переход: <b>" + esc(jt) + "</b></span>" + (noteText ? '<span class="note">' + esc(noteText) + "</span>" : "") + "</div>" +
    '<div class="sigs">' + sigs + "</div>";
}

function stepOnce() {
  if (!prog) return;
  playing = false;
  if (running) return;
  if (finished) { selectProgram(PROGRAMS.indexOf(prog), false); return; }
  startStep(stepIdx + 1);
}

function togglePlay() {
  if (!prog) { selectProgram(0, true); return; }
  if (finished) { selectProgram(PROGRAMS.indexOf(prog), true); return; }
  playing = !playing;
  pauseUntil = performance.now();
  updatePanel();
}

const speedBtns = [...document.querySelectorAll("#speed button")];
function setSpeed(v) {
  speedMul = v;
  speedBtns.forEach(b => {
    const on = parseFloat(b.dataset.v) === v;
    b.classList.toggle("on", on);
    b.setAttribute("aria-checked", on ? "true" : "false");
  });
}
speedBtns.forEach(b => { b.onclick = () => setSpeed(parseFloat(b.dataset.v)); });

playBtn.onclick = togglePlay;
document.getElementById("step").onclick = stepOnce;
document.getElementById("restart").onclick = () => prog && selectProgram(PROGRAMS.indexOf(prog), false);
document.getElementById("exit").onclick = exitProgram;

const pointers = new Map();
let pinchDist = 0, press = null;
canvas.addEventListener("pointerdown", e => {
  canvas.setPointerCapture(e.pointerId);
  pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  canvas.classList.add("dragging");
  press = pointers.size === 1 && e.button === 0 ? { x: e.clientX, y: e.clientY, moved: false } : null;
  if (pointers.size === 2) {
    const [p, q] = [...pointers.values()];
    pinchDist = Math.hypot(p.x - q.x, p.y - q.y);
  }
});
canvas.addEventListener("pointermove", e => {
  if (!pointers.has(e.pointerId)) return;
  const prev = pointers.get(e.pointerId);
  const cur = { x: e.clientX, y: e.clientY };
  pointers.set(e.pointerId, cur);
  if (press && Math.hypot(cur.x - press.x, cur.y - press.y) > 5) press.moved = true;
  if (pointers.size === 1) {
    ox += cur.x - prev.x;
    oy += cur.y - prev.y;
    if (!tipEl.hidden && press && press.moved) placeTipOffset(cur.x - prev.x, cur.y - prev.y);
    draw();
  } else if (pointers.size === 2) {
    const [p, q] = [...pointers.values()];
    const d = Math.hypot(p.x - q.x, p.y - q.y);
    const r = canvas.getBoundingClientRect();
    if (pinchDist > 0) zoomAt(d / pinchDist, (p.x + q.x) / 2 - r.left, (p.y + q.y) / 2 - r.top);
    pinchDist = d;
  }
});
function placeTipOffset(dx, dy) {
  if (tipEl.classList.contains("sheet")) return;
  tipEl.style.left = (parseFloat(tipEl.style.left) || 0) + dx + "px";
  tipEl.style.top = (parseFloat(tipEl.style.top) || 0) + dy + "px";
}
function up(e) {
  const click = e.type === "pointerup" && press && !press.moved && pointers.size === 1;
  pointers.delete(e.pointerId);
  if (pointers.size < 2) pinchDist = 0;
  if (pointers.size === 0) { canvas.classList.remove("dragging"); press = null; }
  if (click) handleClick(e.clientX, e.clientY);
}
canvas.addEventListener("pointerup", up);
canvas.addEventListener("pointercancel", up);
canvas.addEventListener("wheel", e => {
  e.preventDefault();
  const r = canvas.getBoundingClientRect();
  if (e.ctrlKey || Math.abs(e.deltaY) >= Math.abs(e.deltaX)) {
    zoomAt(Math.exp(-e.deltaY * (e.ctrlKey ? 0.01 : 0.0015)), e.clientX - r.left, e.clientY - r.top);
  } else {
    ox -= e.deltaX;
    draw();
  }
  if (!tipEl.hidden) closeTip();
}, { passive: false });
canvas.addEventListener("dblclick", e => {
  const r = canvas.getBoundingClientRect();
  zoomAt(2, e.clientX - r.left, e.clientY - r.top);
  closeTip();
});
document.getElementById("in").onclick = () => zoomAt(1.25, vw / 2, vh / 2);
document.getElementById("out").onclick = () => zoomAt(0.8, vw / 2, vh / 2);
document.getElementById("fit").onclick = fit;

const introEl = document.getElementById("intro");
const introBody = document.getElementById("introBody");
const tabBtns = [...introEl.querySelectorAll("[data-tab]")];
let introReturn = null;

function demoBtn(name) {
  const p = PROGRAMS.find(x => x.name === name);
  if (!p) return "";
  return '<button type="button" class="demo-btn" data-demo="' + esc(name) + '">▶ ' + esc(name) + ' <span>' + p.steps.length + " т.</span></button>";
}

function cmdsHtml() {
  const groups = [...new Set(COMMAND_DOCS.map(d => d.g))];
  return '<div class="docs">' + DOC_INTRO.map(p => "<p>" + esc(p) + "</p>").join("") +
    '<h3 class="doc-h">Режимы адресации</h3><table class="doc-table"><tbody>' +
    DOC_MODES.map(([m, n, e]) => "<tr><td><code>" + esc(m) + "</code></td><td>" + esc(n) + "</td><td>" + esc(e) + "</td></tr>").join("") + "</tbody></table>" +
    groups.map(g => '<h3 class="doc-h">' + esc(g) + "</h3>" + COMMAND_DOCS.filter(d => d.g === g).map(d =>
      '<div class="doc-row"><div class="doc-name"><b>' + esc(d.n) + "</b> <code>" + esc(d.syn) + '</code></div><div class="doc-op">' + esc(d.op) + '</div><div class="doc-fl">' + esc(d.fl) + '</div><div class="doc-demos">' + d.demo.map(demoBtn).join("") + "</div></div>"
    ).join("")).join("") +
    '<p class="doc-note">«т.» — тактов в демонстрации вместе с выборкой команды (3 такта). Чтение или запись порта добавляет такт.</p></div>';
}

function howtoHtml() {
  return '<dl class="howto">' + HOWTO.map(([k, v]) => "<dt>" + esc(k) + "</dt><dd>" + esc(v) + "</dd>").join("") + "</dl>";
}

function setTab(t) {
  tabBtns.forEach(b => {
    const on = b.dataset.tab === t;
    b.classList.toggle("on", on);
    b.setAttribute("aria-selected", on ? "true" : "false");
  });
  introBody.innerHTML = t === "cmds" ? cmdsHtml() : howtoHtml();
  introBody.scrollTop = 0;
}

function openIntro(tab) {
  introReturn = document.activeElement;
  setTab(tab || "cmds");
  introEl.hidden = false;
  document.getElementById("introGo").focus();
}

function closeIntro() {
  introEl.hidden = true;
  if (introReturn && introReturn.focus) introReturn.focus();
}

tabBtns.forEach(b => { b.onclick = () => setTab(b.dataset.tab); });
document.getElementById("introGo").onclick = closeIntro;
document.getElementById("introClose").onclick = closeIntro;
document.getElementById("help").onclick = () => openIntro("cmds");
document.getElementById("storyAgain").onclick = () => { closeIntro(); openStory(); };
introEl.addEventListener("click", e => {
  if (e.target === introEl) { closeIntro(); return; }
  const d = e.target.closest("[data-demo]");
  if (!d) return;
  const i = PROGRAMS.findIndex(p => p.name === d.dataset.demo);
  closeIntro();
  if (i >= 0) selectProgram(i, true);
});

const storyEl = document.getElementById("story");
const bubbleEl = document.getElementById("bubble");
const storyTitle = document.getElementById("storyTitle");
const storyText = document.getElementById("storyText");
const storyDots = document.getElementById("storyDots");
const storyPrev = document.getElementById("storyPrev");
const storyNext = document.getElementById("storyNext");
let slide = 0;

STORY_SLIDES.forEach((s, i) => {
  const d = document.createElement("button");
  d.type = "button";
  d.setAttribute("aria-label", "Слайд " + (i + 1));
  d.onclick = () => showSlide(i);
  storyDots.appendChild(d);
});

function showSlide(i) {
  slide = Math.max(0, Math.min(STORY_SLIDES.length - 1, i));
  const s = STORY_SLIDES[slide];
  storyTitle.textContent = s.t;
  storyText.textContent = s.d;
  [...storyDots.children].forEach((d, j) => d.classList.toggle("on", j === slide));
  storyPrev.disabled = slide === 0;
  storyNext.textContent = slide === STORY_SLIDES.length - 1 ? "Начать →" : "Дальше →";
  bubbleEl.classList.remove("swap");
  void bubbleEl.offsetWidth;
  bubbleEl.classList.add("swap");
}

function openStory() {
  storyEl.classList.remove("done");
  storyEl.hidden = false;
  showSlide(0);
  storyNext.focus();
}

function closeStory() {
  storyEl.classList.add("done");
  setTimeout(() => { storyEl.hidden = true; draw(); }, 450);
}

storyPrev.onclick = () => showSlide(slide - 1);
storyNext.onclick = () => (slide === STORY_SLIDES.length - 1 ? closeStory() : showSlide(slide + 1));
document.getElementById("storySkip").onclick = closeStory;

const bootEl = document.getElementById("boot");
const bootFill = document.getElementById("bootFill");
const bootRunner = document.getElementById("bootRunner");
const bootMsg = document.getElementById("bootMsg");
const bootPct = document.getElementById("bootPct");
const BOOT_MSG = ["Будим мышей…", "Прошиваем μROM…", "Раскладываем шины…", "Сверяем флаги N Z V C…", "Шаромыш разминается…"];

function runBoot() {
  let k = 0, ready = false, progress = 0;
  const msgTimer = setInterval(() => { k = (k + 1) % BOOT_MSG.length; bootMsg.textContent = BOOT_MSG[k]; }, 650);
  const step = () => {
    progress = ready ? Math.min(100, progress + 4) : progress + (92 - progress) * 0.02;
    const p = progress.toFixed(1) + "%";
    bootFill.style.width = p;
    bootRunner.style.left = p;
    bootPct.textContent = Math.floor(progress) + "%";
    if (progress < 100) requestAnimationFrame(step);
  };
  requestAnimationFrame(step);
  const fonts = document.fonts && document.fonts.ready ? document.fonts.ready : Promise.resolve();
  const img = new Promise(res => {
    if (MOUSE.complete) res();
    else { MOUSE.addEventListener("load", res, { once: true }); MOUSE.addEventListener("error", res, { once: true }); }
  });
  const minTime = new Promise(res => setTimeout(res, 3200));
  const maxTime = new Promise(res => setTimeout(res, 7000));
  Promise.race([Promise.all([fonts, img, minTime]), maxTime]).then(() => {
    ready = true;
    clearInterval(msgTimer);
    bootMsg.textContent = "Поехали!";
    setTimeout(() => {
      openStory();
      bootEl.classList.add("done");
      setTimeout(() => { bootEl.hidden = true; }, 480);
    }, 700);
  });
}

window.addEventListener("keydown", e => {
  if (!bootEl.hidden) return;
  if (!storyEl.hidden) {
    if (e.key === "ArrowRight" || e.key === "Enter") { e.preventDefault(); storyNext.click(); }
    else if (e.key === "ArrowLeft") showSlide(slide - 1);
    else if (e.key === "Escape") closeStory();
    return;
  }
  if (!introEl.hidden) { if (e.key === "Escape") closeIntro(); return; }
  if (e.target.tagName === "INPUT") { if (e.key === "Escape") e.target.blur(); return; }
  if (e.key === " ") { e.preventDefault(); togglePlay(); }
  else if (e.key === "n" || e.key === "т" || e.key === ".") stepOnce();
  else if (e.key === "r" || e.key === "к") { if (prog) selectProgram(PROGRAMS.indexOf(prog), false); }
  else if (e.key === "Escape") { if (!tipEl.hidden) closeTip(); else exitProgram(); }
  else if (e.key === "+" || e.key === "=") zoomAt(1.25, vw / 2, vh / 2);
  else if (e.key === "-" || e.key === "_") zoomAt(0.8, vw / 2, vh / 2);
  else if (e.key === "0") fit();
  else if (e.key === "ArrowLeft") { ox += 60; draw(); }
  else if (e.key === "ArrowRight") { ox -= 60; draw(); }
  else if (e.key === "ArrowUp") { oy += 60; draw(); }
  else if (e.key === "ArrowDown") { oy -= 60; draw(); }
});
window.addEventListener("resize", () => { resize(); fit(); if (!tipEl.hidden) closeTip(); });
buildList();
setSpeed(1);
updatePanel();
resize();
fit();
requestAnimationFrame(tick);
runBoot();
if (document.fonts && document.fonts.load) {
  Promise.all([
    document.fonts.load('400 12px "IBM Plex Sans"'),
    document.fonts.load('600 12px "IBM Plex Sans"'),
    document.fonts.load('italic 400 12px "IBM Plex Sans"'),
    document.fonts.load('600 12px "IBM Plex Mono"')
  ]).then(draw).catch(draw);
}
