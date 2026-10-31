'use strict';
// geom.js — static landing / logical-chain helpers shared by engine levers and bots. Pure functions, no deps.
const R = [26, 34, 44, 56, 70, 86, 104, 124, 146, 170];
const W = 600, FLOOR = 900;
function cols(c, n) { const r = R[c], o = new Array(n); for (let i = 0; i < n; i++) o[i] = r + (W - 2 * r) * i / (n - 1); return o; }
const COLS = {}; // cache
function colsCached(c, n) { const k = c * 100 + n; return COLS[k] || (COLS[k] = cols(c, n)); }

// land circle tier c dropped at x onto landed fruit. returns {y, touched[]}
function land(c, x, fruits) {
  const rc = R[c]; let y = FLOOR - rc;
  const n = fruits.length;
  for (let i = 0; i < n; i++) {
    const f = fruits[i]; if (!f.landed) continue;
    const dx = Math.abs(x - f.x), s = rc + f.r;
    if (dx < s) { const yy = f.y - Math.sqrt(s * s - dx * dx); if (yy < y) y = yy; }
  }
  const touched = [];
  for (let i = 0; i < n; i++) {
    const f = fruits[i]; if (!f.landed) continue;
    const dx = x - f.x, dy = y - f.y, s = rc + f.r + 4;
    if (dx * dx + dy * dy <= s * s) touched.push(f);
  }
  return { y, touched };
}

// logical chain. start: tier c at (x,y) with touched set. Returns {top, merges, x, y, tier, after?}
function chainFrom(c, px, py, touched, fruits, wantState) {
  let cur = c, top = -1, merges = 0;
  const dead = [];
  let t = touched;
  while (cur < 9) {
    let best = null;
    for (let i = 0; i < t.length; i++) { const f = t[i]; if (f.tier === cur && dead.indexOf(f.uid) < 0 && (best === null || f.uid < best.uid)) best = f; }
    if (!best) break;
    dead.push(best.uid);
    px = (px + best.x) / 2; py = (py + best.y) / 2; cur++; top = cur; merges++;
    const rn = R[cur];
    px = Math.min(Math.max(px, rn), W - rn); py = Math.min(py, FLOOR - rn);
    const nt = [];
    for (let i = 0; i < fruits.length; i++) {
      const f = fruits[i]; if (!f.landed || dead.indexOf(f.uid) >= 0) continue;
      const dx = px - f.x, dy = py - f.y, s = rn + f.r + 10;
      if (dx * dx + dy * dy <= s * s) nt.push(f);
    }
    t = nt;
  }
  const res = { top, merges, x: px, y: py, tier: cur };
  if (wantState) {
    const after = [];
    for (let i = 0; i < fruits.length; i++) if (dead.indexOf(fruits[i].uid) < 0) after.push(fruits[i]);
    after.push({ uid: 1e9 + after.length, tier: cur, x: px, y: py, r: R[cur], landed: true });
    res.after = after;
  }
  return res;
}
function chainTop(c, x, fruits, wantState) {
  const L = land(c, x, fruits);
  const r = chainFrom(c, x, L.y, L.touched, fruits, wantState);
  r.landY = L.y; r.touched = L.touched; r.landX = x;
  return r;
}
// pair risk: chain starts from tier c+1 at the landing point
function chainTop2(c, x, fruits) {
  if (c >= 9) return -1;
  const L = land(c, x, fruits);
  const rn = R[c + 1];
  const nt = [];
  for (const f of fruits) { if (!f.landed) continue; const dx = x - f.x, dy = L.y - f.y, s = rn + f.r + 10; if (dx * dx + dy * dy <= s * s) nt.push(f); }
  const r = chainFrom(c + 1, x, L.y, nt, fruits, false);
  return Math.max(c + 1, r.top);
}

// bot / autoplay features at (c,x)
function features(c, x, fruits, wantState) {
  const ch = chainTop(c, x, fruits, wantState);
  const y = ch.landY, t = ch.touched, rc = R[c];
  let m = 0, adj = 0, bury = 0;
  for (const f of t) {
    if (f.tier === c) m = 1;
    if (f.tier === c + 1 || f.tier === c - 1) adj = 1;
    if (f.tier < c && f.y > y) bury = 1;
  }
  let nb = -1;
  for (const f of fruits) {
    if (!f.landed) continue;
    const dx = x - f.x, dy = y - f.y, s = rc + f.r + 2 * rc;
    if (dx * dx + dy * dy <= s * s && f.tier > nb) nb = f.tier;
  }
  const hc = (900 - (y - rc)) / 900;
  const out = { m, h: ch.top, hc, adj, bury, nearBig: nb < 0 ? 0 : nb / 9, y, chain: ch };
  if (wantState) {
    out.after = ch.top >= 0 ? ch.after : fruits.concat([{ uid: 1e9 + fruits.length, tier: c, x, y, r: rc, landed: true }]);
  }
  return out;
}
function repV(c, f) { return 100 * f.m + 40 * Math.max(0, f.h - c - 1) + 8 * f.adj - 30 * f.hc - 15 * f.bury; }

module.exports = { R, W, FLOOR, cols, colsCached, land, chainFrom, chainTop, chainTop2, features, repV };
