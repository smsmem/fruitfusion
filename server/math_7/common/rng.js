'use strict';
// rng.js — SHA-256-seeded xoshiro128** sub-streams. No fs/crypto here: sha256 is injected.
const NAMES = ['draw', 'jar', 'spawn', 'jitter', 'checkpoint', 'autoplay', 'bot', 'board', 'rival', 'alert'];
function rotl(x, k) { return ((x << k) | (x >>> (32 - k))) >>> 0; }
class Xo {
  constructor(st) {
    this.s0 = st[0] >>> 0; this.s1 = st[1] >>> 0; this.s2 = st[2] >>> 0; this.s3 = st[3] >>> 0;
    if ((this.s0 | this.s1 | this.s2 | this.s3) === 0) { this.s0 = 1; this.s1 = 2; this.s2 = 3; this.s3 = 4; }
  }
  next() {
    const r = Math.imul(rotl(Math.imul(this.s1, 5) >>> 0, 7), 9) >>> 0;
    const t = (this.s1 << 9) >>> 0;
    this.s2 = (this.s2 ^ this.s0) >>> 0; this.s3 = (this.s3 ^ this.s1) >>> 0;
    this.s1 = (this.s1 ^ this.s2) >>> 0; this.s0 = (this.s0 ^ this.s3) >>> 0;
    this.s2 = (this.s2 ^ t) >>> 0; this.s3 = rotl(this.s3, 11);
    return r;
  }
  float() { return (this.next() >>> 8) / 16777216; }
  int(n) {
    const lim = Math.floor(4294967296 / n) * n;
    let v; do { v = this.next(); } while (v >= lim);
    return v % n;
  }
  gauss() {
    const u1 = 1 - this.float(), u2 = this.float();
    return Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
  }
}
function utf8(s) { return new TextEncoder().encode(s); }
function cat(a, b) { const o = new Uint8Array(a.length + b.length); o.set(a, 0); o.set(b, a.length); return o; }
function stateFrom(bytes) {
  const o = [];
  for (let i = 0; i < 4; i++) o.push((bytes[4 * i] | (bytes[4 * i + 1] << 8) | (bytes[4 * i + 2] << 16) | (bytes[4 * i + 3] << 24)) >>> 0);
  return o;
}
function rootSeed(sha256, serverSeed, clientSeed, nonce) {
  return sha256(utf8(serverSeed + ':' + clientSeed + ':' + String(nonce)));
}
function streamState(sha256, root, name) { return stateFrom(sha256(cat(root, utf8(':' + name)))); }
function makeStreams(sha256, serverSeed, clientSeed, nonce) {
  const root = rootSeed(sha256, serverSeed, clientSeed, nonce);
  const o = {};
  for (const n of NAMES) o[n] = new Xo(streamState(sha256, root, n));
  return o;
}
// integer table: weights out of 10000; Σ w·mult must equal rtp*10000
function solveTable(cfg) {
  const t = cfg.rng.rungs; let sw = 0, sm = 0; const cum = [];
  for (const r of t) { sw += r.weight; sm += r.weight * r.mult; cum.push(sw); }
  if (sw !== 10000) throw new Error('weights sum ' + sw);
  if (sm !== Math.round(cfg.rng.rtp * 10000)) throw new Error('RTP integer check failed: ' + sm);
  return { cum, rungs: t.map(r => r.id), total: sw, sumWM: sm };
}
function rungFromX(table, x) { for (let i = 0; i < table.cum.length; i++) if (x < table.cum[i]) return table.rungs[i]; throw new Error('x'); }
function stateFromBytes(b) { return stateFrom(b); }
module.exports = { stateFromBytes, Xo, makeStreams, rootSeed, streamState, solveTable, rungFromX, NAMES, utf8, cat };
