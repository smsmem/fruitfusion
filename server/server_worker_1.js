'use strict';
// server_worker_1.js (Worker 1): the isolated draw / Rival module. It runs the live math_7 round at 60 ticks/s and posts only the wire messages of BUILD_SPEC_1 4.5.
// Client -> here: boot {port, test}, start {...test fields only in test mode}, drop {x}, getLog, resume, stats, stop.
importScripts('sha256_1.js', 'cjs_1.js', 'env_1.js', 'live_1.js');
const FFs = self.FF, TICK = 1000 / 60;
let w2Self = null, w2ms = 0, env = null, live = null, w2 = null, test = false, nonce = 0, queuedX = null, timer = null, acc = 0, last = 0, scripted = false, script = null, pauseAt = null, paused = false, tickTimes = [], waiter = null;
const wireLog = [];
function readBytes(p) {
  const x = new XMLHttpRequest(); x.open('GET', p, false); x.responseType = 'arraybuffer'; x.send(null);
  if (x.status !== 200 && x.status !== 0) throw new Error('GET ' + p + ' ' + x.status);
  return new Uint8Array(x.response);
}
const post = m => { self.postMessage(m); };
function hexSeed() { const a = new Uint8Array(32); self.crypto.getRandomValues(a); return FFs.hex(a); }
function notify() { if (waiter && live.busy === 0) { const w = waiter; waiter = null; w(); } }
function onW2(e) {
  const m = e.data;
  if (m.k === 'ready') { w2Self = m.selfTest || null; return; }
  if (!live) return;
  if (m.ms) w2ms += m.ms;
  if (m.k === 'look') live.onLook(m.id, m.res); else if (m.k === 'replay') live.onReplay(m.res); else if (m.k === 'work') live.onWork();
  else if (m.k === 'err') post({ k: 'srvErr', msg: m.msg });
  notify();
}
function io() {
  return {
    emit: m => post(m),
    look: q => w2.postMessage(Object.assign({ k: 'look' }, q)),
    work: q => w2.postMessage(Object.assign({ k: 'work' }, q)),
    replay: q => w2.postMessage(Object.assign({ k: 'replay' }, q)),
    now: () => performance.now()
  };
}
function doTick() {
  let x = queuedX; queuedX = null;
  if (script) { const s = script; while (s.ip < s.list.length && s.list[s.ip].t < live.T) s.ip++; if (s.ip < s.list.length && s.list[s.ip].t === live.T) { x = s.list[s.ip].x; s.ip++; } }
  live.tick(x);
  tickTimes.push(performance.now()); if (tickTimes.length > 4000) tickTimes.splice(0, 1000);
}
function loop() {
  timer = null;
  if (!live || live.done || paused) return;
  const now = performance.now(); acc += now - last; last = now;
  let n = 0;
  while (acc >= TICK && n < 10 && !live.done) {
    if (pauseAt !== null && live.T > pauseAt) { paused = true; post({ k: 'paused', t: live.T }); return; }
    doTick(); acc -= TICK; n++;
  }
  if (acc > TICK * 10) acc = 0;
  if (live.done) { post({ k: 'done' }); return; }
  timer = setTimeout(loop, 3);
}
async function runScripted() {
  while (live && !live.done) {
    if (pauseAt !== null && live.T > pauseAt) { paused = true; post({ k: 'paused', t: live.T }); return; }
    doTick();
    while (live.busy > 0) await new Promise(r => { waiter = r; });
    if (live.T % 300 === 0) await new Promise(r => setTimeout(r, 0));
  }
  post({ k: 'done' });
}
function begin(m) {
  if (timer) { clearTimeout(timer); timer = null; }
  const t = test && m;
  nonce++;
  const opt = { serverSeed: t && m.serverSeed || hexSeed(), clientSeed: t && m.clientSeed || 'rollerz-dev', nonce: t && m.nonce !== undefined ? m.nonce : nonce, forcedPlace: t && m.forcedPlace || null, rating: env.bank.gm.classic, test };
  live = new FFs.Live(env, opt, io());
  queuedX = null; paused = false; tickTimes = []; waiter = null; w2ms = 0;
  script = t && m.inputs ? { list: m.inputs, ip: 0 } : null;
  pauseAt = t && m.pauseAt !== undefined && m.pauseAt !== null ? m.pauseAt : null;
  scripted = !!(t && m.mode === 'scripted');
  acc = 0; last = performance.now();
  if (scripted) runScripted(); else timer = setTimeout(loop, 0);
}
self.onmessage = e => {
  const m = e.data;
  switch (m.k) {
    case 'boot':
      test = !!m.test; w2 = m.port; w2.onmessage = onW2;
      try {
        env = FFs.loadEnv(readBytes);
        post({ k: 'init', ok: true, copy: env.cfg.copy, radii: env.cfg.physics.radii, jar: { w: env.cfg.physics.jarW, h: env.cfg.physics.jarH, dropY: env.cfg.physics.dropY, overflowY: env.cfg.physics.overflowY }, drops: env.cfg.rules.classic.drops, places: env.cfg.board.places, rungs: env.cfg.rng.rungs.map(r => ({ id: r.id, label: r.label, tier: r.tier })), engineHash: env.hashes.engine.slice(0, 12), configHash: env.hashes.config.slice(0, 12), selfTest: { ok: env.selfTest.ok, bad: env.selfTest.bad } });
      } catch (err) { post({ k: 'init', ok: false, msg: String(err && err.message || err) }); }
      break;
    case 'start': if (env) begin(m); break;
    case 'drop': queuedX = +m.x; break;
    case 'resume': if (live && paused) { paused = false; pauseAt = m.pauseAt !== undefined ? m.pauseAt : null; last = performance.now(); acc = 0; if (scripted) runScripted(); else timer = setTimeout(loop, 0); } break;
    case 'stop': if (timer) clearTimeout(timer); timer = null; live = null; break;
    case 'getLog': if (test && live && live.log) post({ k: 'log', log: Object.assign({ w2ms, selfTest: { w1: env.selfTest, w2: w2Self } }, live.log) }); else post({ k: 'log', log: null }); break;
    case 'stats': {
      if (!test) { post({ k: 'stats', stats: null }); break; }
      const tt = tickTimes, per = []; for (let i = 0; i < tt.length; i++) { const sec = Math.floor((tt[i] - tt[0]) / 1000); per[sec] = (per[sec] || 0) + 1; }
      post({ k: 'stats', ticksPerSec: per.slice(0, -1), holdMs: live ? live.holdMs.slice() : [], w2ms });
      break;
    }
  }
};
