'use strict';
// server_worker_8.js (PREVIEW): one worker runs the math_8 top-out round at 60 ticks/s (live_8.js) and posts frames, board snapshots, the end and the final board.
importScripts('sha256_1.js', 'cjs_1.js', 'env_8.js', 'live_8.js');
const FFs = self.FF, TICK = 1000 / 60;
let env = null, live = null, test = false, nonce = 0, queuedX = null, timer = null, acc = 0, last = 0;
function readBytes(p) {
  const x = new XMLHttpRequest(); x.open('GET', p, false); x.responseType = 'arraybuffer'; x.send(null);
  if (x.status !== 200 && x.status !== 0) throw new Error('GET ' + p + ' ' + x.status);
  return new Uint8Array(x.response);
}
const post = m => { self.postMessage(m); };
function hexSeed() { const a = new Uint8Array(32); self.crypto.getRandomValues(a); return FFs.hex(a); }
const io = { emit: m => post(m), now: () => performance.now() };
function loop() {
  timer = null;
  if (!live || live.done) return;
  const now = performance.now(); acc += now - last; last = now;
  let n = 0;
  while (acc >= TICK && n < 10 && !live.done) { const x = queuedX; queuedX = null; live.tick(x); acc -= TICK; n++; }
  if (acc > TICK * 10) acc = 0;
  if (live.done) { post({ k: 'done' }); return; }
  timer = setTimeout(loop, 3);
}
function begin(m) {
  if (timer) { clearTimeout(timer); timer = null; }
  const t = test && m; nonce++;
  const opt = { serverSeed: t && m.serverSeed || hexSeed(), clientSeed: t && m.clientSeed || 'rollerz-dev', nonce: t && m.nonce !== undefined ? m.nonce : nonce, forcedPlace: t && m.forcedPlace || null, rating: env.bank.gm.topout, test };
  try { live = new FFs.Live(env, opt, io); } catch (err) { post({ k: 'srvErr', msg: String(err && err.stack || err) }); return; }
  queuedX = null; acc = 0; last = performance.now();
  timer = setTimeout(loop, 0);
}
self.onmessage = e => {
  const m = e.data;
  switch (m.k) {
    case 'boot':
      test = !!m.test;
      try {
        env = FFs.loadEnv(readBytes);
        const P = env.cfg.physics;
        post({ k: 'init', ok: true, copy: env.cfg.copy, radii: P.radii.concat([env.cfg.pom.r]), jar: { w: P.jarW, h: P.jarH, dropY: P.dropY, overflowY: P.overflowY }, hWarn: env.cfg.clock.hWarn, places: env.cfg.board.places, rungs: env.cfg.rng.rungs.map(r => ({ id: r.id, label: r.label, tier: r.tier })), engineHash: env.hashes.engine.slice(0, 12), configHash: env.hashes.config.slice(0, 12), selfTest: { ok: env.selfTest.ok, bad: env.selfTest.bad } });
      } catch (err) { post({ k: 'init', ok: false, msg: String(err && err.message || err) }); }
      break;
    case 'start': if (env) begin(m); break;
    case 'drop': queuedX = +m.x; break;
    case 'stop': if (timer) clearTimeout(timer); timer = null; live = null; break;
    case 'getLog': post({ k: 'log', log: test && live && live.log ? live.log : null }); break;
  }
};
