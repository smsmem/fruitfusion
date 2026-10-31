'use strict';
// look_worker_1.js (Worker 2): the lookaheads and the forward replay of the round, off the live tick (constant work, MATH_SPEC_7 section 7). Answers Worker 1 through a MessagePort.
importScripts('sha256_1.js', 'cjs_1.js', 'env_1.js', 'live_1.js');
const FFw = self.FF;
let tools = null, port = null;
function readBytes(p) {
  const x = new XMLHttpRequest(); x.open('GET', p, false); x.responseType = 'arraybuffer'; x.send(null);
  if (x.status !== 200 && x.status !== 0) throw new Error('GET ' + p + ' ' + x.status);
  return new Uint8Array(x.response);
}
self.onmessage = e => {
  const m = e.data;
  if (m.k !== 'boot') return;
  port = m.port;
  try { const env = FFw.loadEnv(readBytes); tools = FFw.lookTools(env); port.postMessage({ k: 'ready', engine: env.hashes.engine.slice(0, 12), config: env.hashes.config.slice(0, 12), selfTest: env.selfTest }); }
  catch (err) { port.postMessage({ k: 'fail', msg: String(err && err.message || err) }); return; }
  port.onmessage = ev => {
    const q = ev.data, t0 = performance.now();
    try {
      if (q.k === 'look') port.postMessage({ k: 'look', id: q.id, res: tools.runLook(q), ms: performance.now() - t0 });
      else if (q.k === 'work') { tools.lookaheadN({ o: q.o, inputs: q.inputs }, 18, {}); port.postMessage({ k: 'work', id: q.id, ms: performance.now() - t0 }); }
      else if (q.k === 'replay') port.postMessage({ k: 'replay', id: q.id, res: tools.forward(q.o, q.inputs, q.bonusFires), ms: performance.now() - t0 });
    } catch (err) { port.postMessage({ k: 'err', id: q.id, msg: String(err && err.stack || err) }); }
  };
};
