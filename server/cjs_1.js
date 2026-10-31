'use strict';
// cjs_1.js: a tiny synchronous CommonJS loader. readBytes(path) -> Uint8Array. Every loaded file's raw bytes and sha256 are recorded, so env_1.js can pin them.
(function (G) {
  G.FF = G.FF || {};
  function norm(p) { const out = []; for (const s of p.split('/')) { if (s === '' || s === '.') continue; if (s === '..') out.pop(); else out.push(s); } return out.join('/'); }
  function dirOf(p) { const i = p.lastIndexOf('/'); return i < 0 ? '' : p.slice(0, i); }
  G.FF.makeLoader = function (readBytes, sha256, hex) {
    const cache = new Map(), files = new Map(), dec = new TextDecoder('utf-8');
    function bytesOf(path) {
      path = norm(path);
      if (!files.has(path)) { const bytes = readBytes(path); files.set(path, { path, bytes, sha: hex(sha256(bytes)) }); }
      return files.get(path);
    }
    function load(path) {
      path = norm(path);
      if (cache.has(path)) return cache.get(path).exports;
      const f = bytesOf(path), module = { exports: {} };
      cache.set(path, module);
      const req = spec => {
        if (spec[0] !== '.') throw new Error('cjs_1: only relative requires are supported: ' + spec);
        let p = norm(dirOf(path) + '/' + spec); if (!/\.js$/.test(p)) p += '.js';
        return load(p);
      };
      const fn = new Function('module', 'exports', 'require', dec.decode(f.bytes) + '\n//# sourceURL=' + path);
      fn.call(G, module, module.exports, req);
      return module.exports;
    }
    return { load, bytesOf, files };
  };
})(typeof self !== 'undefined' ? self : globalThis);
