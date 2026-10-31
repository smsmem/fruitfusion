'use strict';
// env_1.js: browser/Node port of harness_7.js loadEnv() (lines 30-56): same checks, same hashes, no fs. Build code, not math.
// FF.loadEnv(readBytes) -> {cfg, bank, kern, hashes, E, Matter, RV, rngm, sha256, hexs, files}. Any failed check throws (the page then never starts a round).
(function (G) {
  const FF = G.FF = G.FF || {};
  const PIN = {
    engine: 'fc71c06bf781696a50d0422f6c795278256f74317565c27293d26084746a973c',
    config: 'fcae0b4d1ff3e83c2bf20fed2fefb4ebc9a46eca729e7b925a88b51eaa0fc964',
    kern: 'ed719ba40be70299d06bfd533b8f152b5f101f83932f517512698f960ec59ae0',
    bankFile: '2bfc23160b57a47ef338b8d8c7734105f83b0b1895a23ab92f773de074cc0618',
    matter: '016f108075a42e8bb8f75c43cf5b6d9f07b1d88857975ed9d96b0ede921416ce',
    cfgFile: '3a625ea10edd95eb33ce91a613dadfae86249d7f4fcdad3578c459143467af4a'
  };
  function canon(v) { // harness_7.js canon, verbatim
    if (Array.isArray(v)) return '[' + v.map(canon).join(',') + ']';
    if (v && typeof v === 'object') return '{' + Object.keys(v).sort().map(k => JSON.stringify(k) + ':' + canon(v[k])).join(',') + '}';
    return JSON.stringify(v);
  }

  // ---- determinism shim: Math.sin / Math.cos. V8's sin/cos differ by one ulp in about 3% of inputs between Node 24 (the math_7 harness) and Chromium. The engine, Matter and the Rival
  // layer call them (positions, angles, gaussian draws), so a replay in the page would drift from the batch result. FF.installTrig() replaces Math.sin/cos in the Worker with the
  // fdlibm routines (a port of V8's base/ieee754 sin/cos, which is what Node 24 runs); |x| beyond 2^19 pi/2 falls back to the native function. Checked by G1(c) against Node vectors.
  const _f = new Float64Array(1), _u = new Uint32Array(_f.buffer);
  const hiW = x => { _f[0] = x; return _u[1] | 0; };
  const S1 = -1.66666666666666324348e-01, S2 = 8.33333333332248946124e-03, S3 = -1.98412698298579493134e-04, S4 = 2.75573137070700676789e-06, S5 = -2.50507602534068634195e-08, S6 = 1.58969099521155010221e-10;
  const C1 = 4.16666666666666019037e-02, C2 = -1.38888888888741095749e-03, C3 = 2.48015872894767294178e-05, C4 = -2.75573143513906633035e-07, C5 = 2.08757232129817482790e-09, C6 = -1.13596475577881948265e-11;
  const invpio2 = 6.36619772367581382433e-01, pio2_1 = 1.57079632673412561417e+00, pio2_1t = 6.07710050650619224932e-11, pio2_2 = 6.07710050630396597660e-11, pio2_2t = 2.02226624879595063154e-21, pio2_3 = 2.02226624871116645580e-21, pio2_3t = 8.47842766036889956997e-32;
  const NPIO2 = [0x3FF921FB, 0x400921FB, 0x4012D97C, 0x401921FB, 0x401F6A7A, 0x4022D97C, 0x4025FDBB, 0x402921FB, 0x402C463A, 0x402F6A7A, 0x4031475C, 0x4032D97C, 0x40346B9C, 0x4035FDBB, 0x40378FDB, 0x403921FB, 0x403AB41B, 0x403C463A, 0x403DD85A, 0x403F6A7A, 0x40407E4C, 0x4041475C, 0x4042106C, 0x4042D97C, 0x4043A28C, 0x40446B9C, 0x404534AC, 0x4045FDBB, 0x4046C6CB, 0x40478FDB, 0x404858EB, 0x404921FB];
  function kSin(x, y, iy) {
    const ix = hiW(x) & 0x7FFFFFFF;
    if (ix < 0x3E400000) { if ((x | 0) === 0) return x; }
    const z = x * x, v = z * x, r = S2 + z * (S3 + z * (S4 + z * (S5 + z * S6)));
    if (iy === 0) return x + v * (S1 + z * r);
    return x - ((z * (0.5 * y - v * r) - y) - v * S1);
  }
  function kCos(x, y) {
    const ix = hiW(x) & 0x7FFFFFFF;
    if (ix < 0x3E400000) { if ((x | 0) === 0) return 1; }
    const z = x * x, r = z * (C1 + z * (C2 + z * (C3 + z * (C4 + z * (C5 + z * C6)))));
    if (ix < 0x3FD33333) return 1 - (0.5 * z - (z * r - x * y));
    let qx;
    if (ix > 0x3FE90000) qx = 0.28125; else { _u[1] = (ix - 0x00200000) >>> 0; _u[0] = 0; qx = _f[0]; }
    const iz = 0.5 * z - qx, a = 1 - qx;
    return a - (iz - (z * r - x * y));
  }
  let Y0 = 0, Y1 = 0;
  function remPio2(x) { // returns n; y in Y0, Y1 (|x| <= 2^19 pi/2)
    const hx = hiW(x), ix = hx & 0x7fffffff;
    if (ix <= 0x3fe921fb) { Y0 = x; Y1 = 0; return 0; }
    if (ix < 0x4002d97c) {
      if (hx > 0) { let z = x - pio2_1; if (ix !== 0x3ff921fb) { Y0 = z - pio2_1t; Y1 = (z - Y0) - pio2_1t; } else { z -= pio2_2; Y0 = z - pio2_2t; Y1 = (z - Y0) - pio2_2t; } return 1; }
      let z = x + pio2_1; if (ix !== 0x3ff921fb) { Y0 = z + pio2_1t; Y1 = (z - Y0) + pio2_1t; } else { z += pio2_2; Y0 = z + pio2_2t; Y1 = (z - Y0) + pio2_2t; } return -1;
    }
    let t = Math.abs(x);
    const n = (t * invpio2 + 0.5) | 0, fn = n;
    let r = t - fn * pio2_1, w = fn * pio2_1t;
    if (n < 32 && ix !== NPIO2[n - 1]) Y0 = r - w;
    else {
      const j = ix >> 20;
      Y0 = r - w; let high = hiW(Y0), i = j - ((high >>> 20) & 0x7ff);
      if (i > 16) {
        t = r; w = fn * pio2_2; r = t - w; w = fn * pio2_2t - ((t - r) - w); Y0 = r - w;
        high = hiW(Y0); i = j - ((high >>> 20) & 0x7ff);
        if (i > 49) { t = r; w = fn * pio2_3; r = t - w; w = fn * pio2_3t - ((t - r) - w); Y0 = r - w; }
      }
    }
    Y1 = (r - Y0) - w;
    if (hx < 0) { Y0 = -Y0; Y1 = -Y1; return -n; }
    return n;
  }
  const nativeSin = Math.sin, nativeCos = Math.cos;
  function fSin(x) {
    const ix = hiW(x) & 0x7FFFFFFF;
    if (ix <= 0x3FE921FB) return kSin(x, 0, 0);
    if (ix >= 0x7FF00000) return x - x;
    if (ix > 0x413921fb) return nativeSin(x);
    const n = remPio2(x), y0 = Y0, y1 = Y1;
    switch (n & 3) { case 0: return kSin(y0, y1, 1); case 1: return kCos(y0, y1); case 2: return -kSin(y0, y1, 1); default: return -kCos(y0, y1); }
  }
  function fCos(x) {
    const ix = hiW(x) & 0x7FFFFFFF;
    if (ix <= 0x3FE921FB) return kCos(x, 0);
    if (ix >= 0x7FF00000) return x - x;
    if (ix > 0x413921fb) return nativeCos(x);
    const n = remPio2(x), y0 = Y0, y1 = Y1;
    switch (n & 3) { case 0: return kCos(y0, y1); case 1: return -kSin(y0, y1, 1); case 2: return -kCos(y0, y1); default: return kSin(y0, y1, 1); }
  }
  FF.fSin = fSin; FF.fCos = fCos; FF.nativeSin = nativeSin; FF.nativeCos = nativeCos;
  FF.installTrig = function () { Math.sin = fSin; Math.cos = fCos; };

  // ---- float self-test (rev 1, N1): 2,000 inputs per function from a build-local splitmix64 (constant seed "b1-selftest"); the output doubles (little-endian) are hashed with SHA-256 and compared with
  // digests pinned from the pinned Node (tools/gates/make_selftest.js). Draw-blind: constants only, runs at boot. A mismatch never stops the page (dev); it marks the replay check as off.
  function selfInputs() {
    let st = 0xcbf29ce484222325n; for (const ch of 'b1-selftest') { st ^= BigInt(ch.charCodeAt(0)); st = (st * 0x100000001b3n) & 0xffffffffffffffffn; }
    const M = 0xffffffffffffffffn;
    const next = () => { st = (st + 0x9e3779b97f4a7c15n) & M; let z = st; z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & M; z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & M; return z ^ (z >> 31n); };
    const u = () => Number(next() >> 11n) / 9007199254740992; // [0,1)
    const p2 = e => { let v = 1; if (e >= 0) for (let i = 0; i < e; i++) v *= 2; else for (let i = 0; i < -e; i++) v /= 2; return v; }; // exact powers of two, no library call
    const logu = (e0, e1) => (1 + u()) * p2(e0 + Math.floor(u() * (e1 - e0 + 1))); // base-2 log-uniform, built from exact arithmetic only
    const TAU = 6.283185307179586, o = { sin: [], cos: [], exp: [], log: [], pow: [], atan2: [] };
    for (let i = 0; i < 2000; i++) {
      const x = i < 1600 ? (u() * 2 - 1) * TAU : (u() * 2 - 1) * 1e4;
      o.sin.push(x); o.cos.push(x);
      o.exp.push((u() * 2 - 1) * 30);
      o.log.push(logu(-30, 29));
      o.pow.push([logu(-10, 9), (u() * 2 - 1) * 4]);
      o.atan2.push([(u() * 2 - 1) * 1e3, (u() * 2 - 1) * 1e3]);
    }
    return o;
  }
  function selfDigests() {
    const I = selfInputs(), out = {}, f = new Float64Array(2000), b = new Uint8Array(f.buffer), hexs = FF.hex;
    const run = (name, fn) => { for (let i = 0; i < 2000; i++) f[i] = fn(I[name][i]); out[name] = hexs(FF.sha256(b)); };
    run('sin', x => Math.sin(x)); run('cos', x => Math.cos(x)); run('exp', x => Math.exp(x)); run('log', x => Math.log(x));
    run('pow', a => Math.pow(a[0], a[1])); run('atan2', a => Math.atan2(a[0], a[1]));
    return out;
  }
  const SELF_PIN = {"sin":"1d8359dd644272a9fad8e4921b0e5f48894759f1749ee1ce2978346c4920c881","cos":"5a7b2552108463272e999b5d036b6b5e36561a1abe07ac56409ca01066242586","exp":"a946a12e7204cd3a69de85e193ec04154de3053201c78a5f1c6862cf56fd09ab","log":"d8e83bfc825a2699e14d2f3b375ef974917614de6dc3fcd7942b6170b656b525","pow":"c8daacd59b33c570f4b6a8934e8021f8c33eda01319ed6ef5193b296a29d63dc","atan2":"7531e3ffe319862514529d6b6beb6f89047db8b26a049cf56425d36346cd3934"}; // @@pin
  FF.selfDigests = selfDigests; FF.SELF_PIN = SELF_PIN;
  FF.selfTest = function () { const t0 = typeof performance !== 'undefined' ? performance.now() : 0, d = selfDigests(), bad = Object.keys(SELF_PIN).filter(k => d[k] !== SELF_PIN[k]); if (!Object.keys(SELF_PIN).length) bad.push('unpinned'); return { ok: bad.length === 0, bad, ms: Math.round((typeof performance !== 'undefined' ? performance.now() : 0) - t0) }; };
  FF.canon = canon; FF.PIN = PIN;
  FF.loadEnv = function (readBytes) {
    FF.installTrig();
    const sha256 = FF.sha256, hexs = FF.hex, enc = new TextEncoder(), dec = new TextDecoder('utf-8');
    const L = FF.makeLoader(readBytes, sha256, hexs);
    const need = (ok, m) => { if (!ok) throw new Error('env check failed: ' + m); };
    const cfgF = L.bytesOf('math_7/config_7.json'), bankF = L.bytesOf('math_7/common/bank_summary.json'), kernF = L.bytesOf('math_7/common/kern.json');
    need(cfgF.sha === PIN.cfgFile, 'config_7.json bytes');
    const cfg = JSON.parse(dec.decode(cfgF.bytes)), frozen = cfg.frozenConfigHash;
    delete cfg.frozenConfigHash;
    const bank = JSON.parse(dec.decode(bankF.bytes));
    need(bankF.sha === PIN.bankFile, 'bank_summary.json bytes');
    for (const m of ['classic']) need(Math.abs(cfg.bank.gm_pop[m] - bank.gm[m]) <= 1e-6 && Math.abs(cfg.bank.kappa[m] - bank.kappa[m]) <= 1e-4 && cfg.bank.w5[m] === bank.w5[m], 'config bank constants do not match bank_summary.json');
    const kern = JSON.parse(dec.decode(kernF.bytes)); kern.sha = kernF.sha;
    need(kernF.sha === cfg.board.kernSha256 && kernF.sha === PIN.kern, 'kern.json sha256');
    need(kern.bankSha256 === bankF.sha, 'kern.json was fitted on another bank');
    const names = ['math_7/engine_7.js', 'math_7/rivals_7.js', 'math_7/kernlib.js', 'math_7/common/geom.js', 'math_7/common/rng.js'];
    let tot = 0; const fb = names.map(n => L.bytesOf(n).bytes); for (const b of fb) tot += b.length;
    const cat = new Uint8Array(tot); { let o = 0; for (const b of fb) { cat.set(b, o); o += b.length; } }
    const hashes = { engine: hexs(sha256(cat)), config: hexs(sha256(enc.encode(canon(cfg)))), bank: hexs(sha256(enc.encode(canon(bank)))), kern: kernF.sha };
    need(hashes.engine === PIN.engine, 'engineHash ' + hashes.engine);
    need(hashes.config === PIN.config && hashes.config === frozen, 'configHash ' + hashes.config);
    const mb = L.bytesOf('vendor/matter-js-0.20.0/matter.js'); need(mb.sha === PIN.matter, 'matter.js bytes');
    const Matter = L.load('vendor/matter-js-0.20.0/matter.js');
    need(Matter && Matter.Engine && Matter.version === '0.20.0', 'Matter 0.20.0');
    const makeEngine = L.load('math_7/engine_7.js'), RV = L.load('math_7/rivals_7.js'), rngm = L.load('math_7/common/rng.js');
    const E = makeEngine(Matter, sha256, cfg, hashes);
    const selfTest = FF.selfTest(); // step 6 (rev 1, N1): after step 3, after installTrig
    return { cfg, bank, kern, hashes, E, Matter, RV, rngm, sha256, hexs, files: L.files, selfTest };
  };
})(typeof self !== 'undefined' ? self : globalThis);
