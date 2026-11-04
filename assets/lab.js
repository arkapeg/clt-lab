/* Stats Teaching Lab: shared math and drawing helpers. */
window.Lab = (function () {
  'use strict';

  // ---------- Random numbers ----------
  function gauss() { let u = 0, v = 0; while (!u) u = Math.random(); while (!v) v = Math.random(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v); }
  function seeded(seed) { // mulberry32
    let a = seed >>> 0;
    const r = () => { a = (a + 0x6D2B79F5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
    r.gauss = () => { let u = 0, v = 0; while (!u) u = r(); while (!v) v = r(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v); };
    return r;
  }

  // ---------- Distributions ----------
  function erf(x) {
    const s = x < 0 ? -1 : 1; x = Math.abs(x);
    const t = 1 / (1 + 0.3275911 * x);
    const y = 1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-x * x);
    return s * y;
  }
  const normPdf = z => Math.exp(-0.5 * z * z) / Math.sqrt(2 * Math.PI);
  const normCdf = z => 0.5 * (1 + erf(z / Math.SQRT2));
  function normInv(p) { // Acklam
    const a = [-3.969683028665376e+01, 2.209460984245205e+02, -2.759285104469687e+02, 1.383577518672690e+02, -3.066479806614716e+01, 2.506628277459239e+00];
    const b = [-5.447609879822406e+01, 1.615858368580409e+02, -1.556989798598866e+02, 6.680131188771972e+01, -1.328068155288572e+01];
    const c = [-7.784894002430293e-03, -3.223964580411365e-01, -2.400758277161838e+00, -2.549732539343734e+00, 4.374664141464968e+00, 2.938163982698783e+00];
    const d = [7.784695709041462e-03, 3.224671290700398e-01, 2.445134137142996e+00, 3.754408661907416e+00];
    const pl = 0.02425;
    if (p < pl) { const q = Math.sqrt(-2 * Math.log(p)); return (((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1); }
    if (p > 1 - pl) { const q = Math.sqrt(-2 * Math.log(1 - p)); return -(((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1); }
    const q = p - 0.5, r = q * q;
    return (((((a[0] * r + a[1]) * r + a[2]) * r + a[3]) * r + a[4]) * r + a[5]) * q / (((((b[0] * r + b[1]) * r + b[2]) * r + b[3]) * r + b[4]) * r + 1);
  }
  function lgamma(x) {
    const g = 7, c = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059, 12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
    if (x < 0.5) return Math.log(Math.PI / Math.sin(Math.PI * x)) - lgamma(1 - x);
    x -= 1; let a = c[0]; const t = x + g + 0.5;
    for (let i = 1; i < 9; i++) a += c[i] / (x + i);
    return 0.5 * Math.log(2 * Math.PI) + (x + 0.5) * Math.log(t) - t + Math.log(a);
  }
  function betacf(a, b, x) {
    const MAXIT = 300, EPS = 3e-14, FPMIN = 1e-300;
    const qab = a + b, qap = a + 1, qam = a - 1;
    let c = 1, d = 1 - qab * x / qap; if (Math.abs(d) < FPMIN) d = FPMIN; d = 1 / d; let h = d;
    for (let m = 1; m <= MAXIT; m++) {
      const m2 = 2 * m;
      let aa = m * (b - m) * x / ((qam + m2) * (a + m2));
      d = 1 + aa * d; if (Math.abs(d) < FPMIN) d = FPMIN; c = 1 + aa / c; if (Math.abs(c) < FPMIN) c = FPMIN; d = 1 / d; h *= d * c;
      aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2));
      d = 1 + aa * d; if (Math.abs(d) < FPMIN) d = FPMIN; c = 1 + aa / c; if (Math.abs(c) < FPMIN) c = FPMIN; d = 1 / d;
      const del = d * c; h *= del; if (Math.abs(del - 1) < EPS) break;
    }
    return h;
  }
  function ibeta(a, b, x) {
    if (x <= 0) return 0; if (x >= 1) return 1;
    const bt = Math.exp(lgamma(a + b) - lgamma(a) - lgamma(b) + a * Math.log(x) + b * Math.log(1 - x));
    return x < (a + 1) / (a + b + 2) ? bt * betacf(a, b, x) / a : 1 - bt * betacf(b, a, 1 - x) / b;
  }
  function tCdf(t, df) { const p = 0.5 * ibeta(df / 2, 0.5, df / (df + t * t)); return t > 0 ? 1 - p : p; }
  const tCache = {};
  function tInv(p, df) {
    const key = p + '|' + df; if (key in tCache) return tCache[key];
    let lo = -2000, hi = 2000;
    for (let i = 0; i < 120; i++) { const m = (lo + hi) / 2; if (tCdf(m, df) < p) lo = m; else hi = m; }
    return (tCache[key] = (lo + hi) / 2);
  }

  // ---------- Formatting ----------
  function fmt(x, d = 3) { return Number.isFinite(x) ? x.toFixed(d) : '–'; }
  function niceTicks(lo, hi, target) {
    const span = hi - lo, raw = span / Math.max(1, target), mag = Math.pow(10, Math.floor(Math.log10(raw)));
    const step = [1, 2, 2.5, 5, 10].map(m => m * mag).find(s => span / s <= target) || 10 * mag;
    const out = []; for (let t = Math.ceil(lo / step - 1e-9) * step; t <= hi + 1e-9; t += step) out.push(+t.toFixed(10));
    return out;
  }

  // ---------- Canvas ----------
  // The CSS height comes from the canvas's height attribute, read once and kept in data-h,
  // so resizing the bitmap for sharp screens never feeds back into the layout size.
  function setup(canvas) {
    const dpr = window.devicePixelRatio || 1, w = canvas.clientWidth;
    const h = +(canvas.dataset.h || (canvas.dataset.h = canvas.getAttribute('height')));
    canvas.style.height = h + 'px';
    const W = Math.round(w * dpr), H = Math.round(h * dpr);
    if (canvas.width !== W || canvas.height !== H) { canvas.width = W; canvas.height = H; }
    const ctx = canvas.getContext('2d'); ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, w, h);
    return { ctx, w, h };
  }
  function colors() {
    const cs = getComputedStyle(document.documentElement), g = k => cs.getPropertyValue(k).trim();
    return { ink: g('--ink'), muted: g('--muted'), rule: g('--rule'), surface: g('--surface'), pop: g('--pop'), popSoft: g('--pop-soft'),
      mean: g('--mean'), meanSoft: g('--mean-soft'), bad: g('--bad'), badSoft: g('--bad-soft'), curve: g('--curve'), mono: g('--f-mono') };
  }
  function onRedraw(fn, observeEl) {
    let rz;
    const go = () => { cancelAnimationFrame(rz); rz = requestAnimationFrame(fn); };
    if (observeEl) new ResizeObserver(go).observe(observeEl);
    window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', go);
    new MutationObserver(go).observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });
    if (document.fonts && document.fonts.ready) document.fonts.ready.then(go);
  }
  const reduceMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;

  // Simple chip group: buttons with aria-pressed. items: [{value, label}]
  function chips(container, items, current, onPick) {
    container.innerHTML = '';
    items.forEach(it => {
      const b = document.createElement('button'); b.type = 'button'; b.className = 'chip'; b.textContent = it.label; b.dataset.v = it.value;
      b.addEventListener('click', () => onPick(it.value));
      container.appendChild(b);
    });
    const sync = v => container.querySelectorAll('button').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.v === String(v))));
    sync(current);
    return sync;
  }

  return { gauss, seeded, normPdf, normCdf, normInv, tCdf, tInv, fmt, niceTicks, setup, colors, onRedraw, reduceMotion, chips };
})();
