import * as React from 'react';
const e = React.createElement;

const SANS = "system-ui, -apple-system, 'Segoe UI', sans-serif";
const MONO = "ui-monospace, 'SF Mono', Menlo, monospace";
const hex = b => b.toString(16).padStart(2, '0');
const COLORS = ['transparent', '#3b7dd8', '#e0822c'];

export default function Differences(props) {
  const canvas = React.useRef(null);
  const [hot, setHot] = React.useState({ a: 1, b: 31 });
  const P = 2; // pixels per cell
  const counts = React.useMemo(() => {
    const n = [0, 0, 0];
    for (const ch of props.cells) n[ch.charCodeAt(0) - 48]++;
    return n;
  }, [props.cells]);

  React.useEffect(() => {
    const ctx = canvas.current.getContext('2d');
    ctx.clearRect(0, 0, 256 * P, 255 * P);
    for (let a = 1; a < 256; a++) for (let b = 0; b < 256; b++) {
      const v = props.cells.charCodeAt((a - 1) * 256 + b) - 48;
      if (v) { ctx.fillStyle = COLORS[v]; ctx.fillRect(b * P, (a - 1) * P, P, P); }
    }
  }, [props.cells]);

  const at = ev => {
    const r = canvas.current.getBoundingClientRect();
    const b = Math.floor((ev.clientX - r.left) / (r.width / 256));
    const a = Math.floor((ev.clientY - r.top) / (r.height / 255)) + 1;
    if (a >= 1 && a < 256 && b >= 0 && b < 256) setHot({ a, b });
  };
  const S = props.sbox;
  const xs = [];
  for (let x = 0; x < 256; x++) if ((S[x ^ hot.a] ^ S[x]) === hot.b) xs.push(x);

  const legend = (color, label, n) => e('span', { style: { marginRight: 16, whiteSpace: 'nowrap' } },
    e('span', { style: { display: 'inline-block', width: 11, height: 11, background: color, borderRadius: 2,
      border: color === 'transparent' ? '1px solid currentColor' : 'none', marginRight: 5, verticalAlign: -1 } }),
    `${label}: ${n.toLocaleString()} cells`);

  return e('div', { style: { fontFamily: SANS, lineHeight: 1.4, maxWidth: 780 } },
    e('div', { style: { fontSize: 20, fontWeight: 600 } }, 'The S-box difference table: never more than 4'),
    e('div', { style: { fontSize: 14, opacity: 0.75, margin: '2px 0 10px', maxWidth: 640 } },
      'Row a, column b counts the inputs x with S(x ⊕ a) ⊕ S(x) = b. A differential attack needs a large entry. Out of 256, the largest is 4.'),
    e('div', { style: { display: 'flex', gap: 18, alignItems: 'flex-start', flexWrap: 'wrap' } },
      e('div', null,
        e('div', { style: { fontSize: 12, opacity: 0.6 } }, 'output difference b = 00 … ff →'),
        e('canvas', { ref: canvas, width: 256 * P, height: 255 * P, onMouseMove: at,
          style: { width: 384, height: 383, imageRendering: 'pixelated', border: '1px solid rgba(128,128,128,.35)',
            cursor: 'crosshair', display: 'block' } }),
        e('div', { style: { fontSize: 12, opacity: 0.6 } }, '↑ input difference a = 01 … ff, top to bottom')),
      e('div', { style: { minWidth: 220 } },
        e('div', { style: { fontFamily: MONO, fontSize: 16 } }, `a = ${hex(hot.a)}, b = ${hex(hot.b)}`),
        e('div', { style: { fontSize: 30, fontWeight: 600, color: COLORS[xs.length / 2] === 'transparent' ? 'inherit' : COLORS[xs.length / 2] } },
          `${xs.length} of 256`),
        e('div', { style: { fontSize: 13, opacity: 0.75, margin: '4px 0' } },
          xs.length ? 'inputs x with S(x ⊕ a) ⊕ S(x) = b:' : 'no input reaches this difference'),
        e('div', { style: { fontFamily: MONO, fontSize: 14 } }, xs.map(hex).join('  ')),
        e('div', { style: { fontSize: 13, marginTop: 14, lineHeight: 1.8 } },
          legend(COLORS[2], '4 inputs', counts[2]), e('br'),
          legend(COLORS[1], '2 inputs', counts[1]), e('br'),
          legend(COLORS[0], '0 inputs', counts[0])))),
    e('div', { style: { fontSize: 12.5, opacity: 0.65, marginTop: 12, fontFamily: MONO } },
      props.proved.map((s, k) => e('div', { key: k }, s))));
}
