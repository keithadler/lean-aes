import * as React from 'react';
const e = React.createElement;

const SANS = "system-ui, -apple-system, 'Segoe UI', sans-serif";
const MONO = "ui-monospace, 'SF Mono', Menlo, monospace";
const hex = b => b.toString(16).padStart(2, '0');
const ON = '#e0822c', LINE = '#3f9d5f';
const COL = ['#e0822c', '#3b7dd8', '#9b59b6', '#2a9d8f'];

function Diff({ d, size }) {
  const cells = [];
  for (let r = 0; r < 4; r++) for (let c = 0; c < 4; c++) {
    const i = r + 4 * c, v = d[i];
    cells.push(e('g', { key: i },
      e('rect', { x: c * size + 2, y: r * size + 2, width: size - 4, height: size - 4, rx: 5,
        fill: v ? ON : 'currentColor', fillOpacity: v ? 0.95 : 0.08 }),
      v ? e('text', { x: c * size + size / 2, y: r * size + size / 2 + 5, textAnchor: 'middle',
        fontFamily: MONO, fontSize: size * 0.34, fill: '#fff' }, hex(v)) : null));
  }
  return e('svg', { width: 4 * size, height: 4 * size, style: { display: 'block' } }, cells);
}

export default function Trail(props) {
  const [p, setP] = React.useState(0);
  const pair = props.pairs[p];
  const total = pair.layers.reduce((s, l) => s + l.active, 0);
  const W = 600, H = 34, scale = W / 64;
  let x0 = 0;

  return e('div', { style: { fontFamily: SANS, lineHeight: 1.4, maxWidth: 800 } },
    e('div', { style: { fontSize: 20, fontWeight: 600 } }, 'Four rounds, at least 25 active S-boxes, and a pair that hits 25'),
    e('div', { style: { fontSize: 14, opacity: 0.75, margin: '2px 0 10px', maxWidth: 680 } },
      'Two blocks go through four rounds of AES. An S-box is active when its two inputs differ; every active S-box is a place a differential attack pays at most 4/256. Orange bytes are the difference x ⊕ y entering each round.'),
    e('div', { style: { marginBottom: 10 } },
      props.pairs.map((q, k) => e('button', { key: k, onClick: () => setP(k), style: { font: `14px ${SANS}`,
        padding: '4px 11px', marginRight: 8, borderRadius: 7, cursor: 'pointer',
        border: `1.5px solid ${ON}`, background: k === p ? ON : 'transparent', color: k === p ? '#fff' : 'inherit' } }, q.name))),
    e('div', { style: { display: 'flex', gap: 14, alignItems: 'flex-end' } },
      pair.layers.map((l, k) => e('div', { key: k, style: { textAlign: 'center' } },
        e('div', { style: { fontSize: 13, opacity: 0.7, marginBottom: 3 } }, `into round ${k + 1}`),
        e(Diff, { d: l.diff, size: 34 }),
        e('div', { style: { fontSize: 20, fontWeight: 600, color: COL[k], marginTop: 3 } }, l.active)))),
    e('div', { style: { fontSize: 13, opacity: 0.7, margin: '14px 0 4px' } }, 'active S-boxes, added up'),
    e('svg', { width: W + 60, height: H + 26, style: { display: 'block' } },
      pair.layers.map((l, k) => { const w = l.active * scale, r = e('rect', { key: k, x: x0, y: 4, width: w, height: H,
        fill: COL[k], fillOpacity: 0.85 }); x0 += w; return r; }),
      e('line', { x1: 25 * scale, x2: 25 * scale, y1: 0, y2: H + 8, stroke: LINE, strokeWidth: 3 }),
      e('text', { x: 25 * scale, y: H + 22, textAnchor: 'middle', fontSize: 13, fill: LINE, fontFamily: SANS }, '25, the proved minimum'),
      e('text', { x: total * scale + 8, y: H / 2 + 9, fontSize: 18, fontWeight: 600, fill: 'currentColor', fontFamily: SANS }, total)),
    e('div', { style: { fontSize: 16, margin: '8px 0 0' } },
      e('b', null, pair.layers.map(l => l.active).join(' + ') + ` = ${total}`), `   ${pair.note.split(': ')[1] ?? ''}`),
    e('div', { style: { fontSize: 13.5, opacity: 0.8, margin: '6px 0', maxWidth: 680 } },
      p === 0 ? 'Built backwards: the 4 bytes on the diagonal are chosen so that, after the S-box and ShiftRows gather them into one column, MixColumns turns them into a single byte. Branch number 5 then forces 1 → 4 → 16.'
              : 'One changed byte becomes a column of 4 after MixColumns, then all 16 bytes a round later, and stays spread.'),
    e('div', { style: { fontSize: 12.5, opacity: 0.65, marginTop: 10, fontFamily: MONO } },
      props.proved.map((s, k) => e('div', { key: k }, s))));
}
