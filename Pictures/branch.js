import * as React from 'react';
const e = React.createElement;

const SANS = "system-ui, -apple-system, 'Segoe UI', sans-serif";
const MONO = "ui-monospace, 'SF Mono', Menlo, monospace";
const hex = b => b.toString(16).padStart(2, '0');
const ON = '#e0822c', OK = '#3f9d5f';

export default function Branch(props) {
  const m2 = props.mul2, m3 = props.mul3;
  const mix = a => [m2[a[0]] ^ m3[a[1]] ^ a[2] ^ a[3], a[0] ^ m2[a[1]] ^ m3[a[2]] ^ a[3],
                    a[0] ^ a[1] ^ m2[a[2]] ^ m3[a[3]], m3[a[0]] ^ a[1] ^ a[2] ^ m2[a[3]]];
  // The page's MixColumns, checked against Lean's mixColumn before anything is drawn.
  const agree = props.samples.every(([i, o]) => mix(i).every((v, k) => v === o[k]));
  const [col, setCol] = React.useState(props.tight[0] ?? [1, 0, 0, 0]);
  const [text, setText] = React.useState(col.map(hex));
  const out = mix(col);
  const wIn = col.filter(b => b).length, wOut = out.filter(b => b).length;
  const zero = wIn === 0;

  const set = (k, v) => {
    const t = text.slice(); t[k] = v; setText(t);
    const n = parseInt(v, 16);
    if (/^[0-9a-fA-F]{1,2}$/.test(v)) { const c = col.slice(); c[k] = n; setCol(c); }
  };
  const load = c => { setCol(c); setText(c.map(hex)); };

  const cell = (b, i, editable) => e('div', { key: i, style: { width: 64, height: 50, margin: 4, borderRadius: 8,
      display: 'flex', alignItems: 'center', justifyContent: 'center',
      background: b ? ON : 'rgba(128,128,128,.14)', color: b ? '#fff' : 'inherit' } },
    editable
      ? e('input', { value: text[i], onChange: ev => set(i, ev.target.value), maxLength: 2,
          style: { width: 44, font: `20px ${MONO}`, textAlign: 'center', background: 'transparent',
            border: 'none', color: 'inherit', outline: 'none' } })
      : e('span', { style: { font: `20px ${MONO}` } }, hex(b)));
  const column = (label, bytes, editable, w) => e('div', { style: { display: 'inline-block', verticalAlign: 'middle' } },
    e('div', { style: { fontSize: 13, opacity: 0.7, textAlign: 'center' } }, label),
    bytes.map((b, i) => cell(b, i, editable)),
    e('div', { style: { textAlign: 'center', fontSize: 14 } }, `${w} nonzero`));
  const btn = (label, f) => e('button', { onClick: f, style: { font: `13px ${SANS}`, padding: '3px 9px',
    marginRight: 6, marginBottom: 6, borderRadius: 7, border: '1px solid currentColor', background: 'transparent',
    color: 'inherit', cursor: 'pointer' } }, label);
  const rand = () => { const c = [0, 1, 2, 3].map(() => Math.random() < 0.5 ? 0 : 1 + Math.floor(Math.random() * 255));
    if (c.every(b => !b)) c[0] = 1; load(c); };

  return e('div', { style: { fontFamily: SANS, lineHeight: 1.4, maxWidth: 780 } },
    e('div', { style: { fontSize: 20, fontWeight: 600 } }, 'MixColumns spreads every difference: branch number 5'),
    e('div', { style: { fontSize: 14, opacity: 0.75, margin: '2px 0 10px', maxWidth: 640 } },
      'Type any column (hex). However few bytes you change going in, the nonzero bytes in and out add up to at least 5, so a difference can never slip through a round quietly.'),
    e('div', { style: { marginBottom: 6 } },
      btn('one byte', () => load([1, 0, 0, 0])), btn('tight: 2 in, 3 out', () => load(props.tight[0])),
      btn('another tight one', () => load(props.tight[Math.floor(Math.random() * props.tight.length)])),
      btn('random', rand)),
    e('div', { style: { display: 'flex', alignItems: 'center', gap: 22 } },
      column('column in (edit me)', col, true, wIn),
      e('div', { style: { textAlign: 'center' } },
        e('div', { style: { fontFamily: MONO, fontSize: 13, opacity: 0.8, lineHeight: 1.5 } },
          '02 03 01 01', e('br'), '01 02 03 01', e('br'), '01 01 02 03', e('br'), '03 01 01 02'),
        e('div', { style: { fontSize: 26, margin: '6px 0' } }, '→')),
      column('MixColumns', out, false, wOut),
      e('div', { style: { marginLeft: 10 } },
        e('div', { style: { fontSize: 44, fontWeight: 700, color: zero ? 'inherit' : OK } }, zero ? '0' : `${wIn + wOut}`),
        e('div', { style: { fontSize: 15 } }, zero ? 'the zero column is the only exception' : `${wIn} + ${wOut} ≥ 5`),
        wIn + wOut === 5 ? e('div', { style: { fontSize: 13, color: ON, marginTop: 4 } }, 'exactly 5: the bound is tight') : null)),
    e('div', { style: { fontSize: 12.5, opacity: 0.65, marginTop: 14, fontFamily: MONO } },
      e('div', null, agree ? `✓ this page's MixColumns matches Lean's mixColumn on all ${props.samples.length} sample columns`
                           : '✗ this page disagrees with Lean on a sample column'),
      props.proved.map((s, k) => e('div', { key: k }, s))));
}
