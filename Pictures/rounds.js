import * as React from 'react';
const e = React.createElement;

const SANS = "system-ui, -apple-system, 'Segoe UI', sans-serif";
const MONO = "ui-monospace, 'SF Mono', Menlo, monospace";
const hex = b => b.toString(16).padStart(2, '0');
const block = s => s.map(hex).join('');
const hue = b => `hsl(${Math.round(b * 360 / 256)}, 55%, 42%)`;
const EXPLAIN = {
  Input: 'The plaintext of FIPS-197 C.3, laid out column by column: byte r + 4c sits at row r, column c.',
  SubBytes: 'Every byte goes through the S-box: its inverse in GF(2⁸), then an affine map.',
  ShiftRows: 'Row r rotates left by r places, so each column now holds bytes from four different columns.',
  MixColumns: 'Each column is multiplied by the fixed matrix [2 3 1 1; 1 2 3 1; 1 1 2 3; 3 1 1 2] over GF(2⁸).',
  AddRoundKey: 'The round key, taken from the key expansion, is XORed in.',
};

function Grid({ s, prev, size, label }) {
  const cells = [];
  for (let r = 0; r < 4; r++) for (let c = 0; c < 4; c++) {
    const i = r + 4 * c, changed = prev && prev[i] !== s[i];
    cells.push(e('g', { key: i },
      e('rect', { x: c * size + 2, y: r * size + 2, width: size - 4, height: size - 4, rx: 6,
        fill: hue(s[i]), fillOpacity: changed || !prev ? 0.95 : 0.35 }),
      e('text', { x: c * size + size / 2, y: r * size + size / 2 + 6, textAnchor: 'middle',
        fontFamily: MONO, fontSize: size * 0.34, fill: '#fff' }, hex(s[i]))));
  }
  return e('div', { style: { display: 'inline-block', marginRight: 18, verticalAlign: 'top' } },
    e('div', { style: { fontSize: 13, opacity: 0.7, marginBottom: 4 } }, label),
    e('svg', { width: 4 * size, height: 4 * size }, cells));
}

export default function Rounds(props) {
  const steps = props.steps;
  const [i, setI] = React.useState(steps.length - 1);
  const [play, setPlay] = React.useState(false);
  React.useEffect(() => {
    if (!play) return;
    const t = setTimeout(() => { if (i + 1 < steps.length) setI(i + 1); else setPlay(false); }, 450);
    return () => clearTimeout(t);
  }, [play, i]);
  const st = steps[i], prev = i > 0 ? steps[i - 1].state : null;
  const out = block(st.state);
  const done = i === steps.length - 1;
  const btn = (label, f) => e('button', { onClick: f, style: { font: `14px ${SANS}`, padding: '4px 10px',
    marginRight: 6, borderRadius: 7, border: '1px solid currentColor', background: 'transparent',
    color: 'inherit', cursor: 'pointer' } }, label);

  return e('div', { style: { fontFamily: SANS, lineHeight: 1.4, maxWidth: 780 } },
    e('div', { style: { fontSize: 20, fontWeight: 600 } }, 'AES-256, one step at a time'),
    e('div', { style: { fontSize: 14, opacity: 0.75, margin: '2px 0 10px' } },
      `FIPS-197 Appendix C.3, key ${props.cipherKey.slice(0, 16)}…${props.cipherKey.slice(-8)}. Every state below is computed by the Lean definitions the proofs are about.`),
    e('div', { style: { marginBottom: 10 } },
      btn('⏮', () => { setPlay(false); setI(0); }),
      btn('◀', () => { setPlay(false); setI(Math.max(0, i - 1)); }),
      btn(play ? '⏸' : '▶', () => { if (done) setI(0); setPlay(!play); }),
      btn('▶▎', () => { setPlay(false); setI(Math.min(steps.length - 1, i + 1)); }),
      e('input', { type: 'range', min: 0, max: steps.length - 1, value: i,
        onChange: ev => { setPlay(false); setI(Number(ev.target.value)); },
        style: { width: 260, verticalAlign: 'middle', marginLeft: 6 } })),
    e('div', { style: { fontSize: 17, marginBottom: 6 } },
      e('b', null, st.round === 0 && st.label === 'Input' ? 'Input' : `Round ${st.round}`),
      st.label === 'Input' ? '' : ` · ${st.label}`,
      e('span', { style: { opacity: 0.55, fontSize: 13 } }, `   step ${i + 1} of ${steps.length}`)),
    e(Grid, { s: st.state, prev, size: 64, label: prev ? 'State (bright cells changed in this step)' : 'State' }),
    st.key ? e(Grid, { s: st.key, prev: null, size: 40, label: `⊕ round key ${st.round}` }) : null,
    e('div', { style: { fontSize: 14, opacity: 0.8, margin: '10px 0 6px', maxWidth: 640 } }, EXPLAIN[st.label]),
    e('div', { style: { fontFamily: MONO, fontSize: 15, margin: '6px 0' } },
      out, done ? e('span', { style: { color: '#3f9d5f', fontFamily: SANS, marginLeft: 10 } },
        '✓ the FIPS-197 C.3 ciphertext') : null),
    e('div', { style: { fontSize: 12.5, opacity: 0.65, marginTop: 10, fontFamily: MONO } },
      props.proved.map((s, k) => e('div', { key: k }, s))));
}
