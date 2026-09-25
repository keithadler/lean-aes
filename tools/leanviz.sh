#!/usr/bin/env bash
# Turn this project into a LeanViz site (https://github.com/keithadler/leanviz): a page for every
# declaration, its statement, what it uses and what uses it, the axioms it rests on, and Tenet's verdict.
#
#   tools/leanviz.sh            write the site to site/
#   tools/leanviz.sh --serve    and serve it at http://localhost:8787/?p=aes
#
# Needs the .NET 10 SDK and a built project. check.json from `tools/verify.sh` is stamped in when present.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
WORK=${LEANVIZ_WORK:-$ROOT/.lake/leanviz}
mkdir -p "$WORK"

[ -d "$WORK/leanviz" ] || git clone --depth 1 https://github.com/keithadler/leanviz.git "$WORK/leanviz"
[ -d "$WORK/tenet" ] || git clone --depth 1 https://github.com/keithadler/tenet.git "$WORK/tenet"
if [ ! -f "$WORK/leanviz/generator/bin/Release/net10.0/leanviz.dll" ]; then
  dotnet build "$WORK/tenet/src/Tenet.Olean" -c Release -f net10.0
  mkdir -p "$WORK/leanviz/lib"
  cp "$WORK/tenet/src/Tenet.Olean/bin/Release/net10.0/Tenet.Kernel.dll" \
     "$WORK/tenet/src/Tenet.Olean/bin/Release/net10.0/Tenet.Olean.dll" "$WORK/leanviz/lib/"
  dotnet build "$WORK/leanviz/generator" -c Release
fi

rm -rf site && cp -r "$WORK/leanviz/site" site
check=()
[ -f check.json ] && check=(--check check.json)
dotnet "$WORK/leanviz/generator/bin/Release/net10.0/leanviz.dll" "$ROOT" --out site/data --slug aes \
  --title "AES-256 in Lean" "${check[@]}" --repo https://github.com/keithadler/lean-aes
python3 "$WORK/leanviz/tests/check_bundle.py" site/data

if [ "${1:-}" = "--serve" ]; then
  echo "serving http://localhost:8787/?p=aes#/d/AES.four_rounds_active"
  python3 "$WORK/leanviz/tests/serve.py" 8787 site
fi
