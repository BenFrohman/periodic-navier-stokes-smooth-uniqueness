#!/usr/bin/env bash
# One-command verification: bash scripts/verify.sh
set -euo pipefail
cd "$(dirname "$0")/.."
echo "== commit: $(git rev-parse HEAD 2>/dev/null || echo unknown)"
echo "== toolchain: $(cat lean-toolchain)"
echo "== mathlib rev: $(python3 -c 'import json;print(next(p["rev"] for p in json.load(open("lake-manifest.json"))["packages"] if p["name"]=="mathlib"))')"
lake exe cache get
lake build
echo "== source scan"
if grep -rnE '\bsorry\b|\badmit\b|native_decide|^[[:space:]]*axiom[[:space:]]' NSTorusUniqueness NSTorusUniqueness.lean AxiomAudit.lean; then
  echo "SOURCE SCAN FAILED"; exit 1
fi
echo "OK: no sorry/admit/native_decide/axiom declarations"
echo "== axiom audit"
lake env lean AxiomAudit.lean 2>&1 | tee axioms.txt
python3 - <<'PY'
import re,sys
txt=open('axioms.txt').read()
blocks=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",txt,re.S)
ok={'propext','Classical.choice','Quot.sound'}
bad=[(n,a) for n,a in blocks if not set(x.strip() for x in a.split(','))<=ok]
if not blocks or bad or 'error' in txt or 'sorryAx' in txt:
    print('AXIOM AUDIT FAILED',bad); sys.exit(1)
print(f'AXIOM AUDIT PASS: {len(blocks)} theorems, only propext, Classical.choice, Quot.sound')
if "AUDIT PASS:" not in txt: print("STRICT NAMESPACE AUDIT MISSING"); sys.exit(1)
PY
echo "VERIFY OK"
