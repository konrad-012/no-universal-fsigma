#!/usr/bin/env bash
# Routine source, build, and axiom checks. Comparator adds sandboxed proof replay.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
cd -- "$repo_root"

python3 scripts/check-sources.py
python3 scripts/check-sources.py --compiler
lake --wfail build NoUniversalFSigma Solution
# Challenge intentionally has a sorry: it is the independently reviewed specification.
lake build Challenge

report=$(mktemp)
trap 'rm -f -- "$report"' EXIT
printf '%s\n' 'module' 'public import Solution' \
  '#print axioms NoUniversalFSigma.not_isUniversalFSigma' | \
  lake env lean --stdin | tee "$report"
python3 - "$report" <<'PY'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text()
match = re.search(r"depends on axioms:\s*\[([^]]*)\]", text)
if match:
    used = {name.strip() for name in match.group(1).split(',') if name.strip()}
    illegal = used - {"propext", "Classical.choice", "Quot.sound"}
    if illegal:
        raise SystemExit(f"Forbidden theorem axioms: {sorted(illegal)}")
elif "does not depend on any axioms" not in text:
    raise SystemExit("Could not read the main theorem's axiom report")
print("The main theorem uses only standard Lean axioms")
PY
