#!/usr/bin/env bash
# Use the project's bundled checkers, matching Palomar's verification policy.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
cd -- "$repo_root"
for tool in bwrap lake lean python3; do
  command -v "$tool" >/dev/null || { echo "Missing required tool: $tool" >&2; exit 1; }
done
export COMPARATOR_BWRAP
COMPARATOR_BWRAP=$(command -v bwrap)
python3 scripts/check-sources.py
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [[ ! -x "$prefix/bin/$tool" ]]; then
    echo "The selected toolchain does not bundle $tool; use Lean 4.35.0-rc2 or later." >&2
    exit 1
  fi
done
config=$(mktemp)
trap 'rm -f -- "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
from pathlib import Path
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text())
if "external_kernels" in config:
    raise SystemExit("external_kernels is verifier-owned, not a submitted configuration field")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
Path(destination).write_text(json.dumps(config, indent=2) + "\n")
PY
# Keep bubblewrap enabled. No exports or unsandboxed fallbacks replace the source check.
lake comparator --config "$config"
