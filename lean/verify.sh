#!/usr/bin/env bash
# Complete canonical verification: no conditional result can satisfy this command.
set -euo pipefail
source_dir="$(cd "$(dirname "$0")" && pwd -P)"
source_root="$(cd "$source_dir/.." && pwd -P)"
export PYTHONDONTWRITEBYTECODE=1
python3 "$source_root/scripts/check_canonical_statement.py" --root "$source_root"
if [[ ! -f "$source_dir/SingularValueBounds/Canonical/Results.lean" ]]; then
  printf '%s\n' 'Missing complete canonical proof interface: Canonical/Results.lean.' >&2
  exit 1
fi
# The acceptance command builds every maintained module, independently replays
# it, audits every safe declaration and checks complete source coverage and all
# exact canonical results. Do not repeat a full-library diagnostic beforehand.
"$source_dir/check_acceptance.sh"
printf '%s\n' 'PASS: complete canonical Lean targets, comparisons, and axiom audits.'
