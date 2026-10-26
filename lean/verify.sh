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
# Report every current supporting theorem and complete source coverage here.
# The acceptance command then independently replays every maintained module
# and checks the exact canonical results and comparisons. Avoid a second replay.
SVB_AUDIT_MODE=diagnostic "$source_dir/check.sh"
"$source_dir/check_acceptance.sh"
printf '%s\n' 'PASS: complete canonical Lean targets, comparisons, and axiom audits.'
