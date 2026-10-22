#!/usr/bin/env bash
set -euo pipefail
lean_source_dir="$(cd "$(dirname "$0")" && pwd -P)"
repository_source_dir="$(cd "$lean_source_dir/.." && pwd -P)"
export PYTHONDONTWRITEBYTECODE=1
python3 - <<'CHECK_PYTHON'
if not __debug__:
    raise SystemExit("Hybrid verification requires assertions; disable Python optimization.")
CHECK_PYTHON
project_work_dir="$("$lean_source_dir/setup.sh")"
contribution_check_dir="$project_work_dir/.lake/contribution-ci"
mkdir -p "$contribution_check_dir"
contribution_targets="$contribution_check_dir/ContributionTargets.lean"
python3 "$repository_source_dir/scripts/check_contributions.py" \
  --root "$repository_source_dir" --generate-lean "$contribution_targets"
SVB_EXTRA_LEAN="$contribution_targets" "$lean_source_dir/check.sh"
"$lean_source_dir/check_certificates.sh"
printf '%s\n' 'PASS: contribution registry, claimed Lean theorem targets, analytic proof, and all external exact-arithmetic checks.'
