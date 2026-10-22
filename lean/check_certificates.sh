#!/usr/bin/env bash
set -euo pipefail
lean_source_dir="$(cd "$(dirname "$0")" && pwd -P)"
export PYTHONDONTWRITEBYTECODE=1
python3 - <<'PY'
if not __debug__:
    raise SystemExit("Certificate verification requires assertions; disable Python optimization.")
PY
python3 "$lean_source_dir/../check_main_constants.py"
checkers=(
  check_enclosure_interface.py
  check_polynomial_interface.py
  check_lower_interface.py
  check_lower_plateau_cost.py
  check_endpoint_interface.py
  check_upper_mean_interface.py
  check_general_mean_cells.py
  check_general_mean_entropy.py
  check_upper_mgf_interface.py
  check_general_second_interface.py
  check_profile_integrals.py
)
for checker in "${checkers[@]}"; do
  printf 'Checking %s\n' "$checker"
  python3 "$lean_source_dir/$checker"
done
printf '%s\n' 'PASS: original exact-arithmetic checker and all eleven finite interfaces.'
