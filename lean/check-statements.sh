#!/usr/bin/env bash
# Check the two displayed Lean propositions and their transitive axioms.
set -euo pipefail
source_dir="$(cd "$(dirname "$0")" && pwd -P)"
if (( $# )); then
  printf 'Usage: %s\n' "$0" >&2
  exit 2
fi
export PYTHONDONTWRITEBYTECODE=1
# Setup checks for the installed pinned toolchain and exact existing packages.
work_dir="$("$source_dir/setup.sh")"
toolchain="$(< "$source_dir/lean-toolchain")"
if [[ -n "${SVB_ELAN_BIN:-}" ]]; then
  elan_bin="$SVB_ELAN_BIN"
elif [[ -x "$HOME/.elan/bin/elan" ]]; then
  elan_bin="$HOME/.elan/bin/elan"
else
  elan_bin="$(command -v elan)"
fi
cd "$work_dir"
"$elan_bin" run "$toolchain" lake build MainTheoremStatement SingularValueBounds.Canonical.Results
"$elan_bin" run "$toolchain" lake env lean "$source_dir/Verification/CheckStatements.lean"
printf '%s\n' 'PASS: the two stated Lean propositions and their allowed axioms.'
