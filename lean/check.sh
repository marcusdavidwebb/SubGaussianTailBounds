#!/usr/bin/env bash
set -euo pipefail
project_source_dir="$(cd "$(dirname "$0")" && pwd -P)"
project_work_dir="$("$project_source_dir/setup.sh")"
project_toolchain="$(< "$project_source_dir/lean-toolchain")"
if [[ -n "${SVB_ELAN_BIN:-}" ]]; then
  project_elan="$SVB_ELAN_BIN"
elif [[ -x "$HOME/.elan/bin/elan" ]]; then
  project_elan="$HOME/.elan/bin/elan"
else
  project_elan="$(command -v elan)"
fi
if [[ -z "${MATHLIB_CACHE_DIR:-}" ]]; then
  if [[ "$(uname -s)" == Darwin ]]; then
    export MATHLIB_CACHE_DIR="$HOME/Library/Caches/mathlib"
  else
    export MATHLIB_CACHE_DIR="$HOME/.cache/mathlib"
  fi
fi
cd "$project_work_dir"
# Elan's `run` does not install missing toolchains unless --install is supplied.
"$project_elan" run "$project_toolchain" lake build
audit_output="$("$project_elan" run "$project_toolchain" lake env lean "$project_source_dir/Audit.lean")"
printf '%s\n' "$audit_output"
printf '%s\n' "$audit_output" | python3 "$project_source_dir/check_axiom_audit.py"
if [[ -n "${SVB_EXTRA_LEAN:-}" ]]; then
  if [[ "$SVB_EXTRA_LEAN" != /* || ! -f "$SVB_EXTRA_LEAN" ]]; then
    printf '%s\n' 'SVB_EXTRA_LEAN must name an existing absolute Lean file.' >&2
    exit 1
  fi
  extra_output="$("$project_elan" run "$project_toolchain" lake env lean "$SVB_EXTRA_LEAN")"
  printf '%s\n' "$extra_output"
  if [[ "$extra_output" == *sorryAx* || "$extra_output" == *error:* || "$extra_output" != *CONTRIBUTION_AUDIT_COMPLETE* ]]; then
    printf '%s\n' 'Additional Lean verification failed or its contribution audit marker is absent.' >&2
    exit 1
  fi
fi
