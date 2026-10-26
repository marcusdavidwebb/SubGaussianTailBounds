#!/usr/bin/env bash
set -euo pipefail
project_source_dir="$(cd "$(dirname "$0")" && pwd -P)"
export PYTHONDONTWRITEBYTECODE=1
python3 "$project_source_dir/../scripts/check_canonical_statement.py" \
  --root "$project_source_dir/.."
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
"$project_elan" run "$project_toolchain" lake build MainTheoremStatement
project_lean_path="$("$project_elan" run "$project_toolchain" lake env printenv LEAN_PATH)"
trusted_audit_dir="$project_work_dir/trusted-audit"
mkdir -p "$trusted_audit_dir"
cp "$project_source_dir/TrustedAudit.lean" "$trusted_audit_dir/TrustedAudit.lean"
cd "$trusted_audit_dir"
LEAN_PATH="$project_lean_path" "$project_elan" run "$project_toolchain" lean \
  -o TrustedAudit.olean TrustedAudit.lean
protected_files=(TrustedAudit.lean TrustedAudit.olean
  "$project_source_dir/TrustedAudit.lean" "$project_source_dir/check_axiom_audit.py"
  "$project_source_dir/../MainTheoremStatement.lean"
  "$project_work_dir/.lake/build/lib/lean/MainTheoremStatement.olean")
protected_before="$(shasum -a 256 "${protected_files[@]}")"
cd "$project_work_dir"
python3 "$project_source_dir/../scripts/build_lean_modules.py" \
  --source-root "$project_source_dir/.." --work-dir "$project_work_dir" --elan "$project_elan"
cd "$trusted_audit_dir"
if [[ "$(shasum -a 256 "${protected_files[@]}")" != "$protected_before" ]]; then
  printf '%s\n' 'Project compilation modified a protected canonical audit artifact.' >&2
  exit 1
fi
audit_args=()
case "${SVB_AUDIT_MODE:-replay}" in
  replay) ;;
  diagnostic) audit_args+=(--diagnostic) ;;
  *) printf '%s\n' 'SVB_AUDIT_MODE must be replay or diagnostic.' >&2; exit 1 ;;
esac
audit_output="$(LEAN_PATH="$project_lean_path" "$project_elan" run "$project_toolchain" lean \
  --run TrustedAudit.lean -- "${audit_args[@]}")"
printf '%s\n' "$audit_output"
printf '%s\n' "$audit_output" | python3 "$project_source_dir/check_axiom_audit.py"
