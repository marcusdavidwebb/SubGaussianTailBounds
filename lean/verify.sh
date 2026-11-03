#!/usr/bin/env bash
# Complete local proof check. --focused is the check-statements.sh entry point.
set -euo pipefail
source_dir="$(cd "$(dirname "$0")" && pwd -P)"
source_root="$(cd "$source_dir/.." && pwd -P)"
focused=false
if [[ $# == 1 && $1 == --focused ]]; then
  focused=true
elif (( $# )); then
  printf 'Usage: %s [--focused]\n' "$0" >&2
  exit 2
fi
export PYTHONDONTWRITEBYTECODE=1
snapshot_dir="$(mktemp -d "${TMPDIR:-/tmp}/svb-verification.XXXXXXXX")"
trap 'rm -rf -- "$snapshot_dir"' EXIT
snapshot_file="$snapshot_dir/sources.json"
python3 "$source_root/scripts/configure_lean.py" --snapshot-file "$snapshot_file" \
  --root "$source_root"
python3 "$source_root/scripts/generate_lean_acceptance.py" \
  --root "$source_root" --check-inputs-only
work_dir="$("$source_dir/setup.sh")"
toolchain="$(< "$source_dir/lean-toolchain")"
elan_bin="${SVB_ELAN_BIN:-$HOME/.elan/bin/elan}"
if [[ ! -x "$elan_bin" ]]; then elan_bin="$(command -v elan)"; fi
if $focused; then mode=focused; else mode=full; fi
check_dir="$work_dir/verification/$mode"
mkdir -p "$check_dir"
generator_args=(--root "$source_root" --output-dir "$check_dir")
if $focused; then generator_args+=(--focused); fi
python3 "$source_root/scripts/generate_lean_acceptance.py" "${generator_args[@]}"
cd "$work_dir"
# The actual statement and authoritative coefficients are compiled before any
# implementation syntax is imported by the expected-specification compiler.
"$elan_bin" run "$toolchain" lake build MainTheoremStatement SingularValueBounds.Canonical.Constants
lean_path="$("$elan_bin" run "$toolchain" lake env printenv LEAN_PATH)"
cd "$check_dir"
LEAN_PATH="$lean_path" "$elan_bin" run "$toolchain" lean \
  -o CanonicalAcceptanceExpected.olean CanonicalAcceptanceExpected.lean
export LEAN_PATH="$check_dir:$lean_path"
protected_files=(CanonicalAcceptanceExpected.lean CanonicalAcceptanceExpected.olean
  CanonicalAcceptanceAudit.lean
  "$work_dir/.lake/build/lib/lean/MainTheoremStatement.olean"
  "$work_dir/.lake/build/lib/lean/SingularValueBounds/Canonical/Constants.olean")
if ! $focused; then
  cp "$source_dir/Verification/ModuleReplay.lean" CanonicalModuleReplay.lean
  protected_files+=(CanonicalModuleReplay.lean)
fi
policy_before="$(shasum -a 256 "${protected_files[@]}")"
SECONDS=0
cd "$work_dir"
build_args=(--source-root "$source_root" --work-dir "$work_dir" --elan "$elan_bin")
if $focused; then build_args+=(--target SingularValueBounds.Canonical.Results); fi
python3 "$source_root/scripts/build_lean_modules.py" "${build_args[@]}"
printf 'BUILD_PHASE_SECONDS %s\n' "$SECONDS"
cd "$check_dir"
if [[ "$(shasum -a 256 "${protected_files[@]}")" != "$policy_before" ]]; then
  printf '%s\n' 'Verification inputs changed during compilation.' >&2
  exit 1
fi
SECONDS=0
if $focused; then
  "$elan_bin" run "$toolchain" lean --run CanonicalAcceptanceAudit.lean -- --focused
else
  python3 "$source_root/scripts/replay_lean_modules.py" \
    --elan "$elan_bin" --toolchain "$toolchain" \
    --worker "$check_dir/CanonicalModuleReplay.lean" \
    --auditor "$check_dir/CanonicalAcceptanceAudit.lean" --source-dir "$source_dir"
fi
printf 'AUDIT_PHASE_SECONDS %s\n' "$SECONDS"
if [[ "$(shasum -a 256 "${protected_files[@]}")" != "$policy_before" ]]; then
  printf '%s\n' 'Verification inputs changed during the audit.' >&2
  exit 1
fi
python3 "$source_root/scripts/configure_lean.py" --snapshot-file "$snapshot_file" \
  --snapshot-check --root "$source_root"
# Keep the exact path/content inventory identifying this successful run.
cp "$snapshot_file" "$check_dir/inputs.json"
read -r inputs_hash _ < <(shasum -a 256 "$check_dir/inputs.json")
printf 'CHECKED_INPUTS_SHA256 %s\n' "$inputs_hash"
if $focused; then
  printf '%s\n' 'PASS: the two stated Lean propositions, exact universes and allowed axioms.'
else
  printf '%s\n' 'PASS: both canonical Lean results, full independent kernel replay, source coverage and allowed axioms.'
fi
