#!/usr/bin/env bash
# Complete local verification: compilation, independent replay and exact types.
set -euo pipefail
source_dir="$(cd "$(dirname "$0")" && pwd -P)"
source_root="$(cd "$source_dir/.." && pwd -P)"
trusted_root="$(cd "${SVB_TRUSTED_ROOT:-$source_root}" && pwd -P)"
export PYTHONDONTWRITEBYTECODE=1
if (( $# )); then
  printf 'Usage: %s\n' "$0" >&2
  exit 2
fi
python3 "$trusted_root/scripts/check_canonical_statement.py" --root "$source_root"
if [[ ! -f "$source_dir/SingularValueBounds/Canonical/Results.lean" ]]; then
  printf '%s\n' 'Missing complete canonical proof interface: Canonical/Results.lean.' >&2
  exit 1
fi
# Reject changed build inputs before any candidate setup or Lean source runs.
python3 "$trusted_root/scripts/generate_lean_acceptance.py" \
  --root "$source_root" --trusted-root "$trusted_root" --check-inputs-only
work_dir="$("$source_dir/setup.sh")"
toolchain="$(< "$trusted_root/lean/lean-toolchain")"
if [[ -n "${SVB_ELAN_BIN:-}" ]]; then
  elan_bin="$SVB_ELAN_BIN"
elif [[ -x "$HOME/.elan/bin/elan" ]]; then
  elan_bin="$HOME/.elan/bin/elan"
else
  elan_bin="$(command -v elan)"
fi
# Retain the existing local workspace; former downloaded audit directories are
# never placed on this source build's search path.
acceptance_dir="$work_dir/acceptance/all"
python3 "$trusted_root/scripts/generate_lean_acceptance.py" \
  --root "$source_root" --trusted-root "$trusted_root" --output-dir "$acceptance_dir"
cd "$work_dir"
lean_path="$("$elan_bin" run "$toolchain" lake env printenv LEAN_PATH)"
LEAN_PATH="$lean_path" "$elan_bin" run "$toolchain" lean --run \
  "$trusted_root/lean/Acceptance/SnapshotSource.lean" -- \
  "$trusted_root/lean/SingularValueBounds/Canonical/AcceptedConstants.lean" \
  "$source_dir/SingularValueBounds/Canonical/AcceptedConstants.lean"

# Compile the actual immutable root and trusted checking programs before proof
# implementation modules. The next constants are compiled separately from them.
"$elan_bin" run "$toolchain" lake build MainTheoremStatement
cd "$acceptance_dir"
LEAN_PATH="$lean_path" "$elan_bin" run "$toolchain" lean \
  -o CanonicalTrustedConstants.olean CanonicalTrustedConstants.lean
LEAN_PATH="$acceptance_dir:$lean_path" "$elan_bin" run "$toolchain" lean \
  -o CanonicalAcceptanceExpected.olean CanonicalAcceptanceExpected.lean
LEAN_PATH="$acceptance_dir:$lean_path" "$elan_bin" run "$toolchain" lean \
  -o CanonicalAcceptanceAudit.olean CanonicalAcceptanceAudit.lean
cp "$trusted_root/lean/Acceptance/ModuleReplay.lean" CanonicalModuleReplay.lean
LEAN_PATH="$acceptance_dir:$lean_path" "$elan_bin" run "$toolchain" lean \
  -o CanonicalModuleReplay.olean CanonicalModuleReplay.lean
LEAN_PATH="$lean_path" "$elan_bin" run "$toolchain" lean \
  -o CanonicalCandidateConstants.olean CanonicalCandidateConstants.lean
protected_files=(CanonicalTrustedConstants.olean CanonicalAcceptanceExpected.olean
  CanonicalAcceptanceAudit.lean CanonicalAcceptanceAudit.olean
  CanonicalModuleReplay.lean CanonicalModuleReplay.olean CanonicalCandidateConstants.olean
  "$work_dir/.lake/build/lib/lean/MainTheoremStatement.olean")
policy_before="$(shasum -a 256 "${protected_files[@]}")"

cd "$work_dir"
python3 "$trusted_root/scripts/build_lean_modules.py" \
  --source-root "$source_root" --work-dir "$work_dir" --elan "$elan_bin"
cd "$acceptance_dir"
LEAN_PATH="$acceptance_dir:$lean_path" "$elan_bin" run "$toolchain" lean \
  -o CanonicalAcceptance.olean CanonicalAcceptance.lean
if [[ "$(shasum -a 256 "${protected_files[@]}")" != "$policy_before" ]]; then
  printf '%s\n' 'Candidate compilation modified a protected canonical policy artifact.' >&2
  exit 1
fi
python3 "$trusted_root/scripts/generate_lean_acceptance.py" \
  --root "$source_root" --trusted-root "$trusted_root" --check-inputs-only

# Load compiled project data with extensions disabled. Every module is replayed
# after its ancestors; only then are all 22 exact canonical types checked.
audit_output="$(LEAN_PATH="$acceptance_dir:$lean_path" python3 \
  "$trusted_root/scripts/replay_lean_modules.py" --elan "$elan_bin" --toolchain "$toolchain" \
  --worker "$acceptance_dir/CanonicalModuleReplay.lean" \
  --auditor "$acceptance_dir/CanonicalAcceptanceAudit.lean")"
if [[ "$(shasum -a 256 "${protected_files[@]}")" != "$policy_before" ]]; then
  printf '%s\n' 'Protected canonical policy artifact changed during verification.' >&2
  exit 1
fi
printf '%s\n' "$audit_output"
printf '%s\n' "$audit_output" | python3 "$trusted_root/lean/check_axiom_audit.py" \
  --source-dir "$source_dir"
if [[ "$audit_output" == *sorryAx* || "$audit_output" == *error:* ]] || \
    ! printf '%s\n' "$audit_output" | grep -qx 'CANONICAL_ACCEPTANCE_COMPLETE 22 targets'; then
  printf '%s\n' 'Canonical theorem acceptance did not complete its kernel/axiom audit.' >&2
  exit 1
fi
printf '%s\n' 'PASS: complete canonical Lean targets, comparisons, and axiom audits.'
