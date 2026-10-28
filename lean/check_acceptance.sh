#!/usr/bin/env bash
# Complete canonical verification. CI separates compilation from data-only audit.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
runner_dir="$(cd "$(dirname "$0")" && pwd -P)"
runner_root="$(cd "$runner_dir/.." && pwd -P)"
source_root="$(cd "${SVB_SOURCE_ROOT:-$runner_root}" && pwd -P)"
trusted_root="$(cd "${SVB_TRUSTED_ROOT:-$runner_root}" && pwd -P)"
mode="${1:-all}"
case "$mode" in all|build|snapshot|audit|audit-prepare) ;; *) printf 'Usage: %s [all|build|snapshot|audit|audit-prepare]\n' "$0" >&2; exit 2;; esac
# This trusted preflight runs before any candidate setup or Lean source.
python3 "$trusted_root/scripts/generate_lean_acceptance.py" \
  --root "$source_root" --trusted-root "$trusted_root" --check-inputs-only
if [[ "$mode" == audit || "$mode" == audit-prepare || "$mode" == snapshot ]]; then
  setup_root="$trusted_root"
else
  setup_root="$source_root"
fi
work_dir="$("$setup_root/lean/setup.sh")"
toolchain="$(< "$trusted_root/lean/lean-toolchain")"
if [[ -n "${SVB_ELAN_BIN:-}" ]]; then
  elan_bin="$SVB_ELAN_BIN"
elif [[ -x "$HOME/.elan/bin/elan" ]]; then
  elan_bin="$HOME/.elan/bin/elan"
else
  elan_bin="$(command -v elan)"
fi
# Keep downloaded audit artifacts off the search path of later source builds.
acceptance_dir="$work_dir/acceptance/$mode"
python3 "$trusted_root/scripts/generate_lean_acceptance.py" \
  --root "$source_root" --trusted-root "$trusted_root" --output-dir "$acceptance_dir"
cd "$work_dir"
lean_path="$("$elan_bin" run "$toolchain" lake env printenv LEAN_PATH)"
LEAN_PATH="$lean_path" "$elan_bin" run "$toolchain" lean --run \
  "$trusted_root/lean/Acceptance/SnapshotSource.lean" -- \
  "$trusted_root/lean/SingularValueBounds/Canonical/AcceptedConstants.lean" \
  "$source_root/lean/SingularValueBounds/Canonical/AcceptedConstants.lean"
if [[ "$mode" == snapshot ]]; then
  # This executes candidate constants ONLY in the isolated snapshot job.
  cd "$acceptance_dir"
  LEAN_PATH="$lean_path" "$elan_bin" run "$toolchain" lean \
    -o CanonicalCandidateConstants.olean CanonicalCandidateConstants.lean
  python3 "$trusted_root/scripts/canonical_artifacts.py" export --kind snapshot \
    --build "$work_dir/.lake/build/lib/lean" --acceptance "$acceptance_dir" \
    --output "${SVB_ARTIFACT_DIR:?Set SVB_ARTIFACT_DIR for snapshot export}"
  exit 0
fi
# Compile the actual immutable root. The audit job uses the independent trusted
# checkout and never builds or imports candidate implementation source here.
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
protected_files=(CanonicalTrustedConstants.olean CanonicalAcceptanceExpected.olean
  CanonicalAcceptanceAudit.lean CanonicalAcceptanceAudit.olean
  CanonicalModuleReplay.lean CanonicalModuleReplay.olean
  "$work_dir/.lake/build/lib/lean/MainTheoremStatement.olean")
policy_before="$(shasum -a 256 "${protected_files[@]}")"
if [[ "$mode" == audit || "$mode" == audit-prepare ]]; then
  # A fresh job imports only .olean data. No candidate native library, extension,
  # expected-type template, Mathlib shadow or canonical-module shadow is admitted.
  python3 "$trusted_root/scripts/canonical_artifacts.py" stage --kind proof \
    --source "${SVB_PROOF_ARTIFACT_DIR:?Set SVB_PROOF_ARTIFACT_DIR}" --output "$acceptance_dir"
  python3 "$trusted_root/scripts/canonical_artifacts.py" stage --kind snapshot \
    --source "${SVB_SNAPSHOT_ARTIFACT_DIR:?Set SVB_SNAPSHOT_ARTIFACT_DIR}" --output "$acceptance_dir"
else
  if [[ "$mode" == all ]]; then
    LEAN_PATH="$lean_path" "$elan_bin" run "$toolchain" lean \
      -o CanonicalCandidateConstants.olean CanonicalCandidateConstants.lean
    protected_files+=(CanonicalCandidateConstants.olean)
    policy_before="$(shasum -a 256 "${protected_files[@]}")"
  fi
  cd "$work_dir"
  python3 "$trusted_root/scripts/build_lean_modules.py" \
    --source-root "$source_root" --work-dir "$work_dir" --elan "$elan_bin"
  cd "$acceptance_dir"
  LEAN_PATH="$acceptance_dir:$lean_path" "$elan_bin" run "$toolchain" lean \
    -o CanonicalAcceptance.olean CanonicalAcceptance.lean
fi
if [[ "$(shasum -a 256 "${protected_files[@]}")" != "$policy_before" ]]; then
  printf '%s\n' 'Candidate compilation modified a protected canonical policy artifact.' >&2
  exit 1
fi
python3 "$trusted_root/scripts/generate_lean_acceptance.py" \
  --root "$source_root" --trusted-root "$trusted_root" --check-inputs-only
if [[ "$mode" == build ]]; then
  python3 "$trusted_root/scripts/canonical_artifacts.py" export --kind proof \
    --build "$work_dir/.lake/build/lib/lean" --acceptance "$acceptance_dir" \
    --output "${SVB_ARTIFACT_DIR:?Set SVB_ARTIFACT_DIR for proof export}"
  printf '%s\n' 'Candidate compilation finished; independent canonical verification is still required.'
  exit 0
fi
if [[ "$mode" == audit-prepare ]]; then
  printf '%s\n' 'Prepared isolated trusted auditor and data-only modules; no verification claim.'
  exit 0
fi
# This source imports only trusted Lean code. Candidate modules are loaded as
# data with extensions disabled. Every project module is replayed after all its
# ancestors; only then are the 22 exact canonical types independently checked.
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
  --source-dir "$source_root/lean"
if [[ "$audit_output" == *sorryAx* || "$audit_output" == *error:* ]] || \
    ! printf '%s\n' "$audit_output" | grep -qx 'CANONICAL_ACCEPTANCE_COMPLETE 22 targets'; then
  printf '%s\n' 'Canonical theorem acceptance did not complete its kernel/axiom audit.' >&2
  exit 1
fi
