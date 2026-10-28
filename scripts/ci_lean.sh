#!/usr/bin/env bash
# Trusted workflow entry points. Partial builds/replays never report acceptance.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
policy_root="$(cd "$(dirname "$0")/.." && pwd -P)"
mode="${1:?build or audit}"
operation="${2:?init, shard, merge or final}"
state_dir="${RUNNER_TEMP:?}/lean-state"
mkdir -p "$state_dir"
context="$state_dir/context.json"
python3 - "$context" <<'PY'
import json, os, re, sys
context = {key: os.environ[env] for key, env in (
    ('run_id', 'GITHUB_RUN_ID'), ('run_attempt', 'GITHUB_RUN_ATTEMPT'),
    ('head_sha', 'SVB_HEAD_SHA'), ('base_sha', 'SVB_BASE_SHA'),
    ('policy_sha', 'SVB_POLICY_SHA'))}
for key, value in context.items():
    if not re.fullmatch(r'[1-9][0-9]*' if key.startswith('run_') else r'[0-9a-f]{40}', value):
        raise SystemExit('Invalid trusted workflow context: ' + key)
with open(sys.argv[1], 'w') as stream:
    json.dump(context, stream, sort_keys=True)
PY
checkpoint="$RUNNER_TEMP/checkpoint/checkpoint.json"
output="$RUNNER_TEMP/output"
mkdir -p "$output"
if [[ "$mode" == build ]]; then
  case "$operation" in
    init)
      python3 "$policy_root/scripts/ci_lean_build.py" init --context "$context" \
        --root "$SVB_SOURCE_ROOT" --work "$SVB_WORK_DIR" --output "$output/checkpoint.json"
      ;;
    shard)
      python3 "$policy_root/scripts/ci_lean_build.py" shard --context "$context" \
        --root "$SVB_SOURCE_ROOT" --work "$SVB_WORK_DIR" --checkpoint "$checkpoint" \
        --stage "$SVB_STAGE" --shard "$SVB_SHARD" --output "$output"
      ;;
    merge)
      args=()
      if [[ -d "$RUNNER_TEMP/prior-build" ]]; then args+=(--prior "$RUNNER_TEMP/prior-build"); fi
      python3 "$policy_root/scripts/ci_lean_build.py" merge --context "$context" \
        --checkpoint "$checkpoint" --stage "$SVB_STAGE" --fragments "$RUNNER_TEMP/fragments" \
        --output "$output" "${args[@]}"
      ;;
    *) printf 'Unknown build operation: %s\n' "$operation" >&2; exit 2;;
  esac
elif [[ "$mode" == audit ]]; then
  args=(--context "$context")
  acceptance="$SVB_WORK_DIR/acceptance/audit-prepare"
  policy_before=''
  if [[ "$operation" != merge ]]; then
    toolchain="$(< "$policy_root/lean/lean-toolchain")"
    args+=(--elan "$HOME/.elan/bin/elan" --toolchain "$toolchain" \
      --worker "$acceptance/CanonicalModuleReplay.lean" \
      --auditor "$acceptance/CanonicalAcceptanceAudit.lean")
    if [[ -f "$SVB_WORK_DIR/lakefile.toml" ]]; then
      cd "$SVB_WORK_DIR"
      export LEAN_PATH="$acceptance:$("$HOME/.elan/bin/elan" run "$toolchain" lake env printenv LEAN_PATH)"
      protected_files=("$acceptance/CanonicalTrustedConstants.olean"
        "$acceptance/CanonicalAcceptanceExpected.olean"
        "$acceptance/CanonicalAcceptanceAudit.lean" "$acceptance/CanonicalAcceptanceAudit.olean"
        "$acceptance/CanonicalModuleReplay.lean" "$acceptance/CanonicalModuleReplay.olean"
        "$SVB_WORK_DIR/.lake/build/lib/lean/MainTheoremStatement.olean")
      policy_before="$(shasum -a 256 "${protected_files[@]}")"
    fi
  fi
  case "$operation" in
    init) args+=(--output "$output/checkpoint.json");;
    shard) args+=(--checkpoint "$checkpoint" --stage "$SVB_STAGE" --shard "$SVB_SHARD" \
        --output "$output/report-$SVB_SHARD.json");;
    merge)
      mkdir -p "$RUNNER_TEMP/reports"
      for index in {0..7}; do
        cp "$RUNNER_TEMP/fragments/$index/report-$index.json" "$RUNNER_TEMP/reports/"
      done
      args+=(--checkpoint "$checkpoint" --stage "$SVB_STAGE" --reports-dir "$RUNNER_TEMP/reports" \
        --output "$output/checkpoint.json");;
    final) args+=(--checkpoint "$checkpoint");;
    *) printf 'Unknown audit operation: %s\n' "$operation" >&2; exit 2;;
  esac
  python3 "$policy_root/scripts/ci_lean_audit.py" "$operation" "${args[@]}"
  if [[ -n "$policy_before" && "$(shasum -a 256 "${protected_files[@]}")" != "$policy_before" ]]; then
    printf '%s\n' 'Protected canonical policy artifact changed during staged verification.' >&2
    exit 1
  fi
else
  printf 'Unknown CI mode: %s\n' "$mode" >&2; exit 2
fi
