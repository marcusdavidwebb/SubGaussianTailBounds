#!/usr/bin/env bash
# Focused check of the same two exact targets used by full verification.
set -euo pipefail
source_dir="$(cd "$(dirname "$0")" && pwd -P)"
if (( $# )); then
  printf 'Usage: %s\n' "$0" >&2
  exit 2
fi
exec "$source_dir/verify.sh" --focused
