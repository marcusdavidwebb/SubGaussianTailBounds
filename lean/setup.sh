#!/usr/bin/env bash
set -euo pipefail
project_source_dir="$(cd "$(dirname "$0")" && pwd -P)"
export PYTHONDONTWRITEBYTECODE=1
exec python3 "$project_source_dir/../scripts/configure_lean.py" "$@"
