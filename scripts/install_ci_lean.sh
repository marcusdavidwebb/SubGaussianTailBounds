#!/usr/bin/env bash
# Explicit bootstrap for disposable GitHub-hosted Linux runners only.
set -euo pipefail
if [[ "${GITHUB_ACTIONS:-}" != true || "${RUNNER_ENVIRONMENT:-}" != github-hosted || "$(uname -s)" != Linux ]]; then
  printf '%s\n' 'CI bootstrap is restricted to disposable GitHub-hosted Linux runners.' >&2
  exit 1
fi
mkdir -p "$RUNNER_TEMP/elan-installer"
cd "$RUNNER_TEMP/elan-installer"
curl --fail --location --retry 3 --output elan.tar.gz \
  https://github.com/leanprover/elan/releases/download/v4.1.2/elan-x86_64-unknown-linux-gnu.tar.gz
printf '%s\n' 'f81c2e48c1588d4612cd2c8851947898a45ac8d72748a07dff3a5694f1cf589b  elan.tar.gz' | sha256sum --check
tar -xzf elan.tar.gz
./elan-init -y --default-toolchain none --no-modify-path
printf '%s\n' "$HOME/.elan/bin" >> "$GITHUB_PATH"
printf 'MATHLIB_CACHE_DIR=%s/mathlib-cache\n' "$RUNNER_TEMP" >> "$GITHUB_ENV"
