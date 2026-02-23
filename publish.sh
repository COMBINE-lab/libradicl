#!/usr/bin/env bash
set -euo pipefail

# Publish libradicl workspace crates to crates.io.
# libradicl-macros must be published (and indexed) before libradicl.
#
# Usage:
#   ./publish.sh              # publish both crates
#   ./publish.sh --dry-run    # dry-run only (no actual publish)

DRY_RUN=""
if [[ "${1:-}" == "--dry-run" ]]; then
  DRY_RUN="--dry-run"
  echo "==> Dry-run mode enabled"
fi

# Extract the expected macros version from libradicl's dependency declaration
MACROS_VERSION=$(cargo metadata --format-version=1 --no-deps \
  | python3 -c "
import sys, json
meta = json.load(sys.stdin)
for pkg in meta['packages']:
    if pkg['name'] == 'libradicl-macros':
        print(pkg['version'])
        break
")

echo "==> Publishing libradicl-macros v${MACROS_VERSION}"
cargo publish -p libradicl-macros $DRY_RUN

if [[ -n "$DRY_RUN" ]]; then
  echo "==> Dry-run: skipping crates.io availability check"
  echo "==> Publishing libradicl (dry-run)"
  cargo publish -p libradicl $DRY_RUN
  echo "==> Dry-run complete"
  exit 0
fi

# Wait for crates.io to index the macros crate before publishing the main crate.
echo "==> Waiting for libradicl-macros v${MACROS_VERSION} to appear on crates.io..."
MAX_ATTEMPTS=30
ATTEMPT=0
while (( ATTEMPT < MAX_ATTEMPTS )); do
  if cargo search libradicl-macros 2>/dev/null | grep -q "libradicl-macros = \"${MACROS_VERSION}\""; then
    echo "==> libradicl-macros v${MACROS_VERSION} is available"
    break
  fi
  ATTEMPT=$((ATTEMPT + 1))
  echo "    attempt ${ATTEMPT}/${MAX_ATTEMPTS} — not yet indexed, waiting 10s..."
  sleep 10
done

if (( ATTEMPT >= MAX_ATTEMPTS )); then
  echo "ERROR: timed out waiting for libradicl-macros v${MACROS_VERSION} on crates.io" >&2
  exit 1
fi

echo "==> Publishing libradicl"
cargo publish -p libradicl

echo "==> Done!"
