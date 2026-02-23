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

# Extract crate versions from workspace metadata
read_version() {
  cargo metadata --format-version=1 --no-deps \
    | python3 -c "
import sys, json
meta = json.load(sys.stdin)
for pkg in meta['packages']:
    if pkg['name'] == '$1':
        print(pkg['version'])
        break
"
}

VERSION=$(read_version libradicl)
MACROS_VERSION=$(read_version libradicl-macros)

TAG="v${VERSION}"
echo "==> libradicl version: ${VERSION}"
echo "==> libradicl-macros version: ${MACROS_VERSION}"

# Check that the tag doesn't already exist
if git rev-parse "$TAG" >/dev/null 2>&1; then
  echo "ERROR: tag ${TAG} already exists" >&2
  exit 1
fi

echo "==> Publishing libradicl-macros v${MACROS_VERSION}"
cargo publish -p libradicl-macros $DRY_RUN

if [[ -n "$DRY_RUN" ]]; then
  echo "==> Dry-run: skipping crates.io availability check"
  echo "==> Publishing libradicl (dry-run)"
  cargo publish -p libradicl $DRY_RUN
  echo "==> Dry-run: would create and push tag ${TAG}"
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

echo "==> Publishing libradicl v${VERSION}"
cargo publish -p libradicl

echo "==> Tagging ${TAG} and pushing to origin"
git tag -a "$TAG" -m "Release ${VERSION}"
git push origin "$TAG"

echo "==> Done! Published libradicl v${VERSION} and pushed tag ${TAG}"
