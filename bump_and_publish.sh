#!/usr/bin/env bash
set -euo pipefail

die() {
    echo "error: $*" >&2
    exit 1
}

usage() {
    cat <<'EOF'
Usage:
  ./bump_and_publish.sh <version> [--publish] [--dry-run] [--no-changelog]
  ./bump_and_publish.sh [--publish] [--dry-run] [--no-changelog] <version>

Options:
  --publish       Publish libradicl-macros first, then libradicl, after bumping and committing
  --dry-run       Show what would be done without modifying files, creating commits, tags, or publishing
  --no-changelog  Skip regenerating CHANGELOG.md (requires git-cliff otherwise)
  -h, --help      Show this help message

CHANGELOG.md is regenerated from conventional commits by git-cliff (see
cliff.toml) and included in the release commit. Preview the section the next
release would add, without writing anything:

  git-cliff --tag v<version> --unreleased
EOF
}

print_cmd() {
    printf '+'
    printf ' %q' "$@"
    printf '\n'
}

run() {
    print_cmd "$@"
    if [[ "$DRY_RUN" == true ]]; then
        return 0
    fi
    "$@"
}

VERSION=""
PUBLISH=false
DRY_RUN=false
CHANGELOG_ENABLED=true

while [[ $# -gt 0 ]]; do
    case "$1" in
        --publish)
            PUBLISH=true
            ;;
        --dry-run)
            DRY_RUN=true
            ;;
        --no-changelog)
            CHANGELOG_ENABLED=false
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        -*)
            die "unknown option: $1"
            ;;
        *)
            if [[ -n "$VERSION" ]]; then
                die "version specified more than once"
            fi
            VERSION="$1"
            ;;
    esac
    shift
done

[[ -n "$VERSION" ]] || {
    usage
    exit 1
}

if ! [[ "$VERSION" =~ ^[0-9]+\.[0-9]+\.[0-9]+([+-][0-9A-Za-z.-]+)*$ ]]; then
    die "version must look like X.Y.Z, optionally with prerelease/build suffixes"
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

LOCKFILE="Cargo.lock"
MACROS_CARGO="libradicl-macros/Cargo.toml"
LIBRADICL_CARGO="libradicl/Cargo.toml"
CHANGELOG="CHANGELOG.md"
CLIFF_CONFIG="cliff.toml"
TAG="v${VERSION}"
MACROS_CRATE="libradicl-macros"
LIBRADICL_CRATE="libradicl"

[[ -f "$LOCKFILE" ]] || die "not found: $LOCKFILE"
[[ -f "$MACROS_CARGO" ]] || die "not found: $MACROS_CARGO"
[[ -f "$LIBRADICL_CARGO" ]] || die "not found: $LIBRADICL_CARGO"

if [[ "$CHANGELOG_ENABLED" == true ]]; then
    [[ -f "$CLIFF_CONFIG" ]] || die "not found: $CLIFF_CONFIG (pass --no-changelog to skip changelog generation)"
    command -v git-cliff >/dev/null 2>&1 || die "git-cliff is not installed; install it (cargo binstall git-cliff) or pass --no-changelog"
fi

CURRENT_MACROS_VERSION="$(sed -n 's/^version = "\(.*\)"/\1/p' "$MACROS_CARGO" | head -1)"
CURRENT_LIBRADICL_VERSION="$(sed -n 's/^version = "\(.*\)"/\1/p' "$LIBRADICL_CARGO" | head -1)"
CURRENT_MACROS_DEP_VERSION="$(sed -n 's/^libradicl-macros = { version = "\(.*\)", path = "..\/libradicl-macros" }/\1/p' "$LIBRADICL_CARGO")"

[[ -n "$CURRENT_MACROS_VERSION" ]] || die "could not determine current version from $MACROS_CARGO"
[[ -n "$CURRENT_LIBRADICL_VERSION" ]] || die "could not determine current version from $LIBRADICL_CARGO"
[[ -n "$CURRENT_MACROS_DEP_VERSION" ]] || die "could not determine libradicl-macros dependency version from $LIBRADICL_CARGO"

if [[ "$CURRENT_MACROS_VERSION" == "$VERSION" && "$CURRENT_LIBRADICL_VERSION" == "$VERSION" && "$CURRENT_MACROS_DEP_VERSION" == "$VERSION" ]]; then
    die "crate versions are already set to $VERSION"
fi

if git rev-parse "$TAG" >/dev/null 2>&1; then
    die "tag $TAG already exists"
fi

if [[ -n "$(git status --porcelain)" ]]; then
    die "working tree is not clean; commit or stash existing changes first"
fi

echo "Current ${MACROS_CRATE} version    : $CURRENT_MACROS_VERSION"
echo "Current ${LIBRADICL_CRATE} version : $CURRENT_LIBRADICL_VERSION"
echo "Current macros dep version         : $CURRENT_MACROS_DEP_VERSION"
echo "New crate version                  : $VERSION"
echo "Tag                                : $TAG"
if [[ "$PUBLISH" == true ]]; then
    echo "Publish crates                     : yes"
else
    echo "Publish crates                     : no"
fi
if [[ "$CHANGELOG_ENABLED" == true ]]; then
    echo "Regenerate ${CHANGELOG}              : yes"
else
    echo "Regenerate ${CHANGELOG}              : no"
fi
if [[ "$DRY_RUN" == true ]]; then
    echo "Dry-run                            : yes"
else
    echo "Dry-run                            : no"
fi
echo

echo "Updating $MACROS_CARGO"
echo "  version: $CURRENT_MACROS_VERSION -> $VERSION"
echo "Updating $LIBRADICL_CARGO"
echo "  version: $CURRENT_LIBRADICL_VERSION -> $VERSION"
echo "  ${MACROS_CRATE} dependency: $CURRENT_MACROS_DEP_VERSION -> $VERSION"

if [[ "$DRY_RUN" == false ]]; then
    sed -i.bak "1,/^version = /s/^version = \".*\"/version = \"${VERSION}\"/" "$MACROS_CARGO"
    rm -f "${MACROS_CARGO}.bak"

    sed -i.bak "1,/^version = /s/^version = \".*\"/version = \"${VERSION}\"/" "$LIBRADICL_CARGO"
    rm -f "${LIBRADICL_CARGO}.bak"

    sed -i.bak "s/^libradicl-macros = { version = \".*\", path = \"..\\/libradicl-macros\" }/libradicl-macros = { version = \"${VERSION}\", path = \"..\\/libradicl-macros\" }/" "$LIBRADICL_CARGO"
    rm -f "${LIBRADICL_CARGO}.bak"
fi

UPDATED_MACROS_VERSION="$(sed -n 's/^version = "\(.*\)"/\1/p' "$MACROS_CARGO" | head -1)"
UPDATED_LIBRADICL_VERSION="$(sed -n 's/^version = "\(.*\)"/\1/p' "$LIBRADICL_CARGO" | head -1)"
UPDATED_MACROS_DEP_VERSION="$(sed -n 's/^libradicl-macros = { version = "\(.*\)", path = "..\/libradicl-macros" }/\1/p' "$LIBRADICL_CARGO")"

if [[ "$DRY_RUN" == false ]]; then
    [[ "$UPDATED_MACROS_VERSION" == "$VERSION" ]] || die "${MACROS_CARGO} version update failed"
    [[ "$UPDATED_LIBRADICL_VERSION" == "$VERSION" ]] || die "${LIBRADICL_CARGO} version update failed"
    [[ "$UPDATED_MACROS_DEP_VERSION" == "$VERSION" ]] || die "${LIBRADICL_CARGO} dependency update failed"
else
    echo "Dry-run: would rewrite crate manifests and refresh $LOCKFILE"
fi

run cargo check -p "$MACROS_CRATE" -p "$LIBRADICL_CRATE" -q

# Exercise exactly what crates.io will package before either irreversible
# publish. This must be a workspace dry-run: an individual libradicl dry-run
# resolves its packaged libradicl-macros dependency from crates.io, where the
# new version intentionally does not exist yet. Cargo's workspace publisher
# supplies that in-flight dependency through a temporary local registry and
# verifies both packages in dependency order.
run cargo publish --workspace --dry-run --allow-dirty

if [[ "$CHANGELOG_ENABLED" == true ]]; then
    # Regenerate the whole file rather than prepending: the result is
    # idempotent and stays in one format throughout. `--tag` labels the
    # not-yet-tagged commits with the version about to be cut; without it they
    # would land under "Unreleased".
    echo "Regenerating $CHANGELOG for $TAG"
    run git-cliff --tag "$TAG" -o "$CHANGELOG"
fi

run git add "$MACROS_CARGO" "$LIBRADICL_CARGO"
if [[ "$CHANGELOG_ENABLED" == true ]]; then
    run git add "$CHANGELOG"
fi
run git add -f "$LOCKFILE"
run git commit -m "chore(release): bump Rust crates to v${VERSION}"

if [[ "$PUBLISH" == true ]]; then
    # POSSIBLE SIMPLIFICATION (not done yet): `cargo publish --workspace`
    # publishes workspace members in dependency order and resolves the
    # in-flight libradicl -> libradicl-macros dependency itself, which would
    # replace this whole two-step publish and the index-polling loop below
    # with a single command.
    #
    # Not adopted because it changes the failure modes and deserves a
    # deliberate trial rather than a swap on release day: the two publishes
    # stop being separately observable, and a partial failure has to be
    # reasoned about differently (crates.io accepts no rollback either way, so
    # "macros published, libradicl did not" remains recoverable only by
    # publishing a new version).
    #
    # Before switching: confirm `cargo publish --help` on the release machine
    # lists --workspace (present in cargo 1.97.1; older toolchains may not have
    # it), then rehearse with `cargo publish --workspace --dry-run`. If it
    # works, everything from here to the end of the polling loop collapses to
    #     run cargo publish --workspace
    run cargo publish -p "$MACROS_CRATE"

    if [[ "$DRY_RUN" == true ]]; then
        echo "Dry-run: would wait for ${MACROS_CRATE} v${VERSION} to appear on crates.io before publishing ${LIBRADICL_CRATE}"
    else
        echo "Waiting for ${MACROS_CRATE} v${VERSION} to appear on crates.io..."
        MAX_ATTEMPTS=30
        ATTEMPT=0
        while (( ATTEMPT < MAX_ATTEMPTS )); do
            if cargo search "$MACROS_CRATE" 2>/dev/null | grep -q "^${MACROS_CRATE} = \"${VERSION}\""; then
                echo "${MACROS_CRATE} v${VERSION} is available"
                break
            fi
            ATTEMPT=$((ATTEMPT + 1))
            echo "  attempt ${ATTEMPT}/${MAX_ATTEMPTS}: not indexed yet, waiting 10s..."
            sleep 10
        done

        if (( ATTEMPT >= MAX_ATTEMPTS )); then
            die "timed out waiting for ${MACROS_CRATE} v${VERSION} on crates.io"
        fi
    fi

    run cargo publish -p "$LIBRADICL_CRATE"
fi

run git tag -a "$TAG" -m "Release ${VERSION}"
run git push origin HEAD
run git push origin "$TAG"

if [[ "$DRY_RUN" == true ]]; then
    echo
    echo "Dry-run complete"
else
    echo
    echo "Release bump complete for v${VERSION}"
fi
