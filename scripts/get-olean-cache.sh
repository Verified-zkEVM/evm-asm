#!/usr/bin/env bash
# Warm a contributor checkout from a release's prebuilt-olean archive.
# Usage: scripts/get-olean-cache.sh [tag]   (defaults to the latest release)
#
# Lake's `preferReleaseBuild` only serves EvmAsm *as a dependency*; the root
# package always builds from source, so contributors fetch the archive by hand.
# See docs/build-cache.md. The artifacts only validate if the checkout matches
# the tag's sources and toolchain — on a different commit `lake build` rebuilds
# whatever drifted.
set -euo pipefail
cd "$(dirname "$0")/.."

ARCHIVE="EvmAsm-oleans.tar.gz"
TAG="${1:-}"

if ! command -v gh >/dev/null; then
  echo "error: needs the GitHub CLI (gh)" >&2
  exit 1
fi

if [ -z "$TAG" ]; then
  TAG="$(gh release list --limit 1 --json tagName --jq '.[0].tagName')"
  [ -n "$TAG" ] || { echo "error: no releases found" >&2; exit 1; }
  echo "Using latest release: $TAG"
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

gh release download "$TAG" --pattern "$ARCHIVE" --dir "$tmp"
lake unpack "$tmp/$ARCHIVE"
echo "Unpacked $ARCHIVE from $TAG into .lake/build."
echo "Run 'lake exe cache get' (Mathlib) and 'lake build' to verify/complete."
