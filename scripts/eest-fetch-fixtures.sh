#!/usr/bin/env bash
# eest-fetch-fixtures.sh -- Download the EEST stateless ("zkevm") fixtures.
#
# The stateless guest is validated against the Ethereum Execution Spec
# Tests (EEST) "zkevm" fixture line, which targets the Amsterdam fork
# (the working name for Glamsterdam) and ships the SSZ-encoded
# `StatelessInput` guest program inputs the Lean `run_stateless_guest`
# consumes.
#
# This script downloads the `fixtures_zkevm.tar.gz` asset attached to
# the EEST release tag into a gitignored cache and extracts it. Fixtures are
# fetched from `ethereum/execution-specs` by default; set EEST_REPO to override
# the repository. Fixtures are consumed from the release tarball rather than
# re-filled locally.
#
# Usage:
#   scripts/eest-fetch-fixtures.sh [TAG]
#   TAG defaults to the EEST_FIXTURE_TAG env var, else scripts/eest-fixture-tag.txt.
#
# Output:
#   gen-out/eest-fixtures/<TAG>/fixtures_zkevm.tar.gz   (downloaded)
#   gen-out/eest-fixtures/<TAG>/fixtures/               (extracted tree)
#   gen-out/eest-fixtures/<TAG>/.asset-meta             (size for re-run checks)
#   gen-out/eest-fixtures/<TAG>/.not-available          (release/asset missing marker)
#
# Idempotent: re-running with an already-downloaded asset of the
# expected size skips the download (pass --force to re-download).
#
# Exit:
#   0 -- fixtures present and extracted
#   0 -- fixtures not available upstream for TAG yet (writes .not-available)
#   1 -- download / extraction failed
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

DEFAULT_TAG="$(tr -d '[:space:]' < scripts/eest-fixture-tag.txt 2>/dev/null || true)"
DEFAULT_TAG="${DEFAULT_TAG:-$(cat scripts/eest-fixture-tag.txt)}"
TAG="${1:-${EEST_FIXTURE_TAG:-$DEFAULT_TAG}}"
REPO="${EEST_REPO:-ethereum/execution-specs}"
ASSET="fixtures_zkevm.tar.gz"
FORCE=0
[[ "${2:-}" == "--force" || "${1:-}" == "--force" ]] && FORCE=1

CACHE_DIR="$REPO_ROOT/gen-out/eest-fixtures/$TAG"
TARBALL="$CACHE_DIR/$ASSET"
EXTRACT_DIR="$CACHE_DIR/fixtures"
META_FILE="$CACHE_DIR/.asset-meta"
NOT_AVAILABLE_MARKER="$CACHE_DIR/.not-available"

mkdir -p "$CACHE_DIR"

echo "==> EEST stateless fixtures: $REPO @ $TAG ($ASSET)"

mark_not_available() {
  local reason="$1"
  {
    printf 'tag=%s\n' "$TAG"
    printf 'asset=%s\n' "$ASSET"
    printf 'repo=%s\n' "$REPO"
    printf 'reason=%s\n' "$reason"
  } >"$NOT_AVAILABLE_MARKER"
  echo "EEST fixtures not available for $TAG (upstream release not published yet) -- skipping"
  echo "    $reason"
}

probe_asset() {
  if command -v gh >/dev/null 2>&1; then
    local view_out
    local view_err
    view_err="$(mktemp)"
    if view_out="$(gh release view "$TAG" --repo "$REPO" \
        --json assets \
        --jq ".assets[] | select(.name==\"$ASSET\") | .size" 2>"$view_err")"; then
      rm -f "$view_err"
      if [[ -z "$view_out" ]]; then
        mark_not_available "release exists but asset $ASSET is absent"
        return 2
      fi
      expected_size="$view_out"
      return 0
    fi
    local err
    err="$(<"$view_err")"
    rm -f "$view_err"
    if grep -qiE 'not found|Could not resolve to a Release|HTTP 404' <<<"$err"; then
      mark_not_available "release $TAG not found in $REPO"
      return 2
    fi
    echo "failed to query release $TAG in $REPO: $err" >&2
    return 1
  fi

  # curl fallback -- URL-encode the '@' in the tag as %40.
  enc_tag="${TAG/@/%40}"
  url="https://github.com/$REPO/releases/download/$enc_tag/$ASSET"
  local http_status
  http_status="$(curl -fsIL -o /dev/null -w '%{http_code}' "$url" 2>/dev/null || true)"
  if [[ "$http_status" == "200" || "$http_status" == "302" ]]; then
    return 0
  fi
  if [[ "$http_status" == "404" ]]; then
    mark_not_available "release asset URL returned 404: $url"
    return 2
  fi
  echo "failed to probe release asset URL (HTTP ${http_status:-unknown}): $url" >&2
  return 1
}

# Expected asset size (bytes) from the release metadata, if gh is available.
expected_size=""
probe_rc=0
probe_asset || probe_rc=$?
if [[ "$probe_rc" -eq 2 ]]; then
  exit 0
elif [[ "$probe_rc" -ne 0 ]]; then
  exit "$probe_rc"
fi

need_download=1
if [[ "$FORCE" -eq 0 && -f "$TARBALL" ]]; then
  actual_size="$(stat -c '%s' "$TARBALL" 2>/dev/null || echo 0)"
  if [[ -n "$expected_size" && "$actual_size" == "$expected_size" ]]; then
    echo "    cached tarball matches release size ($actual_size bytes) -- skipping download"
    need_download=0
  elif [[ -z "$expected_size" && "$actual_size" -gt 0 ]]; then
    echo "    cached tarball present ($actual_size bytes); gh unavailable to verify -- reusing"
    need_download=0
  fi
fi

rm -f "$NOT_AVAILABLE_MARKER"

if [[ "$need_download" -eq 1 ]]; then
  echo "==> downloading $ASSET"
  if command -v gh >/dev/null 2>&1; then
    gh release download "$TAG" --repo "$REPO" --pattern "$ASSET" \
      --output "$TARBALL" --clobber
  else
    # curl fallback -- URL-encode the '@' in the tag as %40.
    enc_tag="${TAG/@/%40}"
    url="https://github.com/$REPO/releases/download/$enc_tag/$ASSET"
    echo "    gh not found; curl $url"
    curl -fL --retry 3 -o "$TARBALL" "$url"
  fi
fi

dl_size="$(stat -c '%s' "$TARBALL" 2>/dev/null || echo 0)"
printf 'tag=%s\nasset=%s\nsize=%s\nexpected_size=%s\n' \
  "$TAG" "$ASSET" "$dl_size" "${expected_size:-unknown}" >"$META_FILE"
echo "    tarball: $TARBALL ($dl_size bytes)"

echo "==> extracting into $EXTRACT_DIR"
rm -rf "$EXTRACT_DIR"
mkdir -p "$EXTRACT_DIR"
tar -xzf "$TARBALL" -C "$EXTRACT_DIR"

n_json="$(find "$EXTRACT_DIR" -name '*.json' | wc -l | tr -d ' ')"
echo "==> done: $n_json json file(s) under $EXTRACT_DIR"
echo "    (set EEST_FIXTURES_DIR=$EXTRACT_DIR for the harness)"
