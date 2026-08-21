# Build cache: prebuilt oleans

Two independent caches keep an EvmAsm build from starting cold. Neither is
required — both only ever save time. If a fetch fails, Lake logs a warning and
builds from source.

| What | Covers | How you get it |
| --- | --- | --- |
| Mathlib's cache | `mathlib` and its own dependencies | `lake exe cache get` |
| EvmAsm release archive | the `EvmAsm` library itself | automatic for consumers; see below for contributors |

## Consuming EvmAsm

Nothing to run. A project that requires EvmAsm at a **release tag** gets the
prebuilt library from a plain build:

```bash
lake exe cache get   # Mathlib's oleans
lake build           # downloads EvmAsm's oleans instead of compiling them
```

This works because [`lakefile.toml`](../lakefile.toml) sets
`preferReleaseBuild = true`, so Lake fetches `EvmAsm-oleans.tar.gz` from the
matching GitHub release and unpacks it into the build directory. One archive
serves every platform: the `EvmAsm` library sets `platformIndependent = true`,
so its module traces exclude platform-dependent elements and Linux-built oleans
validate on macOS and Windows.

**This only applies to release tags.** Lake resolves the archive URL from a git
tag reachable at the revision you pinned, so a dependency pinned to an arbitrary
`main` commit has no tag, logs `no release tag found for revision`, and compiles
from source. Pin a release tag to get the cache.

The `lean_exe` targets (`codegen`, the `*-check` gates, …) are not in the
archive — their native output is platform-specific. Consumers who need them
build them locally with `lake build <exe>` as usual.

## Working on EvmAsm itself

Lake skips the release-archive path for the root package, so contributors build
from source. To warm a fresh clone from a release instead:

```bash
scripts/get-olean-cache.sh v0.1.0     # or any release tag; defaults to the latest release
```

which is shorthand for:

```bash
gh release download v0.1.0 --pattern EvmAsm-oleans.tar.gz
lake unpack EvmAsm-oleans.tar.gz
```

The unpacked artifacts only validate if your checkout matches the tag's sources
and toolchain — on a different commit, `lake build` rebuilds whatever drifted
(that is the trace machinery working, not a bug).

## Publishing the archive

[`.github/workflows/release-oleans.yml`](../.github/workflows/release-oleans.yml)
runs whenever a GitHub release is published (tags are manual semver, `v0.1.0`,
`v0.2.0`, …) and can be re-run for an existing tag via `workflow_dispatch`. It
checks out the tag, builds **only** the `EvmAsm` library into a wiped build
directory (a full `lake build` would ship the Linux-only `bin/` and `.o` output,
bloating the asset and contradicting the platform-independence claim), then
`lake upload <tag>` packs `.lake/build` and attaches `EvmAsm-oleans.tar.gz` to
the release. Re-runs clobber the existing asset.

## Reproducing an archive locally

```bash
lake exe cache get
rm -rf .lake/build && lake build EvmAsm
lake pack                       # writes .lake/EvmAsm-oleans.tar.gz
tar tzf .lake/EvmAsm-oleans.tar.gz | head
```

`lake pack` only packs already-built output; it never builds.

## What this does not cover

CI's per-commit incremental cache (`actions/cache` on `.lake` in
[`build.yml`](../.github/workflows/build.yml)) is a separate mechanism keyed on
toolchain + manifest + commit; the release archive is cut once per release tag
and plays no part in it.
