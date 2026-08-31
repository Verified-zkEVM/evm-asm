#!/usr/bin/env python3
"""Experimental probe for Lake's synthetic artifact-cache traces (GH #13092).

This is intentionally *not* a production fix and is not wired into axiomsweep or
CI.  It records the experiment that linked cached outputs named by synthetic
``.trace`` files so the resulting failure can be reproduced and inspected.  The
probe showed that missing links were not the whole problem: after 8,030 outputs
were linked, axiomsweep advanced to an Aesop private-declaration mismatch.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import tempfile
from pathlib import Path


def cache_enabled() -> bool:
    return os.environ.get("LAKE_ARTIFACT_CACHE", "").strip().lower() in {
        "1",
        "true",
        "yes",
        "on",
    }


def cache_root() -> Path:
    configured = os.environ.get("LAKE_CACHE_DIR")
    if configured:
        return Path(configured).expanduser()
    return Path.home() / ".cache" / "lake-artifact-cache"


def output_target(trace: Path, artifact: str) -> Path:
    """Map a cache artifact name to the output named by its trace."""
    suffixes = (".olean.server", ".olean.private", ".olean")
    for suffix in suffixes:
        if artifact.endswith(suffix):
            return trace.with_suffix("").with_suffix(suffix)
    return trace.with_suffix("") / artifact


def iter_traces(root: Path):
    # Package builds have their own nested .lake/build trees, so scan the whole
    # checkout rather than only the root .lake/build directory.
    yield from sorted(root.glob(".lake/**/*.trace"))


def materialize(root: Path) -> tuple[int, int]:
    if not cache_enabled():
        print("materialize-lake-artifacts: LAKE_ARTIFACT_CACHE is disabled; nothing to do")
        return 0, 0

    artifacts = cache_root() / "artifacts"
    linked = 0
    failures = 0
    for trace in iter_traces(root):
        try:
            payload = json.loads(trace.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            print(f"materialize-lake-artifacts: cannot read {trace}: {exc}")
            failures += 1
            continue
        if not payload.get("synthetic", False):
            continue
        outputs = payload.get("outputs", {})
        for artifact in outputs.get("o", []):
            source = artifacts / artifact
            target = output_target(trace, artifact)
            if target.exists():
                continue
            if not source.exists():
                print(f"materialize-lake-artifacts: missing cache artifact {source}")
                failures += 1
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            try:
                os.link(source, target)
            except FileExistsError:
                continue
            except OSError as exc:
                if exc.errno != 18:  # EXDEV: cache and checkout are different filesystems.
                    print(f"materialize-lake-artifacts: cannot link {source} -> {target}: {exc}")
                    failures += 1
                    continue
                try:
                    shutil.copyfile(source, target)
                except OSError as copy_exc:
                    print(f"materialize-lake-artifacts: cannot copy {source} -> {target}: {copy_exc}")
                    failures += 1
                    continue
            linked += 1
    print(f"materialize-lake-artifacts: linked={linked} failures={failures}")
    return linked, failures


def self_test() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        trace = root / ".lake" / "build" / "X.trace"
        trace.parent.mkdir(parents=True)
        trace.write_text(json.dumps({"synthetic": True, "outputs": {"o": ["x.olean"]}}))
        cache = root / "cache" / "artifacts"
        cache.mkdir(parents=True)
        (cache / "x.olean").write_bytes(b"probe")
        old_cache = os.environ.get("LAKE_CACHE_DIR")
        old_enabled = os.environ.get("LAKE_ARTIFACT_CACHE")
        os.environ["LAKE_CACHE_DIR"] = str(root / "cache")
        os.environ["LAKE_ARTIFACT_CACHE"] = "true"
        try:
            linked, failures = materialize(root)
        finally:
            if old_cache is None:
                os.environ.pop("LAKE_CACHE_DIR", None)
            else:
                os.environ["LAKE_CACHE_DIR"] = old_cache
            if old_enabled is None:
                os.environ.pop("LAKE_ARTIFACT_CACHE", None)
            else:
                os.environ["LAKE_ARTIFACT_CACHE"] = old_enabled
        assert (linked, failures) == (1, 0)
        assert (root / ".lake" / "build" / "X.olean").read_bytes() == b"probe"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        print("materialize-lake-artifacts: self-test passed")
        return 0
    _, failures = materialize(args.root.resolve())
    return 2 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
