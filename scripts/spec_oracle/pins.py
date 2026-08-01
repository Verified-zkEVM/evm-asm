"""spec_oracle.pins — reference pinning, branching on vendored vs external.

The single most transferable lesson from the RLP instance: **how a reference is
pinned determines how much machinery an oracle needs**, and getting it wrong
silently makes the oracle authoritative for the wrong version.

Two kinds of reference, with different needs:

* **Vendored** — the reference lives under `execution-specs/src/…`, inside the
  submodule this repo pins by gitlink. The gitlink pins the code; a citation in
  a Lean docstring is already machine-checked by `scripts/check-spec-refs.sh`.
  Nothing more is needed. Most families are this kind.

* **External** — the reference is a PyPI package (`ethereum_rlp`,
  `remerkleable`, …) that execution-specs *depends on* but does not contain.
  The gitlink does not pin it directly; the version lives in
  `execution-specs/uv.lock`. Such a family needs the version resolved from the
  lock, the installed version checked against it, and the version stamped into
  the corpus.

The trap that motivated this split, recorded so the next family does not repeat
it: `ethereum_rlp` **0.1.5 silently accepts trailing bytes after a complete
item; 0.1.6 rejects them.** A stale environment supplies 0.1.5, and reading it
inverts a strictness verdict — you conclude "our decoder is stricter" when it
matches exactly. `pyproject.toml` carries a *range* (`>=0.1.6,<0.2`), not a pin;
only `uv.lock` has the pin.
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys


def execution_specs_sha(repo_root: pathlib.Path) -> str:
    """The execution-specs gitlink SHA recorded in the superproject tree.

    Read from the tree rather than the submodule working copy, so it is
    available even when the submodule is not checked out — which is how CI
    verifies a committed corpus still describes the pinned reference.
    """
    out = subprocess.run(
        ["git", "ls-tree", "HEAD", "execution-specs"],
        cwd=repo_root, capture_output=True, text=True, check=True).stdout
    m = re.search(r"commit ([0-9a-f]{40})", out)
    return m.group(1) if m else "unknown"


class Reference:
    """Base: a reference implementation an oracle runs against."""

    def describe(self) -> str:
        raise NotImplementedError

    def verify_and_describe_version(self) -> str:
        """Return the version stamp, raising if the environment does not match
        the repo's pin. Called before any corpus is written."""
        raise NotImplementedError


class Vendored(Reference):
    """A reference inside the execution-specs submodule.

    The gitlink is the pin, so there is no separate version to verify. Cite the
    module path in the Lean model's docstring and `scripts/check-spec-refs.sh`
    will machine-check that the citation resolves and its `function` anchor
    exists.
    """

    def __init__(self, module_path: str, repo_root: pathlib.Path):
        self.module_path = module_path
        self.repo_root = repo_root

    def describe(self) -> str:
        return f"execution-specs/{self.module_path} (vendored; pinned by gitlink)"

    def verify_and_describe_version(self) -> str:
        path = self.repo_root / "execution-specs" / self.module_path
        if not path.exists():
            sys.stderr.write(
                f"error: {path} not found — the execution-specs submodule is not\n"
                f"populated at the pinned rev. Run:\n"
                f"    git submodule update --init execution-specs\n")
            raise SystemExit(2)
        return f"execution-specs/{self.module_path}@gitlink"


class ExternalPackage(Reference):
    """A PyPI package that execution-specs depends on but does not vendor."""

    def __init__(self, dist_name: str, repo_root: pathlib.Path):
        self.dist_name = dist_name
        self.repo_root = repo_root

    @property
    def uv_lock(self) -> pathlib.Path:
        return self.repo_root / "execution-specs" / "uv.lock"

    def locked_version(self) -> str | None:
        """The version pinned by execution-specs/uv.lock, or None if the
        submodule is not populated. uv.lock `[[package]]` blocks are name/version
        pairs; we want the version line immediately after our name line."""
        if not self.uv_lock.exists():
            return None
        text = self.uv_lock.read_text(encoding="utf-8")
        m = re.search(rf'^name = "{re.escape(self.dist_name)}"\nversion = "([^"]+)"',
                      text, re.MULTILINE)
        return m.group(1) if m else None

    def installed_version(self) -> str:
        from importlib.metadata import version
        return version(self.dist_name)

    def describe(self) -> str:
        return (f"{self.dist_name} (external PyPI package, NOT vendored; "
                f"pinned by execution-specs/uv.lock)")

    def verify_and_describe_version(self) -> str:
        locked = self.locked_version()
        if locked is None:
            sys.stderr.write(
                "error: execution-specs/uv.lock not found — the submodule is not\n"
                "populated, so the reference pin cannot be verified. Run:\n"
                "    git submodule update --init execution-specs\n")
            raise SystemExit(2)
        installed = self.installed_version()
        if installed != locked:
            sys.stderr.write(
                f"error: installed {self.dist_name} {installed} != pinned {locked}\n"
                f"(execution-specs/uv.lock). Generating against the wrong reference\n"
                f"would make the oracle silently authoritative for a version this\n"
                f"repo does not use — and for some packages a minor bump changes\n"
                f"strictness (see this module's docstring). Install the pin:\n"
                f"    uv pip install --target <dir> {self.dist_name}=={locked}\n"
                f"    PYTHONPATH=<dir> scripts/spec-oracle.py ...\n")
            raise SystemExit(2)
        return f"{self.dist_name}=={installed}"
