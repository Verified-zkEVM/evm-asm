"""Shared RISC-V binutils resolution across triple spellings (GH #12503).

CI installs `binutils-riscv64-unknown-elf` (`riscv64-unknown-elf-*`). Homebrew's
`riscv64-elf-binutils` on macOS installs the same GNU tools as `riscv64-elf-*`.
Without a fallback, bytecode / reloc / CFG gates either `FileNotFoundError` mid
lane or silently skip — both read as green while checking nothing.

Same convention as `_riscv_tool` in `asm_to_program.py`, `Driver.lean`'s
candidate lists, and `resolve_riscv_tool` in `codegen-eest-stateless-check.sh`:

  1. `$RISCV_<TOOL>` env override (e.g. `RISCV_AS`, `RISCV_OBJDUMP`)
  2. `riscv64-unknown-elf-<tool>`
  3. `riscv64-elf-<tool>`
"""
from __future__ import annotations

import os
import shutil
import sys


def riscv_candidates(tool: str) -> list[str]:
    return [f"riscv64-unknown-elf-{tool}", f"riscv64-elf-{tool}"]


def env_var_for(tool: str) -> str:
    return f"RISCV_{tool.upper()}"


def resolve_riscv_tool(
    tool: str,
    *,
    env_var: str | None = None,
    fallback_name: bool = True,
) -> str | None:
    """Return an absolute path (or env override string) for ``tool``.

    If nothing is on PATH: return the preferred triple name when
    ``fallback_name`` is True (caller will fail later at exec), else None.
    """
    ev = env_var or env_var_for(tool)
    from_env = os.environ.get(ev)
    if from_env:
        return from_env
    for cand in riscv_candidates(tool):
        path = shutil.which(cand)
        if path:
            return path
    if fallback_name:
        return riscv_candidates(tool)[0]
    return None


def tried_names(tool: str, *, env_var: str | None = None) -> list[str]:
    """Names a human / skip message should list for ``tool``."""
    ev = env_var or env_var_for(tool)
    return [f"${ev}", *riscv_candidates(tool)]


def require_riscv_tools(*tools: str, prog: str = "riscv_tools") -> dict[str, str]:
    """Resolve each tool to a path; exit 1 with a loud miss message otherwise."""
    out: dict[str, str] = {}
    missing: list[str] = []
    for tool in tools:
        path = resolve_riscv_tool(tool, fallback_name=False)
        if path is None:
            missing.append(tool)
        else:
            out[tool] = path
    if missing:
        parts = []
        for tool in missing:
            parts.append(
                f"{tool}: tried {' | '.join(tried_names(tool))} — none found"
            )
        sys.stderr.write(
            f"{prog}: missing RISC-V toolchain tool(s):\n"
            + "\n".join(f"  {p}" for p in parts)
            + "\nInstall binutils-riscv64-unknown-elf (CI/Linux) or "
            "riscv64-elf-binutils (Homebrew macOS), or set the env vars above.\n"
        )
        raise SystemExit(1)
    return out
