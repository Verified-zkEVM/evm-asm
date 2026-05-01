# sail-riscv-lean — Dependency Survey (#84 slice 1)

Survey of [opencompl/sail-riscv-lean](https://github.com/opencompl/sail-riscv-lean)
recorded in support of GH #84 ("Import sail-riscv-lean as Lake dependency"). The
goal of this slice is **investigation only** — no code changes to `EvmAsm/`. The
findings here feed slice 2 (`bd evm-asm-1ghl`: add the `[[require]]` to
`lakefile.toml`) and slice 3 (`bd evm-asm-pmg7`: smoke-import in
`EvmAsm/Rv64/SailBridge.lean`).

Survey performed against upstream `main` HEAD (shallow clone, default branch) on
2026-05-01. Re-run `git ls-remote https://github.com/opencompl/sail-riscv-lean
HEAD` before pinning a `rev` in slice 2.

## (a) Toolchain alignment

`sail-riscv-lean/lean-toolchain`:

```
leanprover/lean4:v4.29.0
```

evm-asm `lean-toolchain`:

```
leanprover/lean4:v4.30.0-rc1
```

**Mismatch.** sail-riscv-lean is one minor version behind. Lake currently
requires identical toolchains across a workspace, so importing as-is will fail
with a toolchain-mismatch error. Options for slice 2:

1. **Pin sail-riscv-lean to a fork/branch matching `v4.30.0-rc1`** — preferred
   if the rems-project / opencompl maintainers have an in-flight bump branch.
   Probe upstream PRs / branches before slice 2 starts.
2. **Wait for upstream to bump.** Defer slice 2 until sail-riscv-lean ships a
   `v4.30.x`-compatible release. Cheapest in engineering effort, but blocks the
   trust anchor work indefinitely.
3. **Bump evm-asm down to `v4.29.0`** — rejected: regression for our own proof
   automation (heartbeat/grind behaviour can shift between minors), and #84's
   intent is to pull SAIL *toward* us, not the other way around.

The AGENTS.md memory note that "sail-riscv-lean uses the same Lean nightly per
project memory" is stale relative to the current upstream HEAD. Update memory /
issue body in slice 2 once the resolution path is chosen.

## (b) Public surface

Top-level umbrella `LeanRV64D.lean` re-exports 25 modules covering the full
RV64D model: registers (`Regs`, `SysRegs`, `InterruptRegs`, `PmpRegs`,
`FdextRegs`, `VextRegs`, `ZicfilpRegs`, `Smcntrpmf`), platform/memory
(`Platform`, `PlatformConfig`, `Pma`, `Vmem`, `VmemTlb`), execution
(`Step`, `Main`, `Fetch`, `ZicsrInsts`, `Zihpm`, `Ssqosid`), and the
core glue (`Flow`, `Common`, `Prelude`, `Xlen`, `RvfiDii`, `SysControl`).

Under `LeanRV64D/`: 155 generated `.lean` files, ~170 k lines total. Notable
modules for our trust-anchor purposes:

- `LeanRV64D/Defs.lean` — base SAIL-translated type definitions
  (heaviest single file at ~18 s build time).
- `LeanRV64D/Step.lean` + `LeanRV64D/Main.lean` — the per-instruction step
  function. This is the primary surface evm-asm wants to bridge to.
- `LeanRV64D/Fetch.lean`, `LeanRV64D/DecodeExt.lean` — instruction decode.
- `LeanRV64D/BaseInsts.lean`, `LeanRV64D/MextInsts.lean` — base + M-extension
  instruction semantics. RV64IM (the extension subset evm-asm targets) is
  covered by `Base*` + `Mext*`.

The umbrella opens `Sail` and `ConcurrencyInterfaceV1` and is wrapped in
`noncomputable section` + `namespace LeanRV64D.Functions`. Importers will need
`open LeanRV64D` (and likely `open Sail`) to reach decode/step.

Per upstream README:

- 4,614 definitions, 194 inductives, 188 abbreviations.
- 0 errors, 0 warnings.
- Tagged "Lean backend for sail is still work-in-progress … Lean code is
  neither executable nor polished". So expect `noncomputable` everywhere — fine
  for type-level / proof bridging, **not** for `#eval`/`native_decide` smoke
  tests on slice 3.

## (c) Lakefile structure

`sail-riscv-lean/lakefile.toml` (full contents):

```toml
name = "Lean_RV64D"
defaultTargets = ["LeanRV64D"]
moreLeanArgs = ["--tstack=400000"]

[[lean_lib]]
name = "LeanRV64D"
leanOptions.weak.linter.style.nameCheck = false
moreLeancArgs = ["-fbracket-depth=500"]

[[require]]
name = "Sail"
git = "https://github.com/rems-project/lean-sail"
rev = "v4"
```

Single transitive dependency: `Sail` from `rems-project/lean-sail` at
ref `v4`. **No mathlib**, no other deps. Per the manifest, `v4` resolved to
commit `79b4d08505af29d88b3918f32d29840fae1fa191` at the time of survey.

Note the package-level `--tstack=400000` and library-level
`-fbracket-depth=500` — these are needed because the SAIL-generated code has
deeply nested expressions. Importers that touch `LeanRV64D.Defs` or instruction
files transitively may need to mirror these flags or accept slow compile.

The package also disables `linter.style.nameCheck` — generated code does not
follow our naming convention, so do not be surprised by SAIL-style names
(snake_case, generated identifiers) leaking into our namespace at the bridge
layer.

## (d) Footprint

- **Repo size:** ~49 MB (shallow clone, including build_log artifact).
- **Source LOC:** ~170 157 lines across 156 `.lean` files.
- **Build job count:** 127 jobs (3 `Sail.*` + 124 `LeanRV64D.*`).
- **Slowest single file:** `LeanRV64D.InstsEnd` at ~80 s; second is
  `LeanRV64D.ZicsrInsts` at ~30 s; `LeanRV64D.Defs` at ~18 s. Most files build
  under 2 s.
- **Total upstream build time:** wall-clock not captured by `build_log.txt`;
  given the 80 s tail item and 127 jobs, expect cold-cache full build in the
  order of several minutes on a single core.

For evm-asm, the cost per `lake build` after the initial fetch is:

- **Mathlib-style cache miss:** none — sail-riscv-lean has no mathlib dep, so
  there is no equivalent of `lake exe cache get`. Every CI runner that doesn't
  hit Lake's per-package olean cache will rebuild from scratch.
- **CI implication:** budget at least the slowest tail (~80 s for
  `InstsEnd` alone) + ~3 minutes for the remaining instruction files when the
  cache is cold. Slice 2 should add a CI cache step keyed on
  `lake-manifest.json` to amortise this.

## Risks / open questions for slice 2

1. **Toolchain bump path** — track upstream branches/PRs for
   `leanprover/lean4:v4.30.0-rc1` compatibility before pinning a `rev`. If none
   exists, file an upstream issue or escalate to @pirapira before adding the
   require.
2. **Build-time blow-up** — `InstsEnd` (~80 s) and `ZicsrInsts` (~30 s) will
   land in our CI critical path if anything in evm-asm transitively imports the
   step function. Slice 3's smoke import should pull the *narrowest* surface
   that demonstrates the bridge (e.g. just `LeanRV64D.BaseTypes` or
   `LeanRV64D.Defs`), to avoid forcing instruction files into our hot rebuild
   loop.
3. **`noncomputable` everywhere** — slice 3 must not attempt `native_decide`
   against any sail-riscv-lean definition. Bridge lemmas will need to stay at
   the propositional level.
4. **`maxHeartbeats 1_000_000_000` in upstream files** — this is upstream's own
   global override and does not affect our files. AGENTS.md's "Do NOT add
   `set_option maxHeartbeats`" rule still applies to evm-asm code. The bridge
   module should not inherit upstream heartbeat settings.

## References

- Upstream repo: <https://github.com/opencompl/sail-riscv-lean>
- Sail-Lean backend: <https://github.com/rems-project/lean-sail> (`v4` ref)
- Original SAIL RISC-V spec: <https://github.com/riscv/sail-riscv>
- Tracking issue: <https://github.com/Verified-zkEVM/evm-asm/issues/84>
- Beads parent: `evm-asm-ihpr`; this slice: `evm-asm-qxv6`.
