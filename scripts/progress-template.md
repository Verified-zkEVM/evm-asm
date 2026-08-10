<!--
  Hand-written prose interpolated by scripts/progress-report.sh.
  Edit this file to refresh narrative sections without touching the
  shell script. The kernel-checked, registry-driven tables are
  emitted by `lake exe progress-report`; everything below is
  reviewer-maintained.
-->

## Role in the L1-zkEVM stack

evm-asm is a **verified guest program core** for Ethereum L1 zero-knowledge
provers. The wider L1 zkEVM ecosystem layers are:

```
┌──────────────────────────────────────────────────────────────────┐
│  Block + execution witness  (EEST fixtures, real-chain RPC)      │
└──────────────────────────────────────────────────────────────────┘
                              │  read_input
┌──────────────────────────────────────────────────────────────────┐
│  Guest program (a stateless block validator ELF)                 │
│  - reth, ethrex, …  ← compiled from a Rust EL client             │
│  - evm-asm          ← built bottom-up from verified RV64         │
└──────────────────────────────────────────────────────────────────┘
                              │  riscv64im_zicclsm-unknown-none-elf
┌──────────────────────────────────────────────────────────────────┐
│  zkVM (Airbender / OpenVM / Risc0 / SP1 / Zisk / …)              │
│  - ere : unified host API                                        │
│  - zkvm-standards : RISC-V target + IO + accelerators + halt     │
└──────────────────────────────────────────────────────────────────┘
                              │  write_output
                              ▼
                        Post-state root
```

External anchors:

- **[`eth-act/zkvm-standards`](https://github.com/eth-act/zkvm-standards)** —
  RISC-V target, IO interface, accelerator C ABI, memory layout, termination
  semantics. evm-asm targets every published clause; current state in axis E below.
- **[`eth-act/ere`](https://github.com/eth-act/ere)** — unified Rust host API
  abstracting Airbender / OpenVM / Risc0 / SP1 / Zisk under one
  `Compiler` / `zkVMProver` / `zkVMVerifier` interface. evm-asm aims to ship as
  a sibling to the existing [`ere-guests`](https://github.com/eth-act/ere-guests)
  `stateless-validator-*` binaries.
- **[`eth-act/zkevm-benchmark-workload`](https://github.com/eth-act/zkevm-benchmark-workload)** —
  fixture-driven benchmark harness (EEST + RPC + raw-input). evm-asm's eventual
  metrics (cycles, proof size, proving/verification time) belong here.
- **[`zkevm.ethereum.foundation/blog/benchmarking-zkvms`](https://zkevm.ethereum.foundation/blog/benchmarking-zkvms)** —
  motivation for the 2026 L1-zkEVM roadmap: real-time proving, multi-zkVM
  redundancy, formal-verification leg.

## What "evm-asm is a complete guest program" means

A guest program for L1 stateless block validation must satisfy nine
obligations. The per-obligation status and the opcodes/infrastructure blocking
each one are tracked in the **kernel-checked obligation matrix** rendered below
(see the *Guest-program obligations* section) — source of truth and counts live
in [`EvmAsm/Progress/Obligations.lean`](EvmAsm/Progress/Obligations.lean), and a
fuller "what is NOT proven" ledger lives in [`DRIFT.md`](DRIFT.md).

## Axes the dashboard below tracks

| Axis | What it measures |
|---|---|
| A | **Verification depth** — kernel invariants + per-opcode proof tier |
| B | **Verification breadth** — bridges, conformance, simulation reach |
| C | **Cost surrogate** — per-opcode `cpsTripleWithin N` cycle bound (a verified gas-cost proxy) |
| D | **End-to-end runnability** — codegen registry, ziskemu round-trips, milestones |
| E | **zkvm-standards conformance** — clause-by-clause |
| F | **execution-specs conformance** — fork, reference-link audit, EEST/RPC pass rate |
| G | **Trust base** — Sail tie, dependency pins, axiom count, unverified codegen gap |
| H | **Process / CI** — guardrails, benchmark history |

Axes A.2, B.5, C.1, D are emitted from `lake exe progress-report` plus the
shell wrapper. Axes E, F, G are maintained below; refresh in this template
when the underlying state changes.

### Proof-tier rubric (axis A.2)

The per-opcode coverage table classifies each opcode by a kernel-checked
`ProofTier` in [`EvmAsm/Progress.lean`](EvmAsm/Progress.lean). The tiers
separate a *complete spec on a restricted input domain* from *half-built work*
— conflating the two is the statement-vacuity blind spot this dashboard exists
to surface (the DIV `b.getLimbN 3 = 0` trap).

| Tier | Meaning |
|---|---|
| ✅ proven | Complete top-level Hoare triple specifying the opcode's full effect, with **no** input-domain precondition. |
| 🔶 conditional | Complete top-level triple, but **gated by a nonvacuous input-domain precondition** that excludes a real input region (DIV/MOD `b.getLimbN 3 = 0`; SDIV `hStack`). Distinct from proven (no restriction) and partial (no complete triple). |
| 🟡 partial | **No** complete triple yet — only an `EvmWord.<op>_correct` lemma, a preamble/partial-effect spec, or a sub-component. |
| ⏳ execSpec | Executable-spec / handler / bridge semantics only; no RV64 subroutine produces the EVM result. |
| ✗ notStarted | Not represented in `EvmOpcode` yet (e.g. unimplemented EIPs). |

A single-point restriction (ADDMOD's `b=0`-only triple, PUSH2..32's
zero-slot-only triple) stays 🟡 partial, not 🔶 conditional. The `Cycles (N)`
column is the typed `cpsTripleWithin N` step bound (cost surrogate); see C.1.

## E — zkvm-standards conformance

| Standard clause | Status |
|---|---|
| `riscv-target` (`riscv64im_zicclsm-unknown-none-elf`) | 🟡 substrate matches; emitter still uses `rv64imac` (track in [#TBD](.)) |
| `io-interface` (`read_input` / `write_output`) | ✅ verified specs + codegen M4 |
| `c-interface-accelerators` (`zkvm_accelerators.h`) | 🟡 header vendored; per-precompile bridges Lean-only |
| `memory-layout-restrictions` | ✅ codegen uses vendor linker conventions (`-Ttext=0x80000000 -Tdata=0xa0000000`) |
| `standard-termination-semantics` | ✅ `--halt linux93` default, ADR landed |

## F — execution-specs conformance

| Aspect | Status |
|---|---|
| Reference fork | Frontier/Shanghai (most opcodes); Amsterdam draft fork referenced for SDIV/SMOD |
| Pin | `ethereum/execution-specs@ec23140` (gitlink in `.gitmodules`) |
| Reference-link audit | machine-checked by [`scripts/check-spec-refs.sh`](scripts/check-spec-refs.sh): every `execution-specs/<path>.py` citation in `EvmAsm/**` must resolve at the pinned rev, and a `function \`name\`` anchor must name a real `def`/`class`. Blocking; known-stale entries burn down in [`scripts/spec-refs-allow.txt`](scripts/spec-refs-allow.txt) |
| Spec-correspondence audit | see **F.2** below — per-routine verdict + basis from the kernel-checked registry in [`EvmAsm/Progress/Correspondence.lean`](EvmAsm/Progress/Correspondence.lean); RLP model differential replayed in CI by `lake exe correspondence-check rlp` |
| EEST fixture pass rate | ✗ harness not yet wired (parking-lot dependency on D obligations 3 + 4) |
| RPC block replay | ✗ not started |

## G — Trust base

| Component | State |
|---|---|
| RV64 instruction semantics tie | `Rv64/SailEquiv/` references the vendored, release-pinned, scoped RV64IM Sail model in `vendor/sail-riscv-zkvm-lean/` (`lakefile.toml` path-dep; pins in `sail-import/PROVENANCE.toml`) |
| Mathlib pin | `lake-manifest.json` (refreshed alongside Lean nightly) |
| Lean toolchain pin | `lean-toolchain` (Lean 4 nightly) |
| Kernel additions | 0 literal `axiom`, 0 `sorry`. Both TCB-expanding tactics are forbidden and fully eliminated (`native_decide` 206→0, `bv_decide` 290→0), so the trusted base is only the three classical axioms (`propext`, `Classical.choice`, `Quot.sound`) off the Sail-correspondence surface; the 74 `Rv64.SailEquiv.*` declarations (and nothing else) additionally rest on four uninterpreted platform constants axiomatized by the vendored Sail model (`Out/RiscvExtras.lean`) — non-Prop constants of inhabited types, so no proposition is assumed; pinned per declaration in `scripts/axiom_baseline.json`, audited by `lake exe axiomsweep --check`. The `scripts/axiom-allow.txt` burndown list is now empty. Audited by `scripts/check-axioms.sh` (axis A.1) and pre-filtered by `scripts/check-forbidden-tactics.sh`. |
| Codegen verification gap | 🟡 codegen is unverified by design (`CODEGEN.md` §Tricky bits #9). Drift caught by build-time `#guard` round-trip tests in `Codegen/RoundTripTests.lean`. |
