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
obligations. evm-asm's current state per obligation:

| # | Obligation | Status |
|---|---|---|
| 1 | RV64 ELF for `riscv64im_zicclsm-unknown-none-elf` | 🟡 substrate ✅; codegen emits `rv64imac` (one extension off) |
| 2 | `read_input` / `write_output` per the IO interface standard | ✅ verified specs in `Rv64/SyscallSpecs.lean`; codegen M4 wired |
| 3 | RLP-decode the (block, witness) input | 🟡 pure-Lean RLP ✅; RV64 RLP decoder phases 1–3 in progress |
| 4 | EVM interpreter loop running on the decoded block | 🟡 `InterpreterLoop.lean` + handler-table simulation theorems ✅; codegen M5 (tiny EVM interp) not yet shipped |
| 5 | Full opcode coverage with verified handlers | 🟡 see axis A.2 below |
| 6 | Accelerator ECALL bridges per `zkvm_accelerators.h` | 🟡 vendored header + per-precompile EL bridges; not yet codegen-wired |
| 7 | MPT verification of pre-state witness proofs | ✗ not started |
| 8 | Verified post-state root → public output | ✗ blocked on 4 + 5 + 6 + 7 |
| 9 | Halt convention per `standard-termination-semantics` | ✅ `--halt linux93` default, `docs/host-io-halt-convention.md` |

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
| Per-opcode reference-link audit | manual; `EvmWord.<op>` defs cite Python files in their docstrings (not yet machine-checked) |
| EEST fixture pass rate | ✗ harness not yet wired (parking-lot dependency on D obligations 3 + 4) |
| RPC block replay | ✗ not started |

## G — Trust base

| Component | State |
|---|---|
| RV64 instruction semantics tie | `Rv64/SailEquiv/` references the vendored, release-pinned, scoped RV64IM Sail model in `vendor/sail-riscv-zkvm-lean/` (`lakefile.toml` path-dep; pins in `sail-import/PROVENANCE.toml`) |
| Mathlib pin | `lake-manifest.json` (refreshed alongside Lean nightly) |
| Lean toolchain pin | `lean-toolchain` (Lean 4 nightly) |
| Kernel additions | 0 `axiom`, 0 `sorry` (axis A.1) |
| Codegen verification gap | 🟡 codegen is unverified by design (`CODEGEN.md` §Tricky bits #9). Drift caught by build-time `#guard` round-trip tests in `Codegen/RoundTripTests.lean`. |
