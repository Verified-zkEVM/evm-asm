# SOUNDNESS survey for evm-asm

This document enumerates the trusted base, the verified properties, and the
known gaps in the evm-asm verification effort, as a feeder for the eventual
top-level `SOUNDNESS.md` (GH issue #465). It is intentionally factual and
concrete so that the SOUNDNESS.md draft can lift sections directly.

## 1. End goal recap

The project's top-level claim, when complete, will be: a verified
RISC-V (RV64IM) implementation of Ethereum's stateless guest entry point —
`run_stateless_guest` from
`execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py` (vendored as
a submodule under `execution-specs/`) — proved correct against the Python
execution-specs by composing Hoare triples through a separation-logic spec
language for the underlying RV64IM machine.

Today the project verifies large *components* of that goal (RV64IM
instruction semantics, EVM opcode subroutines, RLP encode/decode) but **not**
the top-level `run_stateless_guest`.

## 2. Trusted base (assumptions)

These are the things a reader must trust for evm-asm's claims to be
meaningful. They are intentionally listed even when standard, because
SOUNDNESS.md is for an external audience.

### 2.1 Lean 4 toolchain

* Lean version: `leanprover/lean4:v4.30.0-rc1` (pinned in `lean-toolchain`).
* Mathlib via lake (`leanprover-community/mathlib`, scope-pinned in
  `lakefile.toml`).
* The Lean 4 kernel — type-checking and definitional equality.
* Standard Lean axioms used by mathlib: `Classical.choice`,
  `propext`, `Quot.sound`. (Concrete axiom audit per top-level theorem is
  a follow-up; see Gaps.)

### 2.2 RISC-V ISA semantics

* `EvmAsm/Rv64/Instructions.lean` and `EvmAsm/Rv64/Execution.lean` define the
  *project's* RV64IM step relation directly in Lean, plus an `ECALL`
  syscall dispatch layer.
* The repo also tracks `EvmAsm/Rv64/SailEquiv/` and depends on
  `dhsorens/sail-riscv-lean` (a fork of the Sail-generated RISC-V Lean spec)
  via `[[require]] Lean_RV64D` in `lakefile.toml`. The longer-term plan is to
  prove equivalence between the project's RV64IM model and the Sail-derived
  spec; that bridge is partial today.
* So the *current* trust assumption is "the Lean RV64IM model in
  `EvmAsm/Rv64/Instructions.lean` faithfully describes the subset of RV64IM we
  emit". The Sail-equivalence work, when complete, will discharge most of
  that assumption against the official Sail spec.

### 2.3 EVM ground truth

* `execution-specs` (Ethereum's official Python execution layer spec, pinned
  as a git submodule). Specifically, the `amsterdam` fork's
  `stateless_guest.run_stateless_guest` is the reference for the top-level
  claim, and per-opcode Python definitions under `ethereum.forks.amsterdam.vm`
  are the per-opcode reference for the EVM opcode subroutines.
* The translation from Python to Lean specifications is hand-written; we
  trust that the Lean-side spec faithfully encodes the Python reference. A
  systematic differential audit (e.g. cross-checking via the execution-specs
  test vectors, or property-based test extraction) is **not** in scope today.

### 2.4 Calling conventions and ABI

* `EvmAsm/Evm64/zkvm-standards/` (submodule, `eth-act/zkvm-standards`) defines
  the LP64 register convention and stateless-zkVM ABI we target. We assume
  this is what real zkVM hosts implement.
* `EvmAsm/Evm64/CallingConvention.lean` operationalises the LP64 convention
  in our spec language; new code is required to follow it (per AGENTS.md).

### 2.5 Separation-logic primitives

* `EvmAsm/Rv64/SepLogic.lean` defines:
  * `PartialState` — partial maps for registers, memory, code, and the PC.
  * `**` (`sepConj`), `↦ᵣ`, `↦ₘ`, `pcIs`, `codeIs`, `empAssertion`, etc.
  * The `holdsFor` bridge from partial states to full machine states.
* `EvmAsm/Rv64/CPSSpec.lean` defines `cpsTriple` (CPS-style Hoare triples)
  and the structural rules.
* These foundations are themselves *proved* in Lean (no axioms beyond the
  kernel ones) — they are part of the verified base, not the trusted base.

### 2.6 `native_decide` and other proof-time oracles

* `native_decide` *does* extend the trust base when it appears in a proof:
  it compiles a decidable proposition to native code and trusts the native
  compiler / runtime / Lean's `Lean.ofReduceBool` axiom.
* Repo audit (2026-04-30): `native_decide` appears in **5 sites in 1 file**:
  `EvmAsm/Evm64/EvmWordArith/Div128NoWrapInvSearch.lean`. All 5 sites are
  exhaustive search proofs over small bounded ranges (BitVec witness
  searches for the Div128 no-wrap invariant). This is a small, contained
  trust extension and is documented in the file.
* `decide` (without `native`) is widely used and does **not** extend trust
  beyond the kernel.

### 2.7 Build and CI

* `lakefile.toml` (Lake 5.0 format), `lake-manifest.json`. Trusting `lake`,
  the GitHub Actions workflows under `.github/workflows/`, and the
  `scripts/check-unimported.sh` enforcement that every `.lean` under
  `EvmAsm/` is reachable from `EvmAsm.lean` (so no unreachable-but-claimed
  proof can hide).

## 3. What is currently verified

### 3.1 RV64IM instruction Hoare triples

* Per-instruction `cpsTriple` specs for the RV64IM subset we emit, in
  `EvmAsm/Rv64/InstructionSpecs.lean` and the
  `EvmAsm/Rv64/{RegOps,WordOps,HalfwordOps,ByteOps,ControlFlow}.lean` family.
* Generic spec templates in `GenericSpecs.lean`; syscall dispatch specs in
  `SyscallSpecs.lean`.
* Frame-automation tactics (`runBlock`, `seqFrame`, `xperm`, `xperm_hyp`,
  `xcancel`, the `@[spec_gen]` registry, domain grindsets) in
  `EvmAsm/Rv64/Tactics/`. See `TACTICS.md`.

### 3.2 EVM opcode subroutines (RV64IM implementations + specs)

Each opcode lives under `EvmAsm/Evm64/<Opcode>/` with a three-level proof
hierarchy (`LimbSpec` → `Compose` → `Semantic`) per `AGENTS.md`. Currently
landed (non-exhaustive list, by directory):

* Stack/control: `Push0`, `Pop`, `Dup`, `Swap`.
* Arithmetic: `Add`, `Sub`, `Multiply`, `DivMod` (large; in active closure —
  see GH #1337 / #61), `SignExtend`.
* Bitwise: `And`, `Or`, `Xor`, `Not`, `Byte`, `Shift` (SHL/SHR/SAR).
* Comparison: `Eq`, `IsZero`, `Lt`, `Gt`, `Slt`, `Sgt`.

Each opcode's `Semantic.lean` lifts the limb-level proofs to a stack-level
spec over `evmWordIs` (256-bit `EvmWord`s as 4 × 64-bit limbs).

Not yet landed (representative): `SDIV`, `SMOD`, `ADDMOD`, `MULMOD`, `EXP`,
plus storage / memory / context / log / system opcodes.

### 3.3 RLP encoding / decoding

* `EvmAsm/EL/RLP/{Basic,Decode,Properties}.lean` define RLP at the pure
  Ethereum-spec level (no RISC-V dependency) and prove canonical-form
  round-trip properties (some via `native_decide`-free `decide`).
* `EvmAsm/Rv64/RLP.lean` is the in-progress RV64IM implementation tier.

### 3.4 Outstanding `sorry`s (audit 2026-04-30)

13 `.lean` files under `EvmAsm/` contain `sorry` (28 occurrences total).
All are localised in DivMod and Div128 proof closure work that is being
actively driven by GH issues #1337 / #1338 / #61 and tracked in beads.
Specifically:

* `EvmAsm/Evm64/DivMod/{LoopIterN1,LoopIterN2,LoopIterN3,LoopIterN4}*.lean`
  (16 occurrences): per-iteration call/max/beq postcondition proofs.
* `EvmAsm/Evm64/DivMod/Spec/{CallAddback,CallAddbackMod}.lean` (5)
  and `SpecCallAddbackBeq/AlgEuclideans.lean` (1): Euclidean algebra
  closure.
* `EvmAsm/Evm64/DivMod/LoopBody/MulsubCorrectionSkip.lean` (1) and
  `LoopDefs/IterV4.lean` (1): supporting bridge lemmas.
* `EvmAsm/Evm64/EvmWordArith/{Div128CallSkipClose,CallSkipLowerBoundV2/Un21Bridge,CallSkipLowerBoundV2/CompensationCases}.lean`
  (6 across 3 files): Div128 Knuth-B closure (KB-6b/c/d).

No `sorry` exists outside DivMod / Div128. The non-DivMod opcode
subroutines are sorry-free.

## 4. What is NOT yet verified

These are gaps the SOUNDNESS.md should explicitly call out so external
readers do not over-claim.

1. **Top-level `run_stateless_guest`.** No Hoare-triple spec exists yet
   linking the RV64IM image to the Python `run_stateless_guest` function.
   This is the project's headline goal.
2. **Gas accounting.** The opcode subroutines focus on functional
   correctness; gas semantics are not yet tracked.
3. **World state / storage / accounts.** Storage opcodes (SLOAD/SSTORE),
   account creation/deletion, log opcodes, balance/transfer, and the
   stateless-witness (MPT) machinery are not yet verified — only pure
   stack-and-memory opcodes are.
4. **Sail equivalence.** The `EvmAsm/Rv64/SailEquiv/` bridge to
   `dhsorens/sail-riscv-lean` is partial; the project's Lean RV64IM model
   is not yet proved equivalent to the Sail-generated spec across the full
   instruction subset we use.
5. **Open `sorry`s in DivMod / Div128.** See §3.4. DivMod's stack-level
   semantic spec is not closed until the Knuth-B bound (KB-6b/c/d) and
   the addback / addback-beq postcondition proofs land.
6. **Cryptographic precompiles.** ECRECOVER, SHA256, RIPEMD160, MODEXP,
   BN254 curves, BLS12-381, KZG, etc. — not in scope today.
7. **Concrete axiom audit.** No automated `#print axioms` report is
   published per top-level theorem. Standard Lean/mathlib axioms are
   assumed; a concrete report would tighten the trust statement.
8. **`execution-specs` ↔ Lean-spec faithfulness.** Translation is
   hand-written; no systematic differential test against execution-specs
   test vectors is wired up.

## 5. Suggested SOUNDNESS.md structure (input to slice 2)

Mirroring mlkem-native's SOUNDNESS.md, the draft should have:

1. *What we prove.* (§3 above, condensed.)
2. *What we trust.* (§2 above.) Split into "standard" trust (Lean kernel,
   mathlib axioms) and "project-specific" trust (RV64IM Lean model,
   execution-specs faithfulness, `native_decide` sites, zkvm-standards ABI).
3. *Known gaps.* (§4 above.)
4. *How to reproduce.* Build instructions, CI invariants
   (`scripts/check-unimported.sh`, no-`maxHeartbeats`-bumps rule from
   AGENTS.md).
5. *Pointers.* Per-opcode README hooks, beads backlog (#1337, #1338, #61),
   PLAN.md for roadmap.

Slice 2 (evm-asm-dyc) can lift sections 2, 3, and 4 of this document
nearly verbatim.
