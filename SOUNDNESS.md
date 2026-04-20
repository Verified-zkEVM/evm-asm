# SOUNDNESS

This document records, for the EvmAsm verified macro assembler, what is proved,
what is trusted, and the assumptions on which the correctness claims rest. It
is intended as the single reference for anyone evaluating what EvmAsm's
"verified" claim means.

> **Project status.** EvmAsm is an experimental research prototype. The
> `README.md` warning is primary: do not use this project for anything of value.
> This document describes the *intent* of the verification; it does not imply
> the project is production-ready.

## 1. Statements that are proved

All proofs are elaborated and kernel-checked by Lean 4. The build passes with
no `sorry` and no `admit` (enforced by CI via
[`scripts/check-no-sorry.sh`](scripts/check-no-sorry.sh)).

Per-opcode *stack-level* specs (`evm_<opcode>_stack_spec`) state, for each
implemented EVM opcode:

> Given a precondition describing the stack pointer `x12` and two `EvmWord`s
> `a`, `b` at offsets `0` and `32` above the stack pointer, running the
> corresponding RISC-V macro program advances the stack pointer by 32 and
> replaces the top-of-stack memory with the result of applying the EVM opcode
> at the `BitVec 256` level.

Proofs compose four per-limb RISC-V instruction specs (each limb is 64 bits)
via `runBlock`, lift to `EvmWord` via `cpsTriple_weaken`, and rely on
separation logic assertions (`Assertion`) defined in `Rv64/SepLogic.lean`.

## 2. Trusted computing base

The kernel-checked claim depends on the following *not* being audited by
the Lean kernel:

1. **Lean 4 itself**, both the elaborator and the kernel, at the toolchain
   pinned in `lean-toolchain`.
2. **Mathlib**, which supplies bitvector lemmas, `ring`/`omega`/`nlinarith`,
   and general-purpose automation. Mathlib is audited by the Lean community
   but its entire surface is part of this project's TCB.
3. **Sail RISC-V model** (imported as a git dependency under
   `Lean_RV64D`). The Sail spec is generated from the official RISC-V Sail
   sources. The README explicitly disclaims: "The instruction semantics are
   vibe-generated and have NOT been validated against the official RISC-V
   specification." A formal equivalence proof between EvmAsm's RV64IM semantics
   and the Sail model lives in `EvmAsm/Rv64/SailEquiv/`; it is still in
   progress and covers only a subset of the instruction set.

Tactics used inside proofs are restricted to those that produce kernel-checked
proof terms:

- **Allowed**: `decide`, `rfl`, `simp`, `omega`, `bv_omega`, `ring`, `nlinarith`,
  `grind`, `ext`, plus project-specific tactics (`xperm`, `xperm_hyp`,
  `runBlock`, `seqFrame`, `liftSpec`, `pcFree`, `bv_addr`, `rv64_addr`,
  `divmod_addr`) which elaborate to standard Lean terms.
- **Forbidden by `CONTRIBUTING.md`**: `native_decide`, `bv_decide`. The former
  reflects through compiled code; the latter dispatches to an external SAT
  solver and reflects the UNSAT certificate. Neither is verified by the
  kernel. A small number of `bv_decide` uses remain inside a restricted set
  of `Evm64/Basic.lean` and `Evm64/CodeRegion.lean` helpers (tracked for
  replacement); these are documented as existing violations of the policy.

## 3. What is *not* claimed

1. **No EVM specification compliance.** The intended EVM behaviour of each
   opcode spec is the developer's informal understanding of the Yellow Paper
   /  `execution-specs/`. No systematic cross-check against the Ethereum
   reference implementation has been performed.
2. **No RISC-V specification compliance.** See §2 item 3.
3. **No ZK proof soundness.** This project produces *program-level*
   correctness proofs for the assembly program. Any ZK proof that a specific
   execution trace follows this program remains a separate concern handled by
   a downstream zkVM.
4. **No hardware soundness.** Memory-access validity predicates
   (`isValidDwordAccess`, `isValidMemRange`) describe the EvmAsm abstract
   machine, not any physical RISC-V implementation. Hardware-specific
   behaviours (MMU faults, misaligned access traps, cache coherence) are out
   of scope.
5. **Completeness is not a claim.** EvmAsm does not claim that every well-formed
   source program has a proof. Some opcodes (SDIV/SMOD/ADDMOD/EXP and most of
   Phases 5–11 in `PLAN.md`) are not yet implemented.

## 4. Reproducing the proofs

```bash
# On the pinned Lean toolchain (see lean-toolchain):
lake build
```

A successful build is the proof artifact. The build:

- Compiles all declarations in `EvmAsm/` through the Lean kernel.
- Fails if any file under `EvmAsm/` contains `sorry` or `admit` outside
  comments (enforced by [`scripts/check-no-sorry.sh`](scripts/check-no-sorry.sh)
  in the `Build` workflow).
- Forbids `native_decide` and `bv_decide` by policy
  (see [`CONTRIBUTING.md`](CONTRIBUTING.md)). Enforcement is by review;
  existing violations are scoped to the helpers documented in §2.

## 5. Reporting a soundness issue

If you discover a missing axiom disclosure, a proof that uses a forbidden
tactic, or a mismatch between a stack-level spec and the EVM Yellow Paper
semantics, please open an issue tagged `soundness` in the GitHub tracker.
