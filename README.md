# evm.asm: A Verified Macro Assembler for building zkEVM in Lean 4 (early experiment)

A prototype implementation of a verified macro assembler targeting the zkEVM,
built on a RISC-V RV64IM backend, inspired by:

> Andrew Kennedy, Nick Benton, Jonas B. Jensen, Pierre-Evariste Dagand.
> **"Coq: The world's best macro assembler?"**
> *Proceedings of the 15th International Symposium on Principles and Practice
> of Declarative Programming (PPDP 2013)*, September 2013, ACM.
> https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/

## Warning: Experimental Prototype Only

**DO NOT USE THIS PROJECT FOR ANYTHING OF VALUE.**

This is an experimental research prototype with significant limitations:

- **No RISC-V spec compliance**: The instruction semantics are vibe-generated and
  have NOT been validated against the official RISC-V specification. There may
  be subtle (or not-so-subtle) deviations from actual RISC-V behavior.
- **No EVM spec compliance**: The specs for examples are also vibe-generated and
  have NOT been validated against the EVM specification.
- **No conformance testing**: No systematic testing has been performed to verify
  that this implementation matches real RISC-V processors or simulators. No testing has been performed against EVM either.
- **Prototype quality**: This code is for educational and research purposes to
  explore verified macro assembly techniques, not for production use.

## Motivation: Eliminating Compiler Trust in zkEVM

The usual way to use zkVMs is to compile high-level programs to RISC-V
assembly, then prove correctness of the execution trace using a zero-knowledge
proof system. The proof covers the *execution trace*, but it cannot cover the
*compiler*. If the compiler is buggy or malicious, the proof might not
match the developer's (or the receiver's) intent, even though the ZK proof is valid, and even if the
source code is correct.

**evm.asm** explores an alternative: write programs directly as RISC-V code,
and *prove* their correctness in Lean 4 before the ZK proof is ever
generated. The goal is that a developer (or a receiver of a ZK proof) never has to trust a compiler
for the guest program.

More specifically, evm.asm aims at building the guest part of the **zkEVM**. Reducing trusted computing base matters for this usage.

A second motivation is that our Hoare triples are *bounded* in steps
(`cpsTripleWithin N base ...`): every spec carries an explicit upper bound `N`
on the number of RISC-V steps the program executes. Two consequences:

1. **zkVM cycle limits.** `N` is a worst-case cycle budget, summable across
   composed macros, that fits a guest program inside a zkVM's per-proof cap
   without running it.
2. **Gas costs.** `N` is a verified per-opcode instruction count, the main
   input to a sound gas-pricing model.

## Key Idea

Lean 4 serves simultaneously as:

1. **An assembler**: Instructions are an inductive type; programs are lists of
   instructions with sequential composition (`;;`).
2. **A macro language**: Lean functions that produce programs act as macros,
   using all of Lean's facilities (recursion, pattern matching, conditionals).
3. **A specification language**: Hoare triples with separation logic assertions
   express correctness properties of EVM opcodes and macro compositions.
4. **A proof assistant**: Lean's kernel verifies that macros meet their
   specifications, with no external oracle required.

## Example: What a Verified EVM Opcode Looks Like

Each EVM opcode is implemented as a sequence of RISC-V instructions operating on
4×64-bit limbs. A **stack-level spec** ties the low-level implementation back to
the 256-bit EVM semantics using `evmWordIs` — an assertion that four consecutive
memory words encode a single `EvmWord` (a `BitVec 256`):

```lean
-- An EvmWord is stored as 4 limbs of 64 bits at consecutive addresses
def evmWordIs (addr : Addr) (v : EvmWord) : Assertion :=
  (addr ↦ₘ v.getLimb 0) ** ((addr + 8) ↦ₘ v.getLimb 1) **
  ((addr + 16) ↦ₘ v.getLimb 2) ** ((addr + 24) ↦ₘ v.getLimb 3)
```

Here is the stack-level spec for the 256-bit AND opcode
(`EvmAsm/Evm64/And/Spec.lean`). It says: starting from two `EvmWord`s `a` and
`b` on the stack, the 17-instruction RISC-V program `evm_and_code` produces
`a &&& b` — with a machine-checked proof:

```lean
/-- Stack-level 256-bit EVM AND: operates on two EvmWords via evmWordIs. -/
theorem evm_and_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code := evm_and_code base
    cpsTripleWithin 17 base (base + 68) code
      (-- precondition: stack pointer, scratch registers, two 256-bit words
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- postcondition: sp advanced, result is a &&& b
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a.getLimb 3 &&& b.getLimb 3)) **
       (.x6 ↦ᵣ b.getLimb 3) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a &&& b))
```

The statement is a bounded Hoare triple (`cpsTripleWithin`) with separation logic assertions.
The precondition describes the machine state before: register `x12` holds the
stack pointer, and two 256-bit words `a`, `b` sit at `sp` and `sp+32`. The
postcondition says that within 17 RISC-V steps, after running 68 bytes of code, the word at
`sp+32` now holds `a &&& b` — the bitwise AND defined by Lean's `BitVec 256`.

The proof composes four per-limb specs (one AND per 64-bit limb) using the
`runBlock` tactic, then lifts to the `evmWordIs` abstraction via
`cpsTripleWithin_weaken`:

```lean
  -- 1. Compose 4 per-limb ANDs + stack pointer adjustment (limb-level proof)
  have L0 := and_limb_spec 0 32 sp a0 b0 v7 v6 base ...
  have L1 := and_limb_spec 8 40 sp a1 b1 ...
  have L2 := and_limb_spec 16 48 sp a2 b2 ...
  have L3 := and_limb_spec 24 56 sp a3 b3 ...
  have LADDI := addi_spec_gen_same_within .x12 sp 32 ...
  runBlock L0 L1 L2 L3 LADDI

  -- 2. Lift to evmWordIs using EvmWord.getLimb_and semantic lemma
  exact cpsTripleWithin_weaken ...
    (fun h hp => by simp only [evmWordIs] at hp; ... ; xperm_hyp hp)
    (fun h hq => by simp only [evmWordIs, EvmWord.getLimb_and]; ... ; xperm_hyp hq)
    h_main
```

Lean's kernel checks every step — from individual instruction semantics to the
final `a &&& b` result. No external solver or SMT oracle required.

## Project Structure

```
EvmAsm/
  Rv64/                       -- RV64IM backend
    Basic.lean                --   Machine state: registers (64-bit), memory, PC
    Instructions.lean         --   RV64IM instruction set and semantics
    Program.lean              --   Programs as instruction lists, sequential composition
    Execution.lean            --   Branch-aware execution, code memory, step/stepN
    SepLogic.lean             --   Separation logic assertions and combinators
    CPSSpec.lean              --   CPS-style Hoare triples, branch specs, structural rules
    ControlFlow.lean          --   if_eq macro, symbolic proofs, pcIndep
    GenericSpecs.lean         --   Generic specs parameterized over instructions
    InstructionSpecs.lean     --   Per-instruction CPS specs
    SyscallSpecs.lean         --   Syscall specs: HALT, WRITE, HINT_READ
    Tactics/
      PerfTrace.lean          --   Performance tracing infrastructure
      XPerm.lean              --   xperm tactic: AC-permutation of sepConj chains
      XSimp.lean              --   xperm_hyp/xsimp tactics: assertion implication
      XCancel.lean            --   xcancel tactic: cancellation with frame extraction
      SeqFrame.lean           --   seqFrame tactic: auto frame+compose bounded CPS specs
      LiftSpec.lean           --   liftSpec tactic: lift instruction specs
      RunBlock.lean           --   runBlock tactic: block execution automation
      SpecDb.lean             --   @[spec_gen] attribute and spec database
  Evm64/                      -- EVM opcodes on RV64IM (4x64-bit limbs)
    Basic.lean                --   EvmWord (BitVec 256), getLimb64, fromLimbs64
    Stack.lean                --   evmWordIs, evmStackIs, pcFree lemmas
    EvmWordArith.lean         --   Math correctness lemmas (carry chains, etc.)
    Compare/
      LimbSpec.lean           --   Shared comparison per-limb specs (lt, beq, slt_msb)
    Add/                      --   256-bit ADD
      Program.lean            --     RV64 program definition
      LimbSpec.lean           --     Per-limb specs (add_limb0, add_limb_carry)
      Spec.lean               --     Full composition + stack-level spec
    Sub/                      --   256-bit SUB (same layout as Add/)
    And/                      --   256-bit AND (Program + LimbSpec + Spec)
    Or/                       --   256-bit OR
    Xor/                      --   256-bit XOR
    Not/                      --   256-bit NOT
    Lt/                       --   256-bit LT (Program + Spec, uses Compare/LimbSpec)
    Gt/                       --   256-bit GT
    Eq/                       --   256-bit EQ (Program + LimbSpec + Spec)
    IsZero/                   --   256-bit ISZERO (Program + LimbSpec + Spec)
    Slt/                      --   256-bit SLT signed (Program + Spec, uses Compare/LimbSpec)
    Sgt/                      --   256-bit SGT signed
    Pop/                      --   POP (Program + Spec)
    Push0/                    --   PUSH0 (Program + Spec)
    Dup/                      --   DUP1-16 (Program + Spec)
    Swap/                     --   SWAP1-16 (Program + Spec)
    Multiply/                 --   MUL (Program + LimbSpec, schoolbook 4x4 limb)
    DivMod/                   --   DIV/MOD (Program + LimbSpec + Compose, Knuth Algorithm D)
    SignExtend/               --   SIGNEXTEND (Program + LimbSpec + Compose + Spec)
    Shift/                    --   SHR/SHL/SAR (Program + LimbSpec + ShlSpec + SarSpec + Compose + ShlCompose + SarCompose + Semantic + ShlSemantic + SarSemantic)
    Byte/                     --   BYTE (Program + LimbSpec + Spec)
    zkvm-standards/           --   Submodule: zkVM RISC-V target standards
EvmAsm.lean                  -- Top-level module hub
EvmAsm/Rv64.lean             -- Rv64 module hub
EvmAsm/Evm64.lean            -- Evm64 module hub
execution-specs/              -- Submodule: Ethereum execution specs
```

## Building

```bash
# Install elan (Lean version manager) if not already installed
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# download Mathlib cache (optional, recommended)
lake exec cache get

# Build the project
lake build
```

## Status

This is a **prototype** demonstrating the approach. Current state:

- **Infrastructure**: RV64IM backend with separation logic, CPS-style Hoare
  triples, and automated tactics (`xperm`, `xcancel`, `seqFrame`, `liftSpec`,
  `runBlock` with `@[spec_gen]` auto-resolution).
- **Evm64 (0 sorry)** — targets `riscv64im_zicclsm-unknown-none-elf`,
  4x64-bit limbs, 24 fully-proved opcodes:
  AND, OR, XOR, NOT, ADD, SUB, MUL, DIV, MOD, SIGNEXTEND,
  SHR, SHL, SAR, BYTE,
  LT, GT, EQ, ISZERO, SLT, SGT,
  POP, PUSH0, DUP1-16, SWAP1-16
- **0 sorry across the entire codebase** (`lake build` clean).
- **TODO**: EXP, ADDMOD, MULMOD, SDIV, SMOD,
  MLOAD, MSTORE, interpreter loop, state transition function, connect to
  sail-riscv-lean for RISC-V spec compliance, connect to EVM specs in Lean,
  testing.

## References

- Kennedy, A., Benton, N., Jensen, J.B., Dagand, P.-E. (2013).
  "Coq: The world's best macro assembler?" PPDP 2013.
  https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/
- **SPlean** (Separation Logic Proofs in Lean), Verse Lab.
  https://github.com/verse-lab/splean
  The `xperm` / `xperm_hyp` / `xsimp` tactics in `Tactics/` are inspired by
  SPlean's `xsimpl` tactic.
- Charguéraud, A. (2020). "Separation Logic for Sequential Programs
  (Functional Pearl)." *Proc. ACM Program. Lang.* 4, ICFP, Article 116.
  https://doi.org/10.1145/3408998
- **bedrock2**: https://github.com/mit-plv/bedrock2
  The frame automation tactics (`xcancel`, `seqFrame`) in `Tactics/XCancel.lean`
  and `Tactics/SeqFrame.lean` are inspired by bedrock2's separation logic
  automation. Specifically:
  - The `wcancel` tactic in `bedrock2/src/bedrock2/SepLogAddrArith.v` (lines 127-134)
    inspired the cancellation approach: matching atoms by tag+address, computing
    the frame as the residual of unmatched hypothesis atoms.
  - The frame rule infrastructure in `bedrock2/src/bedrock2/FrameRule.v` (lines 75-175)
    inspired the automatic frame extraction pattern where specs include a universal
    frame parameter and tactics instantiate it during composition.
  - The instruction specs with explicit frame in `compiler/src/compiler/GoFlatToRiscv.v`
    (lines 439-546) informed the design of composing instruction specs with
    `cpsTriple_frameR` + `cpsTriple_seq_perm_same_cr`.
- Knuth, D.E. (1997). *The Art of Computer Programming, Volume 2:
  Seminumerical Algorithms* (3rd ed.), §4.3.1 "The Classical Algorithms."
  Addison-Wesley. Algorithm D is used for the DIV/MOD opcodes in `Evm64/DivMod.lean`.
- SP1 zkVM: https://github.com/succinctlabs/sp1
  The `ECALL`-based syscall mechanism follows SP1's conventions.
- zkvm-standards: https://github.com/eth-act/zkvm-standards
  Tentative standards for zkVM RISC-V target, I/O interface, and C-interface accelerators.
- sail-riscv-lean: https://github.com/opencompl/sail-riscv-lean
- RISC-V ISA specification: https://riscv.org/technical/specifications/
