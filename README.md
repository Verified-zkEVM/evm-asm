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
      SeqFrame.lean           --   seqFrame tactic: auto frame+compose cpsTriple specs
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
    Shift/                    --   SHR/SHL/SAR (Program only, specs pending)
    Byte/                     --   BYTE (Program only, specs pending)
    zkvm-standards/           --   Submodule: zkVM RISC-V target standards
EvmAsm.lean                  -- Top-level module hub
EvmAsm/Rv64.lean             -- Rv64 module hub
EvmAsm/Evm64.lean            -- Evm64 module hub
execution-specs/              -- Submodule: Ethereum execution specs (uninitialized)
```

## Lean Toolchain

```
leanprover/lean4:v4.29.0-rc1
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
  4x64-bit limbs, 20 fully-proved opcodes:
  AND, OR, XOR, NOT, ADD, SUB, MUL, DIV, MOD, SIGNEXTEND,
  LT, GT, EQ, ISZERO, SLT, SGT,
  POP, PUSH0, DUP1-16, SWAP1-16
- **Programs without full specs**: SHR, SHL, SAR, BYTE (pending CodeReq
  migration).
- **0 sorry across the entire codebase** (`lake build` clean).
- **TODO**: EXP, ADDMOD, MULMOD, SDIV, SMOD, MLOAD, MSTORE, SHR/SHL/SAR/BYTE
  spec re-creation, interpreter loop, state transition function, connect to
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
    `cpsTriple_frame_left` + `cpsTriple_seq_with_perm`.
- Knuth, D.E. (1997). *The Art of Computer Programming, Volume 2:
  Seminumerical Algorithms* (3rd ed.), §4.3.1 "The Classical Algorithms."
  Addison-Wesley. Algorithm D is used for the DIV/MOD opcodes in `Evm64/DivMod.lean`.
- SP1 zkVM: https://github.com/succinctlabs/sp1
  The `ECALL`-based syscall mechanism follows SP1's conventions.
- zkvm-standards: https://github.com/eth-act/zkvm-standards
  Tentative standards for zkVM RISC-V target, I/O interface, and C-interface accelerators.
- sail-riscv-lean: https://github.com/opencompl/sail-riscv-lean
- RISC-V ISA specification: https://riscv.org/technical/specifications/
