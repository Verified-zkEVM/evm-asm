# evm.asm: A Verified Macro Assembler for building zkEVM in Lean 4 (early experiment)

A prototype implementation of a verified macro assembler targeting the zkEVM,
built on RISC-V backends (RV64IM primary, RV32IM secondary), inspired by:

> Andrew Kennedy, Nick Benton, Jonas B. Jensen, Pierre-Evariste Dagand.
> **"Coq: The world's best macro assembler?"**
> *Proceedings of the 15th International Symposium on Principles and Practice
> of Declarative Programming (PPDP 2013)*, September 2013, ACM.
> https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/

## ⚠️ Warning: Experimental Prototype Only

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

## The `add_mulc` Macro

The simplest example is `add_mulc` (inspired by "Coq: The world's best macro assembler?" cited above), a macro that multiplies a register by a
compile-time constant using the shift-and-add algorithm:

```lean
def add_mulc (nbits : Nat) (rd rs : Reg) (m : Nat) : Program :=
  match nbits with
  | 0 => prog_skip
  | nbits' + 1 =>
    if m % 2 == 1 then
      ADD rd rd rs ;;
      SLLI rs rs 1 ;;
      add_mulc nbits' rd rs (m / 2)
    else
      SLLI rs rs 1 ;;
      add_mulc nbits' rd rs (m / 2)
```

The specification uses separating conjunction:

```lean
theorem add_mulc_spec (m nbits : Nat) (hm : m < 2 ^ nbits)
    (rd rs : Reg) (hrd : rd ≠ .x0) (hrs : rs ≠ .x0)
    (v w : Word) :
    ⦃(rd ↦ᵣ v) ** (rs ↦ᵣ w)⦄
    add_mulc nbits rd rs m
    ⦃fun s => s.getReg rd = v + w * BitVec.ofNat 32 m⦄
```

## Project Structure

```
EvmAsm/
  Rv64/                       -- RV64IM backend (primary)
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
      XPerm.lean              --   xperm tactic: AC-permutation of sepConj chains
      XSimp.lean              --   xperm_hyp/xsimp tactics: assertion implication
      XCancel.lean            --   xcancel tactic: cancellation with frame extraction
      SeqFrame.lean           --   seqFrame tactic: auto frame+compose cpsTriple specs
      LiftSpec.lean           --   liftSpec tactic: lift instruction specs
      RunBlock.lean           --   runBlock tactic: block execution automation
      SpecDb.lean             --   Spec database for tactic lookup
  Rv32/                       -- RV32IM backend (secondary, parallel structure)
    Basic.lean ... Tactics/   --   Same modules as Rv64, 32-bit word size
    MulMacro.lean             --   The add_mulc macro with correctness proofs
  Evm64/                      -- EVM opcodes on RV64IM (primary, 4×64-bit limbs, 18 files)
    Basic.lean                --   EvmWord (BitVec 256), getLimb64, fromLimbs64
    Stack.lean                --   evmWordIs, evmStackIs, pcFree lemmas
    StackOps.lean             --   POP, PUSH0, DUP1, SWAP1, generic DUPn/SWAPn
    Bitwise.lean              --   AND/OR/XOR/NOT programs + per-limb specs
    And.lean                  --   Full 256-bit AND spec
    Or.lean                   --   Full 256-bit OR spec
    Xor.lean                  --   Full 256-bit XOR spec
    Not.lean                  --   Full 256-bit NOT spec
    Arithmetic.lean           --   ADD/SUB programs + per-limb specs
    Add.lean                  --   Full 256-bit ADD spec
    Sub.lean                  --   Full 256-bit SUB spec
    Comparison.lean           --   LT/GT/EQ/ISZERO programs + per-limb specs
    Lt.lean                   --   Full 256-bit LT spec
    Gt.lean                   --   Full 256-bit GT spec
    Eq.lean                   --   Full 256-bit EQ spec
    IsZero.lean               --   Full 256-bit ISZERO spec
    Shift.lean                --   SHR program + per-limb specs
    ShiftSpec.lean            --   Full 256-bit SHR spec
    zkvm-standards/           --   Submodule: zkVM RISC-V target standards
  Evm32/                      -- EVM opcodes on RV32IM (secondary, 8×32-bit limbs, 15 files)
    Basic.lean ... StackOps.lean  -- Same opcodes as Evm64, 32-bit limbs
    Shift.lean                --   SHR program + per-limb specs
    ShiftSpec.lean            --   Full 256-bit SHR spec
    ShiftComposition.lean     --   SHR shift composition (1 sorry)
  Examples/                   -- 12 example files
    Swap.lean                 --   Register swap macro
    Zero.lean                 --   Zero-register macro
    Multiply.lean             --   Multiply-by-constant examples
    LoadModifyStore.lean      --   Load-modify-store pattern
    Combining.lean            --   Combining multiple macros
    Halting.lean              --   HALT/ECALL termination examples
    Commit.lean               --   COMMIT syscall example
    Write.lean                --   WRITE syscall example
    FullPipeline.lean         --   End-to-end pipeline example
    HelloWorld.lean           --   Hello world program
    HelloWorldSpec.lean       --   Hello world correctness proof
    Echo.lean                 --   Echo program with CPS spec
EvmAsm.lean                  -- Top-level module hub
EvmAsm/Rv64.lean             -- Rv64 module hub
EvmAsm/Rv32.lean             -- Rv32 module hub
EvmAsm/Examples.lean         -- Examples module hub
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

- **Infrastructure**: Two complete RISC-V backends (RV64IM, RV32IM) with
  separation logic, CPS-style Hoare triples, and automated tactics
  (`xperm`, `xcancel`, `seqFrame`, `liftSpec`, `runBlock`).
- **Evm64 (primary, 0 sorry)** — targets `riscv64im_zicclsm-unknown-none-elf`,
  4×64-bit limbs, 15 fully-proved opcodes:
  AND, OR, XOR, NOT, ADD, SUB, LT, GT, EQ, ISZERO, SHR,
  POP, PUSH0, DUP1, SWAP1 (+ generic DUPn/SWAPn for 1 ≤ n ≤ 16)
- **Evm32 (secondary, 1 sorry)** — 8×32-bit limbs, same 15 opcodes;
  one sorry remains in `ShiftComposition.lean`.
- **Proved (examples)**: `add_mulc`, register swap, hello world, echo,
  HALT/COMMIT termination, load-modify-store, full pipeline.
- **TODO**: More opcodes (MUL, DIV, MOD, SHL, SAR, MLOAD, MSTORE),
  interpreter loop, state transition function, connect to sail-riscv-lean
  for RISC-V spec compliance, connect to EVM specs in Lean, testing.

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
