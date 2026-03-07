# evm.asm: A Verified Macro Assembler for building zkEVM in Lean 4 (early experiment)

A prototype implementation of a verified macro assembler targeting the zkEVM,
built on a RISC-V backend (RV32IM), inspired by:

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
  Basic.lean            -- Machine state: registers, memory, PC
  Instructions.lean     -- RV32IM instruction set and semantics (incl. ECALL)
  Program.lean          -- Programs as instruction lists, sequential composition
  Execution.lean        -- Branch-aware execution, code memory, step/stepN
  SepLogic.lean         -- Separation logic assertions and combinators
  CPSSpec.lean          -- CPS-style Hoare triples, branch specs, structural rules
  ControlFlow.lean      -- if_eq macro, symbolic proofs, pcIndep
  Tactics/
    XPerm.lean          -- xperm tactic: AC-permutation of sepConj chains
    XSimp.lean          -- xperm_hyp/xsimp tactics: assertion implication
    XCancel.lean        -- xcancel tactic: cancellation with frame extraction
    SeqFrame.lean       -- seqFrame tactic: auto frame+compose cpsTriple specs
  InstructionSpecs.lean -- Per-instruction CPS specs (ADD, SUB, ADDI, LW, SW, BEQ, ...)
  SyscallSpecs.lean     -- Syscall specs: HALT, WRITE, HINT_READ, memory buffers
  MulMacro.lean         -- The add_mulc macro with correctness proofs
  Evm/
    Basic.lean          -- EvmWord (BitVec 256), getLimb, fromLimbs, round-trip lemmas
    Stack.lean          -- evmWordIs, evmStackIs, pcFree lemmas
    StackOps.lean       -- EVM POP/PUSH0/DUP1/SWAP1 programs + specs;
                        --   generic evm_dup n / evm_swap n (1 ≤ n ≤ 16)
    Bitwise.lean        -- EVM AND/OR/XOR/NOT programs + per-limb specs
    And.lean            -- Full 256-bit EVM AND spec (composed from per-limb)
    Or.lean             -- Full 256-bit EVM OR spec
    Xor.lean            -- Full 256-bit EVM XOR spec
    Not.lean            -- Full 256-bit EVM NOT spec
    Arithmetic.lean     -- EVM ADD/SUB programs + per-limb specs
    ArithmeticSpec.lean -- Full 256-bit EVM ADD/SUB specs
    Comparison.lean     -- EVM ISZERO/LT/GT/EQ programs + per-limb specs
    ComparisonSpec.lean -- Full 256-bit EVM LT/GT/EQ/ISZERO specs
  Examples.lean         -- Module hub importing all examples
  Examples/
    Swap.lean           -- Register swap macro
    Zero.lean           -- Zero-register macro
    Multiply.lean       -- Multiply-by-constant examples
    LoadModifyStore.lean -- Load-modify-store pattern
    Combining.lean      -- Combining multiple macros
    Halting.lean        -- HALT/ECALL termination examples
    Commit.lean         -- COMMIT syscall example
    Write.lean          -- WRITE syscall example
    FullPipeline.lean   -- End-to-end pipeline example
    HelloWorld.lean     -- Hello world program
    HelloWorldSpec.lean -- Hello world correctness proof
    Echo.lean           -- Echo program with CPS spec
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

- **Working**: Machine model, instruction semantics, program composition,
  separation logic framework, Hoare triple infrastructure, concrete
  correctness proofs via `native_decide`.
- **Proved**:
  - Separation logic properties (commutativity, associativity, unit)
  - Hoare triple structural rules (skip, sequence, consequence, frame, existential)
  - Register file lemmas, swap correctness, `add_mulc_correct`
  - CPS-style branch specs (`cpsBranch`, `cpsNBranch`), `if_eq` control flow
  - ECALL/HALT termination (SP1 convention)
  - EVM 256-bit bitwise ops: AND, OR, XOR, NOT (full specs)
  - EVM 256-bit arithmetic: ADD, SUB (full specs)
  - EVM 256-bit comparisons: LT, GT, EQ, ISZERO (full specs)
  - EVM stack ops: POP, PUSH0, DUP1, SWAP1 (concrete), DUPn/SWAPn for 1 ≤ n ≤ 16 (generic)
- **TODO**: More control flow macros (loops, function calls), MLOAD/MSTORE,
  additional arithmetic (MUL, DIV, MOD), preprocessed, connect to sail-riscv-lean for making sure this project is really about RISC-V, connect to EVM specs in Lean,
  transaction and block processing, Ethereum state transition, I guess I forgot something, TEST! TEST! TEST!

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
- SP1 zkVM: https://github.com/succinctlabs/sp1
  The `ECALL`-based syscall mechanism follows SP1's conventions.
- sail-riscv-lean: https://github.com/opencompl/sail-riscv-lean
- RISC-V ISA specification: https://riscv.org/technical/specifications/
