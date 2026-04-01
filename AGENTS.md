# AI Agent Guide for EvmAsm

This document provides guidance for AI agents working on the EvmAsm project.

## Project Overview

EvmAsm is a verified macro assembler for RISC-V in Lean 4, inspired by "Coq: The world's best macro assembler?" (Kennedy et al., PPDP 2013). The project demonstrates using Lean 4 as both a macro language and verification framework for assembly code.

## Build System

- **Build tool**: Lake (Lean 4's build system)
- **Toolchain**: Lean 4.28.0-nightly-2026-01-22 (specified in `lean-toolchain`)
- **Build command**: `lake build`
- **Clean build**: `lake clean && lake build`

### Important Lake Configuration Notes

- The `lakefile.toml` uses Lake 5.0 format (root-level package fields, no `[package]` section)
- `defaultTargets = ["EvmAsm"]` is required for `lake build` to work
- The library name is `EvmAsm` and sources are in `EvmAsm/` directory

## Project Structure

```
EvmAsm/
  Rv64/                -- RV64IM machine model + infrastructure
    Basic.lean         -- Machine state: registers, memory, PC
    Instructions.lean  -- RV64IM instruction semantics (incl. ECALL)
    Program.lean       -- Programs as instruction lists, sequential composition
    Execution.lean     -- Step execution, code memory, ECALL dispatch
    SepLogic.lean      -- Separation logic assertions and combinators
    CPSSpec.lean       -- CPS-style Hoare triples, branch specs, structural rules
    GenericSpecs.lean  -- Generic instruction spec templates
    InstructionSpecs.lean -- Concrete instruction specs
    SyscallSpecs.lean  -- Spec database (@[spec_gen_rv64])
    ControlFlow.lean   -- if_eq macro, symbolic proofs
    ByteOps.lean       -- Byte-level: extractByte algebra, LBU/SB specs
    Tactics/           -- Automation: xperm, runBlock, liftSpec, etc.
  Evm64/               -- 256-bit EVM opcodes on RV64IM (4×64-bit limbs)
    Basic.lean         -- EvmWord (BitVec 256), getLimb/fromLimbs
    Stack.lean         -- evmWordIs, evmStackIs assertions
    Add/, Sub/, ...    -- Individual opcode implementations (30+ files)
  EL/                  -- Pure Ethereum Execution Layer specs
    RLP/               -- RLP encoding/decoding (no RISC-V dependency)
      Basic.lean       -- RLPItem type, encode
      Decode.lean      -- decode with canonical enforcement
      Properties.lean  -- Round-trip proofs (native_decide)
EvmAsm.lean            -- Root module: imports Rv64, Evm64, EL
```

## Key Lean 4 API Compatibility Notes

When working with this codebase, be aware of these Lean 4 nightly API changes:

1. **Logic lemmas**: Use lowercase names (`and_assoc`, `and_comm` instead of `And.assoc`, `And.comm`)
2. **Doc comments**: Cannot place `/-- ... -/` doc comments immediately before `#eval` commands (use regular `--` comments)
3. **Proof tactics**: `simp` may need explicit lemma lists or `rw` for manual rewriting
4. **Namespace**: Most theorems are in `namespace MachineState`, so use full names like `MachineState.getReg_setPC`

## Verification Workflow

When adding or modifying proofs:

1. **Build first**: Always run `lake build` to see current errors
2. **Use MCP tools**: The lean-lsp MCP server provides:
   - `lean_goal`: Check proof state at a position
   - `lean_diagnostic_messages`: Get compiler errors
   - `lean_hover_info`: Get type information
   - `lean_completions`: Get IDE completions
   - `lean_local_search`: Search for declarations locally
   - `lean_leansearch`: Natural language search in mathlib
   - `lean_loogle`: Type-based search in mathlib
3. **Test concretely**: Verify specific cases with `native_decide` before generalizing
4. **Incremental development**: Prove helper lemmas before the main theorem

## Critical Rules

- **Do NOT add `set_option maxHeartbeats` to any file** unless you are in `Evm64/Shift/` composition files (Compose, ShlCompose, SarCompose) for body/path composition proofs. Heartbeat limits are configured globally in `lakefile.toml`.
- **Do NOT add `set_option maxRecDepth` to any file.** Recursion depth is configured globally in `lakefile.toml`.
- If a proof times out or hits recursion limits, restructure the proof (e.g., split into smaller lemmas, use intermediate `have` bindings) rather than increasing limits.
- **Exception for Shift composition files**: `set_option maxHeartbeats` up to 6400000 is acceptable for body/path composition proofs (Section 4+) which are bottlenecked by `xperm_hyp` permutation on large atom chains. Subsumption lemmas (Section 2) should NOT need heartbeat overrides — they use structural `unionAll` reasoning.

## Common Pitfalls

1. **Notation issues**: Custom notations (like `↦ᵣ ?`) may not parse correctly; use functions directly
2. **Simp lemmas**: Mark key lemmas with `@[simp]` for automatic application
3. **List operations**: Be careful with `execProgram` and list append - may need explicit `execProgram_append`
4. **Register inequality**: Use `decide` tactic for concrete register inequality proofs
5. **Program type**: `Program = List Instr` is a `def`, not `abbrev` — use `simp only [..., Program]` to unfold before `List.length_append` etc.

## Testing

All concrete examples should pass with no sorries:

```bash
lake build  # Should succeed with 0 errors and 0 sorries
```

The project includes concrete test cases using `native_decide`:
- Multiply by constants: 0, 1, 3, 6, 10, 255
- Swap macro correctness
- Zero and triple macros
- ECALL/halt termination examples
- COMMIT-then-halt examples

## Git Workflow

- Main branch: `main`
- Create feature branches for new work
- Use meaningful commit messages with Co-Authored-By line for AI contributions

## References

- **Original paper**: Kennedy et al., "Coq: The world's best macro assembler?" PPDP 2013
  https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/
- **SP1 zkVM**: https://github.com/succinctlabs/sp1
- **RISC-V ISA**: https://riscv.org/technical/specifications/
- **sail-riscv-lean**: https://github.com/opencompl/sail-riscv-lean (same toolchain)
- **Lean 4 docs**: https://lean-lang.org/documentation/

## Separation Conjunction Permutation Tactic

The `sep_perm` tactic (defined in `SepLogic.lean`) closes goals that require rearranging `sepConj` (`**`) chains. It works by AC-normalizing both the hypothesis and goal using `simp` with three equality lemmas:

- `sepConj_assoc'` : `((P ** Q) ** R) = (P ** (Q ** R))`
- `sepConj_comm'` : `(P ** Q) = (Q ** P)`
- `sepConj_left_comm'` : `(P ** (Q ** R)) = (Q ** (P ** R))`

**Usage**: Given a hypothesis `h : (A ** B ** C) s` and goal `⊢ (C ** A ** B) s`:
```lean
sep_perm h
```

This handles arbitrary permutations of any number of assertions in a `sepConj` chain.

Additional equality lemmas for `empAssertion` elimination:
- `sepConj_emp_right'` : `(P ** empAssertion) = P`
- `sepConj_emp_left'` : `(empAssertion ** P) = P`

When rearranging involves `memBufferIs` (which unfolds to `... ** empAssertion`), combine all rules in one `simp`:
```lean
simp only [memBufferIs, addr_100_plus_4, addr_104_plus_4,
  sepConj_emp_right', sepConj_emp_left',
  sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hab ⊢
exact hab
```

## Calling Convention (LP64)

New functions **must** follow the LP64 calling convention defined in
`Evm64/CallingConvention.lean`. This applies to opcode handlers, the
interpreter dispatch loop, RLP routines, and any new subroutines.

**Register roles** (per zkvm-standards):

| Register | ABI | Role | Saved by |
|----------|-----|------|----------|
| x1 | ra | Return address | Caller |
| x2 | sp | Call stack (grows down) | **Callee** |
| x5-x7 | t0-t2 | Temporaries | Caller |
| x10-x11 | a0-a1 | Args / return values | Caller |
| x12 | a2 | EVM stack pointer | Caller |

**Reusable snippets** (use these, don't hand-roll):

| Snippet | Purpose |
|---------|---------|
| `cc_ret` | Return: `JALR x0, x1, 0` |
| `cc_prologue` | Non-leaf prologue: `ADDI sp, sp, -16 ;; SD sp, ra, 8` |
| `cc_epilogue` | Non-leaf epilogue: `LD ra, sp, 8 ;; ADDI sp, sp, 16 ;; JALR x0, ra, 0` |

**Proved specs** — use these instead of reproving from scratch:

- `callNear_spec` / `callFar_spec` — JAL/JALR call saves return address
- `ret_spec` / `ret_spec'` — JALR x0 x1 0 returns to caller
- `cc_prologue_spec` — prologue block spec (2 instructions)
- `cc_epilogue_spec` — epilogue block spec (3 instructions)
- `callNear_function_spec` — compose JAL + function callable spec → round-trip
- `nonleaf_function_spec` — compose prologue + body + epilogue → full function

**Pattern for a new leaf function:**
```lean
def my_func : Program := body ;; cc_ret
```

**Pattern for a new non-leaf function:**
```lean
def my_func : Program := cc_prologue ;; body ;; cc_epilogue
```

The existing DivMod subroutine uses an older ad-hoc convention (x2 as return
address). New code should **not** copy that pattern — use the LP64 convention.

## Three-Level Opcode Proof Architecture

Each EVM opcode follows a three-level proof hierarchy:

1. **Limb-level specs** (`LimbSpec.lean`, `ShlSpec.lean`, `SarSpec.lean`): Per-instruction specs composed with `runBlock`. These operate on raw 64-bit memory cells (`↦ₘ`).
2. **Composition** (`Compose.lean`, `ShlCompose.lean`, `SarCompose.lean`): Hierarchical composition of limb specs into full-program theorems. Includes:
   - `xyzCode` definition (`CodeReq.unionAll` of per-phase `CodeReq.ofProg` blocks)
   - Subsumption lemmas (structural `skipBlock` + `union_mono_left`, no `native_decide` on full programs)
   - Address normalization lemmas (`bv_omega` proofs)
   - Path composition (zero-path/sign-fill for shift >= 256, body-path for shift < 256)
   - Bridge lemmas connecting per-limb results to `getLimb (result) i`
3. **Semantic** (`Semantic.lean`, `ShlSemantic.lean`, `SarSemantic.lean`): Stack-level `evmWordIs` spec. Lifts composition to `EvmWord` assertions using `cpsTriple_consequence` + `xperm_hyp`.

### Composition File Pattern (for shift opcodes)

Each shift Compose file (~1000-1200 lines) follows this structure:
1. **Section 1**: `xyzCode` definition as `CodeReq.unionAll` of per-phase `ofProg` blocks + length lemmas + `skipBlock` macro + helpers (`singleton_sub_ofProg`, `CodeReq_union_sub_both`, `regIs_to_regOwn`)
2. **Section 2**: Subsumption lemmas — structural reasoning via `skipBlock` + `union_mono_left` (following the DivMod pattern). For union-chain `_code` definitions (Phase A, Phase C, sign-fill), split into bridge sub-lemma (`chain_code ⊆ ofProg small_block`) + structural sub-lemma (`ofProg small_block ⊆ xyzCode`)
3. **Section 3**: Address normalization — `bv_omega` proofs for all offset arithmetic
4. **Section 4**: Zero-path or sign-fill composition — instruction-by-instruction Phase A chain + branch elimination + path composition
5. **Section 5**: Phase C dispatch — `cpsNBranch` with cascade steps
6. **Section 6**: Bridge lemmas — connect limb formulas to `getLimb (operation value n)`
7. **Section 7**: Body path composition — Phase A(ntaken) + B + C + body_L + exit with bridge application

### Bridge Lemma Pattern

Bridge lemmas in `Evm64/Basic.lean` connect per-limb arithmetic to 256-bit operations:
- **SHR**: `getLimb_ushiftRight` (single lemma covering all cases via `getLimbN`)
- **SHL**: `getLimb_shiftLeft`, `getLimb_shiftLeft_eq_div`, `getLimb_shiftLeft_low`
- **SAR**: `getLimb_sshiftRight_eq_ushiftRight` (merge case, delegates to ushiftRight), `getLimb_sshiftRight_last` (SRA on MSB limb), `getLimb_sshiftRight_sign'` (sign extension)

### Key Learnings for Shift Composition

- **SAR sign-fill path** uses `sar_sign_fill_path_spec` which takes `.x5` and `.x10` in its precondition (unlike `shr_zero_path_spec` which only takes `.x12`). This means the frame for sign-fill is smaller than for zero-path.
- **Address normalization direction matters**: The sign-fill path spec uses `sp + 40` directly, not `(sp + 32) + 8`. Don't apply `ha40 : sp + 40 = (sp + 32) + 8` in permutation callbacks if the assertions already use `sp + 40`. Use `xperm_hyp` directly — it handles both forms.
- **Subsumption via unionAll (preferred pattern)**: Define `xyzCode` as `CodeReq.unionAll` of per-phase `ofProg` blocks (not a flat `ofProg base evm_xyz`). Then subsumption is structural: `skipBlock` skips disjoint blocks, `union_mono_left` matches the target block. For union-chain `_code` definitions, add a bridge sub-lemma using `singleton_sub_ofProg`/`ofProg_mono_sub` on the **small** sub-program (5-25 elements). Never use `native_decide` on the full 90-95 instruction program — that's the old pattern and requires 4-8M heartbeats. See `DivMod/Compose.lean` for the canonical reference.
- **`local macro` for file-scoped tactics**: When defining `skipBlock` (or similar) in multiple Compose files, use `local macro` not `macro`. Without `local`, importing multiple files causes "environment already contains" errors.
- **`sshiftRight (sshiftRight x n) 63 = sshiftRight x 63`**: This identity (sign extension is idempotent under further shifting by 63) requires a case split on `63 + j < 64` and `BitVec.msb_sshiftRight`.
- **Phase C for SAR**: Same structure as SHR/SHL Phase C but with different BEQ/cascade offsets. The `shr_cascade_step_code`/`shr_cascade_step_spec` are parameterized and reusable. Only the initial BEQ offset and the `phase_c_code` definition need SAR-specific versions.
- **`native_decide` cannot handle free variables**: For `getLimb_fromLimbs_const`, use `match i with | ⟨0, _⟩ => ...; bv_decide | ⟨1, _⟩ => ...` instead of `fin_cases i <;> bv_decide`.
- **`ext j` for BitVec**: After `ext j`, the variable `j` is a `Nat` and `rename_i hj` gives the bound `hj : j < w`. Use `BitVec.getElem_extractLsb'`, `BitVec.getLsbD_sshiftRight`, `BitVec.getElem_sshiftRight` for simplification.
- **`dif_pos`/`dif_neg` for dependent if**: When `simp` leaves a `dite` (dependent if-then-else), use `rw [dif_pos h]` or `rw [dif_neg h]` to eliminate it, not `simp only [dite_true]`.

## Roadmap (PLAN.md)

The project roadmap is maintained in `PLAN.md`. See `CLAUDE.md` for the
maintenance protocol (when and how to update it).
