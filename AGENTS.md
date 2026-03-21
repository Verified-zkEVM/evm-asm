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
  Basic.lean         -- Machine state: registers, memory, PC
  Instructions.lean  -- RV32I instruction subset and semantics (incl. ECALL)
  Program.lean       -- Programs as instruction lists, sequential composition, HALT/COMMIT macros
  Execution.lean     -- Branch-aware execution, code memory, step/stepN, ECALL dispatch
  SepLogic.lean      -- Separation logic assertions and combinators
  Spec.lean          -- Hoare triples, frame rule, structural rules
  CPSSpec.lean       -- CPS-style Hoare triples, branch specs, structural rules
  ControlFlow.lean   -- if_eq macro, symbolic proofs, pcIndep
  MulMacro.lean      -- The add_mulc macro with correctness proofs
  Examples.lean      -- Swap, zero, triple, halt, commit, and other macro examples
EvmAsm.lean   -- Root module importing all submodules
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

- **Do NOT add `set_option maxHeartbeats` to any file** unless you are in `Evm64/Shift/` composition files (Compose, ShlCompose, SarCompose) or subsumption lemmas where `native_decide` on large programs (90-95 instructions) requires it. Heartbeat limits are configured globally in `lakefile.toml`.
- **Do NOT add `set_option maxRecDepth` to any file.** Recursion depth is configured globally in `lakefile.toml`.
- If a proof times out or hits recursion limits, restructure the proof (e.g., split into smaller lemmas, use intermediate `have` bindings) rather than increasing limits.
- **Exception for Shift composition files**: `set_option maxHeartbeats 4000000` (or up to 8000000) is acceptable for subsumption lemmas using `native_decide` on 90-95 instruction programs, and `set_option maxHeartbeats 6400000` for body composition proofs.

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

## Three-Level Opcode Proof Architecture

Each EVM opcode follows a three-level proof hierarchy:

1. **Limb-level specs** (`LimbSpec.lean`, `ShlSpec.lean`, `SarSpec.lean`): Per-instruction specs composed with `runBlock`. These operate on raw 64-bit memory cells (`↦ₘ`).
2. **Composition** (`Compose.lean`, `ShlCompose.lean`, `SarCompose.lean`): Hierarchical composition of limb specs into full-program theorems. Includes:
   - `xyzCode` definition (`CodeReq.ofProg base evm_xyz`)
   - Subsumption lemmas (prove each sub-spec's code is contained in the full program)
   - Address normalization lemmas (`bv_omega` proofs)
   - Path composition (zero-path/sign-fill for shift >= 256, body-path for shift < 256)
   - Bridge lemmas connecting per-limb results to `getLimb (result) i`
3. **Semantic** (`Semantic.lean`, `ShlSemantic.lean`, `SarSemantic.lean`): Stack-level `evmWordIs` spec. Lifts composition to `EvmWord` assertions using `cpsTriple_consequence` + `xperm_hyp`.

### Composition File Pattern (for shift opcodes)

Each shift Compose file (~1000-1200 lines) follows this structure:
1. **Section 1**: `xyzCode` definition + helpers (`singleton_sub_xyzCode`, `CodeReq_union_sub_both`, `regIs_to_regOwn`)
2. **Section 2**: Subsumption lemmas — prove each phase/body/path code is subsumed by the full program using `CodeReq.ofProg_mono_sub` or `singleton_sub_xyzCode`
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
- **Subsumption for large programs (90-95 instrs)**: Individual `singleton_sub_xyzCode` calls with `native_decide` can timeout. For 7+ instruction blocks, use `CodeReq.ofProg_mono_sub` which batches the proof. For union chains, use `CodeReq_union_sub_both` to decompose.
- **`sshiftRight (sshiftRight x n) 63 = sshiftRight x 63`**: This identity (sign extension is idempotent under further shifting by 63) requires a case split on `63 + j < 64` and `BitVec.msb_sshiftRight`.
- **Phase C for SAR**: Same structure as SHR/SHL Phase C but with different BEQ/cascade offsets. The `shr_cascade_step_code`/`shr_cascade_step_spec` are parameterized and reusable. Only the initial BEQ offset and the `phase_c_code` definition need SAR-specific versions.
- **`native_decide` cannot handle free variables**: For `getLimb_fromLimbs_const`, use `match i with | ⟨0, _⟩ => ...; bv_decide | ⟨1, _⟩ => ...` instead of `fin_cases i <;> bv_decide`.
- **`ext j` for BitVec**: After `ext j`, the variable `j` is a `Nat` and `rename_i hj` gives the bound `hj : j < w`. Use `BitVec.getElem_extractLsb'`, `BitVec.getLsbD_sshiftRight`, `BitVec.getElem_sshiftRight` for simplification.
- **`dif_pos`/`dif_neg` for dependent if**: When `simp` leaves a `dite` (dependent if-then-else), use `rw [dif_pos h]` or `rw [dif_neg h]` to eliminate it, not `simp only [dite_true]`.

## Roadmap (PLAN.md)

The project roadmap is maintained in `PLAN.md` at the repository root. It contains a phased plan for implementing the full EVM state transition function as verified RISC-V programs (for use as a zkEVM).

**When you complete a task from the plan**, update `PLAN.md` to reflect the new status:
- Move completed opcodes from their phase section to the "Done" list under "Current Status"
- Update instruction counts or other details if they changed during implementation
- If you discover new sub-tasks or issues, add them to the appropriate phase

Always check `PLAN.md` at the start of a session to see what's next in the priority order.
