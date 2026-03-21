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

- **Do NOT add `set_option maxHeartbeats` to any file.** Heartbeat limits are configured globally in `lakefile.toml`.
- **Do NOT add `set_option maxRecDepth` to any file.** Recursion depth is configured globally in `lakefile.toml`.
- If a proof times out or hits recursion limits, restructure the proof (e.g., split into smaller lemmas, use intermediate `have` bindings) rather than increasing limits.

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
- **PR descriptions**: Do not include a "Test plan" section. Keep the description to a summary only.

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

## Pattern: Adding a Stack-Level Spec for a Shift Opcode

The SHR and SHL implementations follow a 3-file composition pattern that SAR should also follow:

### File structure (under `Evm64/Shift/`)

1. **`XxxSpec.lean`** — Per-limb and body specs (proved with `runBlock`)
2. **`XxxCompose.lean`** — Hierarchical composition (~1000 lines):
   - `xxxCode` definition (`CodeReq.ofProg base evm_xxx`)
   - Subsumption lemmas (phase/body code ⊆ xxxCode via `CodeReq.ofProg_mono_sub`)
   - Address normalization lemmas (`by bv_omega` / `native_decide + bv_omega`)
   - Zero-path compositions (BNE taken + BEQ taken → zero result)
   - Bridge lemmas (connect per-limb outputs to `getLimb (value OP n)`)
   - Body-path composition (`evm_xxx_body_evmWord_spec`)
3. **`XxxSemantic.lean`** — Stack-level spec (~200 lines):
   - Zero-lift helpers (frame regs, unfold/refold `evmWordIs`)
   - Main theorem case-splitting on `shift ≥ 256`

### Key lessons learned

- **Body code definitions must use `CodeReq.ofProg`** (not explicit union chains of singletons). The `CodeReq.ofProg_mono_sub` subsumption proof requires the code to be in `ofProg` form. If the body code is defined as a union chain, it is NOT definitionally equal to `ofProg` and the proof will fail with "Type mismatch". This requires `_prog` parametric definitions in `Program.lean`.

- **Bridge lemma proofs must use `extractLsb'_split_64`** (the algebraic approach), NOT `ext j` with manual `testBit` reasoning. The `ext j` approach produces `Nat.testBit` goals with modular arithmetic that are far too complex for `omega`/`constructor`. The correct approach: prove helper theorems in `Basic.lean` (`getLimb_shiftLeft`, `getLimb_shiftLeft_eq_div`, `getLimb_shiftLeft_low`) that decompose `getLimb (v <<< n) i` at the `BitVec 64` level using `extractLsb'_split_64`, then the bridge lemmas become 5-10 line algebraic rewrites.

- **SHL bridge differs from SHR bridge** in index direction. SHR uses `i + L` (always ≥ 0, handled by `getLimbN` returning 0 for ≥ 4). SHL uses `i - L` (can underflow with Nat subtraction). Solution: three separate bridge lemma variants (merge for `i > L`, first for `i = L`, zero for `i < L`) instead of a single unified lemma.

- **Phase A/B/C and zero_path specs are code-agnostic**. They're proved against their own local `CodeReq` (e.g., `shr_phase_a_code`), not against `shrCode`/`shlCode`. So the same spec theorems are reused for SHL — only the subsumption extension (`cpsTriple_extend_code`) changes to use `shlCode`.

- **Many helper lemmas in `Compose.lean` are `private`** (`CodeReq_union_sub_both`, `cpsTriple_strip_pure_and_convert`, `cpsNBranch_extend_code`, `cpsNBranch_frame_left`, `validMem_value_portion`). These must be duplicated in `ShlCompose.lean` rather than imported. Consider making them non-private in a future refactor.

- **Body spec parameters**: The body specs take `(sp : Word) (v5 v10 bit_shift anti_shift mask : Word) (v0 v1 v2 v3 : Word)`. After phase C dispatch, `v5 = limb_shift` and `v10` depends on which cascade exit was taken (e.g., `sltiu_val` for exit 0, `0 + signExtend12 1` for exit 1, etc.).

- **`rw` inside `cpsTriple_strip_pure_and_convert` callbacks**: When the postcondition is a `let` binding like `resultPost`, `rw [← eq0]` may fail because `rw` can't find `getLimb result 0` inside the opaque `resultPost`. Fix: expand `show resultPost h` to the full assertion expression so `rw` can find the patterns.

- **`set_option maxHeartbeats N in` placement**: Must come BEFORE the theorem declaration (including any docstring). Placing it after a `/-- ... -/` docstring causes parse errors.

### Subsumption proof pattern

For each sub-program at offset K with M instructions starting at program index J:
```lean
set_option maxHeartbeats 4000000 in
private theorem xxx_sub_xxxCode (base : Addr) :
    ∀ a i, xxx_code (base + K) jal_off a = some i → xxxCode base a = some i := by
  exact CodeReq.ofProg_mono_sub base (base + K) evm_xxx (xxx_prog jal_off) J
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)
```

The 4 proof obligations are: address alignment, length bound, instruction matching, no-dup.

## Roadmap (PLAN.md)

The project roadmap is maintained in `PLAN.md` at the repository root. It contains a phased plan for implementing the full EVM state transition function as verified RISC-V programs (for use as a zkEVM).

**When you complete a task from the plan**, update `PLAN.md` to reflect the new status:
- Move completed opcodes from their phase section to the "Done" list under "Current Status"
- Update instruction counts or other details if they changed during implementation
- If you discover new sub-tasks or issues, add them to the appropriate phase

Always check `PLAN.md` at the start of a session to see what's next in the priority order.
