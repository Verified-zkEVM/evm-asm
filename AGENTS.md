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

- **Naming convention (Mathlib-aligned):**
  - **camelCase** for *value* identifiers: `let`-bound locals, theorem/lemma parameters, function arguments, definitions (e.g. `let qAddr := ...`, `theorem foo (carryNat : Nat)`).
  - **snake_case** for *hypothesis* names — proof bindings introduced by `have h_… : Prop`, `obtain ⟨h_lt, h_eq⟩`, `intro h_pos`, etc. Mathlib keeps these snake_case (e.g. `h_pos`, `h_le`, `h_zero`, `h_eq`). Do **NOT** rename `h_*`-style hypothesis names to camelCase as part of #189 cleanup — that's the wrong direction. PR #1497 made this mistake.
  - When in doubt: if it names a `Prop`-typed term used in a proof, leave snake_case; if it names data (a `Nat`, `Word`, `BitVec`, etc.), use camelCase.

- **Do NOT add `set_option maxHeartbeats` to any file** unless you are in `Evm64/Shift/` composition files (Compose, ShlCompose, SarCompose) for body/path composition proofs. Heartbeat limits are configured globally in `lakefile.toml`.
- **Do NOT add `set_option maxRecDepth` to any file.** Recursion depth is configured globally in `lakefile.toml`.
- If a proof times out or hits recursion limits, restructure the proof (e.g., split into smaller lemmas, use intermediate `have` bindings) rather than increasing limits. Increasing `maxRecDepth`/`maxHeartbeats` is almost always a waste of time — the real issue is typically a unification mismatch, wrong argument order, or missing address canonicalization.
- **Do not bump `maxHeartbeats` to make a slow proof compile.** Large heartbeat budgets just slow experiments — and the effect compounds: every retry, every edit, every CI run pays the cost. Needing monitors or `sleep` loops to wait for a build is itself a symptom that `maxHeartbeats` is too big. If a proof legitimately needs more than the default, it is too complicated — diagnose what is actually slow (a failing `rfl`, a stuck `xperm_hyp`, an accidentally false goal, or an `xperm` target with too many conjuncts) and simplify by:
  1. Splitting the proof into smaller named lemmas.
  2. Marking expensive intermediate definitions `@[irreducible]` and proving a small set of lemmas about them, so later proofs unfold via those lemmas instead of re-reducing the body each time.
  3. Breaking up large `have`s into separate lemmas so the core composition step has fewer atoms to permute.
- **Exception for Shift composition files**: `set_option maxHeartbeats` up to 6400000 is acceptable for body/path composition proofs (Section 4+) which are bottlenecked by `xperm_hyp` permutation on large atom chains. Subsumption lemmas (Section 2) should NOT need heartbeat overrides — they use structural `unionAll` reasoning.

## Common Pitfalls

1. **Notation issues**: Custom notations (like `↦ᵣ ?`) may not parse correctly; use functions directly
2. **Simp lemmas**: Mark key lemmas with `@[simp]` for automatic application
3. **List operations**: Be careful with `execProgram` and list append - may need explicit `execProgram_append`
4. **Register inequality**: Use `decide` tactic for concrete register inequality proofs
5. **Program type**: `Program = List Instr` is a `def`, not `abbrev` — use `simp only [..., Program]` to unfold before `List.length_append` etc.
6. **New `.lean` files must be imported by the umbrella module**: `lake build` will compile every file it can reach from `EvmAsm.lean` via the transitive `import` graph, which goes `EvmAsm.lean → Rv64.lean / Evm64.lean / EL.lean → individual modules`. Leaf files that are **not** imported still get built by `lake build` (Lake discovers them via the directory-scoped library), but they are **invisible to downstream consumers** — proofs in other files cannot `open` or reference their declarations. When you add a file, register it in the corresponding umbrella:
   - `EvmAsm/Rv64/Foo.lean` → add `import EvmAsm.Rv64.Foo` to `EvmAsm/Rv64.lean`.
   - `EvmAsm/Evm64/Foo/Bar.lean` → add `import EvmAsm.Evm64.Foo.Bar` to `EvmAsm/Evm64.lean` (or to an intermediate umbrella like `EvmAsm/Evm64/Foo.lean` if one exists).
   - `EvmAsm/EL/Foo.lean` → add `import EvmAsm.EL.Foo` to `EvmAsm/EL.lean`.

   If your new file declares an attribute via `register_simp_attr`, place the attribute-declaration file **before** any consumer file in the umbrella's import list so the attribute exists when the consumer is elaborated. Typical pattern: split into `FooAttr.lean` (declares the attribute) + `Foo.lean` (uses the attribute, imports `FooAttr`), then import both from the umbrella, attr first. See `Rv64/RegOpsAttr.lean` + `Rv64/RegOps.lean` or `Evm64/DivMod/AddrNormAttr.lean` + `Evm64/DivMod/AddrNorm.lean` for the canonical shape.

   CI enforces this via `scripts/check-unimported.sh` (issues #1209 / #1440): a `.lean` file under `EvmAsm/` that is not transitively reachable from `EvmAsm.lean` will fail the build. The grandfathering allow-list (`scripts/unimported-allow.txt`) was drained and removed in #1440 — there is no escape hatch, so wire new files into the appropriate umbrella when you add them.

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

## Import Hygiene (`lake exe shake`)

We use Mathlib's `shake` tool to flag unused imports. Configuration lives in
`scripts/noshake.json` (curated entries for known false positives — e.g.
files that use `IntervalCases` / `FinCases` / `Fintype` instances, the
`Init` / `Lean` modules referenced by Word notation, and tactic-registry
attributes that shake doesn't track).

Reproduction recipe:

```bash
lake build           # required: shake reads .olean metadata
lake exe shake EvmAsm
```

Pitfalls:

- `shake` does **not** track tactic registries / `@[spec_gen_*]` attributes
  that elaborate via tactics, term-elaborator macros, or `notation`-only
  references (`notation "Word" => BitVec 64` in `EvmAsm.Rv64.Basic`). Many
  of its suggestions are false positives — see the audit in beads
  `evm-asm-o6y` (parent `evm-asm-6qj`) before acting on raw shake output.
  Filter via `scripts/shake-filter.py` / `scripts/shake-filter.md` and
  verify each removal with `lake build` before committing.
- When in doubt, prefer adding a `noshake.json` entry over removing the
  import.

## Git Workflow

- Main branch: `main`
- Create feature branches for new work
- Use meaningful commit messages with Co-Authored-By line for AI contributions
- **PR titles must follow conventional commit format**: `type[(scope)]: subject`
  (e.g. `refactor: extract shared Shift Compose helpers`,
  `fix(shr): address canonicalization in sign-fill path`). The PR summary bot
  flags titles that don't match this format.

## References

- **Original paper**: Kennedy et al., "Coq: The world's best macro assembler?" PPDP 2013
  https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/
- **SP1 zkVM**: https://github.com/succinctlabs/sp1
- **RISC-V ISA**: https://riscv.org/technical/specifications/
- **sail-riscv-lean**: https://github.com/opencompl/sail-riscv-lean (same toolchain)
- **Lean 4 docs**: https://lean-lang.org/documentation/

## Frame-automation Tactics

**Primary reference:** [`TACTICS.md`](TACTICS.md) is the user guide for
`runBlock`, `seqFrame`, `xperm`, `xcancel`, the `@[spec_gen]` registry,
and the domain-specific grindsets (`divmod_addr`, `rv64_addr`, `reg_ops`,
`byte_alg`). Read it before hand-writing a `cpsTriple_seq_*` chain or
wiring a new `@[...]` equality-closing attribute from scratch.

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
   - Address normalization lemmas (`bv_addr` proofs — see Build Performance section)
   - Path composition (zero-path/sign-fill for shift >= 256, body-path for shift < 256)
   - Bridge lemmas connecting per-limb results to `getLimb (result) i`
3. **Semantic** (`Semantic.lean`, `ShlSemantic.lean`, `SarSemantic.lean`): Stack-level `evmWordIs` spec. Lifts composition to `EvmWord` assertions using `cpsTriple_weaken` + `xperm_hyp`.

### Composition File Pattern (for shift opcodes)

Each shift Compose file (~1000-1200 lines) follows this structure:
1. **Section 1**: `xyzCode` definition as `CodeReq.unionAll` of per-phase `ofProg` blocks + length lemmas + `skipBlock` macro + helpers (`singleton_sub_ofProg`, `CodeReq_union_sub_both`, `regIs_to_regOwn`)
2. **Section 2**: Subsumption lemmas — structural reasoning via `skipBlock` + `union_mono_left` (following the DivMod pattern). For union-chain `_code` definitions (Phase A, Phase C, sign-fill), split into bridge sub-lemma (`chain_code ⊆ ofProg small_block`) + structural sub-lemma (`ofProg small_block ⊆ xyzCode`)
3. **Section 3**: Address normalization — `bv_addr` proofs for all offset arithmetic (see Build Performance section)
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

## XPerm AC Reflection and Atom Identity

The `xperm` tactic uses AC reflection (`Lean.Meta.AC.buildNormProof`) for O(n log n) separation logic permutation proofs. This requires atoms on both sides to be **syntactically identical** (same `Expr.hash`). Common causes of hash mismatch:

1. **Type alias differences**: `Word` vs `BitVec 64`. Fixed by defining `Word` as `notation` (not `abbrev`), so the elaborator always produces `BitVec 64`.

2. **Let-binding indirection**: `regIs .x7 result` (fvar) vs `regIs .x7 (if ...)` (definition). Fixed by `zetaReduce` in `buildPermProof`.

3. **OfNat instance differences**: `@OfNat.ofNat Word 8 inst₁` vs `@OfNat.ofNat (BitVec 64) 8 inst₂`. Fixed by recursive `withReducible whnf` normalization in `checkACEligible`.

4. **Fin proof term differences**: `getLimb ⟨0, proof₁⟩` vs `getLimb ⟨0, proof₂⟩` where `proof₁` and `proof₂` are different terms for `0 < 4`. **Not yet fixed.** Workaround: use `getLimbN` (Nat index) instead of `getLimb` (Fin 4 index) in new code.

**Rule for new code**: When writing theorem statements that go through `xperm_hyp`, ensure both sides of the permutation use identical expressions (not just isDefEq). Avoid `Fin` literals and use `Nat` indices where possible.

## Build Performance

### `bv_addr` vs `bv_omega` for address arithmetic

For address offset equalities like `(base + 228) + 24 = base + 252`, use `bv_addr` instead of `bv_omega`:

```lean
-- GOOD: tiny proof term (add_assoc + rfl), fast kernel checking
have : (base + 228 : Word) + 24 = base + 252 := by bv_addr

-- BAD: large proof term (bitvec_to_nat conversion + Presburger arithmetic)
have : (base + 228 : Word) + 24 = base + 252 := by bv_omega
```

`bv_addr` is defined as `(simp only [BitVec.add_assoc]; rfl)` in `Rv64/Tactics/SeqFrame.lean`. It works for any `(a + k₁) + k₂ = a + k₃` where k₁, k₂, k₃ are concrete and a is a variable.

**When to use `bv_addr`**: Address offset equalities, `ofProg_mono_sub` address arguments, pre-computed address theorems.

**When to keep `bv_omega`**: Address inequalities (`≠`), range bounds (`< 2^64`), `skipBlock` disjointness proofs.

**For signExtend patterns**: `rw [signExtend13_1016]; bv_addr` (normalize signExtend first, then use bv_addr).

Impact: olean sizes drop 50-80% (e.g., LoopBody 16MB → 2.8MB), kernel checking time drops proportionally.

### Named grind/simp sets

For closing repetitive proof patterns (e.g., DivMod address-arithmetic equalities via `divmod_addr`), use the registered grind/simp sets rather than inline `simp only [show … from by decide]; bv_omega` chains. See **[GRIND.md](GRIND.md)** for the full conventions, canonical reference implementation (`EvmAsm/Evm64/DivMod/AddrNorm.lean`), layout patterns, empirical justification, and the rollout roadmap.

#### Address-normalization grindset family

Three address grindsets cover all current call-sites; pick the most specific
that matches the proof's domain:

| Grindset | Scope | File pair |
|---|---|---|
| `rv64_addr` | Rv64-wide: `signExtend12/13/21` + `BitVec.add_assoc` + `(N : BitVec 6).toNat` + `(N : Word).toNat` + `BitVec.ofNat 64 (4 * k)`. Subsumes the legacy `bv_addr`. | `EvmAsm/Rv64/AddrNormAttr.lean` + `EvmAsm/Rv64/AddrNorm.lean` |
| `divmod_addr` | DivMod-specific atoms (Phase-1/Phase-2 offsets, `k <<< 3`, scratch-cell projections). Re-tags the relevant `rv64_addr` atoms so `divmod_addr` is a strict superset within DivMod. | `EvmAsm/Evm64/DivMod/AddrNormAttr.lean` + `EvmAsm/Evm64/DivMod/AddrNorm.lean` |
| `exp_addr` | EXP opcode-local atoms (skeleton — attribute reserved; populate atoms + add a `by exp_addr` macro once EXP Compose emits concrete address arithmetic). | `EvmAsm/Evm64/Exp/AddrNormAttr.lean` + `EvmAsm/Evm64/Exp/AddrNorm.lean` |

Usage: write `by rv64_addr` (or `by divmod_addr` / `by exp_addr`) to close
address-arithmetic equalities. Each tactic tries `grind` first and falls back
to `simp only [<set>, BitVec.add_assoc]; rfl`. New concrete offsets are added
as one-line `@[<set>, grind =] theorem <name> : … := by decide` lemmas in the
set's atom file; every downstream proof picks them up.

Opt-in pattern for a new opcode subtree (e.g. `Evm64/Foo/`):

1. Create `Evm64/Foo/AddrNormAttr.lean` with `register_simp_attr foo_addr`.
2. Create `Evm64/Foo/AddrNorm.lean` that imports `AddrNormAttr`, re-tags
   relevant `rv64_addr` atoms with `@[foo_addr]` (or adds opcode-specific
   atoms), and exposes a `foo_addr` macro tactic mirroring `rv64_addr`'s
   shape.
3. Wire both into the umbrella import (attr file first — see the
   `register_simp_attr` rule above).

`EvmAsm/Evm64/Exp/AddrNormAttr.lean` + `EvmAsm/Evm64/Exp/AddrNorm.lean` is the
canonical minimal shape; `EvmAsm/Evm64/DivMod/AddrNorm.lean` shows the
mature pattern with re-tagging and per-domain extensions.

**Do not** introduce a new opcode subtree without an `AddrNorm` pair on the
first commit that adds non-trivial address arithmetic — see
[`EvmAsm/Evm64/OPCODE_TEMPLATE.md`](EvmAsm/Evm64/OPCODE_TEMPLATE.md) §2.5.
Retrofitting the grindset later is the tax that issue #263 documents.

### Parallel file splitting for Compose files

Large composition files (>1000 lines) should be split into independent sub-files under a `Compose/` directory:
- `Compose/Base.lean`: shared definitions (`divCode`, `modCode`, `skipBlock`, length lemmas)
- Independent sub-files (PhaseAB, CLZ, Norm, NormA, Div128, Epilogue) that all import only Base
- `Compose.lean`: lightweight re-export of all sub-files

This enables parallel kernel checking. The split reduced DivMod/Compose from 87s (monolithic) to 55s (critical path through Norm.lean).

### File-size guardrail

The advice above is enforced mechanically by `scripts/check-file-size.sh`, which runs as the first step of the Build CI workflow:

| Path | Hard cap |
|---|---|
| `EvmAsm/Evm64/**/Compose/**/*.lean` | 1200 lines (soft cap 1000) |
| `EvmAsm/Evm64/**/*.lean` (everything else) | 1500 lines |
| `Program.lean` (any directory) | exempt — concrete bytecode + tests, no proof cost |

A file over cap **must** either be split or carry an opt-out comment in its first 20 lines:

```lean
-- file-size-exception: <one-line reason, ideally with a tracking issue>
```

The reason is required so the exception is visible in code review rather than a silent override. Existing oversize files are grandfathered with such comments; new files should not need them.

To run the check locally:

```sh
scripts/check-file-size.sh           # exit 1 on any unexcused violation
scripts/check-file-size.sh --report  # always exit 0; print all over-cap files
```

### Benchmark history (`benchmark-history` orphan branch)

The Monday `benchmark.yml` cron appends one JSON object per successful
run to `history.jsonl` on the long-lived `benchmark-history` orphan
branch (created on first push by the workflow itself). Each row carries
`commit`, `timestamp`, `wall_seconds`, `peak_rss_kb`, `runner_os`,
`runner_cores`, … — see `docs/benchmark-workflow-design.md` for the
full schema and rationale.

To inspect the historical series locally:

```bash
git fetch origin benchmark-history
git show origin/benchmark-history:history.jsonl | tail -n 20
# project a single metric over time:
git show origin/benchmark-history:history.jsonl \
  | jq -r '[.timestamp, .commit[:12], .wall_seconds] | @tsv'
```

When chasing a build-time regression, correlate adjacent `wall_seconds`
jumps with `git log --oneline <prev-sha>..<curr-sha>` between the two
recorded `commit` values. Files that have historically driven the
largest deltas live under `EvmAsm/Evm64/DivMod/` (compose chains; see
the `xperm` notes above) and `EvmAsm/Evm64/Shift/` (composition files
where bumping `set_option maxHeartbeats` is permitted per the Critical
Rules).

## Bundling Postconditions with `let` Bindings

When a composed spec's postcondition has many `let` bindings (e.g., shift
amounts, normalized limb values), wrap the entire postcondition — including
the `let` computations — in an `@[irreducible] def` returning `Assertion`.
This prevents Lean from repeatedly evaluating nested lets during type
elaboration.

### Pattern

**Define** the postcondition function in a shared file (e.g., `Compose/Base.lean`):

```lean
@[irreducible]
def myPost (sp param1 param2 ... : Word) : Assertion :=
  let derived1 := f param1
  let derived2 := g derived1 param2
  -- ... all computed values as let bindings ...
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ derived1) ** ... -- full assertion chain
```

**Provide an unfold lemma** (for consumers that need the expanded form):

```lean
theorem myPost_unfold (sp param1 param2 ... : Word) :
    myPost sp param1 param2 ... =
    let derived1 := f param1
    ... -- same body as the def
    := by delta myPost; rfl
```

**Use in theorem signatures** — the `let` bindings disappear from the type:

```lean
-- BEFORE (11 let bindings in the type, slow elaboration):
theorem my_spec ... :
    let shift := (clzResult b3).1
    let anti_shift := ...
    ... 9 more lets ...
    cpsTriple ... precond (expanded 30-atom postcondition)

-- AFTER (compact type, fast elaboration):
theorem my_spec ... :
    cpsTriple ... precond (myPost sp n_val (clzResult b3).1 a0 a1 a2 a3 ...)
```

**Proof changes** — define the `let` bindings locally and unfold at the end:

```lean
theorem my_spec ... :
    cpsTriple ... precond (myPost sp n_val shift_arg ...) := by
  -- Local lets for use in intermediate composition steps
  let shift := shift_arg
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  ... -- same let bindings as in myPost body
  -- ... composition steps (unchanged) ...
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta myPost; xperm_hyp hq)  -- delta unfolds @[irreducible]
    hFull
```

### Why `@[irreducible]`

- `xperm` uses reducible transparency, so even a plain `def` is opaque to it.
  `@[irreducible]` adds safety: `simp` and `whnf` at default transparency also
  won't accidentally unfold it.
- `delta` ignores transparency and always unfolds — use it in the proof's
  final `cpsTriple_weaken` callback.
- Matches the existing `phaseB_zeroed_mem` pattern in `PhaseAB.lean`.

### Scaling: external weaken lemma

As compositions grow, the inline `delta myPost; xperm_hyp hq` in each
proof's `cpsTriple_weaken` callback may become a bottleneck. To avoid
repeating this work in every consumer, extract the implication as a
standalone lemma (name it `_weaken` to match the `cpsTriple_weaken` /
`cpsBranch_weaken` naming from #331):

```lean
theorem myPost_weaken (sp param1 ... : Word) (h : PartialState)
    (hq : (expanded_postcondition) h) :
    myPost sp param1 ... h := by
  delta myPost; xperm_hyp hq
```

Then each theorem's final step becomes:

```lean
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => myPost_weaken sp param1 ... h hq)
    hFull
```

This pays the `delta + xperm` cost once (when the lemma is checked) rather
than in every theorem that produces `myPost`. Place the weaken lemma
next to the `def` and `_unfold` lemma in the shared file.

### When to apply

Apply this pattern when a theorem's postcondition has **3+ `let` bindings**
that compute derived values used in the assertion chain. The canonical example
is `loopSetupPost` in `Compose/Base.lean` (11 let bindings, used by 8 theorems).

## Adapter Signatures with Deep Let-Chains (Algorithm Intermediates)

For **stack-level adapters** that expose runtime-computed intermediate
values via `let` chains (e.g., `let ms := mulsubN4 ...; let ab := addbackN4
...; let un{i}Out := if carry = 0 then ab'.{i_low} else ab.{i_low}`),
keep the goal small by wrapping each natural intermediate as a separate
`@[irreducible] noncomputable def` rather than letting the proof state
materialize the entire chain inline.

The DivMod call+addback BEQ adapter is the canonical example
(`output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm`). A first
attempt with the inline let-chain in the signature yielded a 246-line
proof that fought 200k-heartbeat `whnf` timeouts in the final fold; a
restart with per-intermediate irreducibles cut it to ~50 lines and
closed the single-addback case cleanly.

### Pattern (3 components per intermediate)

For each algorithm intermediate value `X`:

1. **Irreducible def** capturing the computation as an opaque term:

   ```lean
   @[irreducible]
   noncomputable def algCallAddbackBeqUn0Out (a b : EvmWord) : Word :=
     let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     ... -- full let-chain
     if carry = 0 then ab'.1 else ab.1
   ```

2. **Unfolding lemma** for consumers that need the inline form:

   ```lean
   theorem algCallAddbackBeqUn0Out_unfold {a b : EvmWord} :
       algCallAddbackBeqUn0Out a b = (let shift := ...; ... if-then-else) := by
     show algCallAddbackBeqUn0Out a b = _
     unfold algCallAddbackBeqUn0Out
     rfl
   ```

3. **Bridge lemma** connecting the irreducible to a derived form (e.g.,
   the `single-addback` case where `un{i}Out = post1Limb{i}` because
   `addbackN4`'s low 4 outputs are independent of the `u4_new` parameter):

   ```lean
   theorem algCallAddbackBeqUn0Out_eq_post1Limb0_of_single_addback
       (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b ≠ 0) :
       algCallAddbackBeqUn0Out a b = algCallAddbackBeqPost1Limb0 a b := by
     rw [algCallAddbackBeqCarry_unfold] at hcarry
     unfold algCallAddbackBeqUn0Out algCallAddbackBeqPost1Limb0
     simp only []; rw [if_neg hcarry]; rfl
   ```

### Adapter signature pattern

The adapter's conclusion uses `let` to alias the irreducibles, keeping
the printed type compact while letting consumers refer to them:

```lean
theorem output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm
    (sp : Word) (a b : EvmWord) (...) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let un0Out := algCallAddbackBeqUn0Out a b
    let un1Out := algCallAddbackBeqUn1Out a b
    ...
    (((sp + 32) ↦ₘ ((un0Out >>> shift) ||| (un1Out <<< (64 - shift)))) **
     ...) =
    evmWordIs (sp + 32) (EvmWord.mod a b) := by
  intro shift un0Out un1Out un2Out un3Out
  by_cases hcarry : algCallAddbackBeqCarry a b = 0
  · sorry  -- alternative branch
  · rw [show un0Out = algCallAddbackBeqPost1Limb0 a b from ...,
        show un1Out = algCallAddbackBeqPost1Limb1 a b from ...,
        ...]
    exact (evmWordIs_sp32_limbs_eq sp ...).symm
```

### Caller adaptation

When an adapter's signature changes from inline `let un{i}Out := if-then-else`
to irreducible-bundled `let un{i}Out := algCallAddbackBeqUn{i}Out a b`,
**callers must fold their inline forms back to the irreducibles**. Without
this fold, `xperm_hyp` (which compares atoms syntactically) fails to match
the inline-form atoms in the hypothesis with the irreducible-form atoms
introduced by `rw [adapter.symm]`.

```lean
intro h hq
simp only [fullModN4CallAddbackBeqPost_unfold, denormModPost_unfold] at hq
-- Fold hq's inline un{i}Out forms to the irreducible Un{i}Out names
-- so they match the adapter's new signature.
simp only [← algCallAddbackBeqUn0Out_unfold, ← algCallAddbackBeqUn1Out_unfold,
           ← algCallAddbackBeqUn2Out_unfold, ← algCallAddbackBeqUn3Out_unfold] at hq
...
rw [show evmWordIs (sp + 32) (EvmWord.mod a b) = _ from h_slot.symm]
...
xperm_hyp hq
```

### Symptoms that warrant the irreducible-bundle restructure

If a stack-level adapter's proof exhibits any of these, the let-chain
is too deep and the proof state needs irreducible bundling:

- `rw [← unfold_lemma]` and `simp only [← unfold_lemma]` **silently no-op**
  (succeed without firing) — the rewriter can't match the let-chain RHS
  against the goal's zeta-reduced form.
- `exact (some_helper).symm` produces a `Type mismatch` where the actual
  and expected types **look identical** in the printed output but differ
  in projection-index spacing or implicit args.
- `convert (some_helper).symm using N` (any `N`) hits a 200k-heartbeat
  timeout in `whnf` during defeq slack.
- Diagnostic by `diff` of the error's "actual" and "expected" terms
  reveals the structures are the same up to subtle nested-shape
  differences that no `simp`/`rw` reconciles.

### Why irreducibles work where `set` doesn't

`set X := body with hX_def` creates a let-bound local + the equation
`hX_def : X = body`, but it only matches occurrences of `body` in the
goal **syntactically**. After `dsimp only []` zeta-reduces the goal,
`set` against parent-shaped expressions silently fails (no occurrences
to bind). Irreducible defs sidestep this: their term is opaque from
the outside, so subsequent `rw`/`simp`/`xperm` see one atom rather
than navigating the let-chain.

### Sub-lemma split

Pair the irreducible bundling with **sub-lemma extraction**. A focused
sub-lemma takes the irreducibles as inputs and produces a small
4-tuple of per-limb facts (e.g.,
`mod_n4_call_addback_beq_single_addback_post1_limbs_close`):

```lean
theorem mod_n4_..._post1_limbs_close (a b : EvmWord) (...)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    let s := (clzResult (b.getLimbN 3)).1.toNat % 64
    (EvmWord.mod a b).getLimbN 0 =
      ((algCallAddbackBeqPost1Limb0 a b) >>> s) |||
        ((algCallAddbackBeqPost1Limb1 a b) <<< (64 - s)) ∧
    ... := by
  intro s
  have h_wrapper := parent_post1Val_eq_amod_pow_s_of_single_addback ...
  rw [algCallAddbackBeqPost1Val_eq_val256_limbs] at h_wrapper
  ...
  exact denorm_4limb_eq_mod_of_val256_eq_amod_pow_s ...
```

The adapter's proof body then collapses to a single `rw` of the
bridges plus an `exact` of `evmWordIs_sp32_limbs_eq.symm` applied to
the sub-lemma's output.

### When to apply

Apply this pattern when an adapter's conclusion has **deep let-chains
mixing if-then-else and recursive function calls** (e.g., `mulsubN4`
inside `addbackN4` inside `if`), and a first attempt at the proof body
hits any of the symptoms listed above. Spending the iteration on
irreducible bundles + sub-lemmas pays for itself by avoiding the
"refactoring tax" of multiple failed `simp`/`rw`/`exact` attempts.

## linarith vs omega for Let-Bound Terms

When a goal mixes locally-introduced `let` bindings (e.g. via `intro`) with
hypotheses obtained by applying a separately-stated theorem whose conclusion
unfolds its own lets, `omega` may fail even when the algebra is trivial. The
two sides see syntactically distinct copies of the same definitionally-equal
expression (`(uLo >>> 32).toNat` vs `div_un1.toNat` where
`div_un1 := uLo >>> 32`), and `omega` treats them as opaque, unrelated atoms.

**Try `linarith` first** in this regime. It does a looser syntactic match and
often closes the goal without any extra rewrites:

```lean
intro dHi dLo div_un1 q1 ... q1c
have h_range := some_range_lemma uHi uLo vTop ...
obtain ⟨h_lower, h_upper⟩ := h_range
-- h_lower has the unfolded `(uLo >>> 32).toNat` form;
-- the goal's `div_un1.toNat` is the local-let form. omega chokes; linarith doesn't.
have h_eq : q1c.toNat = ... + 1 := by linarith
```

Reach for `omega` when the reasoning is genuinely Presburger (modular
arithmetic, divisibility); reach for `linarith` when the reasoning is plain
linear inequality and the only friction is term-shape mismatch on
let-bindings. If both fail, fall through to **Pure-Nat Sub-Lemmas** (next
section) — extracting a focused helper sidesteps the let-binding issue
entirely by passing concrete `Nat` values across the call boundary.

## Pure-Nat Sub-Lemmas for omega/maxRecDepth Avoidance

When a proof in a theorem with **deep let-chains and many opaque
non-linear products** (e.g., `(q + 1) * dHi`, `(q + 2) * dLo`) hits
`omega`'s `maxRecDepth` limit, factor the algebraic core into a
**private pure-Nat sub-lemma** with explicit `set` aliases for the
non-linear products.

### Symptoms

- `omega` produces "maximum recursion depth has been reached" inside a
  `have` block, even after splitting the proof.
- The constraint set in `omega`'s error message contains many
  independent product variables (e.g., `g := (q_true + 1) * dHi.toNat`,
  `i := (q_true + 2) * dHi.toNat`) that omega treats as opaque.
- The ambient theorem has **20+ let-bound variables** (full algorithm
  state introduced via `intro`).

### Why omega struggles

`omega` is a decision procedure for **linear** integer arithmetic. When
the ambient context has many non-linear products as terms (`a * b` where
both factors involve variables), omega treats each product as a fresh
variable and tries to discover linear relationships between them. With
many products and many constraints, this exploration can hit elaboration
limits.

### Pattern

For each algebraic deduction that hits `maxRecDepth`, extract a private
helper that takes **only the relevant Nat variables** and uses `set`
aliases inside to keep the constraints linear:

```lean
private theorem my_arith_helper (u4 A B div_un1 : Nat)
    (h_x_lt : u4 * 2^32 + div_un1 < A * 2^32 + B)
    (h_A_le_u4 : A ≤ u4)
    (h_B_bound : B + 2^32 ≤ 2^64) :
    u4 - A < 2^32 := by
  set X := u4 * 2^32 with hX
  set Y := A * 2^32 with hY
  have h_sub_mul : (u4 - A) * 2^32 = X - Y := by
    rw [hX, hY, Nat.sub_mul]
  have h_Y_le_X : Y ≤ X := Nat.mul_le_mul_right _ h_A_le_u4
  have h_step : (u4 - A) * 2^32 < B + 2^32 := by
    rw [h_sub_mul]; omega
  set Z := (u4 - A) * 2^32 with hZ
  by_contra h_ge
  push Not at h_ge
  have h_mul : 2^32 * 2^32 ≤ Z := by
    rw [hZ]; exact Nat.mul_le_mul_right _ h_ge
  have h_pow_eq : (2^32 * 2^32 : Nat) = 2^64 := by decide
  omega
```

### Why this works

- The sub-lemma's **isolated context** has only the few hypotheses it
  needs, so omega's search space is bounded.
- `set X := ...` with `with hX` introduces a local fvar plus an equation;
  omega sees `X` as a single variable and `X = ...` as one linear
  constraint, sidestepping the non-linear product entirely.
- Pre-computing `Nat.mul_le_mul_right _ h_A_le_u4` as `Y ≤ X` (linear
  fact between aliases) gives omega exactly the linear hypothesis it
  needs.
- The main theorem invokes `my_arith_helper u4.toNat A B div_un1.toNat ...`,
  passing concrete Nat values rather than wading through let-zeta.

### When to apply

When a proof body:
1. Has 20+ let-bound variables (typical for algorithm-state-heavy proofs
   like `div128Quot_v2` Phase-1).
2. Contains an algebraic deduction that's **mathematically simple but
   non-linear** (e.g., `(u4 - A) * 2^32 < 2^64` from inequalities
   involving products).
3. Hits `maxRecDepth` in `omega` despite being structurally correct.

Following the Critical Rule "**don't add `set_option maxRecDepth`**" —
extract a pure-Nat helper instead. The helper amortizes the algebraic
work and keeps the main proof readable.

### Canonical example

`phase1b_2nd_guard_arith` in `Evm64/DivMod/SpecCallAddbackBeq.lean` is
the canonical reference. It captures Knuth's TAOCP §4.3.1 rhat bound
under overshoot=2 (`u4 - (q_true + 1) * dHi < 2^32`) as a pure-Nat
statement, allowing the consumer
`div128Quot_v2_phase1b_2nd_guard_under_runtime` to discharge the
algebra in one line. The pattern was extracted after a first proof
attempt repeatedly hit `maxRecDepth` despite restructuring (changing
`set` calls, splitting `have` blocks) within the main theorem body.

Sibling examples in the same file: `conj2_arith`,
`un21_lt_vTop_arith`, `un21_toNat_untruncated_arith` — each isolates
a focused pure-Nat algebraic claim invoked by a Word-level theorem.

## End-to-End Composition with Existential Intermediates

When composing specs where an intermediate postcondition has existentials (e.g., `loopBodyPostN4` which wraps computed values in `∃`), standard `cpsTriple_seq_perm_same_cr` doesn't work because the second spec's precondition depends on the existential witnesses.

### Approach: Unfold `cpsTriple` directly

```lean
show cpsTriple base end_ cr P R
intro F hF st hcr hPF hpc
-- Execute first half
obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF st hcr hPF hpc
-- Destructure holdsFor and sep conj
obtain ⟨h_full, hcompat1, ...⟩ := hQF
-- Expand existential def (e.g., loopBodyPostN4)
dsimp only [loopBodyPostN4] at hLP
obtain ⟨x2v, ..., hLP_atoms⟩ := hLP
-- Now have concrete values → instantiate second spec
have h2 := second_spec ... x2v ...
-- Apply second spec with combined frame
obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := h2 (LEFTOVER ** F) ...
-- Chain steps
exact ⟨k1 + k2, s2, stepN_add_eq ..., hpc2, ...⟩
```

### Key techniques

1. **`cpsTriple_seq_ex_same_cr`** (in `DivN4Full.lean`): Helper lemma for composing `cpsTriple s m cr P (fun h => ∃ v, Q v h)` with `∀ v, cpsTriple m e cr (Q v) R`. Handles the `holdsFor`/`sepConj` plumbing internally.

2. **`rw [← sepConj_assoc']`**: Re-associates `P ** (Q ** F)` to `(P ** Q) ** F` — essential for separating the frame F from the combined assertion when constructing the postcondition existentials.

3. **`intro_lets` at hypothesis**: Expands let-bindings from spec postconditions (e.g., `anti_shift`, `u0'`) into local definitions that can be used as existential witnesses.

4. **Combined frame approach**: When applying a `cpsTriple` spec directly (after unfolding), use `hDE (LEFTOVER ** F) hLOF_pcFree s1 ...` to pass both leftover atoms AND the original frame F as the frame parameter. This avoids a separate `cpsTriple_frameR` step and the resulting 36+ atom xperm.

5. **Address canonicalization for `j=0`**: The `j0_*_addr_eq` lemmas convert `u_base`-relative addresses (from `loopBodyPostN4`) to canonical `sp + signExtend12 XXXX` form. Also need `signExtend12_32/40/48/56` to convert `sp + signExtend12 32` to `sp + 32`. Apply these with `simp only [...] at hLP` after `dsimp only [loopBodyPostN4]`.

6. **`pcFree` for combined frames**: The `pcFree` tactic can't see through `let`/`set` definitions. Either inline the frame assertion or use `pcFree; exact hF` when the frame ends with an abstract `F`.

### Import cycle prevention

`DivN4Full.lean` imports both `LoopBodyN4` and `FullPath.lean`. Since `LoopBody.lean` → `Compose.lean` already forms a chain, do NOT add `DivN4Full` to `Compose.lean`'s imports — it would create a cycle. `DivN4Full` stands alone.

## XPerm Scaling Limits and Sub-Assertion Bundling

`xperm_hyp` is O(n^2) in the number of atoms, with each pair comparison
potentially triggering deep WHNF reduction. At ~36 atoms with complex
sub-expressions (e.g., `iterN3Call` + `iterN3Max` iteration results), this
can exceed the 200k heartbeat budget even in a dedicated theorem.

### Symptoms

- `xperm_hyp hp` times out in perm/consequence callbacks
- The same proof structure works for simpler atom expressions (e.g., all
  `iterN3Max`) but fails when atom values involve mixed function calls
- The let-binding chain itself passes `sorry` tests — the timeout is
  specifically in the `xperm` atom matching

### Solution: bundle sub-assertions as `@[irreducible] def`

Wrap logical groups of atoms into `@[irreducible] def`s so that `xperm`
sees a few opaque atoms instead of 36 individual ones:

```lean
-- Instead of 20 flat atoms for denorm input:
@[irreducible]
def denormInputN3 (sp shift u0 u1 u2 u3 q0 q1 b0' b1' b2' b3' : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** ... ** ((sp + 56) ↦ₘ b3')

-- And 16 flat atoms for the frame:
@[irreducible]
def denormFrameN3 (sp base r0_u4 r1_u4 r0_q a0 a1 a2 a3 b2' u2 : Word) : Assertion :=
  ((sp + 0) ↦ₘ a0) ** ... ** (sp + signExtend12 3944 ↦ₘ div128Un0 u2)
```

Then `xperm` only matches 2-3 opaque atoms instead of 36, avoiding
the O(n^2) blowup. Each sub-assertion is unfolded via `delta` only
when needed (e.g., in the denorm epilogue's own pre-weakening callback).

### When to apply

When a composition has **30+ atoms** in the intermediate assertion and
the atom values involve **two or more complex functions** (e.g., mixed
`iterN3Call`/`iterN3Max` results). Same-function compositions (all
`iterN3Max`) tend to stay within budget because `isDefEq` is faster
when comparing structurally similar expressions.

### Guideline for new compositions

- Keep each `xperm` call to **≤ 20 atoms** with complex sub-expressions
- For multi-iteration loops, define per-iteration postconditions as
  `@[irreducible] def`s (already done: `loopBodyN3SkipPost`, etc.)
- For full-path compositions, also bundle the denorm input and frame
  groups as `@[irreducible] def`s

## Double-Addback (_da) Postcondition Pattern

The double-addback fix (BEQ instruction after addback) introduces a second
addback path when carry=0. The `_da` postconditions use `@[irreducible]`
definitions at two levels — the iteration function and the postcondition —
with equation lemmas bridging between the raw spec output and the collapsed
postcondition. This keeps **producers** cheap (single `rw`) and
**consumers** cheap (single `xperm_hyp`, no case-split).

### Architecture

```
iterN3Max_da          @[irreducible]  — collapsed 6-tuple with double-addback
loopIterPostN3Max_da  @[irreducible]  — loopExitPostN3 with iterN3Max_da values
```

**Producer** (per-iteration _da spec, e.g., `divK_loop_body_n3_max_unified_j1_da_spec`):
- Branches on borrow (`by_cases hb`), dispatches to beq or skip sub-spec
- Wraps postcondition via `rw [← loopIterPostN3Max_da_addback ... hb]` or `_skip`
- For j=0 call-path: also `rw [loopBodyN3CallAddbackBeqPost_eq_J]` to bridge
  the j=0-specific variant to the generic-j equation lemma

**Consumer** (per-path composition, e.g., `divK_loop_n3_max_max_da_spec`):
- `delta loopIterPostN3Max_da loopExitPostN3 loopExitPost at hp` — expands
  the `@[irreducible]` postcondition to raw atoms with opaque
  `(iterN3Max_da ...).X` projections
- `simp only [] at hp ⊢` — normalizes let-bindings
- Address rewrites + `xperm_hyp hp` — single permutation pass, no case-split

### Equation lemmas (in LoopDefs.lean)

Each postcondition has two equation lemmas proved once:

```lean
theorem loopIterPostN3Max_da_addback (sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word)
    (hb : BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) ...)) :
    loopBodyN3AddbackBeqPost sp j (signExtend12 4095) v0 ... u_top =
    loopIterPostN3Max_da sp j v0 ... u_top := by
  delta loopIterPostN3Max_da iterN3Max_da iterWithDoubleAddback
        loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN3 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_pos hb]; split <;> rfl
```

The `split <;> rfl` handles the inner carry=0 conditional: after resolving
the outer borrow `if`, both sides have the same `if carry = 0 then ... else ...`
structure. `split` case-splits on carry, then `rfl` closes each branch since
the tuple projections match the conditional values.

### Why this scales

- **No heartbeat issues**: Consumers never expand `iterN3Max_da` (it's
  `@[irreducible]`), so `simp` and `xperm_hyp` see small terms
- **Single xperm_hyp**: The connecting function in multi-iteration compositions
  does ONE permutation pass on ~25 atoms with opaque iter_da projections,
  identical in cost to the non-_da version
- **Equation lemmas amortize**: The `delta + simp + split <;> rfl` work is done
  once per equation lemma, not repeated in every consumer

### Scratch cell handling for unified postconditions

When the outermost iteration (j=2 for N=2, j=3 for N=1) takes the call path,
it overwrites scratch cells with div128 values. The unified postcondition
(`loopN2UnifiedPost_da`) must conditionally set scratch values:

```lean
let scratch_ret := if bltu_2 then (base + 516) else ret_mem
let scratch_d   := if bltu_2 then v1 else d_mem
...
```

After `cases bltu_2`, use `simp only [Bool.false_eq_true, ↓reduceIte]` (max path)
or `simp only [ite_true]` (call path) to resolve these conditionals before
`xperm_hyp`.

### BLTU projection for N=k

The BLTU condition for iteration N=k compares `un_{k-1}` (the (k-1)-th
u-component) with `v_{k-1}`. In the 6-tuple `(q, un0, un1, un2, un3, u4)`, projections are:
`.1`=q, `.2.1`=un0, `.2.2.1`=un1, `.2.2.2.1`=un2, `.2.2.2.2.1`=un3, `.2.2.2.2.2`=u4.
The BLTU compares `un_{N-1}` with `v_{N-1}`:
- N=1: compare `un0` = `.2.1` with `v0`
- N=2: compare `un1` = `.2.2.1` with `v1`
- N=3: compare `un2` = `.2.2.2.1` with `v2`

Be careful with the projection depth — off-by-one here causes type mismatches
that are hard to diagnose (the error appears at the `hbltu` application site,
far from the definition).

## Roadmap (PLAN.md)

The project roadmap is maintained in `PLAN.md`. See `CLAUDE.md` for the
maintenance protocol (when and how to update it).

## New opcode conventions (OPCODE_TEMPLATE.md)

Before starting a new opcode subtree (SDIV, SMOD, ADDMOD, MULMOD, EXP, …),
read **[`EvmAsm/Evm64/OPCODE_TEMPLATE.md`](EvmAsm/Evm64/OPCODE_TEMPLATE.md)**.
It codifies the directory layout, unified-dispatch-first rule, named offset
constants, address grindset, validity bundling, and review checklist
distilled from the DivMod retrofit work. Landing a new opcode on this
substrate from day one avoids the retrofit tax documented in issues
#262 / #263 / #264 / #265 / #266 / #283 / #301 / #312.
