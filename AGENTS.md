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
      Properties.lean  -- Round-trip proofs (kernel-checkable `decide`)
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
3. **Test concretely**: Verify specific cases with `decide` before generalizing (NOT `native_decide`/`bv_decide` — both are forbidden and CI-gated; see CONTRIBUTING.md. The kernel's `Nat` is GMP-backed, so `decide` is fast even on concrete 256-bit `BitVec` goals.)
4. **Incremental development**: Prove helper lemmas before the main theorem

### Proof-tier rubric (`EvmAsm/Progress.lean`)

The kernel-checked progress registry classifies each opcode by a `ProofTier`.
Pick the tier honestly — the registry distinguishes a *complete spec on a
restricted domain* from *half-built work*, and conflating the two is exactly
the statement-vacuity blind spot the dashboard exists to catch:

| Tier | Meaning | Test to apply |
|---|---|---|
| `proven` | A complete top-level stack-level Hoare triple (`evm_<op>_stack_spec_within`) whose conclusion fully specifies the opcode's effect, with **no input-domain precondition**. | Is there a single triple covering *all* operand values? |
| `conditional` | A **complete** top-level triple exists, but it is **gated by a nonvacuous input-domain precondition** that excludes a real region of inputs (e.g. DIV/MOD require `b.getLimbN 3 = 0`, so the full `n=4` divisor path is uncovered; SDIV carries an `hStack` hypothesis). Distinct from `proven` (no restriction) and from `partly` (no complete triple). | Does a complete triple exist, but only under a hypothesis restricting operand values? |
| `partly` | **No** complete top-level triple yet — only an `EvmWord.<op>_correct` arithmetic lemma, a preamble/partial-effect spec, or a sub-component. | Is there real verification work but *no* full triple (not even a restricted one)? |
| `execSpec` | Pure executable-spec / handler / bridge semantics only; no RV64 subroutine produces the EVM result. | — |
| `notStarted` | Not represented in `EvmOpcode` yet (e.g. unimplemented EIPs). | — |

Do **not** mark an opcode `conditional` when the restriction is a single
degenerate point (e.g. ADDMOD's `b=0`-only triple, PUSH2..32's zero-slot-only
triple) — those stay `partly` until a broader triple lands. A `conditional`
entry should, where possible, also name a `…_precondition_reachable` cover
lemma in its `coverRef` slot, proving the gating antecedent is *satisfiable* on
representative real inputs (the anti-near-vacuity check). Per-opcode cycle
bounds live in the typed `cycleBound` field (not free-text `notes`), so a
silent `cpsTripleWithin N` inflation surfaces as a registry diff.

## Critical Rules

- **Naming convention (Mathlib-aligned):**
  - **camelCase** for *value* identifiers: `let`-bound locals, theorem/lemma parameters, function arguments, definitions (e.g. `let qAddr := ...`, `theorem foo (carryNat : Nat)`).
  - **snake_case** for *hypothesis* names — proof bindings introduced by `have h_… : Prop`, `obtain ⟨h_lt, h_eq⟩`, `intro h_pos`, etc. Mathlib keeps these snake_case (e.g. `h_pos`, `h_le`, `h_zero`, `h_eq`). Do **NOT** rename `h_*`-style hypothesis names to camelCase as part of #189 cleanup — that's the wrong direction. PR #1497 made this mistake.
  - When in doubt: if it names a `Prop`-typed term used in a proof, leave snake_case; if it names data (a `Nat`, `Word`, `BitVec`, etc.), use camelCase.

- **Spec design — keep preconditions static; put outcomes in the postcondition.** A subroutine spec's Lean arguments and hypotheses (preconditions) must contain only information that is **statically known or available before the program runs** — base/pointers, lengths, the input bytes, alignment, memory-validity, and size bounds. Whether the run succeeds or fails, and the value it decodes/produces, must **not** appear in the precondition: no hypothesis that pre-decides which branch is taken (e.g. `content[0] ≠ 0`, `len > 32`, `success`), and no precondition phrased as "if the outcome is X then …". Instead, a **unified** spec states every outcome in the **postcondition as a disjunction** — one disjunct per outcome, each carrying its own guard (a static condition like `32 < len`), status code, and result/output assertion. Use a single static upper bound for the step count: `cpsTripleWithin` means "within N steps" (`∃ k ≤ nSteps`), so pick a bound covering all cases and lift each branch's exact count with `cpsTripleWithin_mono_nSteps`. This keeps the theorem easy to apply — a caller supplies only static facts and reads the case analysis back out. Per-outcome sub-specs (one Hoare triple per branch) are fine as building blocks, but the top-level unified theorem must follow this shape. (Example: `EvmAsm/Rv64/RLP/ContentToU256Be.lean`.)

- **Do NOT add `set_option maxHeartbeats` to any file** unless you are in `Evm64/Shift/` composition files (Compose, ShlCompose, SarCompose) for body/path composition proofs. Heartbeat limits are configured globally in `lakefile.toml`.
- **Do NOT add `set_option maxRecDepth` to any file.** Recursion depth is configured globally in `lakefile.toml`.
- If a proof times out or hits recursion limits, restructure the proof (e.g., split into smaller lemmas, use intermediate `have` bindings) rather than increasing limits. Increasing `maxRecDepth`/`maxHeartbeats` is almost always a waste of time — the real issue is typically a unification mismatch, wrong argument order, or missing address canonicalization.
- **Do not bump `maxHeartbeats` to make a slow proof compile.** Large heartbeat budgets just slow experiments — and the effect compounds: every retry, every edit, every CI run pays the cost. Needing monitors or `sleep` loops to wait for a build is itself a symptom that `maxHeartbeats` is too big. If a proof legitimately needs more than the default, it is too complicated — diagnose what is actually slow (a failing `rfl`, a stuck `xperm_hyp`, an accidentally false goal, or an `xperm` target with too many conjuncts) and simplify by:
  1. Splitting the proof into smaller named lemmas.
  2. Marking expensive intermediate definitions `@[irreducible]` and proving a small set of lemmas about them, so later proofs unfold via those lemmas instead of re-reducing the body each time.
  3. Breaking up large `have`s into separate lemmas so the core composition step has fewer atoms to permute.
- **When DivMod postconditions explode under `xperm` or kernel `whnf`:** fold the postcondition before trying harder tactics. Put the final register/memory assertion spine behind a small `@[irreducible]` helper such as `...PostCore`, parameterized by the final values that the branch proof should expose. If the public post has a deep body let-chain, add a second folded helper such as `...PostFromBody` that takes already-computed intermediates; the public `...Post` should compute the lets and delegate to the helper. In branch bridge proofs, use `change` to refold the expanded target to the helper with local names, simplify only the relevant `if_pos`/`if_neg`, then unfold only the small core immediately before `xperm_hyp`. Split repeated bridge obligations into named lemmas for fresh heartbeat budgets. Use `lean_goal` at the failing line to confirm the target is folded; if it prints a huge `BitVec.toNat 32` or nested-let/nested-if term, fold first instead of running `xperm` on the expanded goal.
- **When extracting framed pure facts in bridge posts:** inspect the shape with `lean_goal` before repeatedly applying `drop_pure` or `extract_pure`. Framed pures may remain behind an extra `sepConj` layer, so remove one layer at a time with small local rewrites (`rw [sepConj_assoc']`, `simp only [sepConj_pure_mid_left]`) and `obtain` the pure fact you need. Broad `simp` or blind repeated extraction can expand the folded post again or destruct useful `sepConj` structure.
- **When `extract_pure`, `drop_pure`, or `xperm_pure` struggle on a folded framed post:** avoid broad pure-extraction tactics on the whole post if they expand the folded helper, trigger kernel `whnf`, leave `xperm` atom-count mismatches, or report an expected-type/free-variable error. First extract only the outer pure fact you need, then rewrite the specific remaining pure assertion to `empAssertion` with a local extensional proof and simplify the emp frame before calling `xperm_hyp`. Shape:

  ```lean
  extract_pure hp
  obtain ⟨hp, h_pure⟩ := hp
  rw [show (⌜P⌝ : Assertion) = empAssertion by
    funext h
    unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
    apply propext
    constructor
    · intro h_p
      exact h_p.1
    · intro h_empty
      exact ⟨h_empty, h_pure⟩] at hp
  simp only [the relevant sepConj_emp lemma] at hp
  xperm_hyp hp
  ```

  Keep `EvmAsm.Rv64.pure` qualified in the unfold so Lean does not choose an unrelated `pure`, and keep the target folded until the final local rewrite. Tracking issue: https://github.com/Verified-zkEVM/evm-asm/issues/7174.
- **Exception for Shift composition files**: `set_option maxHeartbeats` up to 6400000 is acceptable for body/path composition proofs (Section 4+) which are bottlenecked by `xperm_hyp` permutation on large atom chains. Subsumption lemmas (Section 2) should NOT need heartbeat overrides — they use structural `unionAll` reasoning.

- **All memory accesses must be aligned.** The verified RV64 operational semantics in `EvmAsm/Rv64/Basic.lean` defines `isValidDwordAccess = isValidMemAddr && isAligned8` and `isValidMemAccess = isValidMemAddr && isAligned4` — i.e. an `LD`/`SD` has no semantics unless its address is a multiple of 8, and `LW`/`LWU`/`SW` likewise need a multiple of 4. Per-width requirements:

  | Op            | Width | Required alignment |
  |---------------|-------|--------------------|
  | `LD`, `SD`    | 8 B   | `addr % 8 == 0`    |
  | `LW`, `LWU`, `SW` | 4 B   | `addr % 4 == 0`    |
  | `LH`, `LHU`, `SH` | 2 B   | `addr % 2 == 0`    |
  | `LB`, `LBU`, `SB` | 1 B   | any                |

  Proofs that reach an unaligned access cannot close — `isValidDwordAccess`/`isValidMemAccess` evaluate to `false`. Ziskemu may tolerate unaligned reads at runtime, but the verified subset does not, so do **not** rely on runtime tolerance when writing new RV64 snippets.

  When the natural source/dest address is unaligned (e.g. SSZ blob base at `INPUT_BASE + 18 = 0x40000012`, mod 4 = 2), pick accesses whose alignment still works (`LBU`/`SB` always do; `LH`/`LHU` at mod 2 = 0; `LWU` at mod 4 = 0; `LD`/`SD` at mod 8 = 0) and reconstruct wider values by shift/OR packing. Pre-existing unaligned reads in `EvmAsm/Stateless/SSZ/Decode/Program.lean` are debt, not a precedent.

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

The project includes concrete test cases using `decide` (kernel-checkable):
- Multiply by constants: 0, 1, 3, 6, 10, 255
- Swap macro correctness
- Zero and triple macros
- ECALL/halt termination examples
- COMMIT-then-halt examples

### Codegen & ziskemu round-trips

Verified `Program`s can be emitted to executable RV64 ELFs and run on
`ziskemu` — see [`CODEGEN.md`](CODEGEN.md) for the roadmap. Three
shell scripts under `scripts/` codify the per-milestone end-to-end
regression:

- `scripts/codegen-smoke.sh` — synthetic `LI/ADD/halt` toolchain check.
- `scripts/codegen-evm_add-check.sh` — verified 256-bit `evm_add` with
  operands baked into `.data`.
- `scripts/codegen-evm_add-from-input-check.sh` — same `evm_add`, but
  operands loaded at runtime from `ziskemu -i <file>`.

Each script builds via `lake exe codegen`, assembles via
`riscv64-elf-as -march=rv64imac`, links with
`-Ttext=0x80000000 -Tdata=0xa0000000`, runs `ziskemu`, and diffs the
public output against the expected value. They require
`riscv64-elf-binutils` and `ziskemu` on the host; use `--asm-only` on
the codegen invocation to skip assembly/link/run.

`EvmAsm/Codegen/RoundTripTests.lean` houses ~60 `#guard` assertions
covering every `Instr` constructor → GNU-as line; failures abort
`lake build`. Treat this as the build-time correctness gate for
`emitInstr` drift.

## Architecture fitness functions (`scripts/check-*.sh`)

The `scripts/check-*.sh` suite **is** a set of *architecture fitness
functions* in the Ford/Parsons sense (*Building Evolutionary Architectures*):
each script is an automated, objective test of a structural property the
kernel cannot see, run in CI so that drift fails the build instead of
accumulating silently. The kernel proves each theorem; these gates protect
the *shape* of the codebase around the proofs. When a prose convention starts
to matter, the move is to **promote it to a check here** rather than restate it
in docs an agent can ignore.

Two tiers, by design (see `docs/agent-progress-steering-review.md` §6 — do not
hard-gate noisy heuristics):

**Blocking gates** (fail the build; wired in `.github/workflows/build.yml`):

| Gate | Invariant enforced |
|------|--------------------|
| `check-forbidden-tactics.sh` | no `native_decide`/`bv_decide` (TCB-expanding) |
| `check-axioms.sh` | witnessed proofs use only the 3 classical axioms |
| `check-progress.sh` / `check-drift.sh` | `PROGRESS.md`/`DRIFT.md` regenerate identically from the kernel registry |
| `check-conformance-floor.sh` | conformance-vector count never silently drops |
| `check-roundtrip-coverage.sh` | every `Instr` constructor has a round-trip `#guard` |
| `check-file-size.sh` | per-file line caps (Evm64 1200/1500; Codegen/Programs 1500, mirroring the `FileSizeGuard.lean` `#eval` that a warm `.lake` cache otherwise skips) |
| `check-unimported.sh` | zero-orphan module graph |
| `check-no-warnings.sh` | clean build log |
| **`check-heartbeats-approved.sh`** | EVERY mention of `heartbeats` (overrides *and* prose) in `.lean`/lakefiles is sanctioned in `scripts/approved-heartbeat-overrides.txt` at its exact value — a dumb substring scan (no lexer to bypass); a ceiling + audit log, never a license to inflate |
| **`check-layering.sh`** | the verified core (core-by-default: all `EvmAsm/` except Codegen/Tests/Examples) never imports the unverified `Codegen` layer (L1), the progress registry (L2), or the Tests/Examples escape hatches (L3) |
| **`check-opcode-structure.sh`** | `AddrNorm.lean`/`AddrNormAttr.lean` co-occur per opcode dir (Lean forbids `register_simp_attr` in its declaring file) |

**Advisory gates** (CI output / review nudges; always exit 0 — promoted to
blocking only after thresholds calibrate, never prematurely):

| Gate | Signal surfaced |
|------|-----------------|
| `check-statement-tamper.sh` | weakened theorem statements / verifier-config edits (advisory in `build.yml`; blocks only with `--strict`, which CI does not pass) |
| **`check-naming.sh`** | camelCase proof hypotheses newly added in a PR (prefer `h_snake_case`; the PR #1497 regression class) |
| **`check-opcode-structure.sh`** (checklist part) | new *complex* opcode dirs missing template essentials (FullPath, `@[irreducible]` Post, `Offsets.lean`) |
| **`churn-report.sh`** | top-churn files + short-lived churn (AI copy-paste sprawl) |
| **`jscpd`** (`scripts/jscpd.json`) | duplication % reported weekly (advisory); `check-duplication.sh --gate` *would* fail on new sprawl past the calibrated budget once promoted, `codegen-*.sh` excluded (Rule of Three) |

When you add a `.lean` file or a new convention, ask whether a fitness function
should fence it — and whether it belongs in the blocking or advisory tier. Seed
new advisory gates green on the current tree; a gate that red-lights day one is
the false-positive friction the steering review warns against.

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

## Bead closure rules (`bd close`)

The beads tracker is the source of truth for outstanding work. Closing a bead
incorrectly hides unfinished obligations and bumping its priority later does
nothing because the bead is no longer in the queue. Before running
`bd close <id>`, satisfy **all** of the following:

1. **The named deliverable must exist on `origin/main`.** If the bead title
   says "prove `foo_spec_within`", "define `evm_foo`", or "lift X to Y", that
   exact declaration has to be present on `origin/main` — not on a feature
   branch, not in an unmerged stacked PR. Verify with:
   `git fetch origin && git grep -n '<decl name>' origin/main -- '<expected path>'`.
   If the grep is empty, **do not close the bead**.

2. **A "related" PR merging is not the same as the deliverable shipping.** A
   PR titled similarly, or that adds scaffolding, wrappers, or preparation
   lemmas around the deliverable, does not satisfy the bead. If the named
   theorem is still a `placeholder`, `sorry`, or absent, the bead stays open.

3. **Stacked PRs into feature branches don't count.** A PR merged into
   `feat/foo` instead of `main` has not landed. Wait for the bottom of the
   stack to merge into `main`, then verify per (1) before closing the
   dependent beads.

4. **`close_reason` must be truthful.** `"shipped in PR #N"` is only valid
   when PR #N's merge commit is an ancestor of `origin/main` *and* the named
   deliverable is grep-visible there. Otherwise use
   `"superseded by <bead-id>"` or `"duplicate of <bead-id>"`. Never close as
   "shipped" against a PR that merged into a feature branch.

5. **If you finished real work but the named theorem isn't done yet**,
   prefer adding a `bd comment` with status, or filing a follow-up bead, or
   updating the existing bead's description — instead of closing the wrong
   thing.

Recent violations to learn from: `evm-asm-01uh` (SDIV), `evm-asm-6snn` and
`evm-asm-w5mk` (EXP) — all closed as "shipped in PR #…" while the named
theorem was still a placeholder on `main` (and in the EXP cases the PR was
merged into a feature branch, not `main`). All three had to be reopened.

## References

- **Accelerator C ABI (source of truth)**:
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`
  is the canonical interface for cryptographic precompiles, KECCAK256, and
  secp256k1 verification. See [`docs/zkvm-accelerators-interface.md`](docs/zkvm-accelerators-interface.md)
  for how it maps to ECALL syscall IDs (which use SP1 transport conventions)
  and to EVM precompile addresses.
- **Original paper**: Kennedy et al., "Coq: The world's best macro assembler?" PPDP 2013
  https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/
- **zkvm_accelerators.h**: `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`
  is the source of truth for accelerator function signatures, argument
  layouts, and `zkvm_status` framing used by all EVM precompile and
  KECCAK256 bridges. See [`docs/zkvm-accelerators-interface.md`](docs/zkvm-accelerators-interface.md).
- **Host I/O C ABI**: `EvmAsm/Evm64/zkvm-standards/standards/io-interface/README.md`
  defines the canonical host-I/O surface (`read_input` / `write_output`).
  See [`docs/zkvm-host-io-interface.md`](docs/zkvm-host-io-interface.md)
  for the decision record and SP1 `HINT_LEN` / `HINT_READ` / `COMMIT` →
  zkvm-standards mapping. Migration tracked under beads parent
  `evm-asm-96ysd` (GH #114 / #116).
- **SP1 zkVM**: https://github.com/succinctlabs/sp1 (RISC-V `ECALL`
  framing only; function set follows `zkvm_accelerators.h`)
- **RISC-V ISA**: https://riscv.org/technical/specifications/
- **sail-riscv-lean**: https://github.com/opencompl/sail-riscv-lean (same toolchain)
- **Lean 4 docs**: https://lean-lang.org/documentation/
- **Notable Specs Index**: [`docs/notable-specs.md`](docs/notable-specs.md) —
  curated index of proven specifications (per-opcode stack specs, EvmWord
  correctness theorems, RLP/ByteOps/calling-convention helpers) with
  commit-pinned permalinks. Use it to find a spec without grepping. Refresh
  procedure is documented at the bottom of that page; trigger is closure of a
  `#61`-class umbrella issue, or quarterly.

## Deep references

Detailed material has been split out of this file to keep the agent guide compact. **Load each
doc only when its trigger applies** — they are reference material, not required reading.

- [`docs/agents/port-playbook.md`](docs/agents/port-playbook.md) — THE entry point for
  verifying one guest routine end-to-end: class decision table → exemplar → recipe →
  acceptance (`scripts/port-check.sh`, `scripts/gen-port-kit.py` scaffolds).
  **Load when:** working any `port: verify …` bead or any 4ch8f routine-family bead.
- [`docs/agents/top-theorem-ledger.md`](docs/agents/top-theorem-ledger.md) — the obligation
  ledger decomposing `run_stateless_guest_spec` (statement: `EvmAsm/Stateless/EntrySpec.lean`)
  into leaf work, with per-row status and exemplars.
  **Load when:** deciding what stateless-guest proof work to pick up, or closing a port bead
  (update the row).
- [`docs/agents/tactics-deep.md`](docs/agents/tactics-deep.md) — Frame-automation tactics,
  separation-conjunction permutation (`xperm`), LP64 calling convention, three-level opcode
  proof architecture, Compose file splitting, file-size guardrail, benchmark-history branch.
  **Load when:** writing/restructuring `runBlock`/`seqFrame`/`xperm`/`xcancel`, designing a
  callable shim, working on a new opcode's three-level proof, or interpreting benchmark history.
- [`docs/agents/wp-framework.md`](docs/agents/wp-framework.md) — Rv64 weakest-precondition
  certificates, CFG composition, branch/join/loop patterns, and automation attributes.
  **Load when:** composing Rv64 assembly proofs with `WP.CFG`, adding WP automation, using
  generated control-flow descriptions, or proving top-level disjunctive decoder specs.
- [`docs/agents/proof-patterns.md`](docs/agents/proof-patterns.md) — Bundling postconditions
  with `let` + `@[irreducible]`, adapter signatures with deep let-chains, `linarith` vs
  `omega`, pure-Nat sub-lemmas for `maxRecDepth` avoidance, end-to-end composition with
  existentials, `xperm` scaling, double-addback (`_da`) postcondition pattern.
  **Load when:** a specific proof symptom matches a section heading (use the index at the top
  of that file). Do not read top-to-bottom — these are deep recipes for narrow situations.
- [`docs/agents/eest-static-layout.md`](docs/agents/eest-static-layout.md) — Lessons for
  EEST stateless static memory layouts: derive capacities from execution-specs protocol/test
  limits, handle BAL's gas-derived item budget, and reject layout-incompatible fixtures before
  launching the guest.
  **Load when:** changing `stateless_guest`, `block_state_root`, BAL replay, EEST manifest
  conversion, or static `.data` arenas used by EEST codegen programs.
- [`docs/agents/stateless-input-contract.md`](docs/agents/stateless-input-contract.md) —
  Byte-level contract for keeping the zkVM stateless guest input content equivalent to
  execution-specs `run_stateless_guest`, including the ziskemu length wrapper boundary and
  rules for derived manifest fields.
  **Load when:** changing `stateless_guest`, EEST fixture conversion, stateless input schema
  offsets, block RLP-size validation, BAL/request/witness decoding, or any runtime data flow into
  the guest.

Companion files (already separate, unchanged):
- [`TACTICS.md`](TACTICS.md) — user-facing tactic reference.
- [`GRIND.md`](GRIND.md) — domain-specific grindset definitions.
- [`PLAN.md`](PLAN.md) — roadmap.
- [`docs/OPCODE_TEMPLATE.md`](docs/OPCODE_TEMPLATE.md) — new-opcode conventions (referenced below).

## Roadmap (PLAN.md)

The project roadmap is maintained in `PLAN.md`. See `CLAUDE.md` for the
maintenance protocol (when and how to update it).

## Scratchpad Layout (#334)

Routines that need `sp`-relative internal scratch cells (DivMod today, EXP /
Multiply with internal scratch later) must take their scratchpad layout as a
**parameter**, not bake offsets into the spec. Hardcoding offsets like
`sp + signExtend12 4056` makes the routine impossible to compose from a
non-trivial caller frame and forces every call site to use the same fixed
placement.

Convention (per `docs/scratchpad-layout-design.md`):

- One `XxxScratchpadLayout` structure per routine, with named fields for
  each scratch cell (e.g. `dividendNorm`, `divisorNorm`, `quotientHi`).
- A companion `XxxScratchpadLayout.Valid (L : XxxScratchpadLayout) : Prop`
  bundling per-cell validity (`isValidDwordAccess`) plus disjointness from
  the caller frame and from each other.
- A `canonicalXxxScratchpadLayout : XxxScratchpadLayout` matching today's
  hardcoded offsets, and a `canonicalXxxScratchpadLayout_valid` instance.
- Specs take `(L : XxxScratchpadLayout) (hL : L.Valid)` as parameters and
  reference `L.fieldName` instead of `sp + signExtend12 N` literals.
- The routine's existing fixed-offset spec stays as a thin shim that
  instantiates the canonical layout, so existing call sites keep compiling.

The naming convention is fixed: `EvmAsm/Evm64/<Routine>/Layout.lean`,
`<Routine>ScratchpadLayout`, `.Valid`, `canonical<Routine>ScratchpadLayout`,
`canonical<Routine>ScratchpadLayout_valid`. Slice 3 (`EvmAsm/Evm64/Multiply/Layout.lean`)
is the canonical empty-layout pilot — copy its file shape when adding scratch
to a new routine.

When introducing a new opcode subtree that will carry internal scratch
(EXP-class routines, future precompiles), define the layout struct from day
one — even if it starts empty — to avoid the retrofit tax. See `docs/scratchpad-layout-design.md`
for the full design and `docs/scratchpad-layout-survey.md` for the
hardcoded-offset inventory that motivated the change.

## New opcode conventions (OPCODE_TEMPLATE.md)

Before starting a new opcode subtree (SDIV, SMOD, ADDMOD, MULMOD, EXP, …),
read **[`EvmAsm/Evm64/OPCODE_TEMPLATE.md`](EvmAsm/Evm64/OPCODE_TEMPLATE.md)**.
It codifies the directory layout, unified-dispatch-first rule, named offset
constants, address grindset, validity bundling, and review checklist
distilled from the DivMod retrofit work. Landing a new opcode on this
substrate from day one avoids the retrofit tax documented in issues
#262 / #263 / #264 / #265 / #266 / #283 / #301 / #312.
