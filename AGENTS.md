# AI Agent Guide for EvmAsm

Guidance for AI agents working on the EvmAsm project. This page is the compact
router: non-negotiable rules + where to find everything else. Deep material is
in `docs/agents/` — load a deep page only when its trigger applies.

## What this project is (and where it's going)

EvmAsm is a **verified macro assembler for RISC-V in Lean 4** (in the lineage of
"Coq: The world's best macro assembler?", Kennedy et al., PPDP 2013), applied to
one goal: a **formally verified zkEVM stateless guest**. The guest
(`stateless_guest`, run under the ZisK zkVM / `ziskemu`) validates an Ethereum
execution payload against a witness; the north-star theorem is
`run_stateless_guest_spec` (`EvmAsm/Stateless/EntrySpec.lean`) — the emitted
guest's output is correct per the `SpecRef` port of
`execution-specs`' `run_stateless_guest`.

Two layers, with a CI-enforced boundary (`check-layering.sh`):

- **The verified core** (`EvmAsm/` except `Codegen/`/`Tests/`/`Examples/`):
  machine model, separation logic, proofs, the executable spec ports. The core
  must NEVER import `Codegen`.
- **`EvmAsm/Codegen/`**: the *unverified-but-emitted* guest (asm strings,
  emission, region maps, probes) that the verification is progressively
  replacing routine-by-routine. Verified ↔ emitted correspondence is tied by
  byte-identity `_eq_prog` drift guards or full re-emit gates (EEST A/B) — see
  `docs/agents/verified-replacement-strategy.md`.

**The center of gravity is the `evm-asm-4ch8f` epic** ("replace every guest
routine with a verified triple"). The per-opcode Evm64 track that built this
substrate is largely complete (52 opcodes, kernel-checked registry in
`EvmAsm/Progress.lean`); most new work is porting guest routines, in
callee-first order, against the separation-logic state-assertion vocabulary.

## Start here

1. **What to work on**: the in-repo sources are `PLAN.md` (roadmap; see
   `CLAUDE.md` for its maintenance protocol) and
   `docs/agents/top-theorem-ledger.md` (what remains for the north star).
   Work items are coordinated in an external issue tracker ("beads", ids like
   `evm-asm-4ch8f.75.1`) that most agents do NOT have access to — treat bead
   ids appearing in docs/PRs as opaque work-item references; if your session
   does have the tracker, use it, otherwise your task assignment supersedes.
2. Starting any 4ch8f bead → `docs/agents/roadmap-4ch8f.md` (layer DAG,
   pick-next rules, recipe table).
3. Verifying one routine → `docs/agents/port-playbook.md` (mechanics) +
   `docs/agents/verified-replacement-strategy.md` (what to prove, spec shape,
   what to do when a callee doesn't expose enough); **sp-frame routines**
   (stack frame + callee-saved regs, loops, cross-calls) →
   `docs/porting-sp-frame-routines.md` (FramePort tactics, tiered recipe).
4. What remains for the north star → `docs/agents/top-theorem-ledger.md`.
5. Reviewing a PR → `docs/agents/review-playbook.md`.

## Build System

- **Build tool**: Lake; **toolchain** pinned in `lean-toolchain`.
- `lake build` (library `EvmAsm`, sources under `EvmAsm/`); heartbeat/recursion
  limits are configured globally in `lakefile.toml` — never per-file.

## Project Structure

```
EvmAsm/
  Rv64/                -- RV64IM machine model + proof infrastructure
    Basic/Instructions/Program/Execution -- machine state, semantics, step fn
    SepLogic.lean      -- Assertions, sepConj, pure embedding (assertPure)
    CPSSpec.lean       -- cpsTripleWithin Hoare triples + structural rules
    MemRegion.lean     -- bytesRegion byte-region primitive
    ByteOps.lean       -- extractByte/packBytes algebra, LBU/SB specs
    SAsm/              -- structured assembly: Fn/Stmt combinators (while,
                       --   doWhile, whileBreak, call/callReg), vcgen,
                       --   PhaseSplit (anyBytes/aliased-arena views)
    Tactics/           -- xperm, runBlock, seqFrame, WP, extract_pure, ...
  Evm64/               -- 256-bit EVM opcodes on RV64 (4×64-bit LE limbs)
    Basic.lean, Stack.lean            -- EvmWord; evmWordIs/evmStackIs
    StateAssertions.lean, StorageAssertions.lean, MptAssertions.lean,
      WitnessAssertions.lean          -- the state-assertion vocabulary
    Add/, MLoad/, ...                 -- per-opcode subtrees (proven specs)
    EvmState.lean, InterpreterLoop*   -- executable interpreter models
  EL/                  -- pure Ethereum EL specs (RLP, WorldState; no RISC-V)
  Stateless/           -- the stateless-guest port: SpecRef/ (executable port
                       --   of execution-specs), EntrySpec.lean (top theorem),
                       --   SSZ/, Witness/, State/ (incl. AccountAssertions)
  Codegen/             -- UNVERIFIED emitted guest: Programs/ (asm strings),
                       --   Dispatch, RegionMap/CallFrameLayout/CallFramePhase,
                       --   Proofs/ (handler specs, guest image), emitters
  Progress.lean        -- kernel-checked opcode registry + witness abbrevs
                       --   (check-axioms.sh audits every @-ref'd witness)
EvmAsm.lean            -- root umbrella (see Common Pitfalls: new files must
                       --   be reachable from here)
```

## Verification Workflow

1. **Build first** (`lake build`) to see the current error state; iterate
   incrementally (helper lemmas before the main theorem).
2. If the lean-lsp MCP server is available, `lean_goal` /
   `lean_diagnostic_messages` beat rebuild loops for inspecting proof states.
3. **Test concretely** with `decide` before generalizing (NOT
   `native_decide`/`bv_decide` — both forbidden and CI-gated; the kernel's
   GMP-backed `Nat` makes `decide` fast even on concrete 256-bit `BitVec`
   goals).
4. When stuck, route by symptom: `docs/sasm-howto.md` §8 →
   `docs/agents/proof-patterns.md` → `GRIND.md`.

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

- **Read-only memory in SAsm specs stays read-only.** If a routine reads from a
  second input buffer that the caller owns as immutable/ambient memory, do not
  model that buffer as an `rw` region just because the current `Fn.region` is
  the primary mutable focus. Keep the writable focus on the actual mutable
  region, carry the read-only buffer in the ambient assertion (typically
  `A = bytesRegion ptr bytes`), and use `.readAt` with a stable base register
  plus a focus relation for the read-only bytes. If the routine has two input
  buffers and actual callsites guarantee non-overlap, make disjointness a
  static precondition after checking every callsite; do not infer it from the
  memory model. Example: `bnfEq32Fn_spec` keeps `a1` as an ambient read-only
  `bytesRegion`, preserves stable `x11`, uses cursor `x7` only for loads, and
  requires the two 32-byte ranges to be disjoint.

- **Do NOT add `set_option maxHeartbeats` to any file** unless you are in `Evm64/Shift/` composition files (Compose, ShlCompose, SarCompose) for body/path composition proofs. Heartbeat limits are configured globally in `lakefile.toml`.
- **Do NOT add `set_option maxRecDepth` to any file.** Recursion depth is configured globally in `lakefile.toml`.
- If a proof times out or hits recursion limits, restructure the proof (e.g., split into smaller lemmas, use intermediate `have` bindings) rather than increasing limits. Increasing `maxRecDepth`/`maxHeartbeats` is almost always a waste of time — the real issue is typically a unification mismatch, wrong argument order, or missing address canonicalization.
- **Do not bump `maxHeartbeats` to make a slow proof compile.** Large heartbeat budgets just slow experiments — and the effect compounds: every retry, every edit, every CI run pays the cost. Needing monitors or `sleep` loops to wait for a build is itself a symptom that `maxHeartbeats` is too big. If a proof legitimately needs more than the default, it is too complicated — diagnose what is actually slow (a failing `rfl`, a stuck `xperm_hyp`, an accidentally false goal, or an `xperm` target with too many conjuncts) and simplify by:
  1. Splitting the proof into smaller named lemmas.
  2. Marking expensive intermediate definitions `@[irreducible]` and proving a small set of lemmas about them, so later proofs unfold via those lemmas instead of re-reducing the body each time.
  3. Breaking up large `have`s into separate lemmas so the core composition step has fewer atoms to permute.
  4. For straight-line SAsm ports with many memory writes, keeping the emitted body byte-identical as one `.block` is fine, but move the large `blockVCs` proof into named helper lemmas. Normalize concrete address offsets in those helpers before handing the range/alignment tail to `simp`/`omega`; otherwise Lean may expand `BitVec.toNat` modulo arithmetic and lose the simple offset fact.
  5. In `vcgen` post cases, avoid closing large final-state equalities with bare `rfl`. Nontrivial definitional equality can timeout instead of failing clearly. Prove a small execution/engine lemma for the flattened body, rewrite the post target with it, then bridge to the semantic postcondition with an explicit list/value lemma.
  6. For byte-identical bottom-test loops (`Stmt.doWhile`), remember that `inv i` is after the `(i+1)`-th body execution. In the `inv_init` VC, `vcgen` may expose the loop-entry writable bytes under a generated local witness rather than the theorem parameter name; destruct the `sp` hypothesis and use that local witness. In the final post, use the failed guard to prove the exact terminal index, not just the fuel bound.
  7. In SAsm memory VCs, if the hypothesis is `ws.length = (someFn ...).rw.len`, prefer `change ws.length = <literal> at h_len` when the literal is known. `simpa [someFn] using h_len` can unfold the whole `Fn` (including body/post) and hit recursion limits for no useful reason.
  8. When scaling byte-dispersal converter proofs (`*_le_to_be`) to a wider field element, audit all width-coupled constants together: `rw.len`, `frameOk`, outer-loop fuel/terminal guard, destination base offset (`len - 1`), slice offset (`len - 8`), source limb list in the post, and the final byte-list split. If the old proof got `ring` transitively from a sibling converter import, add `Mathlib.Tactic.Ring` explicitly before deleting that import.

- **SAsm fixed byte loops:** for bottom-test byte loops like `blk2_st_le64`, keep the window post as a simple prefix/suffix splice (`targetBytes.take i ++ orig.drop i`) and split three lemmas before `vcgen`: one-byte splice, symbolic `execBlock` engine, and counter-nonzero bound. In `inv_step`, derive the `i + 1 < fuel` bound from the loop guard before calling the engine; otherwise `omega` sees only `i < fuel` and the final iteration looks reachable.
- **Large-post `xperm`/`whnf` blowups and framed-pure extraction** (DivMod-scale
  posts, `extract_pure`/`drop_pure` struggles): fold posts behind
  `@[irreducible]` helpers and extract pures one layer at a time — full
  recipes moved to `docs/agents/proof-patterns.md`
  §"Folded framed posts" (tracking issue #7174).
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

### SAsm Proof Repair Notes

- When `rfl` on a generated SAsm equality times out or spins, assume the equality
  is nontrivial before increasing budgets. Split the proof into named helper
  lemmas that expose the exact register/memory update being used, then rewrite
  with those helpers. This was the difference between a timeout-shaped failure
  and a small proof for `u256FromU64BeFn_spec`.
- For large straight-line or loop bodies, keep `blockVCs` proofs separate from
  the semantic engine lemma. Prove load/store routing and alignment in a
  dedicated helper, and make widths explicit with `change` when `omega` is
  seeing an opaque `nbytes` projection instead of a numeral.
- In `vcgen` cases, generated `sp` hypotheses often substitute names away with
  `rfl`, so do not rely on user-chosen names surviving destructuring. Also
  reduce `(fn ...).region`/`rw.base` before rewriting with an engine lemma;
  a mismatch between `(fn ...).region` and `{ base := ..., bytes := ... }` can
  make an otherwise exact rewrite fail.
- For top-tested `whileHeader` loops whose counter is decremented in the body,
  derive the final pre-step bound from the taken guard (`Cond.holds`) and the
  counter invariant before calling `omega`. The fuel bound alone may still
  admit the exhausted state, producing impossible goals one iteration too late.
- For SAsm loops that read immutable `Fn.region` bytes with `LBU` and have an
  empty writable region, `execInstrRF_lbu_byte` is the wrong helper: it models
  reads routed through `rw`. Use a small read-only `LBU` helper that rewrites
  through `Region.byteAt` after proving `¬ inRw` for the empty `rw` window.
- Descending pointer loops can have a terminal wrapped pointer (`src - 1`) even
  when all loaded byte offsets are natural numbers. Avoid invariants of the
  form `src + BitVec.ofNat _ (7 - k)` at the final state; use an explicit
  finite offset helper and prove the load-address and post-step-pointer lemmas
  separately.
- When adapting a proven SAsm loop to a larger buffer, do not globally replace
  numeric substrings. Buffer counts like 12/24 are ghost/spec constants, but
  instruction immediates still use `BitVec 12` and `signExtend12`; changing those
  silently produces bad imports or non-RISC-V-width instructions.
- For byte-zero loops, prove the byte window step with `setBytes_singleton`
  and make the tail append explicit before rewriting `List.replicate`. The
  stable shape is `(replicate i 0 ++ [0]) ++ tail`, then
  `← List.replicate_append_replicate`; using `List.replicate_succ` rewrites to
  the head-cons form and does not match the window suffix proof.
- For byte-copy loops, distinguish writable-window byte loads from read-only
  source loads. `execInstrRF_lbu_byte` is for `LBU` inside the writable region;
  source-copy loops normally need a local `execInstrRF_lbu_ro` miss lemma plus
  `execInstrRF_sb_byte` and `truncate_zeroExtend_byte` for the store. For
  one-byte window steps, `List.take_add` and `List.take_one_drop_eq_of_lt_length`
  avoid brittle deprecated `take_succ` rewrites.
- For straight-line copy ports, avoid proving the semantic engine by repeatedly
  reassociating appended instruction chunks unless the append lemma is already
  a local simplifier. A failed append rewrite can leave huge nested `execBlock`
  projections. The stable pattern is explicit per-pair `LD`/`SD` rewrites plus
  a separate semantic fold lemma (`copyFold64`-style) that rewrites the nested
  `setBytes` chain to the source bytes.
- For straight-line SAsm store blocks, the final instruction's `blockVCs` tail is
  `True`, so rewriting that last `execInstrRF` in the memory-VC simp set is often
  unused and trips the warning gate. For post proofs, rewrite each store with
  `execInstrRF_sd_dword`, then run `simp only` to collapse pair projections
  before applying the semantic `setBytes` lemma. Avoid `subst` on huge
  `execBlock` equalities; rewrite with the equality instead.

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

All examples and `#guard`s must pass with zero sorries/warnings: `lake build`.

### Codegen & ziskemu round-trips

Verified `Program`s are emitted to RV64 ELFs and run on `ziskemu` — roadmap in
[`CODEGEN.md`](CODEGEN.md). Per-milestone end-to-end regressions live in
`scripts/codegen-*.sh` (toolchain smoke, `evm_add` from `.data` and from
`ziskemu -i`); they need `riscv64-elf-binutils` + `ziskemu` on the host.
`EvmAsm/Codegen/RoundTripTests.lean` (`#guard` per `Instr` constructor → GNU-as
line) is the build-time gate for `emitInstr` drift. The conformance harness for
guest changes is `scripts/codegen-eest-stateless-check.sh` (EEST A/B).

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

- [`docs/agents/roadmap-4ch8f.md`](docs/agents/roadmap-4ch8f.md) — the epic's master map:
  layer DAG + pick-next rules, recipe-by-routine-shape table, the gate matrix (what CI runs
  vs what you must run per change type), non-negotiable conventions, the family-bead
  decomposition pattern, and the session-knowledge index ("where the bodies are buried").
  **Load when:** starting ANY 4ch8f bead, or unsure what to pick up next.
- [`docs/agents/review-playbook.md`](docs/agents/review-playbook.md) — how to review a PR
  here: per-PR-type gate checklists (the ones CI does NOT run), the adversarial
  statement-reading checklist, and the known-hole catalog (every entry was a real defect
  caught in review). **Load when:** reviewing any PR.
- [`docs/agents/port-playbook.md`](docs/agents/port-playbook.md) — THE entry point for
  verifying one guest routine end-to-end: class decision table → exemplar → recipe →
  acceptance (`scripts/port-check.sh`, `scripts/gen-port-kit.py` scaffolds).
  **Load when:** working any `port: verify …` bead or any 4ch8f routine-family bead.
- [`docs/agents/verified-replacement-strategy.md`](docs/agents/verified-replacement-strategy.md) —
  the strategy layer above the port playbook: the drop-in principle (functional
  drop-in, NOT byte equality — and the two byte-tie strategies with their gates),
  how to formulate a routine's specification (vocabulary altitude, value-carrying
  assertions, honest domains, outcome disjunctions), and the escalation ladder for
  when a verified callee doesn't expose enough (bridging lemma → variant theorem →
  reframe → strengthen → re-emit → STOP-and-file-bug).
  **Load when:** replacing an unverified routine with a verified one, deciding what
  a routine's spec should say, or blocked on a callee's spec shape.
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

## Conventions with their own pages

- **Roadmap**: `PLAN.md` (maintenance protocol in `CLAUDE.md`).
- **New opcode subtrees** (rare now): read
  [`EvmAsm/Evm64/OPCODE_TEMPLATE.md`](EvmAsm/Evm64/OPCODE_TEMPLATE.md) first —
  directory layout, unified-dispatch-first, named offsets, review checklist.
- **Scratchpad layouts**: routines with `sp`-relative internal scratch take a
  `<Routine>ScratchpadLayout` structure parameter (+ `.Valid`, canonical
  instance) instead of hardcoded offsets — full convention in
  [`docs/scratchpad-layout-design.md`](docs/scratchpad-layout-design.md);
  pilot: `EvmAsm/Evm64/Multiply/Layout.lean`.
