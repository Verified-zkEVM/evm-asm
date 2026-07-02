# SAsm: A Structured Assembly DSL with VC-Generating Verification

Status: design accepted (see "Decisions" below); implementation staged in
milestones. This document is expected to be refined by subsequent commits as
implementation feedback arrives.

## 1. Motivation

The bounded-CPS WP framework (`EvmAsm/Rv64/WP/`, `CPSSpec.lean`) is sound and
composable, but writing and verifying a program with it today costs far more
than it should. The verified RLP withdrawal decoder is the reference data
point: ~58 instructions of program required ~9,500 lines across five files,
dominated by

- hand-built `CodeReq.union` trees and ~92 manual `CodeReq.Disjoint` proofs,
- hand-computed branch/jump offsets (`BEQ x11, x0, 156`) that must be kept in
  sync with block sizes,
- manual composition of `WP.Branch`/`WP.NBranch` exits, one theorem per
  control-flow merge,
- re-stating the full assertion shape (every register atom, every region) at
  every seam.

`run_stateless_guest` (`EvmAsm/Stateless/Entry.lean`) — the intended
verification target — is check-heavy in exactly the way the RLP decoder is:
long chains of format/bounds checks that bail out to failure exits, a few
bounded loops (byte copies, header walks), and calls between routines using
the project's C-like ABI. Verifying it with today's tooling would multiply the
RLP experience by an order of magnitude.

SAsm ("structured assembly") is a DSL layered *on top of* the existing WP
framework that removes each of the costs above by construction:

- **Structure instead of offsets.** Programs are written with `ite`, `when`
  (if-without-else), bounded `while`, and `call`. A flattener computes every
  branch/jump offset and the program's `CodeReq`; disjointness disappears
  because a function's code is one `CodeReq.ofProg` over one contiguous range.
- **One symbolic state instead of N assertion shapes.** Basic blocks operate
  on a fixed *exposed register file*; the DSL derives each block's
  post-state by symbolic execution, so users never write per-block
  register-atom assertions.
- **Pure VCs instead of separation-logic goals.** A VC generator — a plain
  structurally-recursive Lean function, not a tactic — crunches the annotated
  program into a list of *labeled pure propositions*. One generic soundness
  theorem (proved once, by induction on the AST) converts proofs of those VCs
  into the standard `cpsTripleWithin` statement. Proof search never recurses
  over the program, so `maxRecursion`-style failures are avoided by
  construction.

Nothing in the trusted base changes: the final artifact of every SAsm
verification is an ordinary `cpsTripleWithin` about `stepN` over the existing
machine semantics, kernel-checked, closed under the usual three classical
axioms. All proof conventions from `CLAUDE.md` apply (no `native_decide` /
`bv_decide`).

## 2. Decisions (user-confirmed)

Three interface questions were posed and decided 2026-07-01:

1. **VC front-end: tactic with named cases.** A `vcgen` tactic applies the
   generic soundness theorem and splits the VC list into one *named* goal per
   verification condition. Each goal is pure (registers-as-values, `Nat`/
   `BitVec` arithmetic, list facts); the case name encodes the program path
   (e.g. `check_empty_input`, `copy_loop.inv_step`). Failure feedback for the
   agentic workflow is precise: the leftover named goals *are* the report.
2. **Block leaves: raw instruction lists.** Basic blocks are `List Instr`
   exactly as everywhere else in the repo; the DSL adds structure around them
   and derives their semantics by symbolic execution. This reuses the
   instruction set, the codegen pipeline, and auditability of the emitted
   assembly.
3. **Annotations: inline in the AST.** Loop invariants, bounds, and optional
   mid-conditions are nodes/fields of the program term itself; a function's
   pre/post live in the `Fn` record next to its body.

## 3. Architecture

```
        user writes                        SAsm derives
  ┌───────────────────────┐      ┌────────────────────────────────┐
  │ Fn record:            │      │ Fn.program  : Program (flat)   │
  │  pre/post (pure, over │ ───▶ │ Fn.codeReq  : CodeReq.ofProg   │
  │  exposed reg file)    │      │ Fn.steps    : Nat (step bound) │
  │  regions (spatial)    │      │ Fn.vcs      : List VC (labeled │
  │  body : Stmt          │      │               pure Props)      │
  └───────────────────────┘      └────────────────────────────────┘
                                              │
                     Fn.sound : VCs.Hold f.vcs → Fn.Spec f base
                                              │
                                              ▼
                    cpsTripleWithin f.steps base exit f.codeReq P Q
```

Layer by layer, bottom-up:

### 3.1 Exposed register file (`SAsm/RegFile.lean`)

A fixed set of registers is *exposed* to SAsm basic blocks:

```
exposed := [x5, x6, x7, x28, x29, x30, x31,      -- t0–t6 (scratch)
            x10, x11, x12, x13, x14, x15, x16, x17]  -- a0–a7 (args/returns)
```

`x0` is handled specially (always 0). `x1` (ra), `x2` (sp), and the s-registers
are *not* exposed: `ra`/`sp` are owned by the call machinery (§3.6), and
s-registers are left to the frame (a leaf SAsm function neither reads nor
writes them, so the built-in frame rule of `cpsTripleWithin` preserves them
for free).

```lean
def RegFile := ExposedReg → Word          -- ExposedReg: subtype/enum of the 15
def RegFile.get  : RegFile → Reg → Word   -- x0 ↦ 0; non-exposed: junk (unused)
def RegFile.set  : RegFile → Reg → Word → RegFile

/-- Ownership of exactly the exposed registers, with values `rf`. -/
def regFileIs (rf : RegFile) : Assertion :=
  fun h => h = PartialState.ofRegFile rf     -- pc-free by construction
```

Defining `regFileIs` as a single `PartialState` equality (like
`regIs`/`memIs`) rather than a 15-way `**` chain is deliberate: block
soundness then needs *one* generic per-instruction lemma instead of
permutation reasoning over a big separating conjunction, and `xperm`-style
atom-count blowups (see `build_perf_findings`) never occur, because to the
sep-logic layer the whole register file is one atom.

Bridging lemmas connect `regFileIs rf` with the atom form
(`(.x5 ↦ᵣ rf .x5) ** …`) in both directions, so SAsm specs compose with
existing hand-written specs at function boundaries.

### 3.2 The AST (`SAsm/Ast.lean`)

```lean
/-- Branch conditions available to structured control flow: exactly the
    RV64 conditional branches, over exposed registers. -/
inductive Cond where
  | beq | bne | blt | bge | bltu | bgeu   -- each carries (rs1 rs2 : Reg)

def Cond.holds : Cond → RegFile → Prop    -- e.g. bltu: BitVec.ult (rf rs1) (rf rs2)
def Cond.neg   : Cond → Cond              -- beq↔bne, blt↔bge, bltu↔bgeu
def Cond.toInstr : Cond → BitVec 13 → Instr

inductive Stmt where
  /-- Straight-line block of raw instructions from the supported subset. -/
  | block  (label : String) (instrs : List Instr)
  | seq    (a b : Stmt)                                           -- a ;; b
  | ite    (label : String) (c : Cond) (thn els : Stmt)
  | when   (label : String) (c : Cond) (body : Stmt)              -- if, no else
  /-- Optional mid-condition: no code, cuts the reachable-state set. -/
  | assert (label : String) (P : RegFile → Prop)
  /-- Bounded loop: body runs while `c` holds, at most `fuel` iterations.
      `inv i` must hold on entry to the i-th header evaluation. -/
  | while  (label : String) (c : Cond) (fuel : Nat)
           (inv : Nat → RegFile → Prop) (body : Stmt)
  /-- Direct call to a routine with a registered interface (§3.6). -/
  | call   (label : String) (f : FnHandle)
```

Notes:

- Labels name VCs; they need not be globally unique — the VC generator
  prefixes them with the path (e.g. `outer.body.check_len`).
- `inv`'s `Nat` index is the iteration counter, matching `WP.loopNatCert`.
  Invariants over other ghost data (decoded prefixes, offsets) use ambient
  Lean binders: an SAsm function is defined inside ordinary `variable`s /
  parameters, so `inv`, `assert`, `pre`, `post` may all mention them freely.
- Ghost-state generality: because annotations are arbitrary
  `RegFile → Prop` over ambient binders, the DSL is not RLP-specific;
  any effect expressible in the separation logic can appear in the spatial
  part (§3.3) and any functional property in the pure part.

Sequencing sugar: `a ;;; b` (or reuse a `do`-like macro layer later —
cosmetic, out of scope for v1).

### 3.3 Spatial state: regions (`SAsm/Region.lean`)

Check-heavy code (RLP, SSZ) reads from byte buffers and writes results.
SAsm models spatial state as a list of *regions* owned by the function:

```lean
structure Region where
  base  : Word
  bytes : List Byte          -- current contents
  mode  : Region.Mode        -- .ro (read-only) or .rw

def regionsAssert : List Region → Assertion   -- ⋆ of bytesRegion-style atoms
```

- v1 (Milestones 1–3): `.ro` regions only. Loads (`LBU`/`LHU`/`LWU`/`LD`)
  from an in-range address of a `.ro` region symbolically evaluate to the
  known byte(s); the in-range condition becomes a labeled VC. The regions
  assertion is invariant across the function, so the sep-logic side never
  changes shape — this already covers the *checking* half of RLP decoding.
- v2 (Milestone 5b-2, **landed shape**): one read-only `Region` (base +
  ghost bytes) plus one writable `RwRegion` (base + length; the *contents*
  are part of the symbolic state).  `Reach` is
  `RegFile → List Byte → Prop` — register file plus the writable region's
  current bytes; `asrtOf rw reach` existentially bundles both with the
  byte count pinned to `rw.len`.  Loads route by address: an access fully
  inside the writable window reads the symbolic contents, everything else
  reads the read-only region (the per-load VC follows the same split).
  Overlapping regions need no side condition — the separation conjunction
  makes them unsatisfiable.  Stores (to the writable region only) update
  the symbolic bytes via `setBytes`.
- Other effects (syscalls/hints, publicValues, …) are future extensions at
  the same seam: enlarge `SymState` and the per-leaf soundness lemmas;
  the structural rules (§3.5) do not change.

### 3.4 Block symbolic execution (`SAsm/Sym.lean`)

Two plain functions over the supported instruction subset:

```lean
/-- Forward symbolic execution of a straight-line block. -/
def execBlock (regions : List Region) : RegFile → List Instr → RegFile

/-- Side conditions collected along the way (load in-range, alignment,
    instruction supported). Pure, decidable-or-arithmetic shaped. -/
def blockVCs (regions : List Region) : RegFile → List Instr → Prop
```

Supported subset in v1: ALU reg/imm ops (`ADD(I)(W)`, `SUB`, `AND(I)`,
`OR(I)`, `XOR(I)`, `SLL(I)`, `SRL(I)`, `SRA(I)`, `SLT(I)(U)`), constants
(`LI`, `LUI`, `MV`, `NOP`), `MUL`-family, and `.ro` loads. Everything else
(stores, `ECALL`, …) is rejected by `blockVCs` with a `False`-shaped VC that
names the offending instruction — the failure mode is a readable goal, not a
stuck tactic.

The single enabling soundness lemma, proven once, generically:

```lean
theorem execBlock_sound :
    blockVCs regions rf instrs →
    cpsTripleWithin instrs.length base (base + 4 * instrs.length)
      (CodeReq.ofProg base instrs)
      (regFileIs rf ** regionsAssert regions)
      (regFileIs (execBlock regions rf instrs) ** regionsAssert regions)
```

by induction on `instrs`, with one lemma per supported instruction shape
(mirroring `generic_1reg_spec_within` but stated against `regFileIs`).

### 3.5 VC generation and soundness (`SAsm/Vcgen.lean`, `SAsm/Sound.lean`)

The core is a strongest-postcondition–style generator over the pure
abstraction. `Reach := RegFile → Prop` is the abstract reachable-state set
(v2: over `SymState`).

```lean
structure VC where
  label : String
  prop  : Prop

/-- (VCs of this statement, reachable set at its exit). Structurally
    recursive — unfolds in time linear in the AST, independent of proof
    search. -/
def Stmt.spgen (regions) : Stmt → (reach : Reach) → List VC × Reach
  | block l is  => ([⟨l ++ ".ok", ∀ rf, reach rf → blockVCs regions rf is⟩],
                    fun rf' => ∃ rf, reach rf ∧ rf' = execBlock regions rf is)
  | seq a b     => let (v₁, r₁) := a.spgen reach
                   let (v₂, r₂) := b.spgen r₁
                   (v₁ ++ v₂, r₂)
  | ite l c t e => let (v₁, r₁) := t.spgen (fun rf => reach rf ∧ c.holds rf)
                   let (v₂, r₂) := e.spgen (fun rf => reach rf ∧ ¬ c.holds rf)
                   (v₁ ++ v₂, fun rf => r₁ rf ∨ r₂ rf)
  | when l c b  => -- ite with skip else-branch
  | assert l P  => ([⟨l, ∀ rf, reach rf → P rf⟩],
                    fun rf => reach rf ∧ P rf)          -- cut strengthens
  | while l c n inv b =>
      let (vb, rb) := b.spgen (fun rf => ∃ i < n, inv i rf ∧ c.holds rf)
      ([⟨l ++ ".inv_init⟩", ∀ rf, reach rf → inv 0 rf⟩,
        ⟨l ++ ".inv_step",  ∀ i < n, ∀ rf', rb… → inv (i+1) rf'⟩,   -- see below
        ⟨l ++ ".fuel_exhausted", ∀ rf, inv n rf → ¬ c.holds rf⟩] ++ vb,
       fun rf => ∃ i ≤ n, inv i rf ∧ ¬ c.holds rf)
  | call l f    => ([⟨l ++ ".pre", ∀ rf, reach rf → f.pre rf⟩],
                    fun rf' => ∃ rf, reach rf ∧ f.postRel rf rf')
```

(The `inv_step` VC is generated with the body's reach threaded per iteration
index `i`; the sketch above elides the index plumbing that the implementation
carries through `spgen`.)

The generic soundness theorem, proven **once** by structural induction on
`Stmt`, maps each constructor onto the existing WP combinators:

| AST node | WP machinery used |
|---|---|
| `block`  | `execBlock_sound` (§3.4) |
| `seq`    | `WP.Triple.seq` / `cpsTripleWithin_seq_same_cr` |
| `ite`/`when` | `generic_b*_spec_within` + `WP.Branch.join` |
| `assert` | `WP.Triple.refl` (pure strengthening, 0 instructions) |
| `while`  | `WP.loopNatCert` + `loopNatCert_sound` |
| `call`   | `cpsCallWithin` (§3.6) |

```lean
theorem Stmt.spgen_sound (s : Stmt) (reach : Reach) :
    VCs.Hold (s.spgen regions reach).1 →
    cpsTripleWithin (s.steps) base (base + 4 * s.size)
      (CodeReq.ofProg base (s.flatten …))
      (fun h => ∃ rf, (regFileIs rf ** regionsAssert regions) h ∧ reach rf)
      (fun h => ∃ rf, (regFileIs rf ** regionsAssert regions) h ∧
                      (s.spgen regions reach).2 rf)
```

Everything inside one function shares a *single* `CodeReq.ofProg base prog`;
sub-statements' triples are stated against slices and lifted with
`Triple.extendCode` + `CodeReq.ofProg_append` monotonicity — no
`Disjoint` obligations reach the user, ever. The `ite`/`when`/`while` branch
offsets are synthesized by the flattener (§3.7) and their 13/21-bit range
side-conditions are emitted as VCs that `decide` closes (label suffix
`.ofs`); the `vcgen` tactic discharges these automatically.

Step bound: `Stmt.steps` is computed structurally (`while` uses
`WP.loopBound`); the final `cpsTripleWithin` carries this exact bound, which
is what makes the DSL a *total-correctness* Hoare logic with a max
instruction count, per the project's convention.

### 3.6 Functions and the C-like interface (`SAsm/Fn.lean`)

```lean
structure Fn where
  name    : String
  regions : List Region := []
  pre     : RegFile → Prop                 -- over a0–a7 typically
  post    : RegFile → RegFile → Prop       -- entry rf ↝ exit rf (a0/a1 results)
  body    : Stmt

/-- Everything a caller needs; deliberately forgets the body. -/
structure FnHandle where
  entry   : Word
  code    : CodeReq
  nSteps  : Nat
  regions : List Region
  pre     : RegFile → Prop
  postRel : RegFile → RegFile → Prop
  sound   : ∀ ret rf, ret &&& ~~~(1:Word) = ret → pre rf →
    cpsTripleWithin nSteps entry ret code
      ((.x1 ↦ᵣ ret) ** regFileIs rf ** regionsAssert regions)
      (fun h => ∃ rf', ((.x1 ↦ᵣ ret) ** regFileIs rf' **
                         regionsAssert regions) h ∧ postRel rf rf')
```

- The ABI is the project's convention (`Stateless/MemoryLayout.lean`):
  arguments and returns in a0–a7/a0–a1, t-registers clobbered freely
  (`postRel` simply doesn't constrain them), s-registers/sp untouched by
  leaf functions (framed).
- **Calling a DSL function from another DSL function is one AST node**:
  `Stmt.call l f.handle`. The generator emits a single `.pre` VC and
  continues with `postRel`-shaped reach. `Fn.handle : verified Fn → FnHandle`
  is a projection — its `sound` field *is* the function's SAsm spec
  instantiated at `ret`, since SAsm functions end in `JALR x0, x1, 0` and are
  verified against a universally-quantified return address.
- Hand-verified (non-SAsm) routines join the same ecosystem by packaging
  their existing `cpsTripleWithin` spec as a `FnHandle` (adapter lemmas
  bridge atom-form assertions to `regFileIs`, §3.1).
- Non-leaf functions (bodies containing `call`) need `ra` saved.
  `Fn.toHandleR` (`SAsm/RaSpill.lean`) packages a caller verified via
  `soundR` as a callee: the emitted code is
  `SD rs, x1, sofs ; body ; LD x1, rs, sofs ; JALR x0, x1, 0`, where the
  spill slot is a dword of the function's `.rw` region and `rs` is an
  exposed register that the pre pins to its address.  The return address is
  threaded through the body as a ghost word — the packaging consumes a
  family of `SpecR`s indexed by the spilled value, whose pre/post record
  that the slot holds it, so slot preservation is the caller's own `.post`
  VC.  (`CalleesIn` currently makes the whole call tree share one `.rw`
  region, so the slot is visible to callees as part of the symbolic state;
  per-frame sub-regions are future work.)  The `ExamplesVc` two-level tree
  (`topFn` → `callerRHandle` → `leafHandle`) exercises the full shape.

### 3.7 Flattening (`SAsm/Flatten.lean`)

```lean
def Stmt.size    : Stmt → Nat            -- instructions incl. synthesized ones
def Stmt.flatten : Word → Stmt → Program -- addr-aware; resolves all offsets
def Fn.program (f : Fn) (base : Word) : Program := f.body.flatten base ++ [JALR x0 x1 0]
```

Layouts (sizes in instructions):

| node | emitted code | size |
|---|---|---|
| `block _ is` | `is` | `is.length` |
| `ite c t e`  | `B¬c → Lelse` · `t` · `J → Lend` · `e` | `t.size + e.size + 2` |
| `when c b`   | `B¬c → Lend` · `b` | `b.size + 1` |
| `while c n _ b` | `Lhdr: B¬c → Lend` · `b` · `J → Lhdr` | `b.size + 2` |
| `call _ f`   | `JAL x1, (f.entry − pc)` | `1` |
| `assert`     | (nothing) | `0` |

`#eval`-able: flattened programs plug directly into the existing codegen
`BuildUnit` pipeline, so a verified SAsm routine ships in the same ELF as
today's hand-written programs.

### 3.8 The `vcgen` tactic (`SAsm/Tactic.lean`)

User experience (decided interface):

```lean
theorem memcpy_spec (n : Nat) (xs : List Byte) (base src dst : Word) … :
    (memcpy n xs …).Spec base := by
  vcgen                    -- applies Fn.sound, computes+splits the VC list
  case init               => omega
  case copy.inv_init      => simp
  case copy.inv_step      => intro i hi rf h; …
  case copy.fuel_exhausted=> omega
  case post               => intro rf' h; simpa using h
```

Implementation constraints (robustness / recursion-safety):

- `vcgen` does exactly three things: `apply Fn.sound`, normalize the
  `f.vcs` list by `simp only` with the generator's equation lemmas
  (structural, linear in AST size — no search), then split
  `VCs.Hold (vc₁ :: …)` into named goals, tagging each with its label
  string. It attempts `decide` only on `.ofs`/`.ok`-shaped bookkeeping VCs.
- No recursion over proofs of previous goals; each VC is independent.
  Simp recursion depth is bounded by AST depth (≈ nesting level, single
  digits in practice), never by instruction count or fuel.
- On failure the tactic *names what's missing*: an unsupported instruction
  surfaces as a `False`-conclusion VC labeled with the block and the
  instruction; a missing annotation surfaces as an unprovable `inv_step`
  with the loop label. `vcgen?` (diagnostic variant) prints the VC report
  (label + statement, ✓/✗ after the default pass) without leaving goals,
  for the agentic explore loop.

## 4. What this buys for `run_stateless_guest`

- The existing SSZ decode/encode routines in `Stateless/SSZ/*/Program.lean`
  are already `Program` values built from the same constructors; rewriting
  them as `Fn`s is mostly re-indenting under `block`/`when`/`while` nodes,
  after which their (currently TODO) specs in `EntrySpec.lean` become
  `Fn.Spec` statements with pure VCs.
- The check-heavy shape (validate-or-bail) maps to `when`+`assert` chains
  whose VCs are exactly the format checks — the property one actually wants
  to review.
- The routine-per-module architecture (Headers, Witness, Block, …) maps to
  `FnHandle`s, so per-module verification composes into the top-level
  `run_stateless_guest_spec` by `call` nodes rather than bespoke composition
  theorems.

## 5. Milestones

1. **M1 — skeleton (this PR series):** `RegFile`, `Cond`, `Stmt`, `Region`
   (`.ro`), flattener + sizes + `#eval` tests; design doc (this file).
2. **M2 — block engine:** `execBlock`/`blockVCs` for the ALU+`LI`+`.ro`-load
   subset; `execBlock_sound`.
3. **M3 — structural soundness + tactic:** `spgen`, `spgen_sound` for
   `block`/`seq`/`ite`/`when`/`assert`/`while`; `Fn.Spec`, `Fn.sound`,
   `vcgen`; worked examples (bounds-check chain; bounded copy-style loop
   reading a `.ro` region).
4. **M4 — calls:** `FnHandle`, `call` case of `spgen_sound` via
   `cpsCallWithin`; leaf-callee restriction lifted by flattener-emitted
   ra-spill prologue/epilogue.
5. **M5 — mutable regions:** `.rw` regions, stores, `SymState`
   generalization; RLP-style demo (prefix classification + field walk) and
   first `Stateless/SSZ` routine ported.

Each milestone is a reviewable PR (or short PR chain) that builds green with
`scripts/check-forbidden-tactics.sh` / `check-axioms.sh` clean.

## 6. Alternatives considered

- **Reflective tactic over goals (deep-embed the assertion language too).**
  Rejected: the existing assertion layer (`Assertion := PartialState → Prop`)
  is shallow; re-deep-embedding it would fork the ecosystem. SAsm deep-embeds
  only *programs*, which are already deep (`List Instr`).
- **VCs by tactic recursion (a `wp_rv64`-style walker over the structure).**
  Rejected per the stated requirement: tactic recursion over program
  structure is exactly what hits `maxRecursion` and gives opaque failures
  today. A `def` + one induction theorem keeps proof-time work linear and
  failure modes declarative.
- **Expression-language leaves.** Rejected (user decision): raw `List Instr`
  leaves reuse the instruction ecosystem and the codegen path unchanged.
- **Per-block `CodeReq` unions.** Rejected: single `ofProg` per function +
  monotone extension removes the disjointness tax that dominates the RLP
  proofs.
