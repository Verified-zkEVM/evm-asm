# SAsm how-to: verifying RISC-V routines with the structured-assembly DSL

This is the working manual for the SAsm framework (`EvmAsm/Rv64/SAsm/`).
It is written for an agent (or human) who has to **verify a routine or
port an existing unverified routine to a verified drop-in replacement**,
without first reading the framework's soundness proofs.  The design
rationale lives in `docs/sasm-design.md`; this document is recipes.

Every named lemma/def below exists in the codebase — when in doubt,
`grep` for it under `EvmAsm/Rv64/SAsm/`.  Worked examples live in
`EvmAsm/Rv64/SAsm/ExamplesVc.lean` (small, one per mechanism),
`EvmAsm/Rv64/SAsm/TreeDemo.lean` (the full tree-walk loop), and
`EvmAsm/Stateless/SSZ/Decode/{ChainIdSAsm,ActiveForkSAsm}.lean`
(real drop-in ports).

---

## 1. The model in one page

An SAsm function (`Fn`, in `SAsm/Fn.lean`) is a structured body over a
symbolic state with three components:

| component | type | meaning |
|---|---|---|
| `rf` | `RegFile` | the 15 *exposed* registers: t0–t6 (`.x5,.x6,.x7,.x28–.x31`), a0–a7 (`.x10–.x17`) |
| `ws` | `List (BitVec 8)` | contents of the function's flat writable window (`rw : RwRegion`, a base + length) |
| `A`  | `Assertion` | the *ambient* separation-logic assertion: pointer-shaped data (trees, lists, borrowed cells) |

`Reach := RegFile → List (BitVec 8) → Assertion → Prop` — pre/post
conditions, loop invariants, and `assert` annotations are all `Reach`
predicates (plus a `Nat` index for invariants).  A function also owns a
read-only ghost byte region (`region : Region`, a base + byte list).

- **Blocks** (`.block lbl [instrs]`) execute over `(rf, ws)` by a pure
  engine (`execBlock`); they never touch `A`.  Loads route by address:
  inside the rw window → the window bytes; otherwise → the read-only
  region.  Stores must hit the rw window.
- **`A` changes only at explicit nodes**: `.ghost` (reshape by
  entailment), `.blockAt` (focus: open a byte window out of `A` at a
  register-held address), and `.call` (the callee's contract).
- Everything outside the function's declared footprint is framed
  automatically by the underlying `cpsTripleWithin` — there is no
  disjointness bookkeeping anywhere.

`x0` is hardwired zero.  `x1` (ra) and `x2` (sp) are owned by the call
machinery — a leaf body must not mention them.

## 2. Quickstart: a leaf function

```lean
def clampFn (x y : Word) : Fn where
  name := "clamp"                    -- prefixes the VC case names
  pre  := fun rf _ _ => rf.get .x10 = x ∧ rf.get .x11 = y
  post := fun rf _ _ =>
    rf.get .x10 = (if BitVec.ult x y then x else y) ∧ rf.get .x11 = y
  body := .when "cap" (.bgeu .x10 .x11) (.block "set" [.MV .x10 .x11])

theorem clampFn_spec (x y base : Word) : (clampFn x y).Spec base := by
  vcgen
  case clamp.post => ...
```

Ghost data (`x`, `y`, byte lists, trees) enters through the *ambient
Lean binders* of the `def` — the function is a family, one per ghost
valuation.

`vcgen` reduces `Fn.Spec base` (a bounded CPS triple of the flattened
body) to named pure goals:

- `<name>.flat`, per-block `.ok` — decidable, discharged automatically.
- `region` — `region.wf ∧ rw.wf`; discharged automatically when both are
  concrete, otherwise supply it (`exact ⟨inputRegion_wf …, hwf⟩`).
- one goal per annotation, labeled by its path: `clamp.post`,
  `count.loop.inv_init` / `.inv_step` / `.exhausted`,
  `<fn>.<block>.mem`, `<fn>.<ghost-label>`, `<fn>.<call-label>.pre`, …
- Loop-body VCs live under `<fn>.<loop>.body.` and are generated at the
  ∃i-union reach `fun rf ws A => ∃ i, i < fuel ∧ inv i rf ws A ∧ cond`.

### Discharging the standard goals

**`.post` (and any goal whose hypothesis is a strongest postcondition)**:
`rintro` the sp existentials, then compute the engine.  Block sp shape:

```lean
rintro rf' ws' A' ⟨rf₀, ws₀, hlen, hpre, rfl, rfl⟩
simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
rw [RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide), ...]
```

`RegFile.get_set_ne`'s argument order is `(rf, r_set, r_get, v, h)` with
`h : r_get ≠ r_set` — the *set* register comes first.

**`.mem` (blocks containing loads/stores)**: goal
`∀ rf ws A, ws.length = rw.len → reach rf ws A → blockVCs …`.
Recipe: `rintro`, coerce the length (`have hws8 : ws.length = 8 := hws`
— literal projections like `rw.len` are opaque to `omega`; the defeq
`have` fixes it), then

```lean
simp only [blockVCs, loadSem, storeSem, aluSem, execInstrRF, inRw,
  Region.loadOk, length_..., <address-index equations>]
```

and close with `if_pos`/`omega`.  Address-index equations have the shape
`((rf.get rs + signExtend12 k) - base).toNat = i₀`; prove them by
rewriting `signExtend12` constants to `Word` literals **first**
(`rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]`)
and then `bv_omega` — `bv_omega` treats `signExtend12` as opaque.

## 3. Spec surface, consequence, frame

- **Readable Assertion triples**: `SState reg rw φ Af` is the canonical
  factored machine assertion (register file + windows + ambient pinned to
  `Af`); `Fn.SpecA base P Q` publishes a proved `Fn.Spec` as
  `{P} body {Q}` via `Fn.specA_of_spec` (two entailments, mechanical for
  `SState`-shaped `P`/`Q`).
- **Consequence**: `Fn.spec_conseq` (strengthen pre / weaken post on a
  proved spec), `FnHandle.weaken` (same at the handle level).
- **Frame**:
  - everything outside the footprint is framed by construction;
  - `FnHandle.frameA f Fr hFr` is the frame rule *at call granularity*:
    a callee needing ambient `A₀` becomes callable where the caller holds
    `A₀ ** Fr` (see `twoCellsFn` in ExamplesVc);
  - for hand proofs, `cpsTripleWithin_frameR` frames any pc-free
    assertion around a raw triple.

An Fn whose contract pins the ambient by equality —
`pre := fun rf _ A => … ∧ A = treeAt root t0` — *is* an Assertion
contract; the call machinery consumes it unchanged.

## 4. Loops

```lean
.«while» "loop" (.bltu .x5 .x6) fuel
  (fun i rf ws A => <invariant at header-evaluation i>)
  (.block "step" [...])
```

- `fuel` bounds iterations; it may depend on ghosts (`t0.lDepth`).
- Three VCs: `inv_init` (entry reach ⇒ `inv 0`), `inv_step`
  (body-sp of `inv i ∧ cond` ⇒ `inv (i+1)`, for the *fixed* quantified
  `i`), `exhausted` (`inv fuel` ⇒ ¬cond).
- `Stmt.whileA` is sugar for invariants in factored Assertion form
  (pure part + pinned ambient family).
- **The counter-register bridge**: annotation relations inside the body
  (focus `winR`, ghost `R`) cannot mention `i`.  If they need an
  `i`-dependent fact (e.g. a remaining-depth bound), maintain a counter
  register (`.ADDI .x13 .x13 1` in the body), tie it in the invariant
  (`rf.get .x13 = BitVec.ofNat 64 i`), and state the fact through
  `(rf.get .x13).toNat`.  Registers are the shared channel between
  reach-level and annotation-level facts.  (`TreeDemo.lean`.)

## 5. Calls

- A callee is a `FnHandle` (entry, code, step bound, regions, pre/post,
  and the soundness contract: called with any aligned return address in
  `ra`, it returns there with `post`).
- `Fn.toHandle` packages a **call-free** verified `Fn` (appends
  `jalr x0, ra, 0`).
- `Fn.toHandleR` (`SAsm/RaSpill.lean`) packages a **caller** (body with
  calls, proved via `Fn.soundR`) by wrapping it with an `ra`-spill
  prologue/epilogue against a dword slot of its rw region.  The return
  address threads through as a ghost: you prove a *family* of body specs
  whose pre/post record that the slot holds it (see the
  `callerRVFn`/`callerRHandle` demo).
- Caller obligations (`SpecR` via `vcgen`): `code` (own code ⊆ cr),
  `callees` (callee code ⊆ cr, and the callee's `region`/`rw` must
  **equal** the caller's), `calls` (concrete address arithmetic —
  `decide`), one `.pre` VC per call site, and the call's sp replaces the
  reachable set by the callee's post.
- **Per-frame windows** (`FnHandle.widenRw`, `SAsm/HandleWiden.lean`):
  when the callee's `rw` is a dword-aligned sub-window of the caller's,
  don't verify the callee against the shared region — verify it against
  its own window and widen the handle at the call site, passing the
  caller's bytes outside the window (`preB`/`sufB`, typically ghosts like
  `dwordBytes v`) as the frame.  The widened post pins `preB`/`sufB`
  unchanged, so slot preservation costs the callee nothing.  The call
  `.pre` VC then asks for the sandwich shape: provide
  `win := ws.drop preB.length` and `List.take_append_drop`.  See
  `WidenDemo` (`wLeafFn` owns 8 bytes; `wCallerRVFn` keeps its ra-spill
  slot in its own dword at `x13 - 8`).
- **Read-only slices** (`FnHandle.widenRo`): same move for `.ro` —
  verify the callee against its own slice, widen at the call site with
  the outside bytes (`preR`/`sufR`); pre/post pass through unchanged.
  One code copy serves every slice: instantiate the handle per call site
  and materialize the slice pointer with `LI` (see `RoWidenDemo`).
  Pitfalls (both wideners): pass `hbytes`-style side conditions as
  `show <projection-free form>; ...` — `decide` refuses goals whose
  unreduced projections mention free variables — and if `vcgen` reports
  a `Fn.Spec`/`SpecR` mismatch, insert `show Fn.SpecR _ _ _` before it.
  Design rationale for named arenas: docs/sasm-design.md §3.6.1.
- **Preserving a value across a call** (`SAsm/FrameConv.lean`; design
  §3.6.2).  The call's sp replaces the reachable set by the callee's
  post, so exposed registers are caller-saved.  Two recipes:
  1. *Contract pinning* — callee doesn't touch the register: wrap both
     its pre and post in `Reach.pin r v` with ghost `v`; the callee's
     `.post` VC discharges the preservation (`RegFile.get_set_ne`), and
     the caller instantiates the handle at its live value
     (`PinDemo.pinCallerFn`).
  2. *Spill/reload* — callee clobbers the register: `SD` the value into
     a caller-private dword before the call (its bytes become the
     `preB`/`sufB` ghost of the callee's `widenRw` widening, so the
     widened post returns them intact), then re-materialize the frame
     pointer with `LI` and `LD` the value back
     (`SpillDemo.spCallerFn`).  Don't spill pointers — reload them with
     `LI` from the static layout.
  s-registers and `sp` never need either recipe: they are outside the
  exposed set, so verified code cannot touch them (frames are static
  windows of the stack arena; there is no `addi sp` in verified code).
- **Indirect calls** (`Stmt.callReg lbl rs handles`; design §3.6.3).
  Emits `jalr ra, rs, 0` against a finite table of candidate handles.
  One `.pre` VC: produce `⟨h, membership, rf.get rs = h.entry, h.pre⟩`
  for every reachable state — after a table `ld` or a branch of `LI`s,
  this is `RegFile.get_set_self` plus picking the branch's handle.  The
  call's sp is the disjunction `∃ h ∈ handles, h.post`; destructure the
  membership with `simp only [List.mem_cons, ...] ; rcases ... with rfl | rfl`.
  `callees` asks the per-handle triple (code ⊆ cr, regions equal —
  widen each handle first if it owns a sub-window); `calls` asks
  `pc + 4` aligned plus every entry a `jalr` fixed point (`decide`).
  `offsetsOk` requires `rs` exposed.  To know WHICH handler ran,
  instantiate the handles' ghost contracts per call site (see
  `CallRegDemo` and §3.6.3).

### Calling an existing hand-verified `cpsTripleWithin`

Template: `handAdd_sound` in ExamplesVc.  The bridge toolkit
(`SAsm/AssertionSpec.lean`):

1. Peel exactly the registers the routine touches off the one-atom
   register file: `regFileIs_eq_regFileOn`, then `regFileOn_perm`
   (reorder by membership, prove with `intro r; cases r <;> simp […]` —
   **`decide` cannot do `∀ r : Reg`**), then `regFileOn_cons` per
   register.  The untouched 13 stay as a single opaque `regFileOn` atom.
2. Frame the rest + the ambient `A` + `ra`; run the routine's atom-form
   per-instruction specs; `Fn.jalr_ret_spec` for the return.
3. Re-fold at the updated valuation: spell it as an explicit lambda
   (`fun r => if r = .x10 then … else rf r`) and use `regFileOn_congr`
   (agreement on the untouched set, `fin_cases hr <;> rfl`).  Values of
   a `set`-bound `rf'` need explicit equations
   (`have hv : rf'.get .x10 = … := by rw [hrf']; rfl`) before `xperm` —
   xperm does not unfold `set`-fvars.

## 6. The ambient assertion: ghost, focus, harvest

### `.ghost lbl R` — reshape `A` without code

`R : RegFile → List Byte → Assertion → Assertion → Prop` relates old to
new ambient.  One VC:

```
∀ rf ws A, reach → A.pcFree → (∃ hp, A hp) →
  ∃ A', R rf ws A A' ∧ (∀ hp, A hp → A' hp) ∧ A'.pcFree
```

Uses: fold/unfold recursive predicates, push/pop zipper frames
(`ctxAt_push_left/right`, `ctxAt_zip_fold`), reseal after a focus block.
**The harvest**: the `(∃ hp, A hp)` hypothesis lets you extract pure
facts baked into predicates (`⌜p ≠ 0⌝`, well-formedness) and record them
in `R` for downstream pure VCs — see `treeAt_sat_shadow`,
`treeAt_sat_node`, `sepConj_sat_left/right` (`SAsm/TreeSep.lean`) and
the `harvestFn` demo.

### `.blockAt lbl ptr winR [instrs]` — focus blocks

A block whose *writable window* is the `bytesRegion` at the address in
register `ptr`, opened out of `A` for the block.  The flat rw window is
inaccessible inside; the read-only region stays readable.

`winR : rf → ws → A → win → rest → Prop` names the decomposition.  The
`.focus` VC is **per satisfying state** (recursive predicates carry
existential pointers *inside* the assertion, so no single decomposition
equality exists):

```
∀ rf ws A, reach → A.pcFree → ∀ hp, A hp →
  ∃ win rest, winR … ∧ (bytesRegion (rf.get ptr) win ** rest) hp
    ∧ rest.pcFree ∧ RwRegion.wf ⟨rf.get ptr, win.length⟩
```

Recipe: destructure `A hp` at the given state (this skolemizes the
predicate's inner existentials — `obtain ⟨pl, pr, …⟩`), pick
`win`/`rest`, reassemble with `xperm_hyp`.  Well-formedness comes from
the predicate's baked-in facts (`treeAt_sat_node`).  Design your
predicates to bake `⌜p ≠ 0 ∧ RwRegion.wf ⟨p, n⟩⌝` into every node.

The `.mem` VC is the ordinary block VC against the window.  The sp
records `winR`, satisfiability of the decomposition, and the engine
result; the window after the block is `(execBlock …).2` (definitionally
the window itself for load/ALU-only blocks).

### Engine-value lemmas

For post-VCs you'll want the block's register effects as equations.
Factor a private lemma per block (template: `treeMin_engine`):

```lean
simp only [<block>, execBlock_cons, execBlock_nil, execInstrRF, loadSem, aluSem]
-- resolve the load-routing `if`s in stages:
rw [if_pos hc₁]        -- ONLY if all its branch-instantiations coincide…
simp only [if_pos hc₂] -- …otherwise simp: `rw [if_pos h]` rewrites a single
                       -- branch-instantiation; simp treats branches as variables
```

A later instruction's address condition only reduces after the earlier
routing `if` resolves — stage the simplification.  Generalized projection
helpers (`have hg : ∀ v w, ((rf.set .x12 v).set .x13 w).get .x10 = rf.get .x10 := …`)
make the `get`-chains rewrite regardless of the (opaque) loaded values.

### The tree-walk template

`TreeDemo.lean` is the canonical loop over a recursive structure:

- invariant: `∃ c t', A = ctxAt c root (rf.get p) ** treeAt (rf.get p) t'`
  ∧ plug identity (`c.zip t' = t0`) ∧ nil shadow
  (`rf.get p = 0 ↔ t' = .leaf`) ∧ answer relation ∧ counter tie ∧ depth;
- body: focus-open the node (`winR` restates the ghosts — annotations
  cannot see the invariant's existentials, so they carry their own ∃ and
  re-derive), then a ghost descend (`ctxAt_push_left` + child shadow
  harvested from satisfiability);
- exit: depth bound + shadow give the nil pointer; a post-loop ghost
  reseals via `ctxAt_zip_fold`.

### Multi-dword focus blocks (N loads/stores at one base)

The worked example is `revCellFn` (ExamplesVc.lean): one focus block that
loads all four dwords of a 32-byte cell and stores them back reversed.
**Do not** unfold `execInstrRF` with a broad `simp` — each load leaves a
routing `if` in the register file, and the next access's address then
contains the whole previous load verbatim (term blowup, then `whnf`
heartbeat timeouts).  Instead:

1. **One rewrite per instruction** with the resolved step lemmas
   (Sym.lean): `execInstrRF_ld_dword` (an `LD` landing `k` bytes into the
   window with dword `v` there *is* `(rf.set rd v, ws)`) and
   `execInstrRF_sd_dword` (an `SD` *is* `(rf, setBytes ws k …)`).  Each
   application discharges its own routing `if`; none survive.  Side
   conditions: `haddr` via a `signExtend12`-literal `decide` show +
   `bv_omega`; `hslice` via the MultiDword slice lemmas.
2. **Window algebra** from `SAsm/MultiDword.lean`: slices
   (`take8_dword_append`, `drop8_dword_append`, `packDword_at0`) feed the
   load steps; splices (`setBytes_append_left/right`,
   `setBytes_dword_at0/past/full`) normalize each store's `setBytes` back
   into a `dwordBytes … ++ …` concatenation.  Beware rewriting bare
   numerals (`show (8 : Nat) = 8 + 0`): it abstracts the `8` in
   `BitVec 8` and fails with "motive is not type correct" — instantiate
   the lemma at the right `k` and `simp only [Nat.reduceAdd]` the
   hypothesis instead.
3. **Base-register stability** as `have`-chains
   (`(rf.set .x5 l0).get .x12 = rf.get .x12`, …) so every step's `haddr`
   is about the *original* `rf`.
4. `.mem` VCs: `simp only [<block>, blockVCs, loadSem, storeSem,
   <the same step-lemma instances>, <the get-chains>, inRw,
   Region.loadOk, length_*, <the offset toNat facts>]` reduces every
   condition to literal arithmetic; finish `and_intros <;> trivial`.
   The generic projections `execInstrRF_get_ne` / `execInstrRF_ld_snd` /
   `execInstrRF_sd_fst` cover mixed blocks where a full step resolution
   is unnecessary.
5. **After the block**: do NOT `rintro rfl`/`subst` the
   `rf' = (execBlock …).1` equation of a large block — the unifier
   whnf-grinds through the load `if`s and times out.  Name the equations
   (`hrf`, `hA'`), `rw [<engine lemma>] at hrf hA'` **first** (shrinking
   them to `rf' = rf.set …`-form), and only then rewrite them into the
   goal.

### Byte-granularity focus blocks

The worked example is `rev4Fn` (ExamplesVc.lean): reverse a 4-byte cell
in place with unrolled literal-offset swaps.  Byte accesses differ from
the dword recipe in three ways:

1. **Resolved byte steps** (`Sym.lean`): `execInstrRF_lbu_byte` (an
   `LBU` landing `k` bytes into the window *is*
   `rf.set rd ((ws.getD k 0).zeroExtend 64)`) and `execInstrRF_sb_byte`;
   projections `execInstrRF_sb_fst` (simp) / `execInstrRF_sb_snd`.
   With `setBytes_singleton` a byte store is a plain `List.set`, and
   `truncate_zeroExtend_byte` collapses the LBU→SB round trip
   (MultiDword.lean).  No alignment side conditions — only the
   in-window bound.
2. **Explode fixed-size windows into cons cells.**  For an unrolled
   block over a window of known length, obtain
   `w = [b0, …, bN]` once (an `rcases`-per-cons chain closed by the
   length hypothesis) — then `List.set`/`getD`/`reverse` all reduce
   definitionally and the engine's final window matches the model by
   the closing `rfl`.  No take/drop invariants for unrolled code;
   loops over a window still use invariants (§4).
3. **Pin metavariables through side proofs.**  A step-lemma instance's
   `haddr` side proof runs against a goal that may still contain
   *metavariables* (the instance's `rf`): rewriting with a ∀-quantified
   helper assigns the meta to a pattern-with-metas and the proof leaves
   them unsolved.  Two safe forms: sequential tactic `rw`s on the goal
   (each occurrence pins the metas before the side proof runs — the
   `rev4_engine`/`rev4_blockVCs` style), or *specific* helper equations
   (the `revCell_blockVCs` style).  If a later access's side condition
   mentions an earlier store's `(execInstrRF …).1`, normalize it with
   `simp only [execInstrRF_sb_fst]` first — store steps do not
   `dsimp`-reduce (the def hides the match), but their projections are
   one simp lemma away.

### Branchy straight-line code: joins and disjunction blowup

`sp` of `.when`/`.ite` is a **disjunction** — `n` sequential `when`s make
`2^n` reachable-set disjuncts, and every downstream VC must destructure
all of them.  Two ways out:

- **Prefer branchless data flow** where RV64 allows it: `SLTIU`/`SLTU`
  materialize conditions as 0/1, `SLL`/`SRL` take *register* shift
  amounts — a conditional "shift and bump the counter" step becomes
  `SRLI probe; SLTIU cond; SLLI amt; SLL x; ADD acc` with no branch at
  all, and `sp` stays a single symbolic path.
- **`.assert` as a join point**: `sp(assert P) = reach ∧ P`, so a
  downstream VC can `rintro ⟨-, hP⟩` — the branch disjunction is
  *dropped* and only the summary `P` flows on.  Put an `.assert` pinning
  the registers you care about immediately after each `when`/`ite` (the
  assert's own VC does the 2-way case analysis; done per-branch it stays
  linear, not exponential).  A shared relational ghost at the join does
  the same for the ambient assertion (both `ite` arms ending in the SAME
  `R` — the context existential hides the direction; see
  `treeInsDescendR` in TreeInsert.lean).

### The structural `sp` eliminators (Vc.lean)

For any VC of the form `∀ rf ws A, sp s reach rf ws A → P rf ws A`,
prove it by the shape of `s` instead of hand-destructuring the raw
existentials/disjunctions:

- `Stmt.sp_ite_split` / `sp_when_split` — one subgoal per branch;
- `Stmt.sp_block_split` / `sp_blockAt_split` — prove `P` of the engine
  result at every reachable entry (the post-VC shape after a block,
  without the six-tuple `rintro`);
- `Stmt.sp_ghost_split`; `sp_seq_eq` / `sp_assert_eq` rfl-rewrites.
- **`Stmt.sp_cut`** — the assert cut:
  `sp s (sp (assert P) reach) → sp s P`.  Apply it first in any VC whose
  reach passes through an `.assert`; everything before the assert is
  forgotten and the rest of the proof only sees the summary `P`
  (`ClzSAsm.lean`'s `clz.post`: one `sp_cut`, one `sp_blockAt_split`,
  then five rewrites).

### Branch-tail summaries: `Stmt.EndsWith` + `sp_of_endsWith`

For an `ite` *cascade* (n-way limb select, dispatch trees), a single
`.assert` after the join still faces the full n-way disjunction in its
own VC.  Instead, place the SAME `.assert P` at the **tail of every
branch**:

- each assert VC sees only its own linear path (one branch's blocks and
  conditions — small, engine-lemma-sized);
- the downstream recovers `P` with **zero case analysis** via
  `Stmt.sp_of_endsWith (P := …) (by simp [<cascade def>, Stmt.EndsWith])`
  — `EndsWith` checks syntactically that every path ends in `.assert P`.
- asserts emit no code, so the flattened `Program` (and its `#guard`s)
  are unchanged.

The worked instance is `clzSelectBody`/`clzFn_spec` in
`EvmAsm/Codegen/Programs/ClzSAsm.lean`: a 5-leaf select cascade, five
~25-line leaf VCs, and a `computed` VC that gets the joined summary in
one line.  (A bounded `aesop (add simp [Stmt.sp, …])` can close such
VCs too, but is slower and brittle under definition changes — prefer
the structural lemmas.)

## 7. Porting an unverified routine (the SSZ drop-in recipe)

The pattern of `ChainIdSAsm.lean` / `ActiveForkSAsm.lean`:

1. **Why byte-wise**: the Lean RV64 model traps on misaligned LWU/LD
   (`isValidMemAccess` alignment gates).  SSZ offsets are frequently
   ≡ 2 (mod 4) from the dword-aligned input base — assemble u32/u64
   values from `LBU` + `SLLI` + `OR` chains instead.
2. Ghost input: the whole input buffer `bs : List (BitVec 8)` as the
   read-only `region := ⟨0x40000000, bs⟩`; `inputRegion_wf` for the
   region goal.  Values via `leByte`/`leU32`/`leU64` with
   `leU32_toNat_lt` bounds.
3. The pre carries exactly the assumptions the unverified routine makes
   implicitly (offsets in range); the post pins the ABI registers
   downstream code documents.
4. Proof mechanics: controlled `simp only` keeps BitVec form;
   `signExtend12`-to-literal shows **before** `bv_omega`; index
   conversion shows sized to match the goal's exact spelling; fold
   OR-chains into `leU32`/`leU64` by `rfl`-shows (pick index spellings
   in pre/post so the `leByte` indices match syntactically);
   `and_intros <;> first | trivial | omega | bv_omega`.
5. **Emit + swap**: `def <name>_verified : Program := body.flatten 0`
   with `#guard` pins (length, position-independence:
   `flatten 0 = flatten 0x80000000`); replace the original in
   `EvmAsm/Stateless/Entry.lean` (`run_stateless_guest`).
6. **EEST A/B — required whenever emitted code changes**:
   - baseline ELF: `git stash -u`, then
     `lake exe codegen --program stateless_guest --halt linux93 -o gen-out/<base>`,
     `git stash pop`; candidate ELF likewise from the branch;
   - per leg: `GUEST_ELF=<elf> EEST_RUN_DIR=<dir>
     scripts/codegen-eest-stateless-check.sh --no-build --backend spike
     --random --seed 4242 --limit 200 --jobs 8 --quiet-passes`
     (note: `--all` bypasses `--limit`);
   - diff the per-case `PASS/FAIL/ERROR/BUDGET` labels between legs —
     **failures are acceptable only if identical on both legs**; also
     sanity-diff the two `.s` files (only the expected expansion).

## 8. Pitfalls (hard-won; check here first)

- `decide` refuses goals containing free variables even when they reduce
  away.  Coerce through a closed instance:
  `have h0 : P (f 0) := by decide; have hv : P (f v) := h0` (defeq), or
  ascribe: `((by decide : P₀))` where the expected type is the fvar form.
  `∀ r : Reg, …` has no `Decidable` instance — `intro r; cases r <;> simp [...]`.
- `bv_omega` treats `signExtend12`/`ofInt` as opaque: rewrite constants
  to `Word` literals first (`by decide` shows).
- Inline lambda arguments to big packaging defs elaborate with metavar
  types (`rw` fails with `?m.…`): lift each obligation to a named
  `private theorem` with an explicit statement.
- `cpsTripleWithin_weaken` inside a `have` needs explicit `(P' := …)`
  `(Q' := …)` — unification is otherwise deferred past the tactic block.
- `rintro rfl` on `ws' = (execBlock …).2` whnf-collapses through
  load/ALU blocks; ws-existentials merge into one surviving variable —
  name your `obtain`s accordingly.
- Handle-projection hypotheses (`h : someHandle.code a = some i`) are
  defeq but not syntactic to their definition — `have h' : … := h`
  before `rw`.
- `Option.noConfusion h` on `some i = none` hits universe issues — use
  `cases h`.
- `rw [heq ▸ h]` often fails on motive — `rw [← heq, h'] at …` instead.
- `xperm`/`xperm_hyp` match atoms by defeq but do **not** unfold
  `set`-bound fvars — pin values with explicit equations first.
- The routing `if` inside `execInstrRF` lives in the *RegFile component*
  of the result pair, so `.2` (the window) is definitionally inert —
  rely on it (`from rfl` shows) rather than simp.
- `rintro rfl`/`subst` on `rf' = (execBlock …).1` of a **multi-load
  block** whnf-times-out (the unifier grinds through the routing `if`s).
  Name the equation, `rw [<engine>] at` it first (§6, "Multi-dword focus
  blocks").
- `rw [show (8 : Nat) = 8 + 0 from rfl]` in byte-list goals fails with
  "motive is not type correct" — the numeral also occurs as the width in
  `BitVec 8`.  Instantiate lemmas at the composite index and
  `simp only [Nat.reduceAdd] at h` instead.
- Zero-warning policy: heed `unusedSimpArgs` hints; `lake build EvmAsm`
  must be warning-free under `EvmAsm/`.

## 9. Delivery checklist

1. `lake build EvmAsm` — green, zero warnings under `EvmAsm/`.
2. `scripts/check-forbidden-tactics.sh` — no `native_decide`/`bv_decide`
   anywhere (kernel-checkable proofs only).
3. `#print axioms` on every new theorem — only
   `propext`/`Classical.choice`/`Quot.sound`.
4. If emitted code changed: the EEST A/B procedure of §7.6, results in
   the PR description.
5. Update `PLAN.md` for the work done.
6. Commit/PR per theorem-or-two (small reviewable units); PR bodies end
   with the standard generation footer; GitHub comments end with
   `*Written with Claude*`.
