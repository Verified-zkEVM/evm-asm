/-
  EvmAsm.Rv64.SAsm.Deriv

  Proof-first SAsm: constructive separation-logic derivations from which
  RISC-V code is *generated*, inverting the usual code-then-VCs workflow
  (docs/sasm-deriv.md).

  A `DStmt reg rw S P Q` is a `Type`-valued derivation that any state
  satisfying the entry reach `P` is carried to the exit reach `Q` by the
  statement `S` — with every proof obligation the VC generator would emit
  for `S` carried *inside* the derivation, at the step that incurs it.
  Because `Prop` proofs are irrelevant (no code can be extracted from
  them), the derivation lives in `Type`: the machine code is data
  (recovered by the `S` index / `Σ` projection), the obligations are
  `Prop` fields.

  `DCode reg rw P Q` packages the derivation with its statement
  (`Σ S, DStmt reg rw S P Q`); a `Trans` instance makes ordinary `calc`
  work, so a routine is written as a calc chain from precondition to
  postcondition:

    calc (P : Reach)
      _ ~> Q₁ := .block "load" [...] hok hmem hpost   -- machine steps
      _ ~> Q₂ := .pure "shuffle" h                    -- 0 instructions
      _ ~> Q  := .ite "cmp" c dThen dElse             -- if/fi, both arms to Q₂→Q

  Control flow:
  - `.ite c thn els` — the two arms start from `P ∧ c` / `P ∧ ¬c`
    ("between if and fi execution splits, pre/post match modulo the
    condition") and must reach the SAME post.
  - `.dwhile c fuel inv hinit body hexh` — the body is a *family*
    `(i : Nat) → DCode … (i < fuel ∧ inv i ∧ c) (inv (i+1))`; the erased
    statement is a type index, so the family is forced by unification to
    share ONE code skeleton across all iterations (annotations may mention
    `i`; instructions may not — violations fail at elaboration).

  Soundness is once-and-for-all: `DStmt.vcs_hold`/`DStmt.post_sound`
  discharge exactly the VC list of `Stmt.vcs`, so `DCode.fn_spec` plugs
  into the existing `Fn.sound` and yields the ordinary bounded CPS triple
  (`cpsTripleWithin`, step bound `Stmt.steps` included).  Code is
  extracted with `DCode.program` — the same `Stmt.flatten` used
  everywhere else, so drift guards, handles and the codegen pipeline
  consume the result unchanged.
-/

import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.SAsm.VcExists

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- The derivation family
-- ============================================================================

/-- One guard-cascade stage's obligations: block support, memory VCs, and
    the two semantic steps — falling through (guard false) re-establishes
    the next invariant, firing (guard true) lands in the shared bad-entry
    states `B`. -/
def CascadeStage (reg : Region) (rw : RwRegion) (st : List Instr × Cond)
    (pre post bad : Reach) : Prop :=
  blockOk st.1 = true
  ∧ (hasLoad st.1 = true → ∀ rf ws A, ws.length = rw.len → pre rf ws A →
      blockVCs reg rw.base rf ws st.1)
  ∧ (∀ rf ws A, cascadeStep reg rw st.1 pre rf ws A → ¬ st.2.holds rf →
      post rf ws A)
  ∧ (∀ rf ws A, cascadeStep reg rw st.1 pre rf ws A → st.2.holds rf →
      bad rf ws A)

/-- The whole cascade's obligations, one `CascadeStage` per stage at the
    running invariant index.  For a concrete stage list this unfolds to a
    plain conjunction, built with `⟨…⟩`. -/
def CascadeChain (reg : Region) (rw : RwRegion) :
    List (List Instr × Cond) → (Nat → Reach) → Nat → Reach → Prop
  | [], _, _, _ => True
  | st :: rest, inv, k, B =>
      CascadeStage reg rw st (inv k) (inv (k + 1)) B
      ∧ CascadeChain reg rw rest inv (k + 1) B

/-- One selector-cascade stage's obligations: block support, memory VCs,
    falling through re-establishes the next invariant, and firing lands in
    the reach of the SELECTED tail (`A`/`B`/`C` = pre/ok/bad entries). -/
def SelCascadeStage (reg : Region) (rw : RwRegion)
    (st : List Instr × Cond × RetSel)
    (pre post A B C : Reach) : Prop :=
  blockOk st.1 = true
  ∧ (hasLoad st.1 = true → ∀ rf ws A', ws.length = rw.len → pre rf ws A' →
      blockVCs reg rw.base rf ws st.1)
  ∧ (∀ rf ws A', cascadeStep reg rw st.1 pre rf ws A' →
      ¬ st.2.1.holds rf → post rf ws A')
  ∧ (∀ rf ws A', cascadeStep reg rw st.1 pre rf ws A' → st.2.1.holds rf →
      (match st.2.2 with
        | .pre => A
        | .ok => B
        | .bad => C) rf ws A')

/-- The whole selector cascade's obligations, one `SelCascadeStage` per
    stage at the running invariant index. -/
def SelCascadeChain (reg : Region) (rw : RwRegion) :
    List (List Instr × Cond × RetSel) → (Nat → Reach) → Nat →
      Reach → Reach → Reach → Prop
  | [], _, _, _, _, _ => True
  | st :: rest, inv, k, A, B, C =>
      SelCascadeStage reg rw st (inv k) (inv (k + 1)) A B C
      ∧ SelCascadeChain reg rw rest inv (k + 1) A B C

-- Lean v4.33 cannot derive `SizeOf` for this family (its `Reach`-indexed,
-- `Type`-valued constructors defeat the generator).  Nothing needs the
-- instance: `post_sound`/`vcs_hold` below recurse with the structural
-- recursor and code extraction recurses on the erased `Stmt` index, so
-- generation is skipped rather than worked around.
set_option genSizeOf false in
/-- A constructive derivation that statement `S` carries entry reach `P` to
    exit reach `Q`, with all of `S`'s proof obligations internalized.  The
    erased statement is a type INDEX: derivations that must share code
    (loop-body families, if/fi arms of a shared skeleton) are forced to by
    unification, so register clobbering or endian mistakes surface at the
    step that makes them, not after the code exists. -/
inductive DStmt (reg : Region) (rw : RwRegion) : Stmt → Reach → Reach → Type where
  /-- Pure step: re-describe the reachable states (an entailment — in
      particular an iff — of assertions).  Emits NO instructions; erases
      to a `True`-annotated `.assert` (NOT `.assert lbl Q`): the
      entailment lives in the derivation, and keeping the erased
      annotation constant means pure steps inside a loop body may mention
      the iteration index freely without breaking the shared code
      skeleton. -/
  | pure (lbl : String) {P Q : Reach}
      (h : ∀ rf ws A, P rf ws A → Q rf ws A) :
      DStmt reg rw (.assert lbl (fun _ _ _ => True)) P Q
  /-- Straight-line machine step: a block of raw instructions.  `hok` is
      the supported-subset check (`decide`), `hmem` the memory-safety
      obligations (only if the block loads), `hpost` the semantic step —
      the block engine's result satisfies `Q`. -/
  | block (lbl : String) (is : List Instr) {P Q : Reach}
      (hok : blockOk is = true)
      (hmem : hasLoad is = true → ∀ rf ws A, ws.length = rw.len →
        P rf ws A → blockVCs reg rw.base rf ws is)
      (hpost : ∀ rf ws A, ws.length = rw.len → P rf ws A →
        Q (execBlock reg rw.base rf ws is).1
          (execBlock reg rw.base rf ws is).2 A) :
      DStmt reg rw (.block lbl is) P Q
  /-- PC-aware machine step: a straight-line block that may contain
      `AUIPC` (the `la` idiom), carrying its own placement address and run
      on the PC-threaded engine.  Verifies on the caller-shaped path only
      (`DCode.fn_specR`); `callsOk` pins `addr` to the actual placement. -/
  | blockA (lbl : String) (addr : Word) (is : List Instr) {P Q : Reach}
      (hok : blockOkAt is = true)
      (hmem : hasLoad is = true → ∀ rf ws A, ws.length = rw.len →
        P rf ws A → blockVCsAt reg rw.base addr rf ws is)
      (hpost : ∀ rf ws A, ws.length = rw.len → P rf ws A →
        Q (execBlockAt reg rw.base addr rf ws is).1
          (execBlockAt reg rw.base addr rf ws is).2 A) :
      DStmt reg rw (.blockA lbl addr is) P Q
  /-- Guard cascade with a shared ret-terminated bad tail (the
      "validate; any failure returns the error code" idiom): per-stage
      obligations along a user-chosen invariant family, then the ok tail
      from the final invariant and the bad tail from the shared bad-entry
      states — both ret-terminated, both to the same `Q`. -/
  | dretCascade (lbl : String) (stages : List (List Instr × Cond))
      (inv : Nat → Reach) (B : Reach)
      {Sok Sbad : Stmt} {P Q : Reach}
      (hinit : ∀ rf ws A, P rf ws A → inv 0 rf ws A)
      (hchain : CascadeChain reg rw stages inv 0 B)
      (okD : DStmt reg rw Sok (inv stages.length) Q)
      (badD : DStmt reg rw Sbad B Q) :
      DStmt reg rw (.retCascade lbl stages Sok Sbad) P Q
  /-- Sequential composition — the `calc` step. -/
  | seq {Sa Sb : Stmt} {P Q R : Reach}
      (a : DStmt reg rw Sa P Q) (b : DStmt reg rw Sb Q R) :
      DStmt reg rw (.seq Sa Sb) P R
  /-- if/fi: execution splits on `c`; the arms start from `P` strengthened
      by the condition and must both reach the SAME `Q`. -/
  | ite (lbl : String) (c : Cond) {St Se : Stmt} {P Q : Reach}
      (thn : DStmt reg rw St (fun rf ws A => P rf ws A ∧ c.holds rf) Q)
      (els : DStmt reg rw Se (fun rf ws A => P rf ws A ∧ ¬ c.holds rf) Q) :
      DStmt reg rw (.ite lbl c St Se) P Q
  /-- if without else: the skip path must already satisfy `Q`. -/
  | «when» (lbl : String) (c : Cond) {Sb : Stmt} {P Q : Reach}
      (body : DStmt reg rw Sb (fun rf ws A => P rf ws A ∧ c.holds rf) Q)
      (hskip : ∀ rf ws A, P rf ws A → ¬ c.holds rf → Q rf ws A) :
      DStmt reg rw (.when lbl c Sb) P Q
  /-- Ghost step: replace the ambient assertion `A` by an `Rr`-related
      `A'` (fold/unfold recursive predicates).  Emits NO instructions. -/
  | ghost (lbl : String) {P : Reach}
      (Rr : RegFile → List (BitVec 8) → Assertion → Assertion → Prop)
      (h : ∀ rf ws A, P rf ws A → A.pcFree → (∃ hp, A hp) →
        ∃ A', Rr rf ws A A' ∧ (∀ hp, A hp → A' hp) ∧ A'.pcFree) :
      DStmt reg rw (.ghost lbl Rr) P
        (fun rf ws A' => ∃ A, P rf ws A ∧ (∃ hp, A hp) ∧ Rr rf ws A A')
  /-- Call to a verified routine: `P` must entail the callee's pre, and
      its post must entail `Q`. -/
  | call (lbl : String) (f : FnHandle) {P Q : Reach}
      (hpre : ∀ rf ws A, P rf ws A → f.pre rf ws A)
      (hpost : ∀ rf ws A, f.post rf ws A → Q rf ws A) :
      DStmt reg rw (.call lbl f) P Q
  /-- Write-focus block: a straight-line block whose writable window is a
      `bytesRegion` at the address in register `p`, opened out of the
      ambient assertion (see `Stmt.blockAt`). -/
  | blockAt (lbl : String) (p : Reg)
      (winR : RegFile → List (BitVec 8) → Assertion →
        List (BitVec 8) → Assertion → Prop)
      (is : List Instr) {P Q : Reach}
      (hok : blockOk is = true)
      (hfocus : ∀ rf ws A, P rf ws A → A.pcFree → ∀ hp, A hp →
        ∃ win rest, winR rf ws A win rest
          ∧ (bytesRegion (rf.get p) win ** rest) hp
          ∧ rest.pcFree ∧ RwRegion.wf ⟨rf.get p, win.length⟩)
      (hmem : hasLoad is = true → ∀ rf ws A win rest, ws.length = rw.len →
        P rf ws A → winR rf ws A win rest →
        (∃ hp, (bytesRegion (rf.get p) win ** rest) hp) →
        blockVCs reg (rf.get p) rf win is)
      (hpost : ∀ rf ws A win rest, ws.length = rw.len → P rf ws A →
        (∃ hp, (bytesRegion (rf.get p) win ** rest) hp) →
        winR rf ws A win rest →
        Q (execBlock reg (rf.get p) rf win is).1 ws
          ((bytesRegion (rf.get p) (execBlock reg (rf.get p) rf win is).2)
            ** rest)) :
      DStmt reg rw (.blockAt lbl p winR is) P Q
  /-- Read-focus block: a straight-line block reading a `bytesRegion` at
      the address in register `p`, opened out of the ambient assertion
      (see `Stmt.readAt`). -/
  | readAt (lbl : String) (p : Reg)
      (roR : RegFile → List (BitVec 8) → Assertion →
        List (BitVec 8) → Assertion → Prop)
      (is : List Instr) {P Q : Reach}
      (hok : blockOk is = true)
      (hfocus : ∀ rf ws A, P rf ws A → A.pcFree → ∀ hp, A hp →
        ∃ robytes rest, roR rf ws A robytes rest
          ∧ (bytesRegion (rf.get p) robytes ** rest) hp
          ∧ rest.pcFree ∧ Region.wf ⟨rf.get p, robytes⟩)
      (hmem : hasLoad is = true → ∀ rf ws A robytes rest,
        ws.length = rw.len → P rf ws A → roR rf ws A robytes rest →
        (∃ hp, (bytesRegion (rf.get p) robytes ** rest) hp) →
        blockVCs ⟨rf.get p, robytes⟩ rw.base rf ws is)
      (hpost : ∀ rf ws A robytes rest, ws.length = rw.len → P rf ws A →
        (∃ hp, (bytesRegion (rf.get p) robytes ** rest) hp) →
        roR rf ws A robytes rest →
        Q (execBlock ⟨rf.get p, robytes⟩ rw.base rf ws is).1
          (execBlock ⟨rf.get p, robytes⟩ rw.base rf ws is).2
          (bytesRegion (rf.get p) robytes ** rest)) :
      DStmt reg rw (.readAt lbl p roR is) P Q
  /-- Bounded top-test loop.  The body is a family over the iteration
      index `i` — assertions may mention `i`, code may not (the shared
      index `Sb` enforces this).  The loop exits with the invariant at
      some `i ≤ fuel` and the guard false. -/
  | dwhile (lbl : String) (c : Cond) (fuel : Nat) (inv : Nat → Reach)
      {Sb : Stmt} {P : Reach}
      (hinit : ∀ rf ws A, P rf ws A → inv 0 rf ws A)
      (body : (i : Nat) → DStmt reg rw Sb
        (fun rf ws A => i < fuel ∧ inv i rf ws A ∧ c.holds rf)
        (inv (i + 1)))
      (hexh : ∀ rf ws A, inv fuel rf ws A → ¬ c.holds rf) :
      DStmt reg rw (.while lbl c fuel inv Sb) P
        (fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf)
  /-- Bounded bottom-test (`do`-`while`) loop.  The body family is indexed
      by `Option Nat`: `none` is the unconditional first run (from `P` to
      `inv 0`), `some i` the i-th guarded rerun. -/
  | doWhile (lbl : String) (c : Cond) (fuel : Nat) (inv : Nat → Reach)
      {Sb : Stmt} {P : Reach}
      (body : (x : Option Nat) → DStmt reg rw Sb
        (fun rf ws A => match x with
          | none => P rf ws A
          | some i => i < fuel ∧ inv i rf ws A ∧ c.holds rf)
        (fun rf ws A => match x with
          | none => inv 0 rf ws A
          | some i => inv (i + 1) rf ws A))
      (hexh : ∀ rf ws A, inv fuel rf ws A → ¬ c.holds rf) :
      DStmt reg rw (.doWhile lbl c fuel inv Sb) P
        (fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf)
  /-- Bounded top-test loop with an *entry-snapshot-parameterized*
      invariant (the derivation form of `Stmt.whileS`).  This is the
      nested-loop construct: an inner loop's invariant annotation must not
      mention an outer iteration index (it is part of the shared code
      skeleton), so facts of the enclosing context — an outer counter held
      in a register — survive through the snapshot `(rf₀, ws₀, A₀)`, the
      state at loop entry; the entry-reach fact `P rf₀ ws₀ A₀` is
      available throughout.  The body family may mention the snapshot and
      `i` in its assertions; code may not. -/
  | dwhileS (lbl : String) (c : Cond) (fuel : Nat)
      (inv : RegFile → List (BitVec 8) → Assertion → Nat → Reach)
      {Sb : Stmt} {P : Reach}
      (hinit : ∀ rf ws A, P rf ws A → inv rf ws A 0 rf ws A)
      (body : (rf₀ : RegFile) → (ws₀ : List (BitVec 8)) → (A₀ : Assertion) →
        (i : Nat) → DStmt reg rw Sb
        (fun rf ws A => P rf₀ ws₀ A₀ ∧ i < fuel
          ∧ inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
        (inv rf₀ ws₀ A₀ (i + 1)))
      (hexh : ∀ rf₀ ws₀ A₀, P rf₀ ws₀ A₀ → ∀ rf ws A,
        inv rf₀ ws₀ A₀ fuel rf ws A → ¬ c.holds rf) :
      DStmt reg rw (.whileS lbl c fuel inv Sb) P
        (fun rf ws A => ∃ rf₀ ws₀ A₀, P rf₀ ws₀ A₀
          ∧ (∃ i, i ≤ fuel ∧ inv rf₀ ws₀ A₀ i rf ws A) ∧ ¬ c.holds rf)
  /-- Bounded bottom-test loop with an entry-snapshot-parameterized
      invariant (the derivation form of `Stmt.doWhileS`; the converters'
      idiom).  The body family is indexed by snapshot × `Option Nat`:
      `none` is the unconditional first run (from the exact entry state),
      `some i` the i-th guarded rerun. -/
  | doWhileS (lbl : String) (c : Cond) (fuel : Nat)
      (inv : RegFile → List (BitVec 8) → Assertion → Nat → Reach)
      {Sb : Stmt} {P : Reach}
      (body : (x : RegFile × List (BitVec 8) × Assertion × Option Nat) →
        DStmt reg rw Sb
        (fun rf ws A => match x with
          | (rf₀, ws₀, A₀, none) =>
              P rf₀ ws₀ A₀ ∧ Reach.exact rf₀ ws₀ A₀ rf ws A
          | (rf₀, ws₀, A₀, some i) =>
              P rf₀ ws₀ A₀ ∧ i < fuel ∧ inv rf₀ ws₀ A₀ i rf ws A
                ∧ c.holds rf)
        (fun rf ws A => match x with
          | (rf₀, ws₀, A₀, none) => inv rf₀ ws₀ A₀ 0 rf ws A
          | (rf₀, ws₀, A₀, some i) => inv rf₀ ws₀ A₀ (i + 1) rf ws A))
      (hexh : ∀ rf₀ ws₀ A₀, P rf₀ ws₀ A₀ → ∀ rf ws A,
        inv rf₀ ws₀ A₀ fuel rf ws A → ¬ c.holds rf) :
      DStmt reg rw (.doWhileS lbl c fuel inv Sb) P
        (fun rf ws A => ∃ rf₀ ws₀ A₀, P rf₀ ws₀ A₀
          ∧ (∃ i, i ≤ fuel ∧ inv rf₀ ws₀ A₀ i rf ws A) ∧ ¬ c.holds rf)
  /-- Bounded loop with a **mid-body early exit** (`break`) — the
      structured "scan until a predicate holds".  Each iteration runs
      `bodyBefore` (to the mid-states `mid i`); if `breakCond` holds
      control exits to `Q`, otherwise `bodyAfter` re-establishes the
      invariant.  Both exits — guard failure and break — must entail the
      same `Q`. -/
  | dwhileBreak (lbl : String) (guard : Cond) (fuel : Nat)
      (inv : Nat → Reach) (mid : Nat → Reach) (breakCond : Cond)
      {Sbb Sba : Stmt} {P Q : Reach}
      (hinit : ∀ rf ws A, P rf ws A → inv 0 rf ws A)
      (bodyBefore : (i : Nat) → DStmt reg rw Sbb
        (fun rf ws A => i < fuel ∧ inv i rf ws A ∧ guard.holds rf)
        (mid i))
      (bodyAfter : (i : Nat) → DStmt reg rw Sba
        (fun rf ws A => i < fuel ∧ mid i rf ws A ∧ ¬ breakCond.holds rf)
        (inv (i + 1)))
      (hexh : ∀ rf ws A, inv fuel rf ws A → ¬ guard.holds rf)
      (hguard : ∀ i, i ≤ fuel → ∀ rf ws A, inv i rf ws A →
        ¬ guard.holds rf → Q rf ws A)
      (hbreak : ∀ i, i < fuel → ∀ rf ws A, mid i rf ws A →
        breakCond.holds rf → Q rf ws A) :
      DStmt reg rw (.whileBreak lbl guard fuel inv Q Sbb breakCond Sba) P Q
  /-- Bounded top-guarded loop with a **reloaded header** run before every
      guard evaluation (the derivation form of `Stmt.whileHeader`) — the
      machine idiom `header; B¬c → exit; body; JAL → header`, e.g. a
      guard-limit register reloaded by `li` each trip.  The header family
      is indexed by `Option Nat`: `none` is the entry run (from `P` to
      `inv 0`), `some i` the rerun after the i-th body (from the body's
      mid-states to `inv (i+1)`). -/
  | dwhileHeader (lbl : String) (c : Cond) (fuel : Nat)
      (inv : Nat → Reach) (mid : Nat → Reach)
      {Sh Sb : Stmt} {P : Reach}
      (header : (x : Option Nat) → DStmt reg rw Sh
        (fun rf ws A => match x with
          | none => P rf ws A
          | some i => i < fuel ∧ mid i rf ws A)
        (fun rf ws A => match x with
          | none => inv 0 rf ws A
          | some i => inv (i + 1) rf ws A))
      (body : (i : Nat) → DStmt reg rw Sb
        (fun rf ws A => i < fuel ∧ inv i rf ws A ∧ c.holds rf)
        (mid i))
      (hexh : ∀ rf ws A, inv fuel rf ws A → ¬ c.holds rf) :
      DStmt reg rw (.whileHeader lbl Sh c fuel inv Sb) P
        (fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf)
  /-- Direct call with a **focused read-only region** (the derivation form
      of `Stmt.callAt`): call a leaf routine whose read-only `region` is a
      `bytesRegion` atom carved out of the ambient assertion for this one
      call, while the enclosing regions are framed. -/
  | callAt (lbl : String)
      (roR : RegFile → List (BitVec 8) → Assertion → Assertion → Prop)
      (f : FnHandle) {P Q : Reach}
      (hfocus : ∀ rf ws A, P rf ws A → A.pcFree → ∀ hp, A hp →
        ∃ rest, roR rf ws A rest
          ∧ (bytesRegion f.region.base f.region.bytes ** rest) hp
          ∧ rest.pcFree)
      (hpre : ∀ rf ws A rest, ws.length = rw.len → P rf ws A →
        roR rf ws A rest → f.pre rf ws empAssertion)
      (hemp : ∀ rf ws A, f.post rf ws A → A = empAssertion)
      (hpost : ∀ rf ws A rest, ws.length = rw.len → P rf ws A →
        (∃ hp, (bytesRegion f.region.base f.region.bytes ** rest) hp) →
        roR rf ws A rest →
        ∀ rf' ws', f.post rf' ws' empAssertion →
        Q rf' ws' (bytesRegion f.region.base f.region.bytes ** rest)) :
      DStmt reg rw (.callAt lbl roR f) P Q

  /-- Return to `ra` (`jalr x0, ra, 0`).  Terminates a ret-shaped
      derivation; consumable through `DCode.retSpec` (the
      `Stmt.retSound` path), NOT through `DCode.fn_spec`. -/
  | retJalr (lbl : String) {P : Reach} :
      DStmt reg rw (.retJalr lbl) P P
  /-- Branch to one of two RET-TERMINATED tails (no rejoin): the arms
      start from `P` strengthened by the condition and must reach the
      same `Q` — at their own `ret`s. -/
  | dretIf (lbl : String) (c : Cond) {St Se : Stmt} {P Q : Reach}
      (thn : DStmt reg rw St (fun rf ws A => P rf ws A ∧ c.holds rf) Q)
      (els : DStmt reg rw Se (fun rf ws A => P rf ws A ∧ ¬ c.holds rf) Q) :
      DStmt reg rw (.retIf lbl c St Se) P Q
  /-- Tail-swapped return-terminating break loop (`Stmt.retWhileBreakSwap`):
      a top-guarded scan whose break branch exits to the NEAR ret tail
      (`breakTail`, right after the back-edge) and whose guard-exit lands on
      the FAR tail (`guardTail`, last) — the `modexp_iszero` layout.  The
      body families are indexed by the iteration count; both tails must
      reach the same `Q` at their own `ret`s. -/
  | dretWhileBreakSwap (lbl : String) (guard : Cond) (fuel : Nat)
      (inv : Nat → Reach) (mid : Nat → Reach) (breakCond : Cond)
      {Sbb Sba Sgt Sbt : Stmt} {P Q : Reach}
      (hinit : ∀ rf ws A, P rf ws A → inv 0 rf ws A)
      (bodyBefore : (i : Nat) → DStmt reg rw Sbb
        (fun rf ws A => i < fuel ∧ inv i rf ws A ∧ guard.holds rf)
        (mid i))
      (bodyAfter : (i : Nat) → DStmt reg rw Sba
        (fun rf ws A => i < fuel ∧ mid i rf ws A ∧ ¬ breakCond.holds rf)
        (inv (i + 1)))
      (hexh : ∀ rf ws A, inv fuel rf ws A → ¬ guard.holds rf)
      (guardTail : DStmt reg rw Sgt
        (fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ guard.holds rf) Q)
      (breakTail : DStmt reg rw Sbt
        (fun rf ws A => (∃ i, i < fuel ∧ mid i rf ws A) ∧ breakCond.holds rf) Q) :
      DStmt reg rw (.retWhileBreakSwap lbl guard fuel inv Sbb breakCond Sba Sgt Sbt) P Q
  /-- Return-terminating header-reloaded break loop draining into a guard
      cascade (`Stmt.retWhileHeaderBreak`): the loop's break and every
      fired cascade guard enter ONE shared ret-terminated bad tail.
      Families: `inv i` at the i-th guard evaluation (after the header),
      `mid i` at the break test, `hend i` after `bodyAfter` (the header
      re-runs from there); the header family is indexed by `Option Nat`
      (`none` = entry run from `P`).  The cascade carries its own
      invariant family `cinv` from the loop-exit states into the shared
      bad-entry states `B`. -/
  | dretWhileHeaderBreak (lbl : String) (guard : Cond) (fuel : Nat)
      (inv mid hend : Nat → Reach) (breakCond : Cond)
      (stages : List (List Instr × Cond)) (cinv : Nat → Reach) (B : Reach)
      {Sh Sbb Sba Sok Sbad : Stmt} {P Q : Reach}
      (header : (x : Option Nat) → DStmt reg rw Sh
        (fun rf ws A => match x with
          | none => P rf ws A
          | some i => i < fuel ∧ hend i rf ws A)
        (fun rf ws A => match x with
          | none => inv 0 rf ws A
          | some i => inv (i + 1) rf ws A))
      (bodyBefore : (i : Nat) → DStmt reg rw Sbb
        (fun rf ws A => i < fuel ∧ inv i rf ws A ∧ guard.holds rf)
        (mid i))
      (bodyAfter : (i : Nat) → DStmt reg rw Sba
        (fun rf ws A => i < fuel ∧ mid i rf ws A ∧ ¬ breakCond.holds rf)
        (hend i))
      (hexh : ∀ rf ws A, inv fuel rf ws A → ¬ guard.holds rf)
      (hcasc0 : ∀ rf ws A,
        ((∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ guard.holds rf) → cinv 0 rf ws A)
      (hchain : CascadeChain reg rw stages cinv 0 B)
      (okD : DStmt reg rw Sok (cinv stages.length) Q)
      (badD : DStmt reg rw Sbad
        (fun rf ws A => B rf ws A ∨
          ((∃ i, i < fuel ∧ mid i rf ws A) ∧ breakCond.holds rf)) Q) :
      DStmt reg rw
        (.retWhileHeaderBreak lbl Sh guard fuel inv Sbb breakCond Sba stages Sok Sbad)
        P Q
  /-- Return-terminating selector cascade with a terminal copy loop
      (`Stmt.retSelCascadeLoop`): guards dispatch over three tails along a
      `SelCascadeChain`, the fall-through runs `setup` then a bounded
      top-guarded loop whose exit jumps into the ok tail; the pre tail is
      a straight-line block falling through into ok.  `A`/`B`/`C` are the
      user-chosen entry reaches of the pre/ok/bad tails, `cinv` the
      cascade's running invariant, `linv` the loop invariant. -/
  | dretSelCascadeLoop (lbl : String)
      (stages : List (List Instr × Cond × RetSel))
      (cinv : Nat → Reach) (A B C : Reach)
      (setup : List Instr) (guard : Cond) (fuel : Nat) (linv : Nat → Reach)
      (body : List Instr) (preT : List Instr)
      {Sok Sbad : Stmt} {P Q : Reach}
      (hchain0 : ∀ rf ws A', P rf ws A' → cinv 0 rf ws A')
      (hchain : SelCascadeChain reg rw stages cinv 0 A B C)
      (hsetupOk : blockOk setup = true)
      (hsetupMem : hasLoad setup = true → ∀ rf ws A', ws.length = rw.len →
        cinv stages.length rf ws A' → blockVCs reg rw.base rf ws setup)
      (hinit : ∀ rf ws A',
        cascadeStep reg rw setup (cinv stages.length) rf ws A' →
        linv 0 rf ws A')
      (hbodyOk : blockOk body = true)
      (hbodyMem : hasLoad body = true → ∀ rf ws A', ws.length = rw.len →
        (∃ i, i < fuel ∧ linv i rf ws A' ∧ guard.holds rf) →
        blockVCs reg rw.base rf ws body)
      (hstep : ∀ i, i < fuel → ∀ rf' ws' A',
        cascadeStep reg rw body
          (fun rf ws A' => linv i rf ws A' ∧ guard.holds rf) rf' ws' A' →
        linv (i + 1) rf' ws' A')
      (hexh : ∀ rf ws A', linv fuel rf ws A' → ¬ guard.holds rf)
      (hexit : ∀ rf ws A',
        ((∃ i, i ≤ fuel ∧ linv i rf ws A') ∧ ¬ guard.holds rf) →
        B rf ws A')
      (hpreOk : blockOk preT = true)
      (hpreMem : hasLoad preT = true → ∀ rf ws A', ws.length = rw.len →
        A rf ws A' → blockVCs reg rw.base rf ws preT)
      (hpre : ∀ rf ws A', cascadeStep reg rw preT A rf ws A' → B rf ws A')
      (okD : DStmt reg rw Sok B Q)
      (badD : DStmt reg rw Sbad C Q) :
      DStmt reg rw
        (.retSelCascadeLoop lbl stages setup guard fuel linv body preT
          Sok Sbad)
        P Q

namespace DStmt

variable {reg : Region} {rw : RwRegion}

/-- Bridge from per-stage chain obligations to the generated cascade
    artifacts: the stage VCs hold, falling through all stages reaches the
    final invariant, and every fired guard lands in `B`. -/
theorem cascadeChain_bridge (reg : Region) (rw : RwRegion) :
    ∀ (stages : List (List Instr × Cond)) (inv : Nat → Reach) (B : Reach)
      (pfx : String) (k : Nat),
      CascadeChain reg rw stages inv k B →
      VCs.Hold (Stmt.cascadeVcs reg rw stages pfx k (inv k))
      ∧ (∀ rf ws A, cascadeFall reg rw stages (inv k) rf ws A →
          inv (k + stages.length) rf ws A)
      ∧ (∀ rf ws A, cascadeBad reg rw stages (inv k) rf ws A →
          B rf ws A) := by
  intro stages
  induction stages with
  | nil =>
      intro inv B pfx k _
      exact ⟨VCs.Hold.nil, fun rf ws A h => h, fun _ _ _ hf => hf.elim⟩
  | cons st rest ih =>
      intro inv B pfx k hchain
      obtain ⟨⟨hOk, hMem, hFall, hBad⟩, hrest⟩ := hchain
      obtain ⟨ihHold, ihFall, ihBad⟩ := ih inv B pfx (k + 1) hrest
      obtain ⟨is, c⟩ := st
      have hent : ∀ rf ws A,
          (cascadeStep reg rw is (inv k) rf ws A ∧ ¬ c.holds rf) →
          inv (k + 1) rf ws A :=
        fun rf ws A h => hFall rf ws A h.1 h.2
      refine ⟨?_, ?_, ?_⟩
      · refine VCs.Hold.cons_intro hOk (VCs.Hold.append_intro ?_ ?_)
        · by_cases hl : hasLoad is
          · simp only [if_pos hl]
            exact VCs.Hold.cons_intro (hMem hl) VCs.Hold.nil
          · simp only [if_neg hl]
            exact VCs.Hold.nil
        · exact Stmt.cascadeVcs_antitone reg rw rest pfx (k + 1) hent ihHold
      · intro rf ws A h
        have h1 := cascadeFall_mono reg rw rest hent rf ws A h
        have h2 := ihFall rf ws A h1
        rwa [show k + 1 + rest.length = k + (rest.length + 1) from by omega]
          at h2
      · rintro rf ws A (⟨hs, hc⟩ | hrestBad)
        · exact hBad rf ws A hs hc
        · exact ihBad rf ws A
            (cascadeBad_mono reg rw rest hent rf ws A hrestBad)

/-- Bridge from per-stage selector-chain obligations to the generated
    artifacts: the stage VCs hold, falling through all stages reaches the
    final invariant, and every fired guard lands in its selected tail's
    reach. -/
theorem selCascadeChain_bridge (reg : Region) (rw : RwRegion) :
    ∀ (stages : List (List Instr × Cond × RetSel)) (inv : Nat → Reach)
      (A B C : Reach) (pfx : String) (k : Nat),
      SelCascadeChain reg rw stages inv k A B C →
      VCs.Hold (Stmt.selCascadeVcs reg rw stages pfx k (inv k))
      ∧ (∀ rf ws A', selFall reg rw stages (inv k) rf ws A' →
          inv (k + stages.length) rf ws A')
      ∧ (∀ rf ws A', selTaken reg rw .pre stages (inv k) rf ws A' →
          A rf ws A')
      ∧ (∀ rf ws A', selTaken reg rw .ok stages (inv k) rf ws A' →
          B rf ws A')
      ∧ (∀ rf ws A', selTaken reg rw .bad stages (inv k) rf ws A' →
          C rf ws A') := by
  intro stages
  induction stages with
  | nil =>
      intro inv A B C pfx k _
      exact ⟨VCs.Hold.nil, fun rf ws A' h => h,
        fun _ _ _ hf => hf.elim, fun _ _ _ hf => hf.elim,
        fun _ _ _ hf => hf.elim⟩
  | cons st rest ih =>
      intro inv A B C pfx k hchain
      obtain ⟨⟨hOk, hMem, hFall, hFire⟩, hrest⟩ := hchain
      obtain ⟨ihHold, ihFall, ihPre, ihOk, ihBad⟩ := ih inv A B C pfx (k + 1) hrest
      obtain ⟨is, c, sel⟩ := st
      have hent : ∀ rf ws A',
          (cascadeStep reg rw is (inv k) rf ws A' ∧ ¬ c.holds rf) →
          inv (k + 1) rf ws A' :=
        fun rf ws A' h => hFall rf ws A' h.1 h.2
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · refine VCs.Hold.cons_intro hOk (VCs.Hold.append_intro ?_ ?_)
        · by_cases hl : hasLoad is
          · simp only [if_pos hl]
            exact VCs.Hold.cons_intro (hMem hl) VCs.Hold.nil
          · simp only [if_neg hl]
            exact VCs.Hold.nil
        · exact Stmt.selCascadeVcs_antitone reg rw rest pfx (k + 1) hent
            ihHold
      · intro rf ws A' h
        have h1 := selFall_mono reg rw rest hent rf ws A' h
        have h2 := ihFall rf ws A' h1
        rwa [show k + 1 + rest.length = k + (rest.length + 1) from by omega]
          at h2
      · rintro rf ws A' (⟨hsel, hs, hc⟩ | hrestT)
        · subst hsel
          exact hFire rf ws A' hs hc
        · exact ihPre rf ws A'
            (selTaken_mono reg rw .pre rest hent rf ws A' hrestT)
      · rintro rf ws A' (⟨hsel, hs, hc⟩ | hrestT)
        · subst hsel
          exact hFire rf ws A' hs hc
        · exact ihOk rf ws A'
            (selTaken_mono reg rw .ok rest hent rf ws A' hrestT)
      · rintro rf ws A' (⟨hsel, hs, hc⟩ | hrestT)
        · subst hsel
          exact hFire rf ws A' hs hc
        · exact ihBad rf ws A'
            (selTaken_mono reg rw .bad rest hent rf ws A' hrestT)

/-- The strongest postcondition of the erased statement (from the
    derivation's entry reach) entails the derivation's exit reach. -/
theorem post_sound : ∀ {S : Stmt} {P Q : Reach}, DStmt reg rw S P Q →
    ∀ rf ws A, Stmt.sp reg rw S P rf ws A → Q rf ws A
  | _, _, _, .pure _ h => fun rf ws A hsp => h rf ws A hsp.1
  | _, _, _, .block _ _ _ _ hpost => by
      rintro rf' ws' A ⟨rf, ws, hlen, hP, rfl, rfl⟩
      exact hpost rf ws A hlen hP
  | _, _, _, .blockA _ _ _ _ _ hpost => by
      rintro rf' ws' A ⟨rf, ws, hlen, hP, rfl, rfl⟩
      exact hpost rf ws A hlen hP
  | _, _, _, .seq a b => fun rf ws A hsp =>
      post_sound b rf ws A
        (Stmt.sp_mono reg rw _ (post_sound a) rf ws A hsp)
  | _, _, _, .ite _ _ thn els => by
      rintro rf ws A (h | h)
      · exact post_sound thn rf ws A h
      · exact post_sound els rf ws A h
  | _, _, _, .«when» _ _ body hskip => by
      rintro rf ws A (h | ⟨hP, hn⟩)
      · exact post_sound body rf ws A h
      · exact hskip rf ws A hP hn
  | _, _, _, .ghost _ _ _ => fun _ _ _ hsp => hsp
  | _, _, _, .call _ _ _ hpost => fun rf ws A hsp => hpost rf ws A hsp
  | _, _, _, .blockAt _ _ _ _ _ _ _ hpost =>
      Stmt.sp_blockAt_split reg rw fun rf ws A win rest hlen hP hsat hR =>
        hpost rf ws A win rest hlen hP hsat hR
  | _, _, _, .readAt _ _ _ _ _ _ _ hpost =>
      Stmt.sp_readAt_split reg rw fun rf ws A robytes rest hlen hP hsat hR =>
        hpost rf ws A robytes rest hlen hP hsat hR
  | _, _, _, .dwhile _ _ _ _ _ _ _ => fun _ _ _ hsp => hsp
  | _, _, _, .doWhile _ _ _ _ _ _ => fun _ _ _ hsp => hsp
  | _, _, _, .dwhileS _ _ _ _ _ _ _ => fun _ _ _ hsp => hsp
  | _, _, _, .doWhileS _ _ _ _ _ _ => fun _ _ _ hsp => hsp
  | _, _, _, .dwhileBreak _ _ _ _ _ _ _ _ _ _ _ _ => fun _ _ _ hsp => hsp
  | _, _, _, .dwhileHeader _ _ _ _ _ _ _ _ => fun _ _ _ hsp => hsp
  | _, _, _, .retJalr _ => fun _ _ _ hsp => hsp
  | _, _, _, .dretCascade lbl stages inv B (Sok := Sok) (Sbad := Sbad)
      hinit hchain okD badD => by
      rintro rf ws A (hok | hbad)
      · exact post_sound okD rf ws A
          (Stmt.sp_mono reg rw Sok
            (fun rf ws A h =>
              (Nat.zero_add stages.length ▸
                (cascadeChain_bridge reg rw stages inv B "" 0 hchain).2.1)
                rf ws A
                (cascadeFall_mono reg rw stages hinit rf ws A h))
            rf ws A hok)
      · exact post_sound badD rf ws A
          (Stmt.sp_mono reg rw Sbad
            (fun rf ws A h =>
              (cascadeChain_bridge reg rw stages inv B "" 0 hchain).2.2
                rf ws A
                (cascadeBad_mono reg rw stages hinit rf ws A h))
            rf ws A hbad)
  | _, _, _, .dretIf _ _ thn els => by
      rintro rf ws A (h | h)
      · exact post_sound thn rf ws A h
      · exact post_sound els rf ws A h
  | _, _, _, .dretWhileBreakSwap lbl guard fuel inv mid breakCond
      (Sbb := Sbb) (Sbt := Sbt)
      hinit bodyBefore bodyAfter hexh guardTail breakTail => by
      rintro rf ws A (hgt | hbt)
      · exact post_sound guardTail rf ws A hgt
      · exact post_sound breakTail rf ws A
          (Stmt.sp_mono reg rw Sbt
            (fun rf ws A hr =>
              ⟨hr.1.elim fun i hi => ⟨i, hi.1,
                post_sound (bodyBefore i) rf ws A
                  (Stmt.sp_mono reg rw Sbb (fun _ _ _ h => ⟨hi.1, h⟩)
                    rf ws A hi.2)⟩,
               hr.2⟩)
            rf ws A hbt)
  | _, _, _, .dretWhileHeaderBreak lbl guard fuel inv mid hend breakCond
      stages cinv B (Sbb := Sbb) (Sok := Sok) (Sbad := Sbad)
      header bodyBefore bodyAfter hexh hcasc0 hchain okD badD => by
      rintro rf ws A (hok | hbad)
      · exact post_sound okD rf ws A
          (Stmt.sp_mono reg rw Sok
            (fun rf ws A h =>
              (Nat.zero_add stages.length ▸
                (cascadeChain_bridge reg rw stages cinv B "" 0 hchain).2.1)
                rf ws A
                (cascadeFall_mono reg rw stages hcasc0 rf ws A h))
            rf ws A hok)
      · exact post_sound badD rf ws A
          (Stmt.sp_mono reg rw Sbad
            (fun rf ws A h => h.elim
              (fun hB => Or.inl
                ((cascadeChain_bridge reg rw stages cinv B "" 0 hchain).2.2
                  rf ws A
                  (cascadeBad_mono reg rw stages hcasc0 rf ws A hB)))
              (fun hbr => Or.inr
                ⟨hbr.1.elim fun i hi => ⟨i, hi.1,
                  post_sound (bodyBefore i) rf ws A
                    (Stmt.sp_mono reg rw Sbb (fun _ _ _ h => ⟨hi.1, h⟩)
                      rf ws A hi.2)⟩,
                 hbr.2⟩))
            rf ws A hbad)
  | _, _, _, .dretSelCascadeLoop lbl stages cinv A B C setup guard fuel linv
      body preT (Sok := Sok) (Sbad := Sbad)
      hchain0 hchain hsetupOk hsetupMem hinit hbodyOk hbodyMem hstep hexh
      hexit hpreOk hpreMem hpre okD badD => by
      rintro rf ws A' (hok | hbad)
      · refine post_sound okD rf ws A'
          (Stmt.sp_mono reg rw Sok (fun rf ws A' h => ?_) rf ws A' hok)
        rcases h with h1 | h2 | h3
        · exact (selCascadeChain_bridge reg rw stages cinv A B C "" 0
            hchain).2.2.2.1 rf ws A'
            (selTaken_mono reg rw .ok stages hchain0 rf ws A' h1)
        · exact hexit rf ws A' h2
        · exact hpre rf ws A'
            (cascadeStep_mono reg rw preT
              (fun rf ws A' h =>
                (selCascadeChain_bridge reg rw stages cinv A B C "" 0
                  hchain).2.2.1 rf ws A'
                  (selTaken_mono reg rw .pre stages hchain0 rf ws A' h))
              rf ws A' h3)
      · exact post_sound badD rf ws A'
          (Stmt.sp_mono reg rw Sbad
            (fun rf ws A' h =>
              (selCascadeChain_bridge reg rw stages cinv A B C "" 0
                hchain).2.2.2.2 rf ws A'
                (selTaken_mono reg rw .bad stages hchain0 rf ws A' h))
            rf ws A' hbad)
  | _, _, _, .callAt _ _ _ _ _ _ hpost => by
      rintro rf' ws' A'' ⟨rf, ws, A, rest, hlen, hP, hsat, hroR, hfpost, rfl⟩
      exact hpost rf ws A rest hlen hP hsat hroR rf' ws' hfpost

/-- Every VC the generator emits for the erased statement (at the
    derivation's entry reach) holds — the obligations were carried by the
    derivation's constructors. -/
theorem vcs_hold : ∀ {S : Stmt} {P Q : Reach}, DStmt reg rw S P Q →
    ∀ pfx : String, VCs.Hold (Stmt.vcs reg rw S pfx P)
  | _, _, _, .pure _ _, _ =>
      VCs.Hold.cons_intro (fun _ _ _ _ => trivial) VCs.Hold.nil
  | _, _, _, .block lbl is hok hmem _, pfx => by
      by_cases hl : hasLoad is
      · simp only [Stmt.vcs, if_pos hl]
        exact VCs.Hold.cons_intro hok
          (VCs.Hold.cons_intro (hmem hl) VCs.Hold.nil)
      · simp only [Stmt.vcs, if_neg hl]
        exact VCs.Hold.cons_intro hok VCs.Hold.nil
  | _, _, _, .blockA lbl a is hok hmem _, pfx => by
      by_cases hl : hasLoad is
      · simp only [Stmt.vcs, if_pos hl]
        exact VCs.Hold.cons_intro hok
          (VCs.Hold.cons_intro (hmem hl) VCs.Hold.nil)
      · simp only [Stmt.vcs, if_neg hl]
        exact VCs.Hold.cons_intro hok VCs.Hold.nil
  | _, _, _, .seq a b, pfx =>
      VCs.Hold.append_intro (vcs_hold a pfx)
        (Stmt.vcs_antitone reg rw _ pfx (post_sound a) (vcs_hold b pfx))
  | _, _, _, .ite _ _ thn els, pfx =>
      VCs.Hold.append_intro (vcs_hold thn _) (vcs_hold els _)
  | _, _, _, .«when» _ _ body _, pfx => vcs_hold body _
  | _, _, _, .ghost _ _ h, _ =>
      VCs.Hold.cons_intro (fun rf ws A hr => h rf ws A hr) VCs.Hold.nil
  | _, _, _, .call _ _ hpre _, _ =>
      VCs.Hold.cons_intro (fun rf ws A hr => hpre rf ws A hr) VCs.Hold.nil
  | _, _, _, .blockAt lbl p winR is hok hfocus hmem _, pfx => by
      by_cases hl : hasLoad is
      · simp only [Stmt.vcs, if_pos hl]
        exact VCs.Hold.cons_intro hok (VCs.Hold.cons_intro hfocus
          (VCs.Hold.cons_intro (hmem hl) VCs.Hold.nil))
      · simp only [Stmt.vcs, if_neg hl]
        exact VCs.Hold.cons_intro hok
          (VCs.Hold.cons_intro hfocus VCs.Hold.nil)
  | _, _, _, .readAt lbl p roR is hok hfocus hmem _, pfx => by
      by_cases hl : hasLoad is
      · simp only [Stmt.vcs, if_pos hl]
        exact VCs.Hold.cons_intro hok (VCs.Hold.cons_intro hfocus
          (VCs.Hold.cons_intro (hmem hl) VCs.Hold.nil))
      · simp only [Stmt.vcs, if_neg hl]
        exact VCs.Hold.cons_intro hok
          (VCs.Hold.cons_intro hfocus VCs.Hold.nil)
  | _, _, _, .dwhile lbl c fuel inv (Sb := Sb) hinit body hexh, pfx =>
      VCs.Hold.cons_intro hinit
        (VCs.Hold.cons_intro
          (fun i hi rf' ws' A' hsp =>
            post_sound (body i) rf' ws' A'
              (Stmt.sp_mono reg rw Sb (fun _ _ _ hr => ⟨hi, hr⟩)
                rf' ws' A' hsp))
          (VCs.Hold.cons_intro hexh
            (Stmt.vcs_exists reg rw Sb _
              (fun i rf ws A => i < fuel ∧ inv i rf ws A ∧ c.holds rf)
              (fun i => vcs_hold (body i) _))))
  | _, _, _, .doWhile lbl c fuel inv (Sb := Sb) (P := P) body hexh, pfx =>
      VCs.Hold.cons_intro
        (fun rf' ws' A' hsp =>
          post_sound (body none) rf' ws' A'
            (Stmt.sp_mono reg rw Sb (fun _ _ _ hr => hr) rf' ws' A' hsp))
        (VCs.Hold.cons_intro
          (fun i hi rf' ws' A' hsp =>
            post_sound (body (some i)) rf' ws' A'
              (Stmt.sp_mono reg rw Sb (fun _ _ _ hr => ⟨hi, hr⟩)
                rf' ws' A' hsp))
          (VCs.Hold.cons_intro hexh
            (Stmt.vcs_antitone reg rw Sb _
              (fun rf ws A hr => by
                rcases hr with hr | ⟨i, hi⟩
                · exact ⟨none, hr⟩
                · exact ⟨some i, hi⟩)
              (Stmt.vcs_exists reg rw Sb _
                (fun x rf ws A => match x with
                  | none => P rf ws A
                  | some i => i < fuel ∧ inv i rf ws A ∧ c.holds rf)
                (fun x => vcs_hold (body x) _)))))
  | _, _, _, .dwhileS lbl c fuel inv (Sb := Sb) (P := P) hinit body hexh,
      pfx =>
      VCs.Hold.cons_intro hinit
        (VCs.Hold.cons_intro
          (fun rf₀ ws₀ A₀ hP i hi rf' ws' A' hsp =>
            post_sound (body rf₀ ws₀ A₀ i) rf' ws' A'
              (Stmt.sp_mono reg rw Sb
                (fun _ _ _ hr => ⟨hP, hi, hr.1, hr.2⟩) rf' ws' A' hsp))
          (VCs.Hold.cons_intro hexh
            (Stmt.vcs_antitone reg rw Sb _
              (fun rf ws A hr => by
                rcases hr with ⟨rf₀, ws₀, A₀, hP, i, hi, hinv, hc⟩
                exact ⟨(rf₀, ws₀, A₀, i), hP, hi, hinv, hc⟩)
              (Stmt.vcs_exists reg rw Sb
                (hι := ⟨(fun _ => 0, [], fun _ => True, 0)⟩) _
                (fun (x : RegFile × List (BitVec 8) × Assertion × Nat)
                    rf ws A => P x.1 x.2.1 x.2.2.1
                  ∧ x.2.2.2 < fuel
                  ∧ inv x.1 x.2.1 x.2.2.1 x.2.2.2 rf ws A ∧ c.holds rf)
                (fun x => vcs_hold (body x.1 x.2.1 x.2.2.1 x.2.2.2) _)))))
  | _, _, _, .doWhileS lbl c fuel inv (Sb := Sb) (P := P) body hexh, pfx =>
      VCs.Hold.cons_intro
        (fun rf₀ ws₀ A₀ hP rf' ws' A' hsp =>
          post_sound (body (rf₀, ws₀, A₀, none)) rf' ws' A'
            (Stmt.sp_mono reg rw Sb (fun _ _ _ hr => ⟨hP, hr⟩)
              rf' ws' A' hsp))
        (VCs.Hold.cons_intro
          (fun rf₀ ws₀ A₀ hP i hi rf' ws' A' hsp =>
            post_sound (body (rf₀, ws₀, A₀, some i)) rf' ws' A'
              (Stmt.sp_mono reg rw Sb
                (fun _ _ _ hr => ⟨hP, hi, hr.1, hr.2⟩) rf' ws' A' hsp))
          (VCs.Hold.cons_intro hexh
            (Stmt.vcs_antitone reg rw Sb _
              (fun rf ws A hr => by
                rcases hr with hP | ⟨rf₀, ws₀, A₀, hP, i, hi, hinv, hc⟩
                · exact ⟨(rf, ws, A, none), hP, rfl, rfl, rfl⟩
                · exact ⟨(rf₀, ws₀, A₀, some i), hP, hi, hinv, hc⟩)
              (Stmt.vcs_exists reg rw Sb
                (hι := ⟨(fun _ => 0, [], fun _ => True, none)⟩) _
                (fun (x : RegFile × List (BitVec 8) × Assertion × Option Nat)
                    rf ws A => match x with
                  | (rf₀, ws₀, A₀, none) =>
                      P rf₀ ws₀ A₀ ∧ Reach.exact rf₀ ws₀ A₀ rf ws A
                  | (rf₀, ws₀, A₀, some i) =>
                      P rf₀ ws₀ A₀ ∧ i < fuel
                        ∧ inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
                (fun x => vcs_hold (body x) _)))))
  | _, _, _, .dwhileBreak lbl guard fuel inv mid breakCond
      (Sbb := Sbb) (Sba := Sba) hinit bodyBefore bodyAfter hexh hguard
      hbreak, pfx =>
      VCs.Hold.cons_intro hinit
        (VCs.Hold.cons_intro
          (fun i hi rf' ws' A' hsp =>
            post_sound (bodyAfter i) rf' ws' A'
              (Stmt.sp_mono reg rw Sba
                (fun rf ws A hr =>
                  ⟨hi, post_sound (bodyBefore i) rf ws A
                    (Stmt.sp_mono reg rw Sbb (fun _ _ _ h => ⟨hi, h⟩)
                      rf ws A hr.1),
                   hr.2⟩)
                rf' ws' A' hsp))
          (VCs.Hold.cons_intro hexh
            (VCs.Hold.cons_intro hguard
              (VCs.Hold.cons_intro
                (fun i hi rf' ws' A' hsp hbr =>
                  hbreak i hi rf' ws' A'
                    (post_sound (bodyBefore i) rf' ws' A'
                      (Stmt.sp_mono reg rw Sbb (fun _ _ _ h => ⟨hi, h⟩)
                        rf' ws' A' hsp))
                    hbr)
                (VCs.Hold.append_intro
                  (Stmt.vcs_exists reg rw Sbb _
                    (fun i rf ws A => i < fuel ∧ inv i rf ws A
                      ∧ guard.holds rf)
                    (fun i => vcs_hold (bodyBefore i) _))
                  (Stmt.vcs_antitone reg rw Sba _
                    (fun rf ws A hr => by
                      rcases hr with ⟨i, hi, hbb, hnbr⟩
                      exact ⟨i, hi,
                        post_sound (bodyBefore i) rf ws A
                          (Stmt.sp_mono reg rw Sbb (fun _ _ _ h => ⟨hi, h⟩)
                            rf ws A hbb),
                        hnbr⟩)
                    (Stmt.vcs_exists reg rw Sba _
                      (fun i rf ws A => i < fuel ∧ mid i rf ws A
                        ∧ ¬ breakCond.holds rf)
                      (fun i => vcs_hold (bodyAfter i) _))))))))
  | _, _, _, .dwhileHeader lbl c fuel inv mid (Sh := Sh) (Sb := Sb)
      (P := P) header body hexh, pfx =>
      VCs.Hold.cons_intro
        (fun rf' ws' A' hsp =>
          post_sound (header none) rf' ws' A'
            (Stmt.sp_mono reg rw Sh (fun _ _ _ hr => hr) rf' ws' A' hsp))
        (VCs.Hold.cons_intro
          (fun i hi rf' ws' A' hsp =>
            post_sound (header (some i)) rf' ws' A'
              (Stmt.sp_mono reg rw Sh
                (fun rf ws A hr =>
                  ⟨hi, post_sound (body i) rf ws A
                    (Stmt.sp_mono reg rw Sb (fun _ _ _ h => ⟨hi, h⟩)
                      rf ws A hr)⟩)
                rf' ws' A' hsp))
          (VCs.Hold.cons_intro hexh
            (VCs.Hold.append_intro
              (Stmt.vcs_antitone reg rw Sh _
                (fun rf ws A hr => by
                  rcases hr with hP | ⟨i, hi, hspb⟩
                  · exact ⟨none, hP⟩
                  · exact ⟨some i, hi,
                      post_sound (body i) rf ws A
                        (Stmt.sp_mono reg rw Sb (fun _ _ _ h => ⟨hi, h⟩)
                          rf ws A hspb)⟩)
                (Stmt.vcs_exists reg rw Sh _
                  (fun x rf ws A => match x with
                    | none => P rf ws A
                    | some i => i < fuel ∧ mid i rf ws A)
                  (fun x => vcs_hold (header x) _)))
              (Stmt.vcs_exists reg rw Sb _
                (fun i rf ws A => i < fuel ∧ inv i rf ws A ∧ c.holds rf)
                (fun i => vcs_hold (body i) _)))))
  | _, _, _, .retJalr _, _ => VCs.Hold.nil
  | _, _, _, .dretCascade lbl stages inv B (Sok := Sok) (Sbad := Sbad)
      hinit hchain okD badD, pfx =>
      VCs.Hold.append_intro
        (Stmt.cascadeVcs_antitone reg rw stages _ 0 hinit
          (cascadeChain_bridge reg rw stages inv B _ 0 hchain).1)
        (VCs.Hold.append_intro
          (Stmt.vcs_antitone reg rw Sok _
            (fun rf ws A h =>
              (Nat.zero_add stages.length ▸
                (cascadeChain_bridge reg rw stages inv B "" 0 hchain).2.1)
                rf ws A
                (cascadeFall_mono reg rw stages hinit rf ws A h))
            (vcs_hold okD _))
          (Stmt.vcs_antitone reg rw Sbad _
            (fun rf ws A h =>
              (cascadeChain_bridge reg rw stages inv B "" 0 hchain).2.2
                rf ws A
                (cascadeBad_mono reg rw stages hinit rf ws A h))
            (vcs_hold badD _)))
  | _, _, _, .dretIf _ _ thn els, pfx =>
      VCs.Hold.append_intro (vcs_hold thn _) (vcs_hold els _)
  | _, _, _, .dretWhileBreakSwap lbl guard fuel inv mid breakCond
      (Sbb := Sbb) (Sba := Sba) (Sbt := Sbt)
      hinit bodyBefore bodyAfter hexh guardTail breakTail, pfx =>
      VCs.Hold.cons_intro hinit
        (VCs.Hold.cons_intro
          (fun i hi rf' ws' A' hsp =>
            post_sound (bodyAfter i) rf' ws' A'
              (Stmt.sp_mono reg rw Sba
                (fun rf ws A hr =>
                  ⟨hi, post_sound (bodyBefore i) rf ws A
                    (Stmt.sp_mono reg rw Sbb (fun _ _ _ h => ⟨hi, h⟩)
                      rf ws A hr.1),
                   hr.2⟩)
                rf' ws' A' hsp))
          (VCs.Hold.cons_intro hexh
            (VCs.Hold.append_intro
              (VCs.Hold.append_intro
                (VCs.Hold.append_intro
                  (Stmt.vcs_exists reg rw Sbb _
                    (fun i rf ws A => i < fuel ∧ inv i rf ws A
                      ∧ guard.holds rf)
                    (fun i => vcs_hold (bodyBefore i) _))
                  (Stmt.vcs_antitone reg rw Sba _
                    (fun rf ws A hr => by
                      rcases hr with ⟨i, hi, hbb, hnbr⟩
                      exact ⟨i, hi,
                        post_sound (bodyBefore i) rf ws A
                          (Stmt.sp_mono reg rw Sbb (fun _ _ _ h => ⟨hi, h⟩)
                            rf ws A hbb),
                        hnbr⟩)
                    (Stmt.vcs_exists reg rw Sba _
                      (fun i rf ws A => i < fuel ∧ mid i rf ws A
                        ∧ ¬ breakCond.holds rf)
                      (fun i => vcs_hold (bodyAfter i) _))))
                (vcs_hold guardTail _))
              (Stmt.vcs_antitone reg rw Sbt _
                (fun rf ws A hr =>
                  ⟨hr.1.elim fun i hi => ⟨i, hi.1,
                    post_sound (bodyBefore i) rf ws A
                      (Stmt.sp_mono reg rw Sbb (fun _ _ _ h => ⟨hi.1, h⟩)
                        rf ws A hi.2)⟩,
                   hr.2⟩)
                (vcs_hold breakTail _)))))
  | _, _, _, .dretWhileHeaderBreak lbl guard fuel inv mid hend breakCond
      stages cinv B (Sh := Sh) (Sbb := Sbb) (Sba := Sba) (Sok := Sok)
      (Sbad := Sbad) (P := P)
      header bodyBefore bodyAfter hexh hcasc0 hchain okD badD, pfx =>
      VCs.Hold.cons_intro
        (fun rf' ws' A' hsp =>
          post_sound (header none) rf' ws' A'
            (Stmt.sp_mono reg rw Sh (fun _ _ _ hr => hr) rf' ws' A' hsp))
        (VCs.Hold.cons_intro
          (fun i hi rf' ws' A' hsp =>
            post_sound (header (some i)) rf' ws' A'
              (Stmt.sp_mono reg rw Sh
                (fun rf ws A hr =>
                  ⟨hi, post_sound (bodyAfter i) rf ws A
                    (Stmt.sp_mono reg rw Sba
                      (fun rf ws A hr2 =>
                        ⟨hi, post_sound (bodyBefore i) rf ws A
                          (Stmt.sp_mono reg rw Sbb (fun _ _ _ h => ⟨hi, h⟩)
                            rf ws A hr2.1),
                         hr2.2⟩)
                      rf ws A hr)⟩)
                rf' ws' A' hsp))
          (VCs.Hold.cons_intro hexh
            (VCs.Hold.append_intro
              (VCs.Hold.append_intro
                (VCs.Hold.append_intro
                  (VCs.Hold.append_intro
                    (VCs.Hold.append_intro
                      (Stmt.vcs_antitone reg rw Sh _
                        (fun rf ws A hr => by
                          rcases hr with hP | ⟨i, hi, hspb⟩
                          · exact ⟨none, hP⟩
                          · exact ⟨some i, hi,
                              post_sound (bodyAfter i) rf ws A
                                (Stmt.sp_mono reg rw Sba
                                  (fun rf ws A hr2 =>
                                    ⟨hi, post_sound (bodyBefore i) rf ws A
                                      (Stmt.sp_mono reg rw Sbb
                                        (fun _ _ _ h => ⟨hi, h⟩)
                                        rf ws A hr2.1),
                                     hr2.2⟩)
                                  rf ws A hspb)⟩)
                        (Stmt.vcs_exists reg rw Sh _
                          (fun x rf ws A => match x with
                            | none => P rf ws A
                            | some i => i < fuel ∧ hend i rf ws A)
                          (fun x => vcs_hold (header x) _)))
                      (Stmt.vcs_exists reg rw Sbb _
                        (fun i rf ws A => i < fuel ∧ inv i rf ws A
                          ∧ guard.holds rf)
                        (fun i => vcs_hold (bodyBefore i) _)))
                    (Stmt.vcs_antitone reg rw Sba _
                      (fun rf ws A hr => by
                        rcases hr with ⟨i, hi, hbb, hnbr⟩
                        exact ⟨i, hi,
                          post_sound (bodyBefore i) rf ws A
                            (Stmt.sp_mono reg rw Sbb (fun _ _ _ h => ⟨hi, h⟩)
                              rf ws A hbb),
                          hnbr⟩)
                      (Stmt.vcs_exists reg rw Sba _
                        (fun i rf ws A => i < fuel ∧ mid i rf ws A
                          ∧ ¬ breakCond.holds rf)
                        (fun i => vcs_hold (bodyAfter i) _))))
                  (Stmt.cascadeVcs_antitone reg rw stages _ 0 hcasc0
                    (cascadeChain_bridge reg rw stages cinv B _ 0 hchain).1))
                (Stmt.vcs_antitone reg rw Sok _
                  (fun rf ws A h =>
                    (Nat.zero_add stages.length ▸
                      (cascadeChain_bridge reg rw stages cinv B "" 0 hchain).2.1)
                      rf ws A
                      (cascadeFall_mono reg rw stages hcasc0 rf ws A h))
                  (vcs_hold okD _)))
              (Stmt.vcs_antitone reg rw Sbad _
                (fun rf ws A h => h.elim
                  (fun hB => Or.inl
                    ((cascadeChain_bridge reg rw stages cinv B "" 0 hchain).2.2
                      rf ws A
                      (cascadeBad_mono reg rw stages hcasc0 rf ws A hB)))
                  (fun hbr => Or.inr
                    ⟨hbr.1.elim fun i hi => ⟨i, hi.1,
                      post_sound (bodyBefore i) rf ws A
                        (Stmt.sp_mono reg rw Sbb (fun _ _ _ h => ⟨hi.1, h⟩)
                          rf ws A hi.2)⟩,
                     hbr.2⟩))
                (vcs_hold badD _)))))
  | _, _, _, .dretSelCascadeLoop lbl stages cinv A B C setup guard fuel linv
      body preT (Sok := Sok) (Sbad := Sbad)
      hchain0 hchain hsetupOk hsetupMem hinit hbodyOk hbodyMem hstep hexh
      hexit hpreOk hpreMem hpre okD badD, pfx =>
      VCs.Hold.cons_intro hsetupOk
        (VCs.Hold.cons_intro
          (fun hl rf ws A' hlen hr => hsetupMem hl rf ws A' hlen
            ((Nat.zero_add stages.length ▸
              (selCascadeChain_bridge reg rw stages cinv A B C "" 0
                hchain).2.1) rf ws A'
              (selFall_mono reg rw stages hchain0 rf ws A' hr)))
          (VCs.Hold.cons_intro
            (fun rf ws A' hsp => hinit rf ws A'
              (cascadeStep_mono reg rw setup
                (fun rf ws A' hr =>
                  (Nat.zero_add stages.length ▸
                    (selCascadeChain_bridge reg rw stages cinv A B C "" 0
                      hchain).2.1) rf ws A'
                    (selFall_mono reg rw stages hchain0 rf ws A' hr))
                rf ws A' hsp))
            (VCs.Hold.cons_intro hbodyOk
              (VCs.Hold.cons_intro hbodyMem
                (VCs.Hold.cons_intro hstep
                  (VCs.Hold.cons_intro hexh
                    (VCs.Hold.cons_intro hpreOk
                      (VCs.Hold.cons_intro
                        (fun hl rf ws A' hlen hr => hpreMem hl rf ws A' hlen
                          ((selCascadeChain_bridge reg rw stages cinv A B C
                            "" 0 hchain).2.2.1 rf ws A'
                            (selTaken_mono reg rw .pre stages hchain0
                              rf ws A' hr)))
                        (VCs.Hold.append_intro
                          (VCs.Hold.append_intro
                            (Stmt.selCascadeVcs_antitone reg rw stages _ 0
                              hchain0
                              (selCascadeChain_bridge reg rw stages cinv
                                A B C _ 0 hchain).1)
                            (Stmt.vcs_antitone reg rw Sok _
                              (fun rf ws A' h => by
                                rcases h with h1 | h2 | h3
                                · exact (selCascadeChain_bridge reg rw stages
                                    cinv A B C "" 0 hchain).2.2.2.1 rf ws A'
                                    (selTaken_mono reg rw .ok stages hchain0
                                      rf ws A' h1)
                                · exact hexit rf ws A' h2
                                · exact hpre rf ws A'
                                    (cascadeStep_mono reg rw preT
                                      (fun rf ws A' h =>
                                        (selCascadeChain_bridge reg rw stages
                                          cinv A B C "" 0 hchain).2.2.1
                                          rf ws A'
                                          (selTaken_mono reg rw .pre stages
                                            hchain0 rf ws A' h))
                                      rf ws A' h3))
                              (vcs_hold okD _)))
                          (Stmt.vcs_antitone reg rw Sbad _
                            (fun rf ws A' h =>
                              (selCascadeChain_bridge reg rw stages cinv
                                A B C "" 0 hchain).2.2.2.2 rf ws A'
                                (selTaken_mono reg rw .bad stages hchain0
                                  rf ws A' h))
                            (vcs_hold badD _))))))))))))
  | _, _, _, .callAt _ _ _ hfocus hpre hemp _, _ =>
      VCs.Hold.cons_intro hfocus
        (VCs.Hold.cons_intro hpre
          (VCs.Hold.cons_intro hemp VCs.Hold.nil))

end DStmt

-- ============================================================================
-- Packaged derivations: the calc-chain carrier
-- ============================================================================

/-- A derivation packaged with the statement it justifies.  This is the
    binary "relation" a proof-first routine is written in: a value of
    `DCode reg rw P Q` witnesses that some code carries `P` to `Q`, and
    the code is the `Σ`-projection. -/
def DCode (reg : Region) (rw : RwRegion) (P Q : Reach) : Type :=
  (S : Stmt) × DStmt reg rw S P Q

/-- `calc` support: derivations compose by sequencing their code. -/
instance {reg : Region} {rw : RwRegion} :
    Trans (DCode reg rw) (DCode reg rw) (DCode reg rw) where
  trans a b := ⟨.seq a.1 b.1, .seq a.2 b.2⟩

/-- `calc` support at the unfolded endpoint type: when a calc endpoint is a
    lambda, its inferred type is the unfolding of `Reach`, and instance
    unification (at `instances` transparency) will not fold it back — this
    twin instance carries the same `trans` at the unfolded type. -/
instance {reg : Region} {rw : RwRegion} :
    @Trans (RegFile → List (BitVec 8) → Assertion → Prop)
      (RegFile → List (BitVec 8) → Assertion → Prop)
      (RegFile → List (BitVec 8) → Assertion → Prop)
      (DCode reg rw) (DCode reg rw) (DCode reg rw) where
  trans a b := ⟨.seq a.1 b.1, .seq a.2 b.2⟩

/-- `RegFile` is a def alias, opaque to instance search; the snapshot-loop
    smart constructors use `default` as the canonical family point. -/
instance : Inhabited RegFile := ⟨fun _ => 0⟩

/-- Likewise for `Assertion`. -/
instance : Inhabited Assertion := ⟨fun _ => True⟩

namespace DCode

variable {reg : Region} {rw : RwRegion}

/-- The generated statement. -/
def stmt {P Q : Reach} (d : DCode reg rw P Q) : Stmt := d.1

/-- The generated machine code at `base`. -/
def program {P Q : Reach} (d : DCode reg rw P Q) (base : Word) : Program :=
  d.1.flatten base

/-- Number of machine instructions generated. -/
def size {P Q : Reach} (d : DCode reg rw P Q) : Nat := d.1.size

/-- Step bound of the generated code. -/
def steps {P Q : Reach} (d : DCode reg rw P Q) : Nat := d.1.steps

/-- Sequencing (what `calc`/`Trans` uses). -/
def seq {P Q R : Reach} (a : DCode reg rw P Q) (b : DCode reg rw Q R) :
    DCode reg rw P R :=
  ⟨.seq a.1 b.1, .seq a.2 b.2⟩

/-- Pure step: entailment/iff of assertions, zero instructions. -/
def pure (lbl : String) {P Q : Reach}
    (h : ∀ rf ws A, P rf ws A → Q rf ws A) : DCode reg rw P Q :=
  ⟨_, .pure lbl h⟩

/-- Straight-line machine step. -/
def block (lbl : String) (is : List Instr) {P Q : Reach}
    (hok : blockOk is = true)
    (hmem : hasLoad is = true → ∀ rf ws A, ws.length = rw.len →
      P rf ws A → blockVCs reg rw.base rf ws is)
    (hpost : ∀ rf ws A, ws.length = rw.len → P rf ws A →
      Q (execBlock reg rw.base rf ws is).1
        (execBlock reg rw.base rf ws is).2 A) : DCode reg rw P Q :=
  ⟨_, .block lbl is hok hmem hpost⟩

/-- PC-aware machine step (`la`/`AUIPC` blocks); caller-shaped path only. -/
def blockA (lbl : String) (addr : Word) (is : List Instr) {P Q : Reach}
    (hok : blockOkAt is = true)
    (hmem : hasLoad is = true → ∀ rf ws A, ws.length = rw.len →
      P rf ws A → blockVCsAt reg rw.base addr rf ws is)
    (hpost : ∀ rf ws A, ws.length = rw.len → P rf ws A →
      Q (execBlockAt reg rw.base addr rf ws is).1
        (execBlockAt reg rw.base addr rf ws is).2 A) : DCode reg rw P Q :=
  ⟨_, .blockA lbl addr is hok hmem hpost⟩

/-- if/fi. -/
def ite (lbl : String) (c : Cond) {P Q : Reach}
    (thn : DCode reg rw (fun rf ws A => P rf ws A ∧ c.holds rf) Q)
    (els : DCode reg rw (fun rf ws A => P rf ws A ∧ ¬ c.holds rf) Q) :
    DCode reg rw P Q :=
  ⟨_, .ite lbl c thn.2 els.2⟩

/-- if without else. -/
def «when» (lbl : String) (c : Cond) {P Q : Reach}
    (body : DCode reg rw (fun rf ws A => P rf ws A ∧ c.holds rf) Q)
    (hskip : ∀ rf ws A, P rf ws A → ¬ c.holds rf → Q rf ws A) :
    DCode reg rw P Q :=
  ⟨_, .«when» lbl c body.2 hskip⟩

/-- Ghost step (ambient-assertion surgery), zero instructions. -/
def ghost (lbl : String) {P : Reach}
    (Rr : RegFile → List (BitVec 8) → Assertion → Assertion → Prop)
    (h : ∀ rf ws A, P rf ws A → A.pcFree → (∃ hp, A hp) →
      ∃ A', Rr rf ws A A' ∧ (∀ hp, A hp → A' hp) ∧ A'.pcFree) :
    DCode reg rw P
      (fun rf ws A' => ∃ A, P rf ws A ∧ (∃ hp, A hp) ∧ Rr rf ws A A') :=
  ⟨_, .ghost lbl Rr h⟩

/-- Call to a verified routine. -/
def call (lbl : String) (f : FnHandle) {P Q : Reach}
    (hpre : ∀ rf ws A, P rf ws A → f.pre rf ws A)
    (hpost : ∀ rf ws A, f.post rf ws A → Q rf ws A) : DCode reg rw P Q :=
  ⟨_, .call lbl f hpre hpost⟩

/-- Write-focus block. -/
def blockAt (lbl : String) (p : Reg)
    (winR : RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop)
    (is : List Instr) {P Q : Reach}
    (hok : blockOk is = true)
    (hfocus : ∀ rf ws A, P rf ws A → A.pcFree → ∀ hp, A hp →
      ∃ win rest, winR rf ws A win rest
        ∧ (bytesRegion (rf.get p) win ** rest) hp
        ∧ rest.pcFree ∧ RwRegion.wf ⟨rf.get p, win.length⟩)
    (hmem : hasLoad is = true → ∀ rf ws A win rest, ws.length = rw.len →
      P rf ws A → winR rf ws A win rest →
      (∃ hp, (bytesRegion (rf.get p) win ** rest) hp) →
      blockVCs reg (rf.get p) rf win is)
    (hpost : ∀ rf ws A win rest, ws.length = rw.len → P rf ws A →
      (∃ hp, (bytesRegion (rf.get p) win ** rest) hp) →
      winR rf ws A win rest →
      Q (execBlock reg (rf.get p) rf win is).1 ws
        ((bytesRegion (rf.get p) (execBlock reg (rf.get p) rf win is).2)
          ** rest)) : DCode reg rw P Q :=
  ⟨_, .blockAt lbl p winR is hok hfocus hmem hpost⟩

/-- Read-focus block. -/
def readAt (lbl : String) (p : Reg)
    (roR : RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop)
    (is : List Instr) {P Q : Reach}
    (hok : blockOk is = true)
    (hfocus : ∀ rf ws A, P rf ws A → A.pcFree → ∀ hp, A hp →
      ∃ robytes rest, roR rf ws A robytes rest
        ∧ (bytesRegion (rf.get p) robytes ** rest) hp
        ∧ rest.pcFree ∧ Region.wf ⟨rf.get p, robytes⟩)
    (hmem : hasLoad is = true → ∀ rf ws A robytes rest,
      ws.length = rw.len → P rf ws A → roR rf ws A robytes rest →
      (∃ hp, (bytesRegion (rf.get p) robytes ** rest) hp) →
      blockVCs ⟨rf.get p, robytes⟩ rw.base rf ws is)
    (hpost : ∀ rf ws A robytes rest, ws.length = rw.len → P rf ws A →
      (∃ hp, (bytesRegion (rf.get p) robytes ** rest) hp) →
      roR rf ws A robytes rest →
      Q (execBlock ⟨rf.get p, robytes⟩ rw.base rf ws is).1
        (execBlock ⟨rf.get p, robytes⟩ rw.base rf ws is).2
        (bytesRegion (rf.get p) robytes ** rest)) : DCode reg rw P Q :=
  ⟨_, .readAt lbl p roR is hok hfocus hmem hpost⟩

/-- Bounded top-test loop.  `body` is a per-iteration family of packaged
    derivations; the autoparam `hcode` checks (by `rfl`) that the family
    shares one code skeleton — if the code depends on `i`, elaboration
    fails HERE, at the loop, before any proof work is wasted. -/
def dwhile (lbl : String) (c : Cond) (fuel : Nat) (inv : Nat → Reach)
    {P : Reach}
    (hinit : ∀ rf ws A, P rf ws A → inv 0 rf ws A)
    (body : (i : Nat) → DCode reg rw
      (fun rf ws A => i < fuel ∧ inv i rf ws A ∧ c.holds rf)
      (inv (i + 1)))
    (hexh : ∀ rf ws A, inv fuel rf ws A → ¬ c.holds rf)
    (hcode : ∀ i, (body i).1 = (body 0).1 := by intro i; rfl) :
    DCode reg rw P
      (fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf) :=
  ⟨.while lbl c fuel inv (body 0).1,
   .dwhile lbl c fuel inv hinit (fun i => hcode i ▸ (body i).2) hexh⟩

/-- Bounded bottom-test loop: `bodyEntry` is the unconditional first run
    (from `P` to `inv 0`), `bodyIter` the guarded reruns; both must share
    one code skeleton (checked by the `hcode` autoparam). -/
def doWhile (lbl : String) (c : Cond) (fuel : Nat) (inv : Nat → Reach)
    {P : Reach}
    (bodyEntry : DCode reg rw P (inv 0))
    (bodyIter : (i : Nat) → DCode reg rw
      (fun rf ws A => i < fuel ∧ inv i rf ws A ∧ c.holds rf)
      (inv (i + 1)))
    (hexh : ∀ rf ws A, inv fuel rf ws A → ¬ c.holds rf)
    (hcode : ∀ i, (bodyIter i).1 = bodyEntry.1 := by intro i; rfl) :
    DCode reg rw P
      (fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf) :=
  ⟨.doWhile lbl c fuel inv bodyEntry.1,
   .doWhile lbl c fuel inv
     (fun x => match x with
       | none => bodyEntry.2
       | some i => hcode i ▸ (bodyIter i).2)
     hexh⟩

/-- Bounded top-test loop with an entry-snapshot-parameterized invariant —
    the nested-loop construct.  An inner loop's invariant annotation is
    part of the shared code skeleton, so it must not mention an outer
    iteration index; outer facts survive through the snapshot
    `(rf₀, ws₀, A₀)` (the state at loop entry), whose entry-reach fact
    `P rf₀ ws₀ A₀` is available throughout the body and in the exit
    shape.  The `hcode` autoparam checks (by `rfl`) that the body family
    shares one code skeleton across snapshots and iterations. -/
def dwhileS (lbl : String) (c : Cond) (fuel : Nat)
    (inv : RegFile → List (BitVec 8) → Assertion → Nat → Reach)
    {P : Reach}
    (hinit : ∀ rf ws A, P rf ws A → inv rf ws A 0 rf ws A)
    (body : (rf₀ : RegFile) → (ws₀ : List (BitVec 8)) → (A₀ : Assertion) →
      (i : Nat) → DCode reg rw
      (fun rf ws A => P rf₀ ws₀ A₀ ∧ i < fuel
        ∧ inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
      (inv rf₀ ws₀ A₀ (i + 1)))
    (hexh : ∀ rf₀ ws₀ A₀, P rf₀ ws₀ A₀ → ∀ rf ws A,
      inv rf₀ ws₀ A₀ fuel rf ws A → ¬ c.holds rf)
    (hcode : ∀ rf₀ ws₀ A₀ i, (body rf₀ ws₀ A₀ i).1
        = (body default default default 0).1 := by intro _ _ _ _; rfl) :
    DCode reg rw P
      (fun rf ws A => ∃ rf₀ ws₀ A₀, P rf₀ ws₀ A₀
        ∧ (∃ i, i ≤ fuel ∧ inv rf₀ ws₀ A₀ i rf ws A) ∧ ¬ c.holds rf) :=
  ⟨.whileS lbl c fuel inv (body default default default 0).1,
   .dwhileS lbl c fuel inv hinit
     (fun rf₀ ws₀ A₀ i => hcode rf₀ ws₀ A₀ i ▸ (body rf₀ ws₀ A₀ i).2)
     hexh⟩

/-- Bounded bottom-test loop with an entry-snapshot-parameterized
    invariant: `bodyEntry` is the unconditional first run (from the exact
    entry state), `bodyIter` the guarded reruns; all must share one code
    skeleton (checked by the autoparams). -/
def doWhileS (lbl : String) (c : Cond) (fuel : Nat)
    (inv : RegFile → List (BitVec 8) → Assertion → Nat → Reach)
    {P : Reach}
    (bodyEntry : (rf₀ : RegFile) → (ws₀ : List (BitVec 8)) →
      (A₀ : Assertion) → DCode reg rw
      (fun rf ws A => P rf₀ ws₀ A₀ ∧ Reach.exact rf₀ ws₀ A₀ rf ws A)
      (inv rf₀ ws₀ A₀ 0))
    (bodyIter : (rf₀ : RegFile) → (ws₀ : List (BitVec 8)) →
      (A₀ : Assertion) → (i : Nat) → DCode reg rw
      (fun rf ws A => P rf₀ ws₀ A₀ ∧ i < fuel
        ∧ inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
      (inv rf₀ ws₀ A₀ (i + 1)))
    (hexh : ∀ rf₀ ws₀ A₀, P rf₀ ws₀ A₀ → ∀ rf ws A,
      inv rf₀ ws₀ A₀ fuel rf ws A → ¬ c.holds rf)
    (hcodeE : ∀ rf₀ ws₀ A₀, (bodyEntry rf₀ ws₀ A₀).1
        = (bodyEntry default default default).1 := by intro _ _ _; rfl)
    (hcodeI : ∀ rf₀ ws₀ A₀ i, (bodyIter rf₀ ws₀ A₀ i).1
        = (bodyEntry default default default).1 := by intro _ _ _ _; rfl) :
    DCode reg rw P
      (fun rf ws A => ∃ rf₀ ws₀ A₀, P rf₀ ws₀ A₀
        ∧ (∃ i, i ≤ fuel ∧ inv rf₀ ws₀ A₀ i rf ws A) ∧ ¬ c.holds rf) :=
  ⟨.doWhileS lbl c fuel inv (bodyEntry default default default).1,
   .doWhileS lbl c fuel inv
     (fun x => match x with
       | (rf₀, ws₀, A₀, none) =>
           hcodeE rf₀ ws₀ A₀ ▸ (bodyEntry rf₀ ws₀ A₀).2
       | (rf₀, ws₀, A₀, some i) =>
           hcodeI rf₀ ws₀ A₀ i ▸ (bodyIter rf₀ ws₀ A₀ i).2)
     hexh⟩

/-- Bounded loop with a mid-body break — "scan until a predicate holds".
    `bodyBefore` runs to the mid-states `mid i`; if `breakCond` holds
    control exits to `Q`, otherwise `bodyAfter` re-establishes the
    invariant.  Both exits (guard failure via `hguard`, break via
    `hbreak`) must entail the same `Q`. -/
def dwhileBreak (lbl : String) (guard : Cond) (fuel : Nat)
    (inv : Nat → Reach) (mid : Nat → Reach) (breakCond : Cond)
    {P Q : Reach}
    (hinit : ∀ rf ws A, P rf ws A → inv 0 rf ws A)
    (bodyBefore : (i : Nat) → DCode reg rw
      (fun rf ws A => i < fuel ∧ inv i rf ws A ∧ guard.holds rf)
      (mid i))
    (bodyAfter : (i : Nat) → DCode reg rw
      (fun rf ws A => i < fuel ∧ mid i rf ws A ∧ ¬ breakCond.holds rf)
      (inv (i + 1)))
    (hexh : ∀ rf ws A, inv fuel rf ws A → ¬ guard.holds rf)
    (hguard : ∀ i, i ≤ fuel → ∀ rf ws A, inv i rf ws A →
      ¬ guard.holds rf → Q rf ws A)
    (hbreak : ∀ i, i < fuel → ∀ rf ws A, mid i rf ws A →
      breakCond.holds rf → Q rf ws A)
    (hcodeB : ∀ i, (bodyBefore i).1 = (bodyBefore 0).1 := by intro i; rfl)
    (hcodeA : ∀ i, (bodyAfter i).1 = (bodyAfter 0).1 := by intro i; rfl) :
    DCode reg rw P Q :=
  ⟨.whileBreak lbl guard fuel inv Q (bodyBefore 0).1 breakCond
      (bodyAfter 0).1,
   .dwhileBreak lbl guard fuel inv mid breakCond hinit
     (fun i => hcodeB i ▸ (bodyBefore i).2)
     (fun i => hcodeA i ▸ (bodyAfter i).2)
     hexh hguard hbreak⟩

/-- Bounded top-guarded loop with a reloaded header run before every
    guard evaluation — the `header; B¬c → exit; body; JAL → header`
    idiom (guard-limit registers reloaded by `li` each trip).
    `headerEntry` is the entry run (`P ⤳ inv 0`), `headerIter` the rerun
    after the i-th body (`i < fuel ∧ mid i ⤳ inv (i+1)`); both must share
    one code skeleton, as must the body family (`hcode` autoparams). -/
def dwhileHeader (lbl : String) (c : Cond) (fuel : Nat)
    (inv : Nat → Reach) (mid : Nat → Reach) {P : Reach}
    (headerEntry : DCode reg rw P (inv 0))
    (headerIter : (i : Nat) → DCode reg rw
      (fun rf ws A => i < fuel ∧ mid i rf ws A) (inv (i + 1)))
    (body : (i : Nat) → DCode reg rw
      (fun rf ws A => i < fuel ∧ inv i rf ws A ∧ c.holds rf)
      (mid i))
    (hexh : ∀ rf ws A, inv fuel rf ws A → ¬ c.holds rf)
    (hcodeH : ∀ i, (headerIter i).1 = headerEntry.1 := by intro i; rfl)
    (hcodeB : ∀ i, (body i).1 = (body 0).1 := by intro i; rfl) :
    DCode reg rw P
      (fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf) :=
  ⟨.whileHeader lbl headerEntry.1 c fuel inv (body 0).1,
   .dwhileHeader lbl c fuel inv mid
     (fun x => match x with
       | none => headerEntry.2
       | some i => hcodeH i ▸ (headerIter i).2)
     (fun i => hcodeB i ▸ (body i).2)
     hexh⟩

/-- Call with a focused read-only region (see `DStmt.callAt`). -/
def callAt (lbl : String)
    (roR : RegFile → List (BitVec 8) → Assertion → Assertion → Prop)
    (f : FnHandle) {P Q : Reach}
    (hfocus : ∀ rf ws A, P rf ws A → A.pcFree → ∀ hp, A hp →
      ∃ rest, roR rf ws A rest
        ∧ (bytesRegion f.region.base f.region.bytes ** rest) hp
        ∧ rest.pcFree)
    (hpre : ∀ rf ws A rest, ws.length = rw.len → P rf ws A →
      roR rf ws A rest → f.pre rf ws empAssertion)
    (hemp : ∀ rf ws A, f.post rf ws A → A = empAssertion)
    (hpost : ∀ rf ws A rest, ws.length = rw.len → P rf ws A →
      (∃ hp, (bytesRegion f.region.base f.region.bytes ** rest) hp) →
      roR rf ws A rest →
      ∀ rf' ws', f.post rf' ws' empAssertion →
      Q rf' ws' (bytesRegion f.region.base f.region.bytes ** rest)) :
    DCode reg rw P Q :=
  ⟨_, .callAt lbl roR f hfocus hpre hemp hpost⟩

/-- Return to `ra`. -/
def retJalr (lbl : String) {P : Reach} : DCode reg rw P P :=
  ⟨_, .retJalr lbl⟩

/-- Branch to one of two ret-terminated tails. -/
def dretIf (lbl : String) (c : Cond) {P Q : Reach}
    (thn : DCode reg rw (fun rf ws A => P rf ws A ∧ c.holds rf) Q)
    (els : DCode reg rw (fun rf ws A => P rf ws A ∧ ¬ c.holds rf) Q) :
    DCode reg rw P Q :=
  ⟨_, .dretIf lbl c thn.2 els.2⟩

/-- Guard cascade with a shared ret-terminated bad tail. -/
def dretCascade (lbl : String) (stages : List (List Instr × Cond))
    (inv : Nat → Reach) (B : Reach) {P Q : Reach}
    (hinit : ∀ rf ws A, P rf ws A → inv 0 rf ws A)
    (hchain : CascadeChain reg rw stages inv 0 B)
    (okD : DCode reg rw (inv stages.length) Q)
    (badD : DCode reg rw B Q) : DCode reg rw P Q :=
  ⟨_, .dretCascade lbl stages inv B hinit hchain okD.2 badD.2⟩

/-- Tail-swapped return-terminating break loop — a top-guarded scan whose
    break exits to the NEAR ret tail and whose guard-exhaustion exit lands
    on the FAR tail (`B¬guard → Lgt; before; Bbreak → Lbt; after;
    JAL → header; breakTail; guardTail` — the `modexp_iszero` layout).
    The body families must share one code skeleton (`hcode` autoparams);
    both tails end at their own `ret`s in the same `Q`. -/
def dretWhileBreakSwap (lbl : String) (guard : Cond) (fuel : Nat)
    (inv : Nat → Reach) (mid : Nat → Reach) (breakCond : Cond)
    {P Q : Reach}
    (hinit : ∀ rf ws A, P rf ws A → inv 0 rf ws A)
    (bodyBefore : (i : Nat) → DCode reg rw
      (fun rf ws A => i < fuel ∧ inv i rf ws A ∧ guard.holds rf)
      (mid i))
    (bodyAfter : (i : Nat) → DCode reg rw
      (fun rf ws A => i < fuel ∧ mid i rf ws A ∧ ¬ breakCond.holds rf)
      (inv (i + 1)))
    (hexh : ∀ rf ws A, inv fuel rf ws A → ¬ guard.holds rf)
    (guardTail : DCode reg rw
      (fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ guard.holds rf) Q)
    (breakTail : DCode reg rw
      (fun rf ws A => (∃ i, i < fuel ∧ mid i rf ws A) ∧ breakCond.holds rf) Q)
    (hcodeB : ∀ i, (bodyBefore i).1 = (bodyBefore 0).1 := by intro i; rfl)
    (hcodeA : ∀ i, (bodyAfter i).1 = (bodyAfter 0).1 := by intro i; rfl) :
    DCode reg rw P Q :=
  ⟨.retWhileBreakSwap lbl guard fuel inv (bodyBefore 0).1 breakCond
      (bodyAfter 0).1 guardTail.1 breakTail.1,
   .dretWhileBreakSwap lbl guard fuel inv mid breakCond hinit
     (fun i => hcodeB i ▸ (bodyBefore i).2)
     (fun i => hcodeA i ▸ (bodyAfter i).2)
     hexh guardTail.2 breakTail.2⟩

/-- Return-terminating header-reloaded break loop draining into a guard
    cascade — `header; B¬guard → exit; before; Bbreak → bad; after;
    JAL → header; exit: stages…; ok; bad`, the loop's break entering the
    cascade's shared bad tail (`edd_be32_eq`).  The header family is
    indexed by `Option Nat` (`none` = entry run); all families must
    share one code skeleton (`hcode` autoparams). -/
def dretWhileHeaderBreak (lbl : String) (guard : Cond) (fuel : Nat)
    (inv mid hend : Nat → Reach) (breakCond : Cond)
    (stages : List (List Instr × Cond)) (cinv : Nat → Reach) (B : Reach)
    {P Q : Reach}
    (header : (x : Option Nat) → DCode reg rw
      (fun rf ws A => match x with
        | none => P rf ws A
        | some i => i < fuel ∧ hend i rf ws A)
      (fun rf ws A => match x with
        | none => inv 0 rf ws A
        | some i => inv (i + 1) rf ws A))
    (bodyBefore : (i : Nat) → DCode reg rw
      (fun rf ws A => i < fuel ∧ inv i rf ws A ∧ guard.holds rf)
      (mid i))
    (bodyAfter : (i : Nat) → DCode reg rw
      (fun rf ws A => i < fuel ∧ mid i rf ws A ∧ ¬ breakCond.holds rf)
      (hend i))
    (hexh : ∀ rf ws A, inv fuel rf ws A → ¬ guard.holds rf)
    (hcasc0 : ∀ rf ws A,
      ((∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ guard.holds rf) → cinv 0 rf ws A)
    (hchain : CascadeChain reg rw stages cinv 0 B)
    (okD : DCode reg rw (cinv stages.length) Q)
    (badD : DCode reg rw
      (fun rf ws A => B rf ws A ∨
        ((∃ i, i < fuel ∧ mid i rf ws A) ∧ breakCond.holds rf)) Q)
    (hcodeH : ∀ x, (header x).1 = (header none).1 := by intro x; rfl)
    (hcodeB : ∀ i, (bodyBefore i).1 = (bodyBefore 0).1 := by intro i; rfl)
    (hcodeA : ∀ i, (bodyAfter i).1 = (bodyAfter 0).1 := by intro i; rfl) :
    DCode reg rw P Q :=
  ⟨.retWhileHeaderBreak lbl (header none).1 guard fuel inv (bodyBefore 0).1
      breakCond (bodyAfter 0).1 stages okD.1 badD.1,
   .dretWhileHeaderBreak lbl guard fuel inv mid hend breakCond stages cinv B
     (fun x => hcodeH x ▸ (header x).2)
     (fun i => hcodeB i ▸ (bodyBefore i).2)
     (fun i => hcodeA i ▸ (bodyAfter i).2)
     hexh hcasc0 hchain okD.2 badD.2⟩

/-- Return-terminating selector cascade with a terminal copy loop — the
    RLP-decode idiom (`slot_decode_u256`): guards dispatch over the pre-
    tail/ok/bad exits, the fall-through runs `setup` then a bounded
    top-guarded loop whose exit jumps into the ok tail, and the pre tail
    falls through into ok.  All loop/setup/pre obligations are stated on
    raw instruction blocks; only the two ret-terminated tails are
    sub-derivations. -/
def dretSelCascadeLoop (lbl : String)
    (stages : List (List Instr × Cond × RetSel))
    (cinv : Nat → Reach) (A B C : Reach)
    (setup : List Instr) (guard : Cond) (fuel : Nat) (linv : Nat → Reach)
    (body : List Instr) (preT : List Instr)
    {P Q : Reach}
    (hchain0 : ∀ rf ws A', P rf ws A' → cinv 0 rf ws A')
    (hchain : SelCascadeChain reg rw stages cinv 0 A B C)
    (hsetupOk : blockOk setup = true)
    (hsetupMem : hasLoad setup = true → ∀ rf ws A', ws.length = rw.len →
      cinv stages.length rf ws A' → blockVCs reg rw.base rf ws setup)
    (hinit : ∀ rf ws A',
      cascadeStep reg rw setup (cinv stages.length) rf ws A' →
      linv 0 rf ws A')
    (hbodyOk : blockOk body = true)
    (hbodyMem : hasLoad body = true → ∀ rf ws A', ws.length = rw.len →
      (∃ i, i < fuel ∧ linv i rf ws A' ∧ guard.holds rf) →
      blockVCs reg rw.base rf ws body)
    (hstep : ∀ i, i < fuel → ∀ rf' ws' A',
      cascadeStep reg rw body
        (fun rf ws A' => linv i rf ws A' ∧ guard.holds rf) rf' ws' A' →
      linv (i + 1) rf' ws' A')
    (hexh : ∀ rf ws A', linv fuel rf ws A' → ¬ guard.holds rf)
    (hexit : ∀ rf ws A',
      ((∃ i, i ≤ fuel ∧ linv i rf ws A') ∧ ¬ guard.holds rf) → B rf ws A')
    (hpreOk : blockOk preT = true)
    (hpreMem : hasLoad preT = true → ∀ rf ws A', ws.length = rw.len →
      A rf ws A' → blockVCs reg rw.base rf ws preT)
    (hpre : ∀ rf ws A', cascadeStep reg rw preT A rf ws A' → B rf ws A')
    (okD : DCode reg rw B Q)
    (badD : DCode reg rw C Q) :
    DCode reg rw P Q :=
  ⟨.retSelCascadeLoop lbl stages setup guard fuel linv body preT okD.1
      badD.1,
   .dretSelCascadeLoop lbl stages cinv A B C setup guard fuel linv body preT
     hchain0 hchain hsetupOk hsetupMem hinit hbodyOk hbodyMem hstep hexh
     hexit hpreOk hpreMem hpre okD.2 badD.2⟩

/-- Ret-terminated capstone: a derivation whose code exits through `ra`
    (`retJalr`/`dretIf` tails; a single-exit prefix composed by `seq`)
    satisfies the `ra`-framed bounded CPS triple, at any base, ending at
    the aligned return address — the `FnHandle`-shaped contract.  This is
    the `Stmt.retSound` path; the legacy `offsetsOk` rejects ret nodes,
    so `retOffsetsOk` is the layout autoparam here. -/
theorem retSpec {P Q : Reach} (d : DCode reg rw P Q)
    (base ret : Word) {cr : CodeReq}
    (hreg : reg.wf) (hrw : rw.wf)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hcode : ∀ a i, CodeReq.ofProg base (d.1.flatten base) a = some i →
      cr a = some i)
    (hleaf : d.1.callFree = true := by rfl)
    (hofs : d.1.retOffsetsOk = true := by rfl)
    (hsz : decide (4 * d.1.size < 2 ^ 64) = true := by rfl) :
    cpsTripleWithin d.1.steps base ret cr
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM reg rw P)
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM reg rw Q) :=
  cpsTripleWithin_weaken (fun _ hp => hp)
    (sepConj_mono_right
      (asrtM_mono (fun rf ws A h => d.2.post_sound rf ws A h)))
    (Stmt.retSound reg rw d.1 base ret "ret." P hreg hrw hleaf hofs
      (of_decide_eq_true hsz) halign hcode (d.2.vcs_hold "ret."))

-- ============================================================================
-- Packaging: generated code + generated spec
-- ============================================================================

/-- Package a derivation as an SAsm `Fn` — the code is GENERATED from the
    proof. -/
def fn (name : String) {P Q : Reach} (d : DCode reg rw P Q) : Fn :=
  { name := name, pre := P, post := Q, body := d.1,
    region := reg, rw := rw }

/-- The generated function satisfies its spec: the ordinary bounded CPS
    triple, with all VCs discharged by the derivation.  The decidable
    layout checks are autoparams: the generated code never depends on the
    derivation's ghost arguments, so they close by `rfl` even under
    symbolic binders (where `decide` would refuse the free variables). -/
theorem fn_spec (name : String) {P Q : Reach} (d : DCode reg rw P Q)
    (base : Word) (hreg : reg.wf) (hrw : rw.wf)
    (hcf : d.1.callFree = true := by rfl)
    (hofs : d.1.offsetsOk = true := by rfl)
    (hsz : decide (4 * d.1.size < 2 ^ 64) = true := by rfl) :
    (d.fn name).Spec base :=
  Fn.sound _ base ⟨hreg, hrw⟩
    (VCs.Hold.cons_intro ⟨hcf, hofs, of_decide_eq_true hsz⟩
      (VCs.Hold.append_intro (d.2.vcs_hold (name ++ "."))
        (VCs.Hold.cons_intro (fun rf ws A h => d.2.post_sound rf ws A h)
          VCs.Hold.nil)))

/-- Caller-shaped variant for derivations containing `.call` steps:
    the generated function satisfies `Fn.SpecR` against an ambient code
    requirement containing the body and every callee. -/
theorem fn_specR (name : String) {P Q : Reach} (d : DCode reg rw P Q)
    (base : Word) (cr : CodeReq) (hreg : reg.wf) (hrw : rw.wf)
    (hcode : ∀ a i, CodeReq.ofProg base (d.1.flatten base) a = some i →
      cr a = some i)
    (hcallees : d.1.CalleesIn reg rw cr)
    (hcalls : d.1.callsOk base)
    (hofs : d.1.offsetsOk = true := by rfl)
    (hsz : decide (4 * d.1.size < 2 ^ 64) = true := by rfl) :
    (d.fn name).SpecR base cr :=
  Fn.soundR _ base cr ⟨hreg, hrw⟩ hcode hcallees hcalls
    (VCs.Hold.cons_intro ⟨hofs, of_decide_eq_true hsz⟩
      (VCs.Hold.append_intro (d.2.vcs_hold (name ++ "."))
        (VCs.Hold.cons_intro (fun rf ws A h => d.2.post_sound rf ws A h)
          VCs.Hold.nil)))

end DCode

/-- The calc relation: `P ~[reg, rw]~> Q` is a packaged derivation that
    some generated code carries `P` to `Q`. -/
scoped notation:36 P " ~[" reg ", " rw "]~> " Q => DCode reg rw P Q

end SAsm
end EvmAsm.Rv64
