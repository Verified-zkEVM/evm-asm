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

/-- A constructive derivation that statement `S` carries entry reach `P` to
    exit reach `Q`, with all of `S`'s proof obligations internalized.  The
    erased statement is a type INDEX: derivations that must share code
    (loop-body families, if/fi arms of a shared skeleton) are forced to by
    unification, so register clobbering or endian mistakes surface at the
    step that makes them, not after the code exists. -/
inductive DStmt (reg : Region) (rw : RwRegion) : Stmt → Reach → Reach → Type where
  /-- Pure step: re-describe the reachable states (an entailment — in
      particular an iff — of assertions).  Emits NO instructions; erases
      to `.assert`, whose single VC is exactly `h`. -/
  | pure (lbl : String) {P Q : Reach}
      (h : ∀ rf ws A, P rf ws A → Q rf ws A) :
      DStmt reg rw (.assert lbl Q) P Q
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

namespace DStmt

variable {reg : Region} {rw : RwRegion}

/-- The strongest postcondition of the erased statement (from the
    derivation's entry reach) entails the derivation's exit reach. -/
theorem post_sound : ∀ {S : Stmt} {P Q : Reach}, DStmt reg rw S P Q →
    ∀ rf ws A, Stmt.sp reg rw S P rf ws A → Q rf ws A
  | _, _, _, .pure _ _ => fun _ _ _ hsp => hsp.2
  | _, _, _, .block _ _ _ _ hpost => by
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

/-- Every VC the generator emits for the erased statement (at the
    derivation's entry reach) holds — the obligations were carried by the
    derivation's constructors. -/
theorem vcs_hold : ∀ {S : Stmt} {P Q : Reach}, DStmt reg rw S P Q →
    ∀ pfx : String, VCs.Hold (Stmt.vcs reg rw S pfx P)
  | _, _, _, .pure _ h, _ =>
      VCs.Hold.cons_intro (fun rf ws A hr => h rf ws A hr) VCs.Hold.nil
  | _, _, _, .block lbl is hok hmem _, pfx => by
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
