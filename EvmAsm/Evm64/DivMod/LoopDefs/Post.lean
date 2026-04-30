/-
  EvmAsm.Evm64.DivMod.LoopDefs.Post

  Assertion-valued postcondition defs for the Knuth Algorithm D loop body:
    * loopExitPost (+ abbrevs loopExitPostN1..N4)
    * loopBody{Skip,Addback,AddbackBeq}Post (+ per-n abbrevs)
    * Per-n call-path postconditions (loopBodyN{1,2,3}Call*PostJ)
    * loopBodyN3Call*PostJ and eq_J bridge
    * loopN3MaxSkipSkipPost (legacy max+skip × max+skip path)
    * loopIterPostN{1,2,3}{Max,Call} + producer equations + Bool dispatch
    * Two, three, and four iteration unified postconditions (loopN{1,2,3}UnifiedPost)

  Imports `LoopDefs.Iter` for the underlying pure computations.
-/

import EvmAsm.Evm64.DivMod.LoopDefs.Iter

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Loop exit postcondition for n
-- Common assertion shape for both cpsBranchWithin exits (taken/ntaken).
-- Parameterized by the final output values (un0F..un3F, u4F, q_f, c3).
-- ============================================================================

/-- Loop exit postcondition for n. Both taken (loop-back) and ntaken (exit)
    paths produce this same assertion shape, differing only in the output values.
    Encapsulates uBase/j'/qAddr address computation + 21-atom assertion chain. -/
@[irreducible]
def loopExitPost (n : Word) (sp j q_f c3 un0F un1F un2F un3F u4F
    v0 v1 v2 v3 : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let j' := j + signExtend12 4095
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
  (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ uBase) **
  (.x7 ↦ᵣ qAddr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
  (.x2 ↦ᵣ un3F) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0F) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1F) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2F) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3F) **
  ((uBase + signExtend12 4064) ↦ₘ u4F) **
  (qAddr ↦ₘ q_f)

theorem loopExitPost_unfold {n: Word} {sp j q_f c3 un0F un1F un2F un3F u4F
    v0 v1 v2 v3 : Word} :
    loopExitPost n sp j q_f c3 un0F un1F un2F un3F u4F v0 v1 v2 v3 =
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let j' := j + signExtend12 4095
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
    (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ uBase) **
    (.x7 ↦ᵣ qAddr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
    (.x2 ↦ᵣ un3F) ** (.x0 ↦ᵣ (0 : Word)) **
    (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
    ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0F) **
    ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1F) **
    ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2F) **
    ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3F) **
    ((uBase + signExtend12 4064) ↦ₘ u4F) **
    (qAddr ↦ₘ q_f) := by
  delta loopExitPost; rfl

/-- Loop exit postcondition abbreviations for n -/
abbrev loopExitPostN1 := loopExitPost (1 : Word)
abbrev loopExitPostN2 := loopExitPost (2 : Word)
abbrev loopExitPostN3 := loopExitPost (3 : Word)
abbrev loopExitPostN4 := loopExitPost (4 : Word)

-- ============================================================================
-- Composed postcondition: mulsub skip/addback/addbackBeq (N4 base + n-abbrevs)
-- ============================================================================
/-- Full mulsub-skip postcondition for n loop body. -/
@[irreducible]
def loopBodySkipPost (n : Word) (sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  loopExitPost n sp j qHat ms.2.2.2.2 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3

/-- Full mulsub-addback postcondition for n loop body. -/
@[irreducible]
def loopBodyAddbackPost (n : Word) (sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let un0 := ms.1; let un1 := ms.2.1; let un2 := ms.2.2.1
  let un3 := ms.2.2.2.1; let c3 := ms.2.2.2.2
  let u4_new := uTop - c3
  let ab := addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3
  loopExitPost n sp j (qHat + signExtend12 4095) c3 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3

/-- Backward-compatible abbreviations for loopBodySkipPost and loopBodyAddbackPost. -/
abbrev loopBodyN1SkipPost := loopBodySkipPost (1 : Word)
abbrev loopBodyN1AddbackPost := loopBodyAddbackPost (1 : Word)
abbrev loopBodyN2SkipPost := loopBodySkipPost (2 : Word)
abbrev loopBodyN2AddbackPost := loopBodyAddbackPost (2 : Word)
abbrev loopBodyN3SkipPost := loopBodySkipPost (3 : Word)
abbrev loopBodyN3AddbackPost := loopBodyAddbackPost (3 : Word)
abbrev loopBodyN4SkipPost := loopBodySkipPost (4 : Word)
abbrev loopBodyN4AddbackPost := loopBodyAddbackPost (4 : Word)

/-- Full mulsub-addback postcondition with BEQ double-addback handling.
    Handles both carry=0 (double addback) and carry≠0 (single addback) cases. -/
@[irreducible]
def loopBodyAddbackBeqPost (n : Word) (sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
               else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  loopExitPost n sp j q_out c3 un0Out un1Out un2Out un3Out u4_out v0 v1 v2 v3

abbrev loopBodyN1AddbackBeqPost := loopBodyAddbackBeqPost (1 : Word)
abbrev loopBodyN2AddbackBeqPost := loopBodyAddbackBeqPost (2 : Word)
abbrev loopBodyN3AddbackBeqPost := loopBodyAddbackBeqPost (3 : Word)
abbrev loopBodyN4AddbackBeqPost := loopBodyAddbackBeqPost (4 : Word)

-- ============================================================================
-- Unified (Bool-parameterized) loop body postcondition: skip/addback+BEQ
-- Issue #283: Unify skip/addback via `(borrow_zero : Bool)`.
-- `borrow_zero = true`  → skip path (borrow = 0, mulsub didn't underflow)
-- `borrow_zero = false` → addback+BEQ path (borrow ≠ 0, mulsub underflowed)
-- ============================================================================

/-- Unified loop body postcondition parameterized on borrow condition.
    `borrow_zero = true` selects the skip path;
    `borrow_zero = false` selects the addback+BEQ (double-addback) path. -/
@[irreducible]
def loopBodyUnifiedPost (borrow_zero : Bool) (n : Word)
    (sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  if borrow_zero then loopBodySkipPost n sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else loopBodyAddbackBeqPost n sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[simp]
theorem loopBodyUnifiedPost_true {n : Word}
    {sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    loopBodyUnifiedPost true n sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopBodySkipPost n sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [loopBodyUnifiedPost]

@[simp]
theorem loopBodyUnifiedPost_false {n : Word}
    {sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    loopBodyUnifiedPost false n sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopBodyAddbackBeqPost n sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [loopBodyUnifiedPost]

/-- Per-n abbreviations for the unified postcondition. -/
abbrev loopBodyUnifiedPostN1 (borrow_zero : Bool) := loopBodyUnifiedPost borrow_zero (1 : Word)
abbrev loopBodyUnifiedPostN2 (borrow_zero : Bool) := loopBodyUnifiedPost borrow_zero (2 : Word)
abbrev loopBodyUnifiedPostN3 (borrow_zero : Bool) := loopBodyUnifiedPost borrow_zero (3 : Word)
abbrev loopBodyUnifiedPostN4 (borrow_zero : Bool) := loopBodyUnifiedPost borrow_zero (4 : Word)

-- ============================================================================
-- Call path postconditions for n=3 (includes div128 scratch cells)
-- ============================================================================

/-- Call+skip postcondition for n=3 loop body at j=0.
    Bundles div128Quot computation + loopBodyN3SkipPost + scratch cells. -/
@[irreducible]
def loopBodyN3CallSkipPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let qHat := div128Quot u3 u2 v2
  loopBodyN3SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Call+addback postcondition for n=3 loop body at j=0.
    Bundles div128Quot computation + loopBodyN3AddbackPost + scratch cells. -/
@[irreducible]
def loopBodyN3CallAddbackPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let qHat := div128Quot u3 u2 v2
  loopBodyN3AddbackPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Borrow condition for n=3 call+skip: mulsub doesn't overflow. -/
def isSkipBorrowN3Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := div128Quot u3 u2 v2
  (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)

/-- Borrow condition for n=3 call+addback: mulsub overflows. -/
def isAddbackBorrowN3Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := div128Quot u3 u2 v2
  (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word)

-- ============================================================================
-- Generic j versions of call path postconditions (for multi-iteration loops)
-- ============================================================================

/-- Call+skip postcondition for n=3 loop body, generic j.
    Bundles div128Quot computation + loopBodyN3SkipPost + scratch cells. -/
@[irreducible]
def loopBodyN3CallSkipPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let qHat := div128Quot u3 u2 v2
  loopBodyN3SkipPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Call+addback postcondition for n=3 loop body, generic j.
    Bundles div128Quot computation + loopBodyN3AddbackPost + scratch cells. -/
@[irreducible]
def loopBodyN3CallAddbackPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let qHat := div128Quot u3 u2 v2
  loopBodyN3AddbackPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Call+addback BEQ postcondition for n=3 at j=0, with double-addback handling. -/
@[irreducible]
def loopBodyN3CallAddbackBeqPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let qHat := div128Quot u3 u2 v2
  loopBodyN3AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Call+addback BEQ postcondition for n=3, generic j, with double-addback handling. -/
@[irreducible]
def loopBodyN3CallAddbackBeqPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let qHat := div128Quot u3 u2 v2
  loopBodyN3AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Bridge: j=0 specific call addback beq = generic-j at j=0. -/
theorem loopBodyN3CallAddbackBeqPost_eq_J {sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    loopBodyN3CallAddbackBeqPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopBodyN3CallAddbackBeqPostJ sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN3CallAddbackBeqPost loopBodyN3CallAddbackBeqPostJ; rfl


-- ============================================================================
-- Generic j versions of n=1 call path postconditions
-- ============================================================================

/-- Call+skip postcondition for n=1 loop body, generic j.
    Bundles div128Quot computation + loopBodyN1SkipPost + scratch cells.
    For n=1: div128 uses uHi=u1, uLo=u0, vTop=v0. -/
@[irreducible]
def loopBodyN1CallSkipPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let qHat := div128Quot u1 u0 v0
  loopBodyN1SkipPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u0)

/-- Call+addback postcondition for n=1 loop body, generic j.
    Bundles div128Quot computation + loopBodyN1AddbackPost + scratch cells. -/
@[irreducible]
def loopBodyN1CallAddbackPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let qHat := div128Quot u1 u0 v0
  loopBodyN1AddbackPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u0)

/-- Call+addback BEQ postcondition for n=1, generic j, with double-addback handling. -/
@[irreducible]
def loopBodyN1CallAddbackBeqPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let qHat := div128Quot u1 u0 v0
  loopBodyN1AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u0)

-- ============================================================================
-- Generic j versions of n=2 call path postconditions
-- ============================================================================

/-- Call+skip postcondition for n=2 loop body, generic j.
    Bundles div128Quot computation + loopBodyN2SkipPost + scratch cells.
    For n=2: div128 uses uHi=u2, uLo=u1, vTop=v1. -/
@[irreducible]
def loopBodyN2CallSkipPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let qHat := div128Quot u2 u1 v1
  loopBodyN2SkipPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u1)

/-- Call+addback postcondition for n=2 loop body, generic j.
    Bundles div128Quot computation + loopBodyN2AddbackPost + scratch cells. -/
@[irreducible]
def loopBodyN2CallAddbackPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let qHat := div128Quot u2 u1 v1
  loopBodyN2AddbackPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u1)

/-- Call+addback BEQ postcondition for n=2, generic j, with double-addback handling. -/
@[irreducible]
def loopBodyN2CallAddbackBeqPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let qHat := div128Quot u2 u1 v1
  loopBodyN2AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u1)

-- ============================================================================
-- Legacy two-iteration postcondition (n=3 max+skip × max+skip)
-- ============================================================================

/-- Postcondition for the full n=3 two-iteration loop (max+skip at both j=1 and j=0).
    Includes the j=0 exit postcondition plus j=1's carried frame atoms (u4_new, q[1]). -/
@[irreducible]
def loopN3MaxSkipSkipPost (sp v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word) : Assertion :=
  let qHat : Word := signExtend12 4095
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopBodyN3SkipPost sp (0 : Word) qHat v0 v1 v2 v3
    u0Orig ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ (uTop - ms.2.2.2.2)) **
  (q_addr_1 ↦ₘ qHat)

-- ============================================================================
-- Double-addback iteration postconditions
-- ============================================================================

@[irreducible] def loopIterPostN1Max (sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let r := iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let c3 := (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN1 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3

theorem loopIterPostN1Max_addback {sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN1AddbackBeqPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopIterPostN1Max iterN1Max iterWithDoubleAddback
        loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN1 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_pos hb]; split <;> rfl

theorem loopIterPostN1Max_skip {sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : ¬BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN1SkipPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopIterPostN1Max iterN1Max iterWithDoubleAddback
        loopBodyN1SkipPost loopBodySkipPost loopExitPostN1 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_neg hb]

@[irreducible] def loopIterPostN1Call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let r := iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let qHat := div128Quot u1 u0 v0
  let c3 := (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN1 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u0)

theorem loopIterPostN1Call_addback {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN1CallAddbackBeqPostJ sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopIterPostN1Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopIterPostN1Call iterN1Call iterWithDoubleAddback
        loopBodyN1CallAddbackBeqPostJ loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN1 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_pos hb]; split <;> rfl

theorem loopIterPostN1Call_skip {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : ¬BitVec.ult uTop (mulsubN4_c3 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN1CallSkipPostJ sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopIterPostN1Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopIterPostN1Call iterN1Call iterWithDoubleAddback
        loopBodyN1CallSkipPostJ loopBodyN1SkipPost loopBodySkipPost loopExitPostN1 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_neg hb]

def loopIterPostN1 (bltu : Bool) (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  match bltu with
  | true => loopIterPostN1Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop
  | false => loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop ** empAssertion

@[irreducible] def loopIterPostN2Max (sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let r := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let c3 := (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN2 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3

theorem loopIterPostN2Max_addback {sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN2AddbackBeqPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopIterPostN2Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopIterPostN2Max iterN2Max iterWithDoubleAddback
        loopBodyN2AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN2 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_pos hb]; split <;> rfl

theorem loopIterPostN2Max_skip {sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : ¬BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN2SkipPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopIterPostN2Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopIterPostN2Max iterN2Max iterWithDoubleAddback
        loopBodyN2SkipPost loopBodySkipPost loopExitPostN2 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_neg hb]

@[irreducible] def loopIterPostN2Call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let r := iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let qHat := div128Quot u2 u1 v1
  let c3 := (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN2 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u1)

theorem loopIterPostN2Call_addback {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN2CallAddbackBeqPostJ sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopIterPostN2Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopIterPostN2Call iterN2Call iterWithDoubleAddback
        loopBodyN2CallAddbackBeqPostJ loopBodyN2AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN2 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_pos hb]; split <;> rfl

theorem loopIterPostN2Call_skip {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : ¬BitVec.ult uTop (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN2CallSkipPostJ sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopIterPostN2Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopIterPostN2Call iterN2Call iterWithDoubleAddback
        loopBodyN2CallSkipPostJ loopBodyN2SkipPost loopBodySkipPost loopExitPostN2 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_neg hb]

def loopIterPostN2 (bltu : Bool) (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  match bltu with
  | true => loopIterPostN2Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop
  | false => loopIterPostN2Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop ** empAssertion

@[irreducible] def loopIterPostN3Max (sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let r := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let c3 := (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN3 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3

/-- Producer equation: addback beq postcondition equals loopIterPostN3Max when borrow holds. -/
theorem loopIterPostN3Max_addback {sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN3AddbackBeqPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopIterPostN3Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopIterPostN3Max iterN3Max iterWithDoubleAddback
        loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN3 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_pos hb]; split <;> rfl

/-- Producer equation: skip postcondition equals loopIterPostN3Max when ¬borrow. -/
theorem loopIterPostN3Max_skip {sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : ¬BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN3SkipPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopIterPostN3Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopIterPostN3Max iterN3Max iterWithDoubleAddback
        loopBodyN3SkipPost loopBodySkipPost loopExitPostN3 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_neg hb]

@[irreducible] def loopIterPostN3Call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let r := iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let qHat := div128Quot u3 u2 v2
  let c3 := (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN3 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Producer equation: call addback beq postcondition equals loopIterPostN3Call when borrow holds. -/
theorem loopIterPostN3Call_addback {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN3CallAddbackBeqPostJ sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopIterPostN3Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopIterPostN3Call iterN3Call iterWithDoubleAddback
        loopBodyN3CallAddbackBeqPostJ loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN3 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_pos hb]; split <;> rfl

/-- Producer equation: call skip postcondition equals loopIterPostN3Call when ¬borrow. -/
theorem loopIterPostN3Call_skip {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : ¬BitVec.ult uTop (mulsubN4_c3 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN3CallSkipPostJ sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    loopIterPostN3Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopIterPostN3Call iterN3Call iterWithDoubleAddback
        loopBodyN3CallSkipPostJ loopBodyN3SkipPost loopBodySkipPost loopExitPostN3 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_neg hb]

def loopIterPostN3 (bltu : Bool) (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  match bltu with
  | true => loopIterPostN3Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop
  | false => loopIterPostN3Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop ** empAssertion

-- ============================================================================
-- Two-iteration path postconditions with double addback for n=3
-- ============================================================================

/-- Postcondition for n=3 two-iteration loop (both max path) with double addback. -/
@[irreducible]
def loopN3MaxPost (sp v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word) : Assertion :=
  let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
    u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1)

/-- Postcondition for n=3 two-iteration loop (both call path) with double addback. -/
@[irreducible]
def loopN3CallCallPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word) : Assertion :=
  let r1 := iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN3Call sp base (0 : Word) v0 v1 v2 v3
    u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1)

/-- Postcondition for n=3 two-iteration loop (j=1 max, j=0 call) with double addback. -/
@[irreducible]
def loopN3MaxCallPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word) : Assertion :=
  let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN3Call sp base (0 : Word) v0 v1 v2 v3
    u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1)

/-- Postcondition for n=3 two-iteration loop (j=1 call, j=0 max) with double addback. -/
@[irreducible]
def loopN3CallMaxPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word) : Assertion :=
  let r1 := iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
    u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Unified n=3 two-iteration postcondition with double addback. -/
def loopN3UnifiedPost (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  match bltu_1, bltu_0 with
  | false, false =>
    loopN3MaxPost sp v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig **
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | true,  true  => loopN3CallCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
  | false, true  => loopN3MaxCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
  | true,  false => loopN3CallMaxPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig

-- ============================================================================
-- Two-/three-iteration path postconditions with double addback for n=2
-- ============================================================================

/-- Postcondition for n=2 two-iteration loop (both max path) with double addback. -/
@[irreducible]
def loopN2MaxPost (sp v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word) : Assertion :=
  let r1 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
    u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1)

/-- Postcondition for n=2 two-iteration loop (both call path) with double addback. -/
@[irreducible]
def loopN2CallCallPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word) : Assertion :=
  let r1 := iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN2Call sp base (0 : Word) v0 v1 v2 v3
    u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1)

/-- Postcondition for n=2 two-iteration loop (j=1 max, j=0 call) with double addback. -/
@[irreducible]
def loopN2MaxCallPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word) : Assertion :=
  let r1 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN2Call sp base (0 : Word) v0 v1 v2 v3
    u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1)

/-- Postcondition for n=2 two-iteration loop (j=1 call, j=0 max) with double addback. -/
@[irreducible]
def loopN2CallMaxPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word) : Assertion :=
  let r1 := iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
    u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u1)

/-- Unified n=2 two-iteration postcondition with double addback. -/
def loopN2Iter10Post (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  match bltu_1, bltu_0 with
  | false, false =>
    loopN2MaxPost sp v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig **
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | true,  true  => loopN2CallCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
  | false, true  => loopN2MaxCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
  | true,  false => loopN2CallMaxPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig

/-- Unified n=2 three-iteration postcondition with double addback.
    Parameterized by `(bltu_2 bltu_1 bltu_0 : Bool)` covering all 8 path combinations. -/
@[irreducible]
def loopN2UnifiedPost (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  -- Compute j=2 result
  let r2 := iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  -- Address bases for j=2 carried atoms
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  -- Scratch values: call path overwrites them, max path passes through
  let scratch_ret := if bltu_2 then (base + div128CallRetOff) else retMem
  let scratch_d := if bltu_2 then v1 else dMem
  let scratch_dlo := if bltu_2 then div128DLo v1 else dloMem
  let scratch_un0 := if bltu_2 then div128Un0 u1 else scratch_un0
  -- Two-iteration (j=1,j=0)  postcondition with j=2's outputs as inputs
  loopN2Iter10Post bltu_1 bltu_0 sp base v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 u0_orig_0
    scratch_ret scratch_d scratch_dlo scratch_un0 **
  -- Carried atoms from j=2
  ((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1)

-- ============================================================================
-- Two-/three-/four-iteration path postconditions with double addback for n=1
-- ============================================================================

/-- Postcondition for n=1 two-iteration loop (j=1, j=0) with double addback.
    Same structure as loopN1Iter10Post but uses iterN1 and loopIterPostN1. -/
def loopN1Iter10Post (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
     retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  let r1 := iterN1 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN1 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  match bltu_1, bltu_0 with
  | false, false =>
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, true  => empAssertion
  | true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0)
  | true,  true  => empAssertion

/-- Postcondition for n=1 three-iteration loop (j=2, j=1, j=0) with double addback.
    Parameterized by `(bltu_2 bltu_1 bltu_0 : Bool)` covering all 8 path combinations. -/
@[irreducible]
def loopN1Iter210Post (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  let r2 := iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  -- Scratch values: call path overwrites them, max path passes through
  let scratch_ret := if bltu_2 then (base + div128CallRetOff) else retMem
  let scratch_d := if bltu_2 then v0 else dMem
  let scratch_dlo := if bltu_2 then div128DLo v0 else dloMem
  let scratch_un0 := if bltu_2 then div128Un0 u0 else scratch_un0
  -- Two-iteration (j=1,j=0)  postcondition with j=2's outputs as inputs
  loopN1Iter10Post bltu_1 bltu_0 sp base v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 u0_orig_0
    scratch_ret scratch_d scratch_dlo scratch_un0 **
  -- Carried atoms from j=2
  ((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1)

/-- Unified n=1 four-iteration postcondition with double addback.
    Parameterized by `(bltu_3 bltu_2 bltu_1 bltu_0 : Bool)` covering all 16 path combinations. -/
@[irreducible]
def loopN1UnifiedPost (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_2 u0_orig_1 u0_orig_0
     retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  -- Compute j=3 result
  let r3 := iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  -- Address bases for j=3 carried atoms
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  -- Scratch values: call path overwrites them, max path passes through
  let scratch_ret := if bltu_3 then (base + div128CallRetOff) else retMem
  let scratch_d := if bltu_3 then v0 else dMem
  let scratch_dlo := if bltu_3 then div128DLo v0 else dloMem
  let scratch_un0 := if bltu_3 then div128Un0 u0 else scratch_un0
  -- Three-iteration (j=2,j=1,j=0)  postcondition with j=3's outputs as inputs
  loopN1Iter210Post bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3
    u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    u0_orig_1 u0_orig_0
    scratch_ret scratch_d scratch_dlo scratch_un0 **
  -- Carried atoms from j=3
  ((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1)

end EvmAsm.Evm64
