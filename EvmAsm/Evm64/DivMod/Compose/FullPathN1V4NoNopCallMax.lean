/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopCallMax

  Call/max/max/max setup wrappers for the n=1 v4/no-NOP full DIV path.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopLoopBody

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_1 jpred_2 jpred_3 slt_jpos_1 slt_jpos_2 slt_jpos_3)

/-- Explicit no-`x1` precondition for the N1 path where j=3 uses the v4
    call path and j=2/j=1/j=0 all use max. It extends the ordinary no-X1
    loop precondition with the extra v4 div128 scratch cell. -/
@[irreducible]
def loopN1CallMaxmaxmaxScratchPreNoX1 (sp : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopN1PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
    retMem dMem dloMem scratchUn0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- First j=3 call-body step for the N1 call/max/max/max path. This
    exposes the v4-call scratch post while framing the j=2/j=1/j=0 cells
    needed by the following all-max iter210 wrapper. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopN1CallMaxmaxmaxScratchPreNoX1 sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (3 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal) **
        ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat +
          signExtend12 0) ↦ₘ u0Orig2) **
        ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q2Old) **
        ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat +
          signExtend12 0) ↦ₘ u0Orig1) **
        ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old) **
        ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat +
          signExtend12 0) ↦ₘ u0Orig0) **
        ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)) := by
  let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J3 := divK_loop_body_n1_call_j3_exact_loopIterScratch_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q3Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu hcarry2_nz
  have J3f := cpsTripleWithin_frameR
    (((uBase2 + signExtend12 0) ↦ₘ u0Orig2) ** (qAddr2 ↦ₘ q2Old) **
     ((uBase1 + signExtend12 0) ↦ₘ u0Orig1) ** (qAddr1 ↦ₘ q1Old) **
     ((uBase0 + signExtend12 0) ↦ₘ u0Orig0) ** (qAddr0 ↦ₘ q0Old))
    (by pcFree) J3
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN1CallMaxmaxmaxScratchPreNoX1 loopN1PreWithScratchNoX1 loopN1Pre at hp
      delta loopBodyN1CallSkipJgt0PreV4NoX1 at ⊢
      dsimp only [uBase2, qAddr2, uBase1, qAddr1, uBase0, qAddr0] at hp ⊢
      simp only [se12_32, se12_40, se12_48, se12_56] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      dsimp only [uBase2, qAddr2, uBase1, qAddr1, uBase0, qAddr0] at hp
      rw [sepConj_assoc'] at hp
      exact hp)
    J3f

/-- Explicit no-`x1` post for the N1 path where j=3 uses the v4 call path
    and j=2/j=1/j=0 all use max. The extra v4 div128 scratch cell is
    retained as caller frame state. -/
@[irreducible]
def loopN1CallMaxmaxmaxScratchPostNoX1 (sp base : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 scratchMem : Word) : Assertion :=
  let r3 := iterWithDoubleAddback (divKTrialCallV4QHat u1 u0 v0)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  loopN1Iter210PostNoX1 false false false sp base v0 v1 v2 v3
    u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    u0Orig1 u0Orig0
    (base + div128CallRetOff) v0 (divKTrialCallV4DLo v0) (divKTrialCallV4Un0 u0) **
  ((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)

/-- Double-addback progress for the v4 n=1 call path, using the quotient
    selected by `divKTrialCallV4QHat`. -/
@[irreducible]
def isAddbackCarry2NzN1CallV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  isAddbackCarry2Nz (divKTrialCallV4QHat u1 u0 v0)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Specialize the universal double-addback carry hypothesis to the quotient
    selected by the v4 n=1 call path. -/
theorem isAddbackCarry2NzN1CallV4_of_carry2All
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    isAddbackCarry2NzN1CallV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold isAddbackCarry2NzN1CallV4
  exact hcarry2 (divKTrialCallV4QHat u1 u0 v0) u0 u1 u2 u3 uTop

/-- Expand the compact v4 n=1 call carry predicate into the raw
    double-addback progress hypothesis expected by the j=3 call-body spec. -/
theorem isAddbackCarry2NzN1CallV4_raw
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hcarry2 : isAddbackCarry2NzN1CallV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let qHat := divKTrialCallV4QHat u1 u0 v0
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
    carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 := by
  simpa [isAddbackCarry2NzN1CallV4, isAddbackCarry2Nz] using hcarry2

/-- Result of the j=3 v4 call iteration in the N1 call/max/max/max path. -/
@[irreducible]
def loopN1CallMaxmaxmaxR3
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (divKTrialCallV4QHat u1 u0 v0)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Result of the following j=2 all-max iteration in the N1 call/max/max/max path. -/
@[irreducible]
def loopN1CallMaxmaxmaxR2
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  iterN1Max v0 v1 v2 v3 u0Orig2
    r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1

/-- Result of the following j=1 all-max iteration in the N1 call/max/max/max path. -/
@[irreducible]
def loopN1CallMaxmaxmaxR1
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  iterN1Max v0 v1 v2 v3 u0Orig1
    r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

/-- Selected carry facts for the N1 call/max/max/max path. -/
@[irreducible]
def loopN1CallMaxmaxmaxSelectedCarryFacts
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word) : Prop :=
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  isAddbackCarry2NzN1CallV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop ∧
  isAddbackCarry2NzN1Max v0 v1 v2 v3 u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1
    r3.2.2.2.2.1 ∧
  isAddbackCarry2NzN1Max v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1
    r2.2.2.2.2.1 ∧
  isAddbackCarry2NzN1Max v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1
    r1.2.2.2.2.1

/-- Conditional carry evidence for one selected N1 max iteration. The
    double-addback progress proof is only needed on the addback branch, i.e.
    when the computed mulsub borrow bit is nonzero. -/
@[irreducible]
def selectedN1MaxCarryIfBorrow
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  isAddbackCarry2NzN1MaxIfBorrow v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Control-flow-shaped selected carry facts for the N1 call/max/max/max path.
    Unlike `loopN1CallMaxmaxmaxSelectedCarryFacts`, the max-step carry facts
    are conditional on the corresponding addback branch being selected. This
    matches the loop-body specs that consume the carry proof only after the
    borrow branch split. -/
@[irreducible]
def loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word) : Prop :=
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  isAddbackCarry2NzN1CallV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop ∧
  selectedN1MaxCarryIfBorrow v0 v1 v2 v3 u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1
    r3.2.2.2.2.1 ∧
  selectedN1MaxCarryIfBorrow v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1
    r2.2.2.2.2.1 ∧
  selectedN1MaxCarryIfBorrow v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1
    r1.2.2.2.2.1

theorem selectedN1MaxCarryIfBorrow_of_carry
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hcarry : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    selectedN1MaxCarryIfBorrow v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold selectedN1MaxCarryIfBorrow
  exact isAddbackCarry2NzN1MaxIfBorrow_of_carry v0 v1 v2 v3 u0 u1 u2 u3 uTop hcarry

theorem loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_of_selected
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word)
    (hselected : loopN1CallMaxmaxmaxSelectedCarryFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0) :
    loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 := by
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  unfold loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
  exact ⟨hselected.1,
    selectedN1MaxCarryIfBorrow_of_carry _ _ _ _ _ _ _ _ _ hselected.2.1,
    selectedN1MaxCarryIfBorrow_of_carry _ _ _ _ _ _ _ _ _ hselected.2.2.1,
    selectedN1MaxCarryIfBorrow_of_carry _ _ _ _ _ _ _ _ _ hselected.2.2.2⟩

theorem loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_call
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word)
    (hselected : loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0) :
    isAddbackCarry2NzN1CallV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts at hselected
  exact hselected.1

theorem loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_max2
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word)
    (hselected : loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0) :
    selectedN1MaxCarryIfBorrow v0 v1 v2 v3 u0Orig2
      (loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1 := by
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  unfold loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts at hselected
  change (_ ∧ selectedN1MaxCarryIfBorrow v0 v1 v2 v3 u0Orig2
      r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 ∧ _ ∧ _) at hselected
  simpa [r3] using hselected.2.1

theorem loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_max1
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word)
    (hselected : loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0) :
    selectedN1MaxCarryIfBorrow v0 v1 v2 v3 u0Orig1
      (loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2).2.1
      (loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2).2.2.1
      (loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2).2.2.2.1
      (loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2).2.2.2.2.1 := by
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  unfold loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts at hselected
  change (_ ∧ _ ∧ selectedN1MaxCarryIfBorrow v0 v1 v2 v3 u0Orig1
      r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 ∧ _) at hselected
  simpa [r2] using hselected.2.2.1

theorem loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_max0
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word)
    (hselected : loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0) :
    selectedN1MaxCarryIfBorrow v0 v1 v2 v3 u0Orig0
      (loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1).2.1
      (loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1).2.2.1
      (loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1).2.2.2.1
      (loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1).2.2.2.2.1 := by
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  unfold loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts at hselected
  change (_ ∧ _ ∧ _ ∧ selectedN1MaxCarryIfBorrow v0 v1 v2 v3 u0Orig0
      r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) at hselected
  simpa [r1] using hselected.2.2.2

theorem loopN1CallMaxmaxmaxSelectedCarryFacts_of_carry2All
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    loopN1CallMaxmaxmaxSelectedCarryFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 := by
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts
  exact ⟨isAddbackCarry2NzN1CallV4_of_carry2All
      v0 v1 v2 v3 u0 u1 u2 u3 uTop hcarry2,
    hcarry2 (signExtend12 4095) u0Orig2
      (loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1,
    hcarry2 (signExtend12 4095) u0Orig1
      (loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2).2.1
      (loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2).2.2.1
      (loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2).2.2.2.1
      (loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2).2.2.2.2.1,
    hcarry2 (signExtend12 4095) u0Orig0
      (loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1).2.1
      (loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1).2.2.1
      (loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1).2.2.2.1
      (loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1).2.2.2.2.1⟩

/-- Compact all-max branch facts after the j=3 v4 call iteration in the
    N1 call/max/max/max path. -/
@[irreducible]
def loopN1CallMaxmaxmaxBranchFacts
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 : Word) : Prop :=
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  ¬BitVec.ult r3.2.1 v0 ∧
  ¬BitVec.ult r2.2.1 v0 ∧
  ¬BitVec.ult r1.2.1 v0

/-- Build the compact all-max branch-fact bundle from the three branch
    conditions that follow the j=3 v4 call iteration. -/
theorem loopN1CallMaxmaxmaxBranchFacts_of_bltu
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2).2.1 v0)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1).2.1 v0) :
    loopN1CallMaxmaxmaxBranchFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 := by
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  unfold loopN1CallMaxmaxmaxBranchFacts
  change (¬BitVec.ult r3.2.1 v0 ∧ ¬BitVec.ult r2.2.1 v0 ∧
      ¬BitVec.ult r1.2.1 v0)
  exact ⟨by simpa [r3] using hbltu2, by
    exact ⟨by simpa [r2] using hbltu1, by simpa [r1] using hbltu0⟩⟩

/-- The j=2 all-max branch fact packaged in
    `loopN1CallMaxmaxmaxBranchFacts`. -/
theorem loopN1CallMaxmaxmaxBranchFacts_hbltu2
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0 := by
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  have hbranches' := hbranches
  unfold loopN1CallMaxmaxmaxBranchFacts at hbranches'
  change (¬BitVec.ult r3.2.1 v0 ∧ ¬BitVec.ult r2.2.1 v0 ∧
      ¬BitVec.ult r1.2.1 v0) at hbranches'
  simpa [r3] using hbranches'.1

/-- The j=1 all-max branch fact packaged in
    `loopN1CallMaxmaxmaxBranchFacts`. -/
theorem loopN1CallMaxmaxmaxBranchFacts_hbltu1
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2).2.1 v0 := by
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  have hbranches' := hbranches
  unfold loopN1CallMaxmaxmaxBranchFacts at hbranches'
  change (¬BitVec.ult r3.2.1 v0 ∧ ¬BitVec.ult r2.2.1 v0 ∧
      ¬BitVec.ult r1.2.1 v0) at hbranches'
  simpa [r2] using hbranches'.2.1

/-- The j=0 all-max branch fact packaged in
    `loopN1CallMaxmaxmaxBranchFacts`. -/
theorem loopN1CallMaxmaxmaxBranchFacts_hbltu0
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1).2.1 v0 := by
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  have hbranches' := hbranches
  unfold loopN1CallMaxmaxmaxBranchFacts at hbranches'
  change (¬BitVec.ult r3.2.1 v0 ∧ ¬BitVec.ult r2.2.1 v0 ∧
      ¬BitVec.ult r1.2.1 v0) at hbranches'
  simpa [r1] using hbranches'.2.2

/-- Denormalization entry state for the N1 path where j=3 uses the v4
    call path and j=2/j=1/j=0 all use max. This mirrors
    `fullDivN1DenormPre`, but uses the v4 call/max/max/max quotient and
    remainder chain instead of the generic `div128Quot` chain. The shift is
    threaded from the original divisor; it must not be recomputed from the
    normalized top limb. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxDenormPre (sp shift : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word) :
    Assertion :=
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  let r0 := iterN1Max v0 v1 v2 v3 u0Orig0
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  let c0 := (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3
    u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ sp + signExtend12 4056) ** (.x0 ↦ᵣ (0 : Word)) **
   (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ sp + signExtend12 4088) **
   (.x2 ↦ᵣ r0.2.2.2.2.1) ** (.x10 ↦ᵣ c0) **
   ((sp + signExtend12 3992) ↦ₘ shift) **
   ((sp + signExtend12 4056) ↦ₘ r0.2.1) **
   ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
   ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) **
   ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
   ((sp + signExtend12 4088) ↦ₘ r0.1) **
   ((sp + signExtend12 4080) ↦ₘ r1.1) **
   ((sp + signExtend12 4072) ↦ₘ r2.1) **
   ((sp + signExtend12 4064) ↦ₘ r3.1) **
   ((sp + signExtend12 32) ↦ₘ v0) **
   ((sp + signExtend12 40) ↦ₘ v1) **
   ((sp + signExtend12 48) ↦ₘ v2) **
   ((sp + signExtend12 56) ↦ₘ v3))

/-- Caller frame retained at the v4 call/max/max/max denormalization entry. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxDenormFrameNoX1 (sp base : Word)
    (a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 scratchMem : Word) : Assertion :=
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  let r0 := iterN1Max v0 v1 v2 v3 u0Orig0
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ r3.2.2.2.2.2) **
  (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ divKTrialCallV4DLo v0) **
  (sp + signExtend12 3944 ↦ₘ divKTrialCallV4Un0 u0) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)

theorem fullDivN1CallMaxmaxmaxDenormFrameNoX1_pcFree (sp base : Word)
    (a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 scratchMem : Word) :
    (fullDivN1CallMaxmaxmaxDenormFrameNoX1 sp base
      a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 scratchMem).pcFree := by
  delta fullDivN1CallMaxmaxmaxDenormFrameNoX1
  pcFree

instance pcFreeInst_fullDivN1CallMaxmaxmaxDenormFrameNoX1
    (sp base : Word)
    (a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 scratchMem : Word) :
    Assertion.PCFree
      (fullDivN1CallMaxmaxmaxDenormFrameNoX1 sp base
        a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 scratchMem) :=
  ⟨fullDivN1CallMaxmaxmaxDenormFrameNoX1_pcFree sp base
    a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0Orig2 u0Orig1 u0Orig0 scratchMem⟩

/-- Denormalization+DIV-epilogue postcondition for the N1 path where j=3
    uses the v4 call path and j=2/j=1/j=0 all use max. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxDenormPost (sp shift : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word) :
    Assertion :=
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  let r0 := iterN1Max v0 v1 v2 v3 u0Orig0
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1
    r0.1 r1.1 r2.1 r3.1 **
  ((sp + signExtend12 3992) ↦ₘ shift)

@[irreducible]
def fullDivN1CallMaxmaxmaxUnifiedPostNoX1 (sp base shift : Word)
    (a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 scratchMem : Word) : Assertion :=
  fullDivN1CallMaxmaxmaxDenormPost sp shift
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 **
  fullDivN1CallMaxmaxmaxDenormFrameNoX1 sp base
    a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0Orig2 u0Orig1 u0Orig0 scratchMem

theorem fullDivN1CallMaxmaxmaxUnifiedPostNoX1_pcFree (sp base shift : Word)
    (a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 scratchMem : Word) :
    (fullDivN1CallMaxmaxmaxUnifiedPostNoX1 sp base shift
      a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 scratchMem).pcFree := by
  delta fullDivN1CallMaxmaxmaxUnifiedPostNoX1
  pcFree
  · delta fullDivN1CallMaxmaxmaxDenormPost
    pcFree
  · delta fullDivN1CallMaxmaxmaxDenormFrameNoX1
    pcFree

instance pcFreeInst_fullDivN1CallMaxmaxmaxUnifiedPostNoX1
    (sp base shift : Word)
    (a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 scratchMem : Word) :
    Assertion.PCFree
      (fullDivN1CallMaxmaxmaxUnifiedPostNoX1 sp base shift
        a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 scratchMem) :=
  ⟨fullDivN1CallMaxmaxmaxUnifiedPostNoX1_pcFree sp base shift
    a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0Orig2 u0Orig1 u0Orig0 scratchMem⟩

/-- v4 no-NOP N1 denormalization and DIV epilogue for the path where j=3
    uses the call path and j=2/j=1/j=0 all use max. -/
theorem evm_div_n1_call_maxmaxmax_denorm_epilogue_spec_v4_noNop
    (sp base shift : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (divCode_noNop_v4 base)
      (fullDivN1CallMaxmaxmaxDenormPre sp shift
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0)
      (fullDivN1CallMaxmaxmaxDenormPost sp shift
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0) := by
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  let r0 := iterN1Max v0 v1 v2 v3 u0Orig0
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  let c0 := (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3
    u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  have h := evm_div_preamble_denorm_epilogue_spec_v4_noNop sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c0 r0.1 r1.1 r2.1 r3.1
    v0 v1 v2 v3 hshift_nz
  exact cpsTripleWithin_weaken
    (fun h hp => by
      subst r3; subst r2; subst r1; subst r0; subst c0
      delta fullDivN1CallMaxmaxmaxDenormPre at hp
      simp only [se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp)
    (fun h hq => by
      subst r3; subst r2; subst r1; subst r0
      delta fullDivN1CallMaxmaxmaxDenormPost
      xperm_hyp hq)
    h

/-- Exact-`x1` framed v4 no-NOP N1 denormalization and DIV epilogue for
    the call/max/max/max path. -/
theorem evm_div_n1_call_maxmaxmax_denorm_epilogue_spec_v4_noNop_exact_x1
    (sp base shift : Word)
    (a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 scratchMem raVal : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (divCode_noNop_v4 base)
      (fullDivN1CallMaxmaxmaxDenormPre sp shift
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 **
       fullDivN1CallMaxmaxmaxDenormFrameNoX1 sp base
        a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 scratchMem **
       (.x1 ↦ᵣ raVal))
      (fullDivN1CallMaxmaxmaxUnifiedPostNoX1 sp base shift
        a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hDenorm :=
    evm_div_n1_call_maxmaxmax_denorm_epilogue_spec_v4_noNop
      sp base shift v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 hshift_nz
  have hFramed := cpsTripleWithin_frameR
    (fullDivN1CallMaxmaxmaxDenormFrameNoX1 sp base
      a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 scratchMem **
     (.x1 ↦ᵣ raVal))
    (by pcFree) hDenorm
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      delta fullDivN1CallMaxmaxmaxUnifiedPostNoX1
      xperm_hyp hq)
    hFramed

/-- Repackage the explicit v4 call/max/max/max loop post as the denorm entry
    surface plus retained caller frame. -/
theorem loopN1CallMaxmaxmaxScratchPostNoX1_to_denormPre_frame
    (sp base : Word)
    (a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 scratchMem shift raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN1CallMaxmaxmaxScratchPostNoX1 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 3992) ↦ₘ shift))) h) :
    ((fullDivN1CallMaxmaxmaxDenormPre sp shift
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 **
      fullDivN1CallMaxmaxmaxDenormFrameNoX1 sp base
        a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 scratchMem) ** (.x1 ↦ᵣ raVal)) h := by
  delta loopN1CallMaxmaxmaxScratchPostNoX1 loopN1Iter210PostNoX1
    loopN1Iter10PostNoX1 loopIterPostN1NoX1 loopIterPostN1Max
    fullDivN1CallMaxmaxmaxDenormPre fullDivN1CallMaxmaxmaxDenormFrameNoX1
    loopN1CallMaxmaxmaxR3 loopN1CallMaxmaxmaxR2 loopN1CallMaxmaxmaxR1 at hp ⊢
  simp (config := { decide := true }) only
    [iterN1_false, ite_false, n1_ub3_off4064, n1_qa3,
      n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
      sepConj_emp_right'] at hp ⊢
  rw [loopExitPostN1_j0_eq] at hp
  simp (config := { decide := true }) only
    [se12_32, se12_40, se12_48, se12_56] at hp ⊢
  xperm_hyp hp

/-- The named scratch precondition is PC-free, so later composed call/max
    surfaces can use it under `cpsTripleWithin_frameR`. -/
theorem loopN1CallMaxmaxmaxScratchPreNoX1_pcFree (sp : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) :
    (loopN1CallMaxmaxmaxScratchPreNoX1 sp
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratchUn0 scratchMem).pcFree := by
  delta loopN1CallMaxmaxmaxScratchPreNoX1
  pcFree

instance pcFreeInst_loopN1CallMaxmaxmaxScratchPreNoX1 (sp : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) :
    Assertion.PCFree
      (loopN1CallMaxmaxmaxScratchPreNoX1 sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem) :=
  ⟨loopN1CallMaxmaxmaxScratchPreNoX1_pcFree sp
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
    retMem dMem dloMem scratchUn0 scratchMem⟩

/-- Handoff from the n=1 v4 preloop postcondition to the canonical framed
    call/max/max/max loop precondition, preserving exact `x1`. -/
theorem loopSetupPost_to_fullDivN1CallMaxmaxmaxScratchPreNoX1_framed
    (sp : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v11Old : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    ∀ h,
      (loopSetupPost sp (1 : Word) (clzResult b0).1 a0 a1 a2 a3 b0 b1 b2 b3 **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) h →
      (((loopN1CallMaxmaxmaxScratchPreNoX1 sp
        jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
        (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        (0 : Word) (0 : Word) (0 : Word)
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1
        (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1))) h) := by
  intro h hp
  delta loopN1CallMaxmaxmaxScratchPreNoX1 loopN1PreWithScratchNoX1 loopN1Pre at ⊢
  delta loopSetupPost fullDivN1NormV fullDivN1NormU fullDivN1Shift fullDivN1AntiShift at hp ⊢
  simp only [x1_val_n1] at hp
  simp only [n1_ub3_off0, n1_ub3_off4088, n1_ub3_off4080,
              n1_ub3_off4072, n1_ub3_off4064,
              n2_ub2_off0, n3_ub1_off0, n3_ub0_off0,
              n1_qa3, n2_qa2, n3_qa1, n3_qa0,
              se12_32, se12_40, se12_48, se12_56] at hp ⊢
  xperm_hyp hp

/-- Opaque statement wrapper for the N1 path where j=3 uses the v4 call path
    and j=2/j=1/j=0 all use max. Keeping this triple behind a name avoids
    repeatedly elaborating the full pre/post shape at downstream theorem
    declarations. -/
@[irreducible]
def loopN1CallMaxmaxmaxExactX1ScratchSpec (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word) : Prop :=
  cpsTripleWithin 780 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
    (loopN1CallMaxmaxmaxScratchPreNoX1 sp
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
    (loopN1CallMaxmaxmaxScratchPostNoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 scratchMem ** (.x1 ↦ᵣ raVal))

/-- Compact assumptions for the N1 call/max/max/max exact path. -/
@[irreducible]
def loopN1CallMaxmaxmaxExactHypotheses
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word) : Prop :=
  BitVec.ult u1 v0 ∧
  loopN1CallMaxmaxmaxBranchFacts v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 ∧
  Carry2NzAll v0 v1 v2 v3 ∧
  loopN1CallMaxmaxmaxSelectedCarryFacts
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0

/-- Build the compact N1 call/max/max/max exact-path hypothesis bundle from
    the branch facts plus the universal carry2 assumption. -/
theorem loopN1CallMaxmaxmaxExactHypotheses_of_branches
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word)
    (hbltu3 : BitVec.ult u1 v0)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    loopN1CallMaxmaxmaxExactHypotheses
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 := by
  unfold loopN1CallMaxmaxmaxExactHypotheses
  exact ⟨hbltu3, hbranches, hcarry2,
    loopN1CallMaxmaxmaxSelectedCarryFacts_of_carry2All
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 hcarry2⟩

/-- Project the j=3 BLTU-taken fact from the compact N1 call/max/max/max hypotheses. -/
theorem loopN1CallMaxmaxmaxExactHypotheses_hbltu3
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (h : loopN1CallMaxmaxmaxExactHypotheses
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0) :
    BitVec.ult u1 v0 := by
  unfold loopN1CallMaxmaxmaxExactHypotheses at h
  exact h.1

/-- Project the all-max branch facts from the compact N1 call/max/max/max hypotheses. -/
theorem loopN1CallMaxmaxmaxExactHypotheses_branches
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (h : loopN1CallMaxmaxmaxExactHypotheses
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0) :
    loopN1CallMaxmaxmaxBranchFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 := by
  unfold loopN1CallMaxmaxmaxExactHypotheses at h
  exact h.2.1

/-- Project the global carry2 condition from the compact N1 call/max/max/max hypotheses. -/
theorem loopN1CallMaxmaxmaxExactHypotheses_carry2
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (h : loopN1CallMaxmaxmaxExactHypotheses
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0) :
    Carry2NzAll v0 v1 v2 v3 := by
  unfold loopN1CallMaxmaxmaxExactHypotheses at h
  exact h.2.2.1

/-- Project the v4 N1 call carry condition from the compact N1 call/max/max/max hypotheses. -/
theorem loopN1CallMaxmaxmaxExactHypotheses_carry2Call
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (h : loopN1CallMaxmaxmaxExactHypotheses
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0) :
    isAddbackCarry2NzN1CallV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold loopN1CallMaxmaxmaxExactHypotheses at h
  have hselected := h.2.2.2
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  exact hselected.1

/-- Bundle the many scalar inputs to the N1 call/max/max/max exact path.
    This gives later theorem statements a single data parameter instead of a
    long spine of old-register, limb, scratch, and memory-cell arguments. -/
structure LoopN1CallMaxmaxmaxExactInputs where
  sp : Word
  base : Word
  jOld : Word
  v5Old : Word
  v6Old : Word
  v7Old : Word
  v10Old : Word
  v11Old : Word
  v2Old : Word
  v0 : Word
  v1 : Word
  v2 : Word
  v3 : Word
  u0 : Word
  u1 : Word
  u2 : Word
  u3 : Word
  uTop : Word
  u0Orig2 : Word
  u0Orig1 : Word
  u0Orig0 : Word
  q3Old : Word
  q2Old : Word
  q1Old : Word
  q0Old : Word
  retMem : Word
  dMem : Word
  dloMem : Word
  scratchUn0 : Word
  scratchMem : Word
  raVal : Word

/-- Canonical bundled inputs for the full-DIV n=1 branch where the j=3
    iteration uses the v4 call path and j=2/j=1/j=0 use all-max. -/
def fullDivN1CallMaxmaxmaxExactInputs (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    LoopN1CallMaxmaxmaxExactInputs :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  { sp := sp
    base := base
    jOld := jOld
    v5Old := v5Old
    v6Old := v6Old
    v7Old := v7Old
    v10Old := v10Old
    v11Old := v11Old
    v2Old := v2Old
    v0 := v.1
    v1 := v.2.1
    v2 := v.2.2.1
    v3 := v.2.2.2
    u0 := u.2.2.2.1
    u1 := u.2.2.2.2
    u2 := 0
    u3 := 0
    uTop := 0
    u0Orig2 := u.2.2.1
    u0Orig1 := u.2.1
    u0Orig0 := u.1
    q3Old := q3Old
    q2Old := q2Old
    q1Old := q1Old
    q0Old := q0Old
    retMem := retMem
    dMem := dMem
    dloMem := dloMem
    scratchUn0 := scratchUn0
    scratchMem := scratchMem
    raVal := raVal }

/-- The full-DIV n=1 j=3 trial predicate gives the j=3 taken branch fact
    for the canonical call/max/max/max bundled inputs. -/
theorem fullDivN1CallMaxmaxmaxExactInputs_hbltu3
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbltu3 : isTrialN1_j3 true a3 b0) :
    BitVec.ult
      (fullDivN1CallMaxmaxmaxExactInputs sp base
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        a0 a1 a2 a3 b0 b1 b2 b3
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal).u1
      (fullDivN1CallMaxmaxmaxExactInputs sp base
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        a0 a1 a2 a3 b0 b1 b2 b3
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal).v0 := by
  unfold isTrialN1_j3 at hbltu3
  unfold fullDivN1CallMaxmaxmaxExactInputs fullDivN1NormU fullDivN1NormV
    fullDivN1AntiShift fullDivN1Shift
  simpa using hbltu3.symm

/-- Spec wrapper specialized to bundled N1 call/max/max/max inputs. -/
@[irreducible]
def loopN1CallMaxmaxmaxExactInputSpec
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  loopN1CallMaxmaxmaxExactX1ScratchSpec I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
    I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem I.raVal

/-- Final spec wrapper for the canonical full-DIV n=1 call/max/max/max
    bundled inputs. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxExactInputSpec (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Prop :=
  loopN1CallMaxmaxmaxExactInputSpec
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)

/-- Compact hypotheses specialized to bundled N1 call/max/max/max inputs. -/
@[irreducible]
def loopN1CallMaxmaxmaxExactInputHypotheses
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  loopN1CallMaxmaxmaxExactHypotheses
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 I.u0Orig0

/-- Build the bundled N1 call/max/max/max exact-path hypothesis wrapper
    from the bundled branch facts plus the universal carry2 assumption. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_of_branches
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hbltu3 : BitVec.ult I.u1 I.v0)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1)
    (hcarry2 : Carry2NzAll I.v0 I.v1 I.v2 I.v3) :
    loopN1CallMaxmaxmaxExactInputHypotheses I := by
  unfold loopN1CallMaxmaxmaxExactInputHypotheses
  exact loopN1CallMaxmaxmaxExactHypotheses_of_branches
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 I.u0Orig0
    hbltu3 hbranches hcarry2

/-- Build the bundled N1 call/max/max/max exact-path hypotheses directly
    from the four path branch facts and the universal carry2 assumption. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_of_bltu
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hbltu3 : BitVec.ult I.u1 I.v0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop).2.1
      I.v0)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2).2.1 I.v0)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1).2.1 I.v0)
    (hcarry2 : Carry2NzAll I.v0 I.v1 I.v2 I.v3) :
    loopN1CallMaxmaxmaxExactInputHypotheses I := by
  exact loopN1CallMaxmaxmaxExactInputHypotheses_of_branches I hbltu3
    (loopN1CallMaxmaxmaxBranchFacts_of_bltu
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
      hbltu2 hbltu1 hbltu0)
    hcarry2

/-- Project the j=3 BLTU-taken fact from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_hbltu3
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    BitVec.ult I.u1 I.v0 := by
  unfold loopN1CallMaxmaxmaxExactInputHypotheses at h
  exact loopN1CallMaxmaxmaxExactHypotheses_hbltu3
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 h

/-- Project the all-max branch facts from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_branches
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxBranchFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 := by
  unfold loopN1CallMaxmaxmaxExactInputHypotheses at h
  exact loopN1CallMaxmaxmaxExactHypotheses_branches
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 h

/-- Project the global carry2 condition from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_carry2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    Carry2NzAll I.v0 I.v1 I.v2 I.v3 := by
  unfold loopN1CallMaxmaxmaxExactInputHypotheses at h
  exact loopN1CallMaxmaxmaxExactHypotheses_carry2
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 h

/-- Project the v4 N1 call carry condition from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_carry2Call
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    isAddbackCarry2NzN1CallV4 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop := by
  unfold loopN1CallMaxmaxmaxExactInputHypotheses at h
  exact loopN1CallMaxmaxmaxExactHypotheses_carry2Call
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 h

/-- Project the j=2 all-max branch fact from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_hbltu2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop).2.1
      I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu2
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxExactInputHypotheses_branches I h)

/-- Project the j=1 all-max branch fact from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_hbltu1
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2).2.1 I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu1
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxExactInputHypotheses_branches I h)

/-- Project the j=0 all-max branch fact from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_hbltu0
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1).2.1 I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu0
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxExactInputHypotheses_branches I h)

/-- Bundled alignment condition for the v4 div128 call return address. -/
@[irreducible]
def loopN1CallMaxmaxmaxExactInputAligned
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  ((I.base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
    ~~~(1 : Word) = I.base + div128CallRetOff

/-- Unpack bundled alignment into the raw equality expected by the j=3 call step. -/
theorem loopN1CallMaxmaxmaxExactInputAligned_raw
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputAligned I) :
    ((I.base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
      ~~~(1 : Word) = I.base + div128CallRetOff := by
  unfold loopN1CallMaxmaxmaxExactInputAligned at h
  exact h

/-- Alignment wrapper for the canonical full-DIV n=1 call/max/max/max
    bundled inputs. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxExactInputAligned (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Prop :=
  loopN1CallMaxmaxmaxExactInputAligned
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)

/-- Hypothesis wrapper for the canonical full-DIV n=1 call/max/max/max
    bundled inputs. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxExactInputHypotheses (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Prop :=
  loopN1CallMaxmaxmaxExactInputHypotheses
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)

/-- Build the canonical full-DIV n=1 call/max/max/max hypothesis wrapper
    from the path branch facts and the universal carry2 assumption. -/
theorem fullDivN1CallMaxmaxmaxExactInputHypotheses_of_bltu
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1CallMaxmaxmaxExactInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxExactInputHypotheses
  exact loopN1CallMaxmaxmaxExactInputHypotheses_of_bltu
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (fullDivN1CallMaxmaxmaxExactInputs_hbltu3 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3)
    hbltu2 hbltu1 hbltu0 hcarry2


end EvmAsm.Evm64
