module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNop
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNopPreloop
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3PcFree
public import EvmAsm.Evm64.DivMod.Compose.V4Code

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Loop body n=3, max+skip, j=0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n3_max_skip_j0_norm_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN3MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n3_max_skip_j0_norm_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow)

/-- Loop body n=3, max+skip, j=1 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n3_max_skip_j1_norm_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN3MaxSkipJ1NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3SkipPost sp (1 : Word) (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n3_max_skip_j1_norm_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow)

/-- Loop body n=3, max+addback (BEQ double-addback), j>0 over the full
    `divCode_v4` bundle. -/
theorem divK_loop_body_n3_max_addback_jgt0_beq_norm_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN3MaxAddbackJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3AddbackBeqPost sp j (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n3_max_addback_jgt0_beq_norm_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hcarry2_nz hborrow)

/-- Loop body n=3, call+skip, j=0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n3_call_skip_j0_norm_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN3CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n3_call_skip_j0_norm_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu hborrow)

/-- Loop body n=3, call+skip, j=1 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n3_call_skip_j1_norm_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN3CallSkipJ1NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallSkipJgt0PostV4 sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n3_call_skip_j1_norm_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu hborrow)

/-- Loop body n=3, call+addback (BEQ double-addback), j>0 over the full
    `divCode_v4` bundle. -/
theorem divK_loop_body_n3_call_addback_jgt0_beq_norm_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN3CallAddbackJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n3_call_addback_jgt0_beq_norm_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu hborrow hcarry2_nz)

/-- Lift the n=3 exact-x1/scratch v4 preloop+loop path from the no-NOP body
    to the full `divCode_v4` dispatcher bundle. -/
theorem fullDivN3_preloop_loop_unified_exact_x1_scratch_v4
    {P Q : Assertion} (base : Word)
    (h :
      cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 448)
        base (base + denormOff) (divCode_noNop_v4 base) P Q) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 448)
      base (base + denormOff) (divCode_v4 base) P Q := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4 h

@[irreducible]
def fullDivN3R1V4 (bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  iterN3V4 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word)

@[simp]
theorem fullDivN3R1V4_false (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN3R1V4 false a0 a1 a2 a3 b0 b1 b2 b3 =
      iterN3Max
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word) := by
  rw [fullDivN3R1V4, iterN3V4]
  simp

@[simp]
theorem fullDivN3R1V4_true (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN3R1V4 true a0 a1 a2 a3 b0 b1 b2 b3 =
      iterWithDoubleAddback
        (divKTrialCallV4QHat
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1)
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word) := by
  rw [fullDivN3R1V4, iterN3V4]
  simp

@[irreducible]
def fullDivN3R0V4 (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  iterN3V4 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

@[irreducible]
def fullDivN3C3V4 (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  if bltu_0 then
    (mulsubN4 (divKTrialCallV4QHat r1.2.2.2.1 r1.2.2.1 v.2.2.1)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  else
    (mulsubN4 (signExtend12 4095 : Word)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2

/-- N3 denorm precondition whose call-path arithmetic matches the v4 callable
    trial-division qhat, rather than the older `div128Quot` model. -/
@[irreducible]
def fullDivN3DenormPreV4 (bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN3Shift b2
  let v := fullDivN3NormV b0 b1 b2 b3
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ sp + signExtend12 4056) ** (.x0 ↦ᵣ (0 : Word)) **
   (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ sp + signExtend12 4088) **
   (.x2 ↦ᵣ r0.2.2.2.2.1) **
   (.x10 ↦ᵣ fullDivN3C3V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) **
   ((sp + signExtend12 3992) ↦ₘ shift) **
   ((sp + signExtend12 4056) ↦ₘ r0.2.1) **
   ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
   ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) **
   ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
   ((sp + signExtend12 4088) ↦ₘ r0.1) **
   ((sp + signExtend12 4080) ↦ₘ r1.1) **
   ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
   ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
   ((sp + signExtend12 32) ↦ₘ v.1) **
   ((sp + signExtend12 40) ↦ₘ v.2.1) **
   ((sp + signExtend12 48) ↦ₘ v.2.2.1) **
   ((sp + signExtend12 56) ↦ₘ v.2.2.2))

/-- N3 denorm postcondition paired with `fullDivN3DenormPreV4`. -/
@[irreducible]
def fullDivN3DenormPostV4 (bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN3Shift b2
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1
    r0.1 r1.1 (0 : Word) (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift)

@[irreducible]
def fullDivN3ScratchNoX1V4 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 : Word) :
    Assertion :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let scratchRet1 := if bltu_1 then (base + div128CallRetOff) else retMem
  let scratchD1 := if bltu_1 then v.2.2.1 else dMem
  let scratchDLo1 := if bltu_1 then divKTrialCallV4DLo v.2.2.1 else dloMem
  let scratchUn01 := if bltu_1 then divKTrialCallV4Un0 u.2.2.2.1 else scratchUn0
  (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratchRet1)) **
  (sp + signExtend12 3960 ↦ₘ (if bltu_0 then v.2.2.1 else scratchD1)) **
  (sp + signExtend12 3952 ↦ₘ (if bltu_0 then divKTrialCallV4DLo v.2.2.1 else scratchDLo1)) **
  (sp + signExtend12 3944 ↦ₘ (if bltu_0 then divKTrialCallV4Un0 r1.2.2.1 else scratchUn01))

@[irreducible]
def fullDivN3ScratchMemV4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Word :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let scratch1 := if bltu_1 then
      divKTrialCallV4ScratchOut u.2.2.2.2 u.2.2.2.1 v.2.2.1 scratchMem
    else
      scratchMem
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  if bltu_0 then
    divKTrialCallV4ScratchOut r1.2.2.2.1 r1.2.2.1 v.2.2.1 scratch1
  else
    scratch1

@[irreducible]
def fullDivN3FrameNoX1V4 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 : Word) :
    Assertion :=
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  fullDivN3ScratchNoX1V4 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratchUn0

@[irreducible]
def fullDivN3UnifiedPostNoX1V4 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  fullDivN3DenormPostV4 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
  fullDivN3FrameNoX1V4 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratchUn0 **
  ((sp + signExtend12 3936) ↦ₘ
    fullDivN3ScratchMemV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)

/-- N3 denormalization and DIV epilogue over the v4/no-NOP dispatcher body. -/
theorem evm_div_n3_denorm_epilogue_bundled_spec_v4_noNop (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (divCode_noNop_v4 base)
      (fullDivN3DenormPre bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3)
      (fullDivN3DenormPost bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := fullDivN3Shift b2
  let v := fullDivN3NormV b0 b1 b2 b3
  let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let c3 := fullDivN3C3 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  have h := evm_div_preamble_denorm_epilogue_spec_v4_noNop sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3 r0.1 r1.1 (0 : Word) (0 : Word)
    v.1 v.2.1 v.2.2.1 v.2.2.2 hshift_nz
  exact cpsTripleWithin_weaken
    (fun h hp => by
      subst shift; subst v; subst r1; subst r0; subst c3
      delta fullDivN3DenormPre at hp
      simp only [se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp)
    (fun h hq => by
      subst shift; subst r1; subst r0
      delta fullDivN3DenormPost
      xperm_hyp hq)
    h

/-- N3 denormalization and DIV epilogue over the v4/no-NOP dispatcher body,
    using the v4 callable-trial final computation family. -/
theorem evm_div_n3_denorm_epilogue_bundled_spec_v4_noNop_v4Final
    (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (divCode_noNop_v4 base)
      (fullDivN3DenormPreV4 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3)
      (fullDivN3DenormPostV4 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := fullDivN3Shift b2
  let v := fullDivN3NormV b0 b1 b2 b3
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let c3 := fullDivN3C3V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  have h := evm_div_preamble_denorm_epilogue_spec_v4_noNop sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3 r0.1 r1.1 (0 : Word) (0 : Word)
    v.1 v.2.1 v.2.2.1 v.2.2.2 hshift_nz
  exact cpsTripleWithin_weaken
    (fun h hp => by
      subst shift; subst v; subst r1; subst r0; subst c3
      delta fullDivN3DenormPreV4 at hp
      simp only [se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp)
    (fun h hq => by
      subst shift; subst r1; subst r0
      delta fullDivN3DenormPostV4
      xperm_hyp hq)
    h

/-- N3 denormalization and DIV epilogue over v4/no-NOP for the v4 final
    computation family, preserving exact caller `x1` and the final v4 div128
    scratch cell. -/
theorem evm_div_n3_denorm_epilogue_bundled_spec_v4_noNop_v4Final_exact_x1_scratch_frame
    (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff)
      (divCode_noNop_v4 base)
      (fullDivN3DenormPreV4 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
       fullDivN3FrameNoX1V4 bltu_1 bltu_0 sp base
         a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ
         fullDivN3ScratchMemV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
       (.x1 ↦ᵣ raVal))
      (fullDivN3UnifiedPostNoX1V4 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hDenorm := evm_div_n3_denorm_epilogue_bundled_spec_v4_noNop_v4Final
    bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz
  have hFramed := cpsTripleWithin_frameR
    (fullDivN3FrameNoX1V4 bltu_1 bltu_0 sp base
     a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal))
    (by
      delta fullDivN3FrameNoX1V4 fullDivN3ScratchNoX1V4
      pcFree) hDenorm
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      delta fullDivN3UnifiedPostNoX1V4
      xperm_hyp hq)
    hFramed

theorem loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_FF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN3UnifiedPostV4NoX1 false false sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) h) :
    (fullDivN3DenormPreV4 false false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN3FrameNoX1V4 false false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV4 false false a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN3UnifiedPostV4NoX1 loopIterPostN3Max at hp
  delta fullDivN3DenormPreV4 fullDivN3FrameNoX1V4 fullDivN3ScratchNoX1V4
    fullDivN3ScratchMemV4 fullDivN3Shift fullDivN3AntiShift fullDivN3NormV
    fullDivN3NormU fullDivN3R1V4 fullDivN3R0V4 fullDivN3C3V4 iterN3V4 at hp ⊢
  simp (config := { decide := true }) only [ite_false] at hp ⊢
  rw [loopExitPostN3_j0_eq] at hp
  simp (config := { decide := true }) only
    [n3_ub1_off4064, n3_qa1, se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_FT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN3UnifiedPostV4NoX1 false true sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) h) :
    (fullDivN3DenormPreV4 false true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN3FrameNoX1V4 false true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV4 false true a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN3UnifiedPostV4NoX1 loopIterPostN3CallScratchNoX1 at hp
  simp (config := { decide := true }) only [] at hp
  simp (config := { decide := true }) only
    [loopExitPostN3_j0_eq, n3_ub1_off4064, n3_qa1,
      se12_32, se12_40, se12_48, se12_56] at hp
  delta fullDivN3Shift fullDivN3AntiShift fullDivN3NormV fullDivN3NormU at hp
  simp (config := { decide := true }) only [] at hp
  delta fullDivN3DenormPreV4 fullDivN3FrameNoX1V4 fullDivN3ScratchNoX1V4
    fullDivN3ScratchMemV4 fullDivN3Shift fullDivN3AntiShift fullDivN3NormV
    fullDivN3NormU fullDivN3R1V4 fullDivN3R0V4 fullDivN3C3V4 iterN3V4
  simp (config := { decide := true }) only
    [ite_false, ite_true, se12_32, se12_40, se12_48, se12_56]
  set shift := (clzResult b2).1 with hshift
  set antiShift := (signExtend12 (0 : BitVec 12) - shift) with hantiShift
  set v0 := b0 <<< (shift.toNat % 64) with hv0
  set v1 := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)) with hv1
  set v2 := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)) with hv2
  set v3 := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)) with hv3
  set u0 := a0 <<< (shift.toNat % 64) with hu0
  set u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)) with hu1
  set u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)) with hu2
  set u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)) with hu3
  set u4 := a3 >>> (antiShift.toNat % 64) with hu4
  set r1 := iterN3Max v0 v1 v2 v3 u1 u2 u3 u4 (0 : Word) with hr1
  set qHat := divKTrialCallV4QHat r1.2.2.2.1 r1.2.2.1 v2 with hqHat
  set r0 := iterWithDoubleAddback qHat v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1
    r1.2.2.2.1 r1.2.2.2.2.1 with hr0
  set c3 := (mulsubN4 qHat v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1
    r1.2.2.2.1).2.2.2.2 with hc3
  subst c3
  subst r0
  subst qHat
  xperm_hyp hp

theorem loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_TF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN3UnifiedPostV4NoX1 true false sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) h) :
    (fullDivN3DenormPreV4 true false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN3FrameNoX1V4 true false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV4 true false a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN3UnifiedPostV4NoX1 loopIterPostN3Max at hp
  simp (config := { decide := true }) only [] at hp
  simp (config := { decide := true }) only
    [loopExitPostN3_j0_eq, n3_ub1_off4064, n3_qa1,
      se12_32, se12_40, se12_48, se12_56] at hp
  delta fullDivN3Shift fullDivN3AntiShift fullDivN3NormV fullDivN3NormU at hp
  simp (config := { decide := true }) only [] at hp
  delta fullDivN3DenormPreV4 fullDivN3FrameNoX1V4 fullDivN3ScratchNoX1V4
    fullDivN3ScratchMemV4 fullDivN3Shift fullDivN3AntiShift fullDivN3NormV
    fullDivN3NormU fullDivN3R1V4 fullDivN3R0V4 fullDivN3C3V4 iterN3V4
  simp (config := { decide := true }) only
    [ite_false, ite_true, se12_32, se12_40, se12_48, se12_56]
  set shift := (clzResult b2).1 with hshift
  set antiShift := (signExtend12 (0 : BitVec 12) - shift) with hantiShift
  set v0 := b0 <<< (shift.toNat % 64) with hv0
  set v1 := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)) with hv1
  set v2 := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)) with hv2
  set v3 := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)) with hv3
  set u0 := a0 <<< (shift.toNat % 64) with hu0
  set u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)) with hu1
  set u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)) with hu2
  set u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)) with hu3
  set u4 := a3 >>> (antiShift.toNat % 64) with hu4
  set qHat1 := divKTrialCallV4QHat u4 u3 v2 with hqHat1
  set r1 := iterWithDoubleAddback qHat1 v0 v1 v2 v3 u1 u2 u3 u4 (0 : Word) with hr1
  set r0 := iterN3Max v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1 r1.2.2.2.1
    r1.2.2.2.2.1 with hr0
  set c3 := (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0
    r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2 with hc3
  subst c3
  subst r0
  subst r1
  subst qHat1
  xperm_hyp hp

theorem loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_TT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN3UnifiedPostV4NoX1 true true sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) h) :
    (fullDivN3DenormPreV4 true true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN3FrameNoX1V4 true true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV4 true true a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN3UnifiedPostV4NoX1 loopIterPostN3CallScratchNoX1 at hp
  simp (config := { decide := true }) only [] at hp
  simp (config := { decide := true }) only
    [loopExitPostN3_j0_eq, n3_ub1_off4064, n3_qa1,
      se12_32, se12_40, se12_48, se12_56] at hp
  delta fullDivN3Shift fullDivN3AntiShift fullDivN3NormV fullDivN3NormU at hp
  simp (config := { decide := true }) only [] at hp
  delta fullDivN3DenormPreV4 fullDivN3FrameNoX1V4 fullDivN3ScratchNoX1V4
    fullDivN3ScratchMemV4 fullDivN3Shift fullDivN3AntiShift fullDivN3NormV
    fullDivN3NormU fullDivN3R1V4 fullDivN3R0V4 fullDivN3C3V4 iterN3V4
  simp (config := { decide := true }) only
    [ite_true, se12_32, se12_40, se12_48, se12_56]
  set shift := (clzResult b2).1 with hshift
  set antiShift := (signExtend12 (0 : BitVec 12) - shift) with hantiShift
  set v0 := b0 <<< (shift.toNat % 64) with hv0
  set v1 := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)) with hv1
  set v2 := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)) with hv2
  set v3 := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)) with hv3
  set u0 := a0 <<< (shift.toNat % 64) with hu0
  set u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)) with hu1
  set u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)) with hu2
  set u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)) with hu3
  set u4 := a3 >>> (antiShift.toNat % 64) with hu4
  set qHat1 := divKTrialCallV4QHat u4 u3 v2 with hqHat1
  set r1 := iterWithDoubleAddback qHat1 v0 v1 v2 v3 u1 u2 u3 u4 (0 : Word) with hr1
  set qHat0 := divKTrialCallV4QHat r1.2.2.2.1 r1.2.2.1 v2 with hqHat0
  set r0 := iterWithDoubleAddback qHat0 v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1
    r1.2.2.2.1 r1.2.2.2.2.1 with hr0
  set c3 := (mulsubN4 qHat0 v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1
    r1.2.2.2.1).2.2.2.2 with hc3
  subst c3
  subst r0
  subst qHat0
  subst r1
  subst qHat1
  xperm_hyp hp

/-- N3 denormalization and DIV epilogue over v4/no-NOP, preserving exact caller
    `x1` and carrying the v4 div128 scratch cell as frame. -/
theorem evm_div_n3_denorm_epilogue_bundled_spec_v4_noNop_exact_x1_scratch_frame
    (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff)
      (divCode_noNop_v4 base)
      (fullDivN3DenormPre bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
       fullDivN3FrameNoX1 bltu_1 bltu_0 sp base
         a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (fullDivN3UnifiedPostNoX1 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal)) := by
  have hDenorm := evm_div_n3_denorm_epilogue_bundled_spec_v4_noNop
    bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz
  have hFramed := cpsTripleWithin_frameR
    (fullDivN3FrameNoX1 bltu_1 bltu_0 sp base
     a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ scratchMem) **
     (.x1 ↦ᵣ raVal))
    (by pcFree) hDenorm
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      delta fullDivN3UnifiedPostNoX1 fullDivN3DenormPost at hq ⊢
      xperm_hyp hq)
    hFramed

end EvmAsm.Evm64
