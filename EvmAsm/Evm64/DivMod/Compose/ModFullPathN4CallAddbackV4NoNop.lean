module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V4
public import EvmAsm.Evm64.DivMod.Compose.ModPreloopN4V4NoNop

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Full MOD n=4 call+addback BEQ precondition for the v4 path.
    Keeping this large frame behind an irreducible name prevents downstream
    users from elaborating the whole CPS surface unless a proof explicitly
    unfolds it. -/
@[irreducible]
def fullModN4CallAddbackBeqPreV4
    (sp b3 v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 : Word)
    (nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
   (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
   (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) ** (.x11 ↦ᵣ v11Old) **
   ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
   ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
   ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
   ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
   ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
   ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
   ((sp + signExtend12 4024) ↦ₘ u4Old) **
   ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
   ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
   ((sp + signExtend12 3992) ↦ₘ shiftMem) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
   (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
   (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratchUn0) **
   regOwn .x1) ** (sp + signExtend12 3936 ↦ₘ scratchMem))

theorem fullModN4CallAddbackBeqPreV4_unfold
    {sp b3 v5 v6 v7 v10 v11Old : Word}
    {a0 a1 a2 a3 b0 b1 b2 : Word}
    {q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 : Word}
    {nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word} :
    fullModN4CallAddbackBeqPreV4
      sp b3 v5 v6 v7 v10 v11Old
      a0 a1 a2 a3 b0 b1 b2
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem =
    (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) ** (.x11 ↦ᵣ v11Old) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old) **
     ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
     ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
     ((sp + signExtend12 3992) ↦ₘ shiftMem) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratchUn0) **
     regOwn .x1) ** (sp + signExtend12 3936 ↦ₘ scratchMem)) := by
  rw [fullModN4CallAddbackBeqPreV4]

/-- Full MOD n=4 call+addback BEQ postcondition for the v4 div128 subroutine.
    This mirrors `fullDivN4CallAddbackBeqPostV4`, but keeps the MOD denorm
    postcondition and carries the v4 trial-call scratch output. -/
def fullModN4CallAddbackBeqPostV4
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Assertion :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := divKTrialCallV4QHat u4 u3 b3'
  let dLo := divKTrialCallV4DLo b3'
  let divUn0 := divKTrialCallV4Un0 u3
  let scratchOut := divKTrialCallV4ScratchOut u4 u3 b3' scratchMem
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u4 - c3) b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  let qOut := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
              else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4Out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  denormModPost sp shift un0Out un1Out un2Out un3Out **
  ((sp + signExtend12 4088) ↦ₘ qOut) **
  ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ u4Out) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qOut) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ b3') **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ divUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1

/-- Unfold `fullModN4CallAddbackBeqPostV4`, exposing the abstract v4 quotient
    `div128Quot_v4` instead of the executable trial-call helper. -/
theorem fullModN4CallAddbackBeqPostV4_div128Quot_unfold
    {sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word} :
    fullModN4CallAddbackBeqPostV4 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem =
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    let qHat := div128Quot_v4 u4 u3 b3'
    let dLo := divKTrialCallV4DLo b3'
    let divUn0 := divKTrialCallV4Un0 u3
    let scratchOut := divKTrialCallV4ScratchOut u4 u3 b3' scratchMem
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u4 - c3) b0' b1' b2' b3'
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
    let qOut := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
                else qHat + signExtend12 4095
    let un0Out := if carry = 0 then ab'.1 else ab.1
    let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
    let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
    let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
    let u4Out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
    denormModPost sp shift un0Out un1Out un2Out un3Out **
    ((sp + signExtend12 4088) ↦ₘ qOut) **
    ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 3992) ↦ₘ shift) **
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
    ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + signExtend12 4024) ↦ₘ u4Out) **
    ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
    (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
    (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
    (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qOut) **
    (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
    (sp + signExtend12 3960 ↦ₘ b3') **
    (sp + signExtend12 3952 ↦ₘ dLo) **
    (sp + signExtend12 3944 ↦ₘ divUn0) **
    (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1 := by
  delta fullModN4CallAddbackBeqPostV4
  simp only [divKTrialCallV4QHat_eq_div128Quot_v4]

/-- Full n=4 MOD call+addback BEQ path over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_n4_full_call_addback_beq_spec_within_v4_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4 a3 b2 b3)
    (hcarry2_nz : isAddbackCarry2NzN4CallV4Ab a0 a1 a2 a3 b0 b1 b2 b3)
    (hborrow : isAddbackBorrowN4CallV4Ab a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (modCode_noNop_v4 base)
      (fullModN4CallAddbackBeqPreV4
        sp b3 v5 v6 v7 v10 v11Old
        a0 a1 a2 a3 b0 b1 b2
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem)
      (fullModN4CallAddbackBeqPostV4 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) := by
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := divKTrialCallV4QHat u4 u3 b3'
  let dLo := divKTrialCallV4DLo b3'
  let divUn0 := divKTrialCallV4Un0 u3
  let scratchOut := divKTrialCallV4ScratchOut u4 u3 b3' scratchMem
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u4 - c3) b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  let qOut := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
              else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4Out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  have hA := evm_mod_n4_preloop_call_addback_beq_spec_within_v4_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  have hB := evm_mod_preamble_denorm_epilogue_spec_within_noNop_v4 sp base
    un0Out un1Out un2Out un3Out shift
    un3Out (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3
    b0' b1' b2' b3'
    hshift_nz
  have hBF := cpsTripleWithin_frameR
    (((sp + signExtend12 4088) ↦ₘ qOut) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4Out) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qOut) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ b3') **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ divUn0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [preloopCallAddbackBeqPostN4V4_unfold] at hp
      unfold loopBodyN4CallAddbackJ0PostV4 at hp
      unfold loopBodyN4AddbackBeqPost at hp
      unfold loopBodyAddbackBeqPost at hp
      simp only [loopExitPostN4_j0_eq, se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp) hA hBF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by
      rw [fullModN4CallAddbackBeqPreV4_unfold] at hp
      xperm_hyp hp)
    (fun h hq => by
      delta fullModN4CallAddbackBeqPostV4
      rw [sepConj_assoc'] at hq
      xperm_hyp hq)
    hFull

/-- Full n=4 MOD call+addback BEQ path over the full v4 MOD code bundle. -/
theorem evm_mod_n4_full_call_addback_beq_spec_within_v4 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4 a3 b2 b3)
    (hcarry2_nz : isAddbackCarry2NzN4CallV4Ab a0 a1 a2 a3 b0 b1 b2 b3)
    (hborrow : isAddbackBorrowN4CallV4Ab a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (modCode_v4 base)
      (fullModN4CallAddbackBeqPreV4
        sp b3 v5 v6 v7 v10 v11Old
        a0 a1 a2 a3 b0 b1 b2
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem)
      (fullModN4CallAddbackBeqPostV4 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (evm_mod_n4_full_call_addback_beq_spec_within_v4_noNop sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow)

end EvmAsm.Evm64
