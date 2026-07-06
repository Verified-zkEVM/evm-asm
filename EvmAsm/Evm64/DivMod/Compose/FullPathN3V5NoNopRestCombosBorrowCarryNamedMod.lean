/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopRestCombosBorrowCarryNamedMod

  Named-carry restatements of the call_max and max_call n=3 borrowCarry combos
  (#7532): the CALL obligation's second-addback carry is written as the NAMED
  `loopBodyN3CallAddbackCarry2NzV5` (defeq to inline, unfolded here where
  `mulsubN4`/`addbackN4` are transparent).  Completes the named-carry combo set
  (call_j1/call_call in #7534 + call_max/max_call here; max_max already takes the
  named `isAddbackCarry2NzN3Max`) so the from-source borrowCarry dispatch can feed
  the bundle's named obligations named-to-named without the isDefEq explosion.
  Bead `evm-asm-wbc4i.9.3.3.3.4`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopRestCombosBorrowCarryMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnifiedMod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Named-carry restatement of `divK_loop_n3_call_max_from_source_..._borrowCarry`. -/
theorem divK_loop_n3_call_max_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry_named
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : BitVec.ult u3 v2)
    (hcarry2_borrow_1 :
      BitVec.ult uTop (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) →
      loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_0 :
      let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      ¬BitVec.ult r1.2.2.2.1 v2)
    (hcarry2_borrow_0 :
      let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r1.2.2.2.2.1
        (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1) →
      isAddbackCarry2NzN3Max v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (234 + 152) (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
        (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
        (sp + signExtend12 3960 ↦ₘ v2) **
        (sp + signExtend12 3952 ↦ₘ (divKTrialCallV5DLo v2)) **
        (sp + signExtend12 3944 ↦ₘ (divKTrialCallV5Un0 u2)) **
        (sp + signExtend12 3936 ↦ₘ (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)) **
        (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1))) :=
  divK_loop_n3_call_max_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu_1 hcarry2_borrow_1 hbltu_0 hcarry2_borrow_0

/-- Named-carry restatement of `divK_loop_n3_max_call_from_source_..._borrowCarry`. -/
theorem divK_loop_n3_max_call_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry_named
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hcarry2_borrow_1 :
      BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) →
      isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r1.2.2.2.1 v2)
    (hcarry2_borrow_0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r1.2.2.2.2.1
        (mulsubN4_c3 (divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2)
          v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1) →
      loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (152 + 234) (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2)
        (divKTrialCallV5DLo v2)
        (divKTrialCallV5Un0 r1.2.2.1)
        (divKTrialCallV5ScratchOut r1.2.2.2.1 r1.2.2.1 v2 scratchMem)
        v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
        (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1))) :=
  divK_loop_n3_max_call_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu_1 hcarry2_borrow_1 hbltu_0 hcarry2_borrow_0

end EvmAsm.Evm64
