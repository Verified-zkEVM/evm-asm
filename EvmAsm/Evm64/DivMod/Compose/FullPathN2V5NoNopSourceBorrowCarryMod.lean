/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopSourceBorrowCarryMod

  MOD mirror of `FullPathN2V5NoNopSourceBorrowCarry`: the borrow-dispatched j=2
  single-call loop source theorem over `modCode_noNop_v5`, requiring carry2nz only
  conditionally on the runtime borrow.  Byte-for-byte the DIV proof — compose the
  MOD j=2 call iter borrowCarry body (#7695) with the code-agnostic source-pre
  bridge `loopN2PreWithScratchV4NoX1_to_call_j2_pre`.  Brick 9 of the n=2 MOD loop
  body (call source layer).  Bead `evm-asm-wbc4i.10.3.2.4.5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopSourceShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallIterBorrowCarryMod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- First n=2 call iteration from the loop source over `modCode_noNop_v5`, with
    carry2nz required only on the runtime-borrow branch. -/
theorem divK_loop_n2_call_j2_from_source_exact_loopIterScratch_v5_noNop_borrowCarry_modCode
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_borrow :
      BitVec.ult uTop (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3) →
      callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2CallScratchNoX1 sp base (2 : Word)
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop ** (.x1 ↦ᵣ raVal)) **
        ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) := by
  have J2 := divK_loop_body_n2_call_j2_exact_loopIterScratch_v5_noNop_borrowCarry_modCode sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu hcarry2_borrow
  have J2f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig1) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      have hp' := loopN2PreWithScratchV4NoX1_to_call_j2_pre
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem h hp
      xperm_hyp hp')
    (fun h hp => hp)
    J2f

end EvmAsm.Evm64
