/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopCallCallCall

  Three-iteration call-call-call composition for the n=2 v4/no-NOP source path.
  Proves `LoopN2CallCallCallSourceSpec` (defined in `FullPathN2V4NoNopFinalPost`)
  for the call×call×call branch of the eight-case unified dispatcher by
  composing the j=2/j=1 source theorem with the j=0 call body.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopFinalPost

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The n=2 v4/no-NOP source path whose three loop iterations all take the
    callable trial-division (call) path, packaged as a single
    `cpsTripleWithin` from `loopN2PreWithScratchV4NoX1 ** (.x1 ↦ᵣ raVal)` to
    `loopN2CallCallCallSourceFinalPostNoX1` over `divCode_noNop_v4 base`.

    Runtime branch conditions are bundled in `loopN2CallCallCallSourceConds`. -/
theorem divK_loop_n2_call_call_call_from_source_exact_loopIterScratch_v4_noNop
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hconds :
      loopN2CallCallCallSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig1 u0Orig0) :
    cpsTripleWithin (224 + 224 + 224) (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2CallCallCallSourceFinalPostNoX1 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem) := by
  rw [loopN2CallCallCallSourceConds_unfold] at hconds
  simp only [r2CCCN2V4_eq, r1CCCN2V4_eq] at hconds
  obtain ⟨hbltu_2, hcarry2_nz_2, hbltu_1, hcarry2_nz_1, hbltu_0, hcarry2_nz_0⟩ := hconds
  -- j=2,j=1 composed source theorem (raw iterWithDoubleAddback shape).
  have JCC := divK_loop_n2_call_call_from_source_exact_loopIterScratch_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem
    halign hbltu_2 hcarry2_nz_2 hbltu_1 hcarry2_nz_1
  -- j=0 call body theorem at the j=1 iteration result (raw shape).
  have J0 := divK_loop_body_n2_call_j0_exact_loopIterScratch_v4_noNop sp base
    (1 : Word) ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3
      (divKTrialCallV4QHat
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
      v0 v1 v2 v3 u0Orig1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1)
    (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).1
    (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    v0 v1 v2 v3 u0Orig0
    (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
    (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
    (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
    (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    q0Old raVal
    (base + div128CallRetOff) v1
    (divKTrialCallV4DLo v1)
    (divKTrialCallV4Un0
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1)
    (divKTrialCallV4ScratchOut
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1
      (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem))
    halign hbltu_0 hcarry2_nz_0
  -- Frame the j=0 body with the j=1 and j=2 stored u4/q atoms.
  have J0f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
      (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
      (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).1)) **
     (((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)))
    (by pcFree) J0
  -- Compose via the j=1 -> j=0 call bridge that retains the j=2 frame.
  have hcomp := cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN2CallScratchNoX1_j1_to_call_j0_pre_with_j2_frame
      sp base
      (divKTrialCallV4QHat
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
      (divKTrialCallV4DLo v1)
      (divKTrialCallV4Un0
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1)
      (divKTrialCallV4ScratchOut
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1
        (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem))
      v0 v1 v2 v3 u0Orig1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      u0Orig0 q0Old raVal
      (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat)
      (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat)
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    JCC J0f
  have hsteps : (224 + 224) + 224 = 224 + 224 + 224 := by decide
  rw [hsteps] at hcomp
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hcomp
  intro h hp
  rw [loopN2CallCallCallSourceFinalPostNoX1_unfold]
  simp only [r2CCCN2V4_eq, r1CCCN2V4_eq] at hp ⊢
  xperm_hyp hp

end EvmAsm.Evm64
