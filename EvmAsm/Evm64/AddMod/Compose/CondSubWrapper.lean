/-
  EvmAsm.Evm64.AddMod.Compose.CondSubWrapper

  Phase-3 M3c for total ADDMOD (issue #9704): the whole-block machine spec
  for the 55-instruction `evm_addmod_carry_cond_sub` conditional subtract,
  composing `evm_addmod_cond_sub_pass1take_spec_within` (25 instr) with
  `evm_addmod_cond_sub_pass2_spec_within` (30 instr).

  Two techniques keep the composition inside the 200k heartbeat budget
  (the M2 deferral was the naive 55-instruction `runBlock`, which needs
  >500k):

  * **Opaque mask parameter.** Pass-1's output `maskE` is a deep borrow-chain
    expression; substituting it into pass-2's 30 result cells is what blows
    the budget. So `mask` is a real theorem PARAMETER carrying
    `hmask : mask = maskE`, and the pass-2 spec runs at the opaque `mask` —
    the deep `maskE` appears only once (in `hmask`), never nested 30×.
  * **Shed the dead intermediate registers.** Pass-1's `x5/x6/x7` outputs
    (`t3/d3/u3` — deep) are immediately overwritten by pass-2, so
    `evm_addmod_cond_sub_pass1take_clean` weakens them to `regOwn` before the
    join. The intermediate assertion is then shallow (only `x10`/`x11`/`x12`
    concrete), so `runBlock` reconciles it cheaply.
-/

import EvmAsm.Evm64.AddMod.Compose.CallAdapter

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64
open EvmAsm.Evm64

/-- Pass-1 ;; take with the dead `x5/x6/x7` outputs shed to `regOwn` and the
    mask folded to the opaque parameter `mask`. This is the shallow-intermediate
    feed for the whole-block composition. -/
theorem evm_addmod_cond_sub_pass1take_clean
    (base sp carry x6Old x7Old x10Old x11Old : Word)
    (s0 s1 s2 s3 n0 n1 n2 n3 mask : Word)
    (hmask : mask = (0 : Word) -
      ((carry + signExtend12 (0 : BitVec 12)) |||
       (((if BitVec.ult s3 n3 then (1 : Word) else 0) |||
          (if BitVec.ult (s3 - n3)
            ((if BitVec.ult s2 n2 then (1 : Word) else 0) |||
             (if BitVec.ult (s2 - n2)
               ((if BitVec.ult s1 n1 then (1 : Word) else 0) |||
                (if BitVec.ult (s1 - n1)
                  (if BitVec.ult s0 n0 then (1 : Word) else 0)
                  then (1 : Word) else 0))
               then (1 : Word) else 0))
            then (1 : Word) else 0))
         ^^^ signExtend12 (1 : BitVec 12)))) :
    cpsTripleWithin 25 base (base + 100)
      (CodeReq.union (CodeReq.singleton base (.ADDI .x10 .x5 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x7 .x12 (3872 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x11 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x6 .x12 (8 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x12 (3880 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 24) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SLTU .x7 .x6 .x11))
      (CodeReq.union (CodeReq.singleton (base + 36) (.OR .x11 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x6 .x12 (16 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 44) (.LD .x7 .x12 (3888 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 48) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 52) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 56) (.SLTU .x7 .x6 .x11))
      (CodeReq.union (CodeReq.singleton (base + 60) (.OR .x11 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x6 .x12 (24 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 68) (.LD .x7 .x12 (3896 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 72) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 76) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 80) (.SLTU .x7 .x6 .x11))
      (CodeReq.union (CodeReq.singleton (base + 84) (.OR .x11 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 88) (.XORI .x11 .x11 (1 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 92) (.OR .x11 .x10 .x11))
       (CodeReq.singleton (base + 96) (.SUB .x11 .x0 .x11))))))))))))))))))))))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ carry) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x10 ↦ᵣ (carry + signExtend12 (0 : BitVec 12))) ** (.x11 ↦ᵣ mask) **
       (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) := by
  have P1 := evm_addmod_cond_sub_pass1take_spec_within base sp carry x6Old x7Old
    x10Old x11Old s0 s1 s2 s3 n0 n1 n2 n3
  refine cpsTripleWithin_weaken (fun _ h => h) ?_ P1
  intro st hp
  simp only [← hmask] at hp
  exact sepConj_mono (fun _ h => h)
    (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6)
        (sepConj_mono (regIs_implies_regOwn .x7) (fun _ h => h)))) st hp

end EvmAsm.Evm64.AddMod.Compose
