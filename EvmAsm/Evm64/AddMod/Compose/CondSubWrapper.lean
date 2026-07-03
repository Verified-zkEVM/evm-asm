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
import EvmAsm.Evm64.AddMod.Compose.CarryBranch

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

/-- Pass-2 with its dead-on-entry `x5/x6/x7` inputs merely `regOwn` (the
    cond-subtract's second pass reloads them immediately). This is the shape
    that joins onto `evm_addmod_cond_sub_pass1take_clean`'s shed post. Proven by
    peeling the three owned registers to generic values (the pass-2 spec is
    parametric in them) via `cpsTripleWithin_pre_regOwn(_under)`. -/
theorem evm_addmod_cond_sub_pass2_owned
    (base sp maskIn x10Old : Word)
    (s0 s1 s2 s3 n0 n1 n2 n3 : Word) :
    let mm0 := n0 &&& maskIn
    let c0 := if BitVec.ult s0 mm0 then (1 : Word) else 0
    let r0 := s0 - mm0
    let mm1 := n1 &&& maskIn
    let f1 := if BitVec.ult s1 mm1 then (1 : Word) else 0
    let e1 := s1 - mm1
    let g1 := if BitVec.ult e1 c0 then (1 : Word) else 0
    let r1 := e1 - c0
    let c1 := f1 ||| g1
    let mm2 := n2 &&& maskIn
    let f2 := if BitVec.ult s2 mm2 then (1 : Word) else 0
    let e2 := s2 - mm2
    let g2 := if BitVec.ult e2 c1 then (1 : Word) else 0
    let r2 := e2 - c1
    let c2 := f2 ||| g2
    let mm3 := n3 &&& maskIn
    let r3 := (s3 - mm3) - c2
    cpsTripleWithin 30 base (base + 120)
      (CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 (3872 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x10 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x5 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x6 .x12 (8 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x7 .x12 (3880 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 32) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 40) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 44) (.SLTU .x7 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 48) (.SUB .x6 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 52) (.OR .x10 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 56) (.SD .x12 .x6 (8 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 60) (.LD .x6 .x12 (16 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x7 .x12 (3888 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 68) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 72) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 76) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 80) (.SLTU .x7 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 84) (.SUB .x6 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 88) (.OR .x10 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 92) (.SD .x12 .x6 (16 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 96) (.LD .x6 .x12 (24 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 100) (.LD .x7 .x12 (3896 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 104) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 108) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 112) (.SUB .x6 .x6 .x10))
       (CodeReq.singleton (base + 116) (.SD .x12 .x6 (24 : BitVec 12))))))))))))))))))))))))))))))))
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ f2) ** (.x6 ↦ᵣ r3) ** (.x7 ↦ᵣ mm3) **
       (.x10 ↦ᵣ c2) ** (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) := by
  intro mm0 c0 r0 mm1 f1 e1 g1 r1 c1 mm2 f2 e2 g2 r2 c2 mm3 r3
  refine cpsTripleWithin_pre_regOwn (fun v5 => ?_)
  refine cpsTripleWithin_pre_regOwn_under (fun v6 => ?_)
  rw [← sepConj_assoc']
  refine cpsTripleWithin_pre_regOwn_under (fun v7 => ?_)
  rw [sepConj_assoc']
  have P := evm_addmod_cond_sub_pass2_spec_within base sp maskIn v5 v6 v7 x10Old
    s0 s1 s2 s3 n0 n1 n2 n3
  simp only [mm0, c0, r0, mm1, f1, e1, g1, r1, c1, mm2, f2, e2, g2, r2, c2,
    mm3, r3] at P ⊢
  exact cpsTripleWithin_weaken (fun st h => by xperm_hyp h) (fun _ h => h) P

end EvmAsm.Evm64.AddMod.Compose
