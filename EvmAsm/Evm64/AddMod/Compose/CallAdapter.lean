/-
  EvmAsm.Evm64.AddMod.Compose.CallAdapter

  Phase-3 M2 for total ADDMOD (issue #9704):

  * `evm_addmod_carry_cond_sub_spec_within` — the whole-block spec for the
    55-instruction branch-free conditional subtract, composing the proven
    pass-1 / take / pass-2 sub-specs (CondSubSpec.lean) with the mask
    threaded through. Raw per-limb result expressions in the post (the
    `EvmWord.modAdd` semantic bridge is M3's job).

  * `evm_addmod_v5_call_adapter` — the reusable near-call adapter: one ADDMOD
    MOD near-call (`JAL .x1 modOff ;; ADDI .x12 .x12 (−32)`) discharged by the
    proven `evm_mod_callable_v5_stack_spec_within_x9owned`, via
    `WP.cpsCallWithin` + the trailing frame-pointer restore.
-/

import EvmAsm.Evm64.AddMod.Compose.CondSubSpec
import EvmAsm.Evm64.DivMod.Compose.ModCallableV5Assembly
import EvmAsm.Rv64.CPSCall

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64
open EvmAsm.Evm64

-- ============================================================================
-- (A) cond_sub whole-block spec
-- ============================================================================

/-- Union-of-singletons `_code` handle for the 55-instruction
    `evm_addmod_carry_cond_sub` block. -/
abbrev evm_addmod_carry_cond_sub_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x10 .x5 (0 : BitVec 12)))
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
  (CodeReq.union (CodeReq.singleton (base + 96) (.SUB .x11 .x0 .x11))
  (CodeReq.union (CodeReq.singleton (base + 100) (.LD .x6 .x12 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 104) (.LD .x7 .x12 (3872 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 108) (.AND .x7 .x7 .x11))
  (CodeReq.union (CodeReq.singleton (base + 112) (.SLTU .x10 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 116) (.SUB .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 120) (.SD .x12 .x5 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 124) (.LD .x6 .x12 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 128) (.LD .x7 .x12 (3880 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 132) (.AND .x7 .x7 .x11))
  (CodeReq.union (CodeReq.singleton (base + 136) (.SLTU .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 140) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 144) (.SLTU .x7 .x6 .x10))
  (CodeReq.union (CodeReq.singleton (base + 148) (.SUB .x6 .x6 .x10))
  (CodeReq.union (CodeReq.singleton (base + 152) (.OR .x10 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 156) (.SD .x12 .x6 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 160) (.LD .x6 .x12 (16 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 164) (.LD .x7 .x12 (3888 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 168) (.AND .x7 .x7 .x11))
  (CodeReq.union (CodeReq.singleton (base + 172) (.SLTU .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 176) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 180) (.SLTU .x7 .x6 .x10))
  (CodeReq.union (CodeReq.singleton (base + 184) (.SUB .x6 .x6 .x10))
  (CodeReq.union (CodeReq.singleton (base + 188) (.OR .x10 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 192) (.SD .x12 .x6 (16 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 196) (.LD .x6 .x12 (24 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 200) (.LD .x7 .x12 (3896 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 204) (.AND .x7 .x7 .x11))
  (CodeReq.union (CodeReq.singleton (base + 208) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 212) (.SUB .x6 .x6 .x10))
  (CodeReq.singleton (base + 216) (.SD .x12 .x6 (24 : BitVec 12))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem evm_addmod_carry_cond_sub_code_eq_ofProg (base : Word) :
    evm_addmod_carry_cond_sub_code base =
      CodeReq.ofProg base evm_addmod_carry_cond_sub := by
  unfold evm_addmod_carry_cond_sub_code evm_addmod_carry_cond_sub
    LD SD ADDI SUB AND' OR' SLTU XORI single seq
  change _ = CodeReq.ofProg base
    [.ADDI .x10 .x5 0,
     .LD .x6 .x12 0,
     .LD .x7 .x12 3872,
     .SLTU .x11 .x6 .x7,
     .LD .x6 .x12 8,
     .LD .x7 .x12 3880,
     .SLTU .x5 .x6 .x7,
     .SUB .x6 .x6 .x7,
     .SLTU .x7 .x6 .x11,
     .OR .x11 .x5 .x7,
     .LD .x6 .x12 16,
     .LD .x7 .x12 3888,
     .SLTU .x5 .x6 .x7,
     .SUB .x6 .x6 .x7,
     .SLTU .x7 .x6 .x11,
     .OR .x11 .x5 .x7,
     .LD .x6 .x12 24,
     .LD .x7 .x12 3896,
     .SLTU .x5 .x6 .x7,
     .SUB .x6 .x6 .x7,
     .SLTU .x7 .x6 .x11,
     .OR .x11 .x5 .x7,
     .XORI .x11 .x11 1,
     .OR .x11 .x10 .x11,
     .SUB .x11 .x0 .x11,
     .LD .x6 .x12 0,
     .LD .x7 .x12 3872,
     .AND .x7 .x7 .x11,
     .SLTU .x10 .x6 .x7,
     .SUB .x5 .x6 .x7,
     .SD .x12 .x5 0,
     .LD .x6 .x12 8,
     .LD .x7 .x12 3880,
     .AND .x7 .x7 .x11,
     .SLTU .x5 .x6 .x7,
     .SUB .x6 .x6 .x7,
     .SLTU .x7 .x6 .x10,
     .SUB .x6 .x6 .x10,
     .OR .x10 .x5 .x7,
     .SD .x12 .x6 8,
     .LD .x6 .x12 16,
     .LD .x7 .x12 3888,
     .AND .x7 .x7 .x11,
     .SLTU .x5 .x6 .x7,
     .SUB .x6 .x6 .x7,
     .SLTU .x7 .x6 .x10,
     .SUB .x6 .x6 .x10,
     .OR .x10 .x5 .x7,
     .SD .x12 .x6 16,
     .LD .x6 .x12 24,
     .LD .x7 .x12 3896,
     .AND .x7 .x7 .x11,
     .SUB .x6 .x6 .x7,
     .SUB .x6 .x6 .x10,
     .SD .x12 .x6 24]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right, BitVec.add_assoc, BitVec.reduceAdd]
  rfl

/-- Pass-1 ;; take (25 instructions): borrow-out of `s − N`, then the mask
    `maskE = 0 − (carry ||| ¬B)`. Raw-expression post. -/
theorem evm_addmod_cond_sub_pass1take_spec_within
    (base sp carry x6Old x7Old x10Old x11Old : Word)
    (s0 s1 s2 s3 n0 n1 n2 n3 : Word) :
    let b0 := if BitVec.ult s0 n0 then (1 : Word) else 0
    let t1 := if BitVec.ult s1 n1 then (1 : Word) else 0
    let d1 := s1 - n1
    let u1 := if BitVec.ult d1 b0 then (1 : Word) else 0
    let b1 := t1 ||| u1
    let t2 := if BitVec.ult s2 n2 then (1 : Word) else 0
    let d2 := s2 - n2
    let u2 := if BitVec.ult d2 b1 then (1 : Word) else 0
    let b2 := t2 ||| u2
    let t3 := if BitVec.ult s3 n3 then (1 : Word) else 0
    let d3 := s3 - n3
    let u3 := if BitVec.ult d3 b2 then (1 : Word) else 0
    let b3 := t3 ||| u3
    let cIn := carry + signExtend12 (0 : BitVec 12)
    let maskE := (0 : Word) - (cIn ||| (b3 ^^^ signExtend12 (1 : BitVec 12)))
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
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ t3) ** (.x6 ↦ᵣ d3) ** (.x7 ↦ᵣ u3) **
       (.x10 ↦ᵣ cIn) ** (.x11 ↦ᵣ maskE) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) := by
  intro b0 t1 d1 u1 b1 t2 d2 u2 b2 t3 d3 u3 b3 cIn maskE
  have P1 := evm_addmod_cond_sub_pass1_spec_within base sp carry x6Old x7Old
    x10Old x11Old s0 s1 s2 s3 n0 n1 n2 n3
  have T := evm_addmod_cond_sub_take_spec_within (base + 88) cIn b3
  simp only [b0, t1, d1, u1, b1, t2, d2, u2, b2, t3, d3, u3, b3, cIn, maskE] at P1 T ⊢
  runBlock P1 T

-- ============================================================================
-- (B) v5 MOD-callable near-call adapter
-- ============================================================================

/-- The register/memory frame carried across one ADDMOD MOD near-call, minus
    the `.x1` return-address atom (which `cpsCallWithin` supplies). This is
    exactly `divModStackDispatchPreNoX1 F divd divr …` with `.x1` removed,
    plus the `div128` scratch cell — the callable's full working frame. -/
def addmodCallRest
    (F : Word) (divd divr : EvmWord)
    (x9In v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word) :
    Assertion :=
  (.x12 ↦ᵣ F) ** (.x9 ↦ᵣ x9In) ** (.x2 ↦ᵣ v2) **
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs F divd ** evmWordIs (F + 32) divr **
  divScratchValuesCallNoX1 F q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
  ((F + signExtend12 3936) ↦ₘ scratchMem)

theorem addmodCallRest_pcFree
    (F : Word) (divd divr : EvmWord)
    (x9In v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word) :
    (addmodCallRest F divd divr x9In v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem).pcFree := by
  unfold addmodCallRest divScratchValuesCallNoX1
  pcFree

/-- **Reusable v5 MOD-callable near-call adapter.** One ADDMOD MOD near-call
    (`JAL .x1 modOff` at `callPC`, target `evm_mod_callable_v5` at
    `callPC + signExtend21 modOff`) discharged by the proven callable spec
    `evm_mod_callable_v5_stack_spec_within_x9owned`. From `callPC` to
    `callPC + 4` (the callable returns via `cc_ret` to `x1 = callPC + 4`);
    the trailing `ADDI .x12 .x12 (−32)` frame restore is a separate block.

    Frame base `F` is the caller's MOD window: dividend `divd` at `F + 0..24`,
    divisor `divr` at `F + 32..56`, remainder `EvmWord.mod divd divr` returned
    at `F + 32..56` with `x12 = F + 32`. `x1`/`x9` are shed to owned in the
    post. `callerAlign`/`retAlign`/`hoffset`/`hdisj` are pinned by the
    surrounding dispatcher frame. -/
theorem evm_addmod_v5_call_adapter
    (callPC F calleeEntry : Word) (modOff : BitVec 21) (divd divr : EvmWord)
    (x9In vOld v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hoffset : callPC + signExtend21 modOff = calleeEntry)
    (callerAlign : (callPC + 4) &&& ~~~(1 : Word) = callPC + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj : (CodeReq.singleton callPC (.JAL .x1 modOff)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin (1 + (unifiedDivBound + 1)) callPC (callPC + 4)
      ((CodeReq.singleton callPC (.JAL .x1 modOff)).union
        (evm_mod_callable_code_v5 calleeEntry))
      ((divModStackDispatchPreNoX1 F divd divr x9In vOld v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0) **
       ((F + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableX9Owned F divd divr (callPC + 4) **
       memOwn (F + signExtend12 3936)) := by
  have hcallable :=
    EvmAsm.Evm64.evm_mod_callable_v5_stack_spec_within_x9owned
      F calleeEntry divd divr x9In (callPC + 4) v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem retAlign
  have hcallee :
      cpsTripleWithin (unifiedDivBound + 1) calleeEntry ((callPC + 4) &&& ~~~1)
        (evm_mod_callable_code_v5 calleeEntry)
        ((.x1 ↦ᵣ (callPC + 4)) **
          addmodCallRest F divd divr x9In v2 v5 v6 v7 v10 v11
            q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
            shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
        (modStackDispatchPostCallableX9Owned F divd divr (callPC + 4) **
         memOwn (F + signExtend12 3936)) :=
    cpsTripleWithin_weaken
      (fun h hp => by
        rw [divModStackDispatchPreNoX1_unfold]
        unfold addmodCallRest at hp
        xperm_hyp hp)
      (fun _ hp => hp)
      hcallable
  refine cpsTripleWithin_weaken
    (fun h hp => by
      unfold addmodCallRest
      rw [divModStackDispatchPreNoX1_unfold] at hp
      xperm_hyp hp)
    (fun _ hp => hp)
    (cpsCallWithin (vOld := vOld) modOff hoffset callerAlign
      (addmodCallRest_pcFree F divd divr x9In v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      hdisj hcallee)

end EvmAsm.Evm64.AddMod.Compose
