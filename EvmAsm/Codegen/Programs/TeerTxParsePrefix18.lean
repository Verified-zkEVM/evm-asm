/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix18

  PASS 11 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The **walk-boundary scratch-ownership adaptor**.

  At every walk boundary the previous `…_toglue` block returns the walk-callee
  scratch as `teerWalkScratch` (the seven `regOwn` cells `x5`/`x6`/`x7`/`x28..x31`
  plus `x0` and the single physical `bytesRegion`), but the next walk dispatch
  GROUP's precondition wants those seven scratch registers CONCRETE
  (`x5 ↦ t0Old … x31 ↦ t6Old`).  `teer_walk_scratch_regOwn_adaptor` bridges the
  gap once and for all: given a walk block that holds for EVERY concrete choice
  of the seven scratch values (which every group spec is, being universally
  quantified over `t0Old..t6Old`), it produces the variant whose precondition
  carries only `teerWalkScratch` — so the join is a pure permutation match
  (`teerWalkScratch` as a single atom) with the previous block's fall post.

  Built on `cpsBranchWithin_of_forall_regIs_to_regOwn7` (module 15): reshape the
  precondition to the trailing-`regIs` form the `∀`→`regOwn` lemma expects,
  abstract the seven scratch registers, then reshape back to `teerWalkScratch`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix17

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## The walk-boundary scratch-ownership adaptor -/

set_option maxRecDepth 8000 in
/-- **Walk-boundary scratch adaptor.**  Turns a walk block that holds for every
    concrete scratch (`x5 ↦ t0 … x31 ↦ t6`, with `x0 ↦ 0` and the physical
    `bytesRegion` trailing) into the variant whose precondition carries only the
    bundled `teerWalkScratch srcBase srcBytes`, keeping the leading `x1`/`x10`/
    `x11`/`x12` register cells and the trailing frame `REST` unchanged. -/
theorem teer_walk_scratch_regOwn_adaptor
    {nSteps : Nat} {entry exit_t exit_f : Word} {Q_t Q_f : Assertion}
    (x1v x10v x11v x12v srcBase : Word) (srcBytes : List (BitVec 8))
    (REST : Assertion)
    (h : ∀ t0 t1 t2 t3 t4 t5 t6 : Word,
      cpsBranchWithin nSteps entry fullCode
        (((.x1 ↦ᵣ x1v) **
          ((.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) ** (.x12 ↦ᵣ x12v) **
            (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) ** (.x28 ↦ᵣ t3) **
            (.x29 ↦ᵣ t4) ** (.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes)) ** REST)
        exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry fullCode
      (((.x1 ↦ᵣ x1v) **
        ((.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) ** (.x12 ↦ᵣ x12v) **
          teerWalkScratch srcBase srcBytes)) ** REST)
      exit_t Q_t exit_f Q_f := by
  -- Step 1: reshape into the trailing-regIs form `regOwn7` expects.
  have h' : ∀ v1 v2 v3 v4 v5 v6 v7 : Word,
      cpsBranchWithin nSteps entry fullCode
        ((((.x1 ↦ᵣ x1v) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) ** (.x12 ↦ᵣ x12v) **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** REST) **
          (.x5 ↦ᵣ v1) ** (.x6 ↦ᵣ v2) ** (.x7 ↦ᵣ v3) ** (.x28 ↦ᵣ v4) **
          (.x29 ↦ᵣ v5) ** (.x30 ↦ᵣ v6) ** (.x31 ↦ᵣ v7)))
        exit_t Q_t exit_f Q_f := by
    intro v1 v2 v3 v4 v5 v6 v7
    exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) (h v1 v2 v3 v4 v5 v6 v7)
  -- Step 2: abstract the seven scratch registers to `regOwn`.
  have h'' := cpsBranchWithin_of_forall_regIs_to_regOwn7 .x5 .x6 .x7 .x28 .x29 .x30 .x31 h'
  -- Step 3: fold the `regOwn` block back into `teerWalkScratch`.
  exact cpsBranchWithin_weaken
    (fun _ hp => by simp only [teerWalkScratch] at hp; xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq) h''

/-! ## First walk boundary join (`teerB + 216 → {2856, 260}`)

    Chains the proven `rlp_walk_init`@54 group+pin ;; first `to`-walk glue
    (`teer_walkinit54_toglue0_spec`, `teerB + 216 → 240`) onto the proven
    `rlp_walk_next`@60 group+pin ;; `to`-walk glue 1
    (`teer_walknext60_toglue1_spec`, `teerB + 240 → 260`), applying the scratch
    adaptor at the boundary.  The walk-0 output cursor `C0` matches the walk-1
    input cursor via the parse-success offset correspondence
    `listBase + srcOff1 = C0`. -/
set_option maxRecDepth 8000 in
theorem teer_walk01_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listOff srcOff1 : Nat)
    (halign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hoff1 : srcOff1 < listBytes.length) (hover1 : listBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff1) = true)
    (C0 C1 : Word)
    (hc1 : (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) = C0)
    (hc2 : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) = C0)
    (hoc : listBase + BitVec.ofNat 64 srcOff1 = C0)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff1
        (listBase + BitVec.ofNat 64 srcOff1) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C1) :
    cpsBranchWithin (((((1 + 81) + 1) + 4) + (((1 + 87) + 1) + 3))) (teerB + 216) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes)) **
        ((.x24 ↦ᵣ t0Old) ** (.x25 ↦ᵣ t1Old)))
      (teerB + 2856) teerFail
      (teerB + 260)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C1) ** (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
            (.x24 ↦ᵣ C1) ** (.x25 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen))) **
          ((.x1 ↦ᵣ (teerB + 244)) ** teerWalkScratch listBase listBytes **
            (.x12 ↦ᵣ len))) h) := by
  -- Block 0: walk-init@54 group+pin ;; toglue0 (216 → 240).
  have hB0 := teer_walkinit54_toglue0_spec wi hwi listBase listLen a2Old t0Old t1Old t2Old
    t3Old t4Old t5Old t6Old raIn t0Old t1Old listBytes listOff halign hoff hover hvalid
    C0 hc1 hc2
  -- Block 1: walk-next@60 group+pin ;; toglue1 (240 → 260), scratch-adapted.
  have hB1 := teer_walk_scratch_regOwn_adaptor (teerB + 220)
    (listBase + BitVec.ofNat 64 srcOff1) ((listBase + BitVec.ofNat 64 listOff) + listLen)
    (0 : Word) listBase listBytes ((.x24 ↦ᵣ C0) ** (.x25 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)))
    (fun t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext60_toglue1_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) (0 : Word)
        t0 t1 t2 t3 t4 t5 t6 (teerB + 220) C0
        ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff1
        halign hoff1 hover1 hvalid1 C1 hc)
  exact cpsBranchWithin_seq_cpsBranchWithin_with_perm_same_cr hB0
    (fun h hq => by rw [hoc]; xperm_hyp hq) hB1
    (fun h hq => to_teerFail _ h hq) (fun h hq => to_teerFail _ h hq)

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
