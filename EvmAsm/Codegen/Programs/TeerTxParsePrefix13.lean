/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix13

  PASS 9 of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The **walk-init cursor-pinning bridge** — the piece that lets each
  `rlp_walk_init` dispatch group (module 11) feed the next straight-line block
  deterministically.

  Each walk-init group's fall-through post carries the TWO-arm success
  disjunction

      (x10 = cur1, x11 = endc, x12 = 0) ∨ (x10 = cur2, x11 = endc, x12 = 0)

  where `cur1`/`cur2` are the SHORT- / LONG-list content cursors (differing only
  in `x10`; `x11`/`x12` are pinned in both arms).  The downstream glue block
  reads a single concrete cursor in `x10`, so before the join the disjunction
  must collapse to one forward cursor `C`.

  `teer_walkinit_group_pin` performs exactly this collapse: under the PER-WALK
  concrete-RLP hypotheses `cur1 = C` and `cur2 = C` (the forward-cursor facts
  that a later concrete-RLP pass discharges — here supplied as theorem args, so
  the whole prefix stays CONDITIONAL), it rewrites both arms to the shared `C`
  and folds the `A ∨ A` disjunction back to `A`.  The frame (the walk-callee
  scratch `regOwn` block and the single physical `bytesRegion` — for these walks
  `listBase = v8`, so it is already `bytesRegion v8 txBytes`) passes through
  unchanged, and the far-epilogue `teerFail` taken exit is untouched.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix12

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## The walk-init cursor-pinning bridge -/

set_option maxRecDepth 8000 in
/-- **Walk-init cursor-pinning.**  Collapses a walk-init dispatch group's
    two-arm fall post `(x10 = cur1 ∨ x10 = cur2)` (short/long RLP list, shared
    `x11 = endc`, `x12 = 0`) to a single forward cursor `x10 = C`, given the
    per-walk concrete-RLP facts `cur1 = C` and `cur2 = C`.  The frame `F`
    (walk-callee scratch `regOwn` + the single physical `bytesRegion`) and the
    `teerFail` taken exit are carried through unchanged. -/
theorem teer_walkinit_group_pin
    (nSteps : Nat) (callPC fallPC midPC C endc cur1 cur2 : Word)
    (P F : Assertion)
    (hc1 : cur1 = C) (hc2 : cur2 = C)
    (hgrp : cpsBranchWithin nSteps callPC fullCode P
      (teerB + 2856) teerFail
      fallPC
      ((.x1 ↦ᵣ midPC) **
        (F **
         (fun h =>
           (((.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h))))) :
    cpsBranchWithin nSteps callPC fullCode P
      (teerB + 2856) teerFail
      fallPC
      ((.x1 ↦ᵣ midPC) **
        (F **
         ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))))) := by
  refine cpsBranchWithin_weaken (fun _ hp => hp) (fun _ hq => hq) (fun h hq => ?_) hgrp
  simp only [hc1, hc2] at hq
  exact sepConj_mono_right
    (sepConj_mono_right (fun _ hd => Or.elim hd id id)) h hq

/-! ## Pin application: loop-head reach from the `rlp_walk_init`@176 CALL

    Composes the authorization-list `rlp_walk_init` dispatch group
    (`teer_walkinit176_group_spec`, `teerB + 704 → {2856, 712}`, carrying the
    short/long cursor disjunction) with the cursor-pinning bridge and the
    per-auth loop counter/cursor init (`teer_loop_init_spec`, `teerB + 712 →
    724`, lifted to `fullCode`), producing the loop-head-reaching branch
    `teerB + 704 → {far epilogue 2856, loop head 724}`.

    This is the strictly-earlier-starting analogue of `teer_loophead_reach_spec`
    (module 8, `teerB + 708 → 724`): here the walk-init CALL itself is inside the
    composed segment, and the pin collapses the group's two-arm success post to
    the single forward list cursor `C` (under the per-walk facts `hc1`/`hc2`)
    before it feeds `teer_loop_init_spec`.  The not-taken exit establishes the
    initial loop state `x21 = list cursor C`, `x22 = list end`, `x24 = i = 0`
    (the register core of `LoopInv 0` at the per-auth loop head); the walk-init
    parse-shape failure collapses to the shared `teerFail`. -/
set_option maxRecDepth 8000 in
theorem teer_walkinit176_loophead_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat)
    (halign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (C v21o v22o v24o : Word)
    (hc1 : (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) = C)
    (hc2 : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) = C) :
    cpsBranchWithin (((1 + 81) + 1) + 3) (teerB + 704) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes)) **
       ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) ** (.x24 ↦ᵣ v24o)))
      (teerB + 2856) teerFail
      (teerB + 724)
      (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
          (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
          (.x24 ↦ᵣ (0 : Word))) **
        ((.x1 ↦ᵣ (teerB + 708)) **
         ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes) **
          (.x12 ↦ᵣ (0 : Word))))) := by
  -- The pinned walk-init group: two-arm success collapses to the single cursor C.
  have hpin := teer_walkinit_group_pin ((1 + 81) + 1) (teerB + 704) (teerB + 712)
    (teerB + 708) C ((listBase + BitVec.ofNat 64 listOff) + listLen)
    ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))
    ((listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)))
    _
    ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes))
    hc1 hc2
    (teer_walkinit176_group_spec wi hwi listBase listLen a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn listBytes listOff halign hoff hover hvalid)
  -- Frame the loop-register triple around the (pinned) group.
  have h1 := cpsBranchWithin_frameR
    ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) ** (.x24 ↦ᵣ v24o))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    hpin
  -- Frame the group remainder (ra, scratch, bytesRegion, x12) around loop_init.
  have h2 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (teerB + 708)) **
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase listBytes) **
       (.x12 ↦ᵣ (0 : Word))))
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_regOwn | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj)
    (cpsTripleWithin_extend_code teer_mono (teer_loop_init_spec C
      ((listBase + BitVec.ofNat 64 listOff) + listLen) v21o v22o v24o))
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1
    (fun h hq => by xperm_hyp hq)
    h2
    (fun h hq => to_teerFail _ h hq)

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

