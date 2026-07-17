/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix14

  PASS 10 of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The **count-segment head join**: sequences the `rlp_list_count_items`@169
  dispatch group (`teer_count169_group_spec`, module 12, `teerB + 676 →
  {2856, 684}`) into the count-load / list re-init straight-line block
  (`teer_countload_setup_spec`, module 2, `teerB + 684 → 704`, lifted to
  `fullCode`), producing the branch `teerB + 676 → {far epilogue 2856, 704}`.

  The count group's fall post carries the count-success existential
  `∃ cnt, countModel = some cnt ∧ (a0 = 0, teer_auth_count := cnt)` plus the
  walk-callee scratch `regOwn` block and the physical `bytesRegion`.  The frame
  registers the count call does not name — the list ptr/len `x21`/`x22`
  (captured by `teer_authlist_setup_spec`), the loop counter `x23`, and the
  index register `x24` — are threaded around the group with
  `cpsBranchWithin_frameR`.

  The join eliminates the `∃ cnt` (`cpsTripleWithin_exists_pre_gen`), discharges
  the `countModel = some cnt` pure conjunct (`cpsTripleWithin_pure_pre`), and
  exposes the two owned scratch registers `x5`/`x11` the count group returns
  (`cpsTripleWithin_of_forall_regIs_to_regOwn2`) so `teer_countload_setup_spec`
  can consume them.  The count-out cell `outPtr` is instantiated to the prefix
  out-cell `teer_auth_count`.  The forward post keeps the count existential:
  `∃ cnt, countModel = some cnt ∧ (x23 = cnt, x10 = x11 = list ptr/len, …)` —
  the count-load state one step before the authorization-list `rlp_walk_init`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix13

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000 in
/-- **Count-segment head join** (`teerB + 676 → {2856, 704}`).  Chains the
    `rlp_list_count_items`@169 dispatch group into the count-load / list re-init
    block, threading the list ptr/len (`x21`/`x22`), the counter `x23`, and the
    index `x24` as a frame.  The forward exit carries the count-success
    existential with the counter loaded into `x23` and the list ptr/len staged
    into `a0`/`a1` for the authorization-list `rlp_walk_init`@176. -/
theorem teer_count_to_countload_spec (rc : RlpListCountItemsAssumed fullCode)
    (hrc : rc.entry = BitVec.ofNat 64 GuestAddrs.rlp_list_count_items)
    (listBase outOld t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21 v22 v23o v24o : Word)
    (listBytes : List (BitVec 8)) (listLen : Nat)
    (halign : listBase.toNat % 8 = 0)
    (hbound : listLen ≤ listBytes.length)
    (hover : listBase.toNat + listBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < listBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsBranchWithin (((1 + nRlpListCountItemsSteps) + 1) + 5) (teerB + 676) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) ** (.x12 ↦ᵣ teerAuthCount) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes ** (teerAuthCount ↦ₘ outOld))) **
       ((.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23o) ** (.x24 ↦ᵣ v24o)))
      (teerB + 2856) teerFail
      (teerB + 704)
      (fun h => ∃ cnt,
        (⌜rc.countModel listBytes listLen = some cnt⌝ **
          (((.x1 ↦ᵣ (teerB + 680)) ** (.x5 ↦ᵣ teerAuthCount) ** (.x10 ↦ᵣ v21) **
            (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ cnt) **
            (.x24 ↦ᵣ v24o) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes ** (teerAuthCount ↦ₘ cnt)))) h) := by
  -- Frame the list ptr/len, counter, and index around the count group.
  have h1 := cpsBranchWithin_frameR
    ((.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23o) ** (.x24 ↦ᵣ v24o))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_count169_group_spec rc hrc listBase teerAuthCount outOld t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn listBytes listLen halign hbound hover hvalid)
  -- The count-load block, per count value, exposing the two owned scratch regs.
  have h2 : cpsTripleWithin 5 (teerB + 684) (teerB + 704) fullCode
      (fun h => ∃ cnt,
        (⌜rc.countModel listBytes listLen = some cnt⌝ **
          (((.x1 ↦ᵣ (teerB + 680)) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23o) **
            (.x24 ↦ᵣ v24o) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes ** (.x10 ↦ᵣ (0 : Word)) ** (teerAuthCount ↦ₘ cnt)) **
           regOwn .x5 ** regOwn .x11)) h)
      (fun h => ∃ cnt,
        (⌜rc.countModel listBytes listLen = some cnt⌝ **
          (((.x1 ↦ᵣ (teerB + 680)) ** (.x5 ↦ᵣ teerAuthCount) ** (.x10 ↦ᵣ v21) **
            (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ cnt) **
            (.x24 ↦ᵣ v24o) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes ** (teerAuthCount ↦ₘ cnt)))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro cnt
    apply cpsTripleWithin_pure_pre
    intro hcnt
    apply cpsTripleWithin_of_forall_regIs_to_regOwn2
    intro v5o v11o
    have hcl := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 680)) ** (.x24 ↦ᵣ v24o) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x12 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes)
      (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact bytesRegion_pcFree _ _
          | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono
        (teer_countload_setup_spec v21 v22 v5o v23o (0 : Word) v11o cnt))
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hcl
    exact ⟨cnt, (sepConj_pure_left h).2 ⟨hcnt, by xperm_hyp hq⟩⟩
  refine cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr h1 (fun h hq => ?_) h2
    (fun h hq => to_teerFail _ h hq)
  -- Reconcile the framed count-group fall post with the count-load pre.
  obtain ⟨hq1, hq2, hqd, hqu, hQ684, hF1⟩ := hq
  obtain ⟨ha1, ha2, had, hau, hx1, hBC⟩ := hQ684
  obtain ⟨hb1, hb2, hbd, hbu, hFrame, hEx⟩ := hBC
  obtain ⟨cnt, hcnt, hx10⟩ := hEx
  refine ⟨cnt, (sepConj_pure_left h).2 ⟨hcnt, ?_⟩⟩
  have inner1 :
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase listBytes) **
       ((.x10 ↦ᵣ (0 : Word)) ** (teerAuthCount ↦ₘ cnt)))) ha2 :=
    ⟨hb1, hb2, hbd, hbu, hFrame, hx10⟩
  have inner2 :
      (((.x1 ↦ᵣ (teerB + 680)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         ((.x10 ↦ᵣ (0 : Word)) ** (teerAuthCount ↦ₘ cnt))))) hq1 :=
    ⟨ha1, ha2, had, hau, hx1, inner1⟩
  have hstart :
      ((((.x1 ↦ᵣ (teerB + 680)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         ((.x10 ↦ᵣ (0 : Word)) ** (teerAuthCount ↦ₘ cnt)))) **
       ((.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23o) ** (.x24 ↦ᵣ v24o)))) h :=
    ⟨hq1, hq2, hqd, hqu, inner2, hF1⟩
  xperm_hyp hstart

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
