/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix15

  PASS 11 of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The **count segment** (`teerB + 676 → {2856, 724}`): chains the count-segment
  head join (`teer_count_to_countload_spec`, module 14, `teerB + 676 → 704`)
  onto the proven authorization-list `rlp_walk_init`@176 loop-head reach
  (`teer_walkinit176_loophead_spec`, module 13, `teerB + 704 → {2856, 724}`),
  producing the full count-segment branch to the per-auth loop head.

  The join threads the count-success existential `∃ cnt, countModel = some cnt`
  (with the loaded counter `x23 = cnt` and the out-cell `teer_auth_count = cnt`)
  as a frame around the loop-head reach, and exposes the seven owned scratch
  registers (`x6`/`x7`/`x28..x31` — the walk callee's `t1..t6` — and `x12` — the
  parse-shape status arg) the count group returns, so the `rlp_walk_init`@176
  CALL can consume them.  The list ptr/len captured by the count-load block
  (`x10 = x21 = listBase + listOff`, `x11 = x22 = llLen`) feeds the walk-init
  directly.  The not-taken exit establishes the initial loop state
  `x21 = list cursor C`, `x22 = list end`, `x24 = 0` — the register core of the
  per-auth loop head — with the counter `x23 = cnt`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix14

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## Bulk owned-register precondition exposure -/

/-- Expose seven trailing owned registers in a branch precondition: if a branch
    spec holds for every concrete value of `r1..r7`, its precondition may carry
    only ownership of those registers.  (The 7-register analogue of
    `cpsTripleWithin_of_forall_regIs_to_regOwn2`.) -/
theorem cpsBranchWithin_of_forall_regIs_to_regOwn7
    {nSteps : Nat} {entry : Word} {cr : CodeReq} {P : Assertion}
    {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (r1 r2 r3 r4 r5 r6 r7 : Reg)
    (h : ∀ v1 v2 v3 v4 v5 v6 v7, cpsBranchWithin nSteps entry cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5) **
        (r6 ↦ᵣ v6) ** (r7 ↦ᵣ v7)) exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5 **
        regOwn r6 ** regOwn r7) exit_t Q_t exit_f Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, k1, k2, kd, ku, hPregs, hR2⟩ := hPR
  obtain ⟨m1, m2, md, mu, hP, hr1⟩ := hPregs
  obtain ⟨a1, a2, ad, au, ⟨v1, hv1⟩, hr2⟩ := hr1
  obtain ⟨b1, b2, bd, bu, ⟨v2, hv2⟩, hr3⟩ := hr2
  obtain ⟨c1, c2, cd, cu, ⟨v3, hv3⟩, hr4⟩ := hr3
  obtain ⟨d1, d2, dd, du, ⟨v4, hv4⟩, hr5⟩ := hr4
  obtain ⟨e1, e2, ed, eu, ⟨v5, hv5⟩, hr6⟩ := hr5
  obtain ⟨f1, f2, fd, fu, ⟨v6, hv6⟩, ⟨v7, hv7⟩⟩ := hr6
  exact h v1 v2 v3 v4 v5 v6 v7 R hR s hcr
    ⟨hp, hcompat, k1, k2, kd, ku,
      ⟨m1, m2, md, mu, hP,
        a1, a2, ad, au, hv1, b1, b2, bd, bu, hv2, c1, c2, cd, cu, hv3,
        d1, d2, dd, du, hv4, e1, e2, ed, eu, hv5, f1, f2, fd, fu, hv6, hv7⟩,
      hR2⟩ hpc

/-! ## The count segment -/

/-- The count-segment forward post at the per-auth loop head (`teerB + 724`):
    the loop-head-reach register core (`x21 = cursor C`, `x22 = list end`,
    `x24 = 0`, `x1 = teerB + 708`, scratch owned, `x12 = 0`) carrying the
    count-success existential with the loaded counter `x23 = cnt` and out-cell
    `teer_auth_count = cnt`. -/
def teerCountSegPost (rc : RlpListCountItemsAssumed fullCode)
    (listBase C llLen : Word) (listBytes : List (BitVec 8))
    (listLen listOff : Nat) : Assertion :=
  fun h => ∃ cnt,
    (⌜rc.countModel listBytes listLen = some cnt⌝ **
      ((((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + llLen)) **
          (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + llLen)) **
          (.x24 ↦ᵣ (0 : Word))) **
        ((.x1 ↦ᵣ (teerB + 708)) **
         ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes) **
          (.x12 ↦ᵣ (0 : Word))))) **
       ((.x23 ↦ᵣ cnt) ** (teerAuthCount ↦ₘ cnt)))) h

/-- The count-segment head-join forward post (`= teer_count_to_countload_spec`'s
    exit at `teerB + 704`), written with `v21 := listBase + listOff`,
    `v22 := llLen`. -/
def teerCountloadPost (rc : RlpListCountItemsAssumed fullCode)
    (listBase v24o llLen : Word) (listBytes : List (BitVec 8))
    (listLen listOff : Nat) : Assertion :=
  fun h => ∃ cnt,
    (⌜rc.countModel listBytes listLen = some cnt⌝ **
      (((.x1 ↦ᵣ (teerB + 680)) ** (.x5 ↦ᵣ teerAuthCount) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ llLen) **
        (.x21 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x22 ↦ᵣ llLen) ** (.x23 ↦ᵣ cnt) **
        (.x24 ↦ᵣ v24o) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase listBytes ** (teerAuthCount ↦ₘ cnt)))) h

set_option maxRecDepth 8000 in
/-- **Count segment** (`teerB + 676 → {2856, 724}`).  Chains the count-segment
    head join (module 14) onto the authorization-list `rlp_walk_init`@176
    loop-head reach (module 13). -/
theorem teer_count_segment_spec
    (rc : RlpListCountItemsAssumed fullCode)
    (hrc : rc.entry = BitVec.ofNat 64 GuestAddrs.rlp_list_count_items)
    (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (listBase outOld t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v24o llLen C : Word)
    (listBytes : List (BitVec 8)) (listLen listOff : Nat)
    (halign : listBase.toNat % 8 = 0)
    (hbound : listLen ≤ listBytes.length)
    (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < listBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hc1 : (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) = C)
    (hc2 : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) = C) :
    cpsBranchWithin ((((1 + nRlpListCountItemsSteps) + 1) + 5) + (((1 + 81) + 1) + 3))
      (teerB + 676) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) ** (.x12 ↦ᵣ teerAuthCount) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes ** (teerAuthCount ↦ₘ outOld))) **
       ((.x21 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x22 ↦ᵣ llLen) **
         (.x23 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ v24o)))
      (teerB + 2856) teerFail
      (teerB + 724)
      (teerCountSegPost rc listBase C llLen listBytes listLen listOff) := by
  have hover_lh : listBase.toNat + listOff < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_of_lt hoff) _) hover
  have hvalid_lh : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true :=
    hvalid listOff hoff
  -- The head join (module 14) at v21 := listBase+listOff, v22 := llLen, v23o := 0.
  have h14 := teer_count_to_countload_spec rc hrc listBase outOld t0Old t1Old t2Old
    t3Old t4Old t5Old t6Old raIn (listBase + BitVec.ofNat 64 listOff) llLen (0 : Word) v24o
    listBytes listLen halign hbound hover hvalid
  -- The loop-head reach (module 13), framed with the count existential + counter.
  have h2 : cpsBranchWithin (((1 + 81) + 1) + 3) (teerB + 704) fullCode
      (teerCountloadPost rc listBase v24o llLen listBytes listLen listOff)
      (teerB + 2856) teerFail
      (teerB + 724)
      (teerCountSegPost rc listBase C llLen listBytes listLen listOff) := by
    apply cpsBranchWithin_exists_pre; intro cnt
    apply cpsBranchWithin_pure_pre; intro hcnt
    have hro : cpsBranchWithin (((1 + 81) + 1) + 3) (teerB + 704) fullCode
        (((.x1 ↦ᵣ (teerB + 680)) ** (.x5 ↦ᵣ teerAuthCount) **
          (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ llLen) **
          (.x21 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x22 ↦ᵣ llLen) ** (.x23 ↦ᵣ cnt) **
          (.x24 ↦ᵣ v24o) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes **
          (teerAuthCount ↦ₘ cnt)) **
         regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** regOwn .x12)
        (teerB + 2856) teerFail
        (teerB + 724)
        (teerCountSegPost rc listBase C llLen listBytes listLen listOff) := by
      apply cpsBranchWithin_of_forall_regIs_to_regOwn7 .x6 .x7 .x28 .x29 .x30 .x31 .x12
      intro t1 t2 t3 t4 t5 t6 a2
      have hfr := cpsBranchWithin_frameR ((.x23 ↦ᵣ cnt) ** (teerAuthCount ↦ₘ cnt))
        (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
        (teer_walkinit176_loophead_spec wi hwi listBase llLen a2 teerAuthCount t1 t2 t3 t4 t5 t6
          (teerB + 680) listBytes listOff halign hoff hover_lh hvalid_lh C
          (listBase + BitVec.ofNat 64 listOff) llLen v24o hc1 hc2)
      refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hq => to_teerFail _ h hq) (fun h hq => ?_) hfr
      exact ⟨cnt, (sepConj_pure_left h).2 ⟨hcnt, by xperm_hyp hq⟩⟩
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq) hro
    -- pre: teerCountloadPost's per-cnt body (regOwns in middle) → hro pre (regOwns tail).
    xperm_hyp hp
  refine cpsBranchWithin_seq_cpsBranchWithin_with_perm_same_cr h14 (fun h hq => ?_) h2
    (fun h hq => to_teerFail _ h hq) (fun h hq => to_teerFail _ h hq)
  -- module-14 post = teerCountloadPost (identity, up to `def` unfolding).
  exact hq

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
