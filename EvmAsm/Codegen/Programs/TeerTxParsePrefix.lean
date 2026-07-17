/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix

  PASS 3 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  Composes the tx-parse prefix call sites over `fullCode` from the assumed
  callee contracts (`TeerBodyAssumptions`).  Each call group is
  `[arg setup] ;; [jal callee, lifted via callWithin_spec against the assumed
  contract] ;; [post-call BNE dispatch]`.  Because the assumed contracts are
  stated over the SHARED `cr` (here instantiated to `fullCode`), the callee
  triple drops in with NO `_mono` lift — only the teer body's own straight-line
  blocks and the `jal` instruction are lifted (`teer_mono`).

  This module lands the FIRST call group — the `tx_type_dispatch` dispatch
  (instrs 34..41): the body-entry argument shuffle, the `jal`, and the
  parse-failure `BNE`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerBodyAssumptions

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## First call group: `tx_type_dispatch` (instructions 34..41)

    The body-entry shuffle (`teer_body_entry_spec`, instrs 34..39) sets
    `a0 = txPtr`, `a1 = txLen`, `a2 = &teer_type`, `a3 = &teer_inner_off`; the
    `jal tx_type_dispatch` at instruction 40 (`teerB + 160`) runs the callee;
    the `bne a0, 0` at instruction 41 (`teerB + 164`) exits to the far
    epilogue on a parse failure. -/

/-- The linked `jal` offset to `tx_type_dispatch` from the call site
    `teerB + 160`. -/
abbrev txdJalOff : BitVec 21 :=
  jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_eip7702_existing_authority_refund + 160)

set_option maxRecDepth 8000 in
/-- **The `tx_type_dispatch` call** (instr 40, `teerB + 160 → teerB + 164`).

    Lifts the assumed `TxTypeDispatchAssumed` contract through the `jal` via
    `callWithin_spec`: the incumbent `ra` (`raIn`) is clobbered with the
    return PC `teerB + 164`, and the dispatch result (`teerTxTypeDispatch`) is
    published into `a0` and the two out cells. -/
theorem teer_txtype_call_spec (txd : TxTypeDispatchAssumed fullCode)
    (htxd : txd.entry = BitVec.ofNat 64 GuestAddrs.tx_type_dispatch)
    (v8 v9 raIn t0Old t1Old typeOld innerOld : Word) (txBytes : List (BitVec 8))
    (hlen : v9 = BitVec.ofNat 64 txBytes.length)
    (halign : v8.toNat % 8 = 0)
    (hover : v8.toNat + txBytes.length ≤ 2 ^ 64)
    (hvalid : ∀ k, k < txBytes.length →
      isValidByteAccess (v8 + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + nTxTypeDispatchSteps) (teerB + 160) (teerB + 164) fullCode
      ((.x1 ↦ᵣ raIn) ** ((.x10 ↦ᵣ v8) ** (.x11 ↦ᵣ v9) **
        (.x12 ↦ᵣ teerType) ** (.x13 ↦ᵣ teerInnerOff) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion v8 txBytes ** (teerType ↦ₘ typeOld) ** (teerInnerOff ↦ₘ innerOld)))
      ((.x1 ↦ᵣ (teerB + 164)) ** ((regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion v8 txBytes) **
       (fun h =>
         ((.x10 ↦ᵣ (teerTxTypeDispatch txBytes).1) **
           (teerType ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
           (teerInnerOff ↦ₘ (teerTxTypeDispatch txBytes).2.2)) h))) := by
  have hflat := txd.flat (teerB + 164) v8 v9 teerType teerInnerOff t0Old t1Old
    typeOld innerOld txBytes (by decide) hlen halign hover hvalid
  have hcallee : cpsTripleWithin nTxTypeDispatchSteps txd.entry (teerB + 164) fullCode
      ((.x1 ↦ᵣ (teerB + 164)) ** ((.x10 ↦ᵣ v8) ** (.x11 ↦ᵣ v9) **
        (.x12 ↦ᵣ teerType) ** (.x13 ↦ᵣ teerInnerOff) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion v8 txBytes ** (teerType ↦ₘ typeOld) ** (teerInnerOff ↦ₘ innerOld)))
      ((.x1 ↦ᵣ (teerB + 164)) ** ((regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion v8 txBytes) **
       (fun h =>
         ((.x10 ↦ᵣ (teerTxTypeDispatch txBytes).1) **
           (teerType ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
           (teerInnerOff ↦ₘ (teerTxTypeDispatch txBytes).2.2)) h))) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by xperm_hyp hq) hflat
  have htarget : (teerB + 160) + signExtend21 txdJalOff = txd.entry := by
    rw [htxd]; decide
  have hmem : ∀ a i, CodeReq.singleton (teerB + 160) (.JAL .x1 txdJalOff) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 160) teerProg 40 (.JAL .x1 txdJalOff)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hP : Assertion.pcFree ((.x10 ↦ᵣ v8) ** (.x11 ↦ᵣ v9) **
      (.x12 ↦ᵣ teerType) ** (.x13 ↦ᵣ teerInnerOff) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion v8 txBytes ** (teerType ↦ₘ typeOld) ** (teerInnerOff ↦ₘ innerOld)) := by
    repeat' first
      | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
      | apply pcFree_sepConj
  have hcall := callWithin_spec (teerB + 160) txd.entry raIn txdJalOff
    nTxTypeDispatchSteps htarget hmem hP hcallee
  rw [show (teerB + 160) + 4 = teerB + 164 from by bv_omega] at hcall
  exact hcall

/-! ## First call GROUP: arg-setup ;; call (instructions 34..40)

    Chains `teer_body_entry_spec` (the `a0..a3` shuffle, lifted to `fullCode`
    via `teer_mono`) into `teer_txtype_call_spec`.  Straight line
    `teerB + 136 → teerB + 164`; the parse-failure `BNE` at instruction 41
    follows.  The body-entry-only registers `x8`/`x9` (saved tx ptr/len) frame
    the call; the call-only footprint (`ra`, `t0`/`t1`, tx bytes, the two out
    cells) frames the shuffle. -/
set_option maxRecDepth 8000 in
theorem teer_txtype_group_spec (txd : TxTypeDispatchAssumed fullCode)
    (htxd : txd.entry = BitVec.ofNat 64 GuestAddrs.tx_type_dispatch)
    (v8 v9 v10o v11o v12o v13o raIn t0Old t1Old typeOld innerOld : Word)
    (txBytes : List (BitVec 8))
    (hlen : v9 = BitVec.ofNat 64 txBytes.length)
    (halign : v8.toNat % 8 = 0)
    (hover : v8.toNat + txBytes.length ≤ 2 ^ 64)
    (hvalid : ∀ k, k < txBytes.length →
      isValidByteAccess (v8 + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 + (1 + nTxTypeDispatchSteps)) (teerB + 136) (teerB + 164) fullCode
      (((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10o) ** (.x11 ↦ᵣ v11o) **
        (.x12 ↦ᵣ v12o) ** (.x13 ↦ᵣ v13o)) **
       ((.x1 ↦ᵣ raIn) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion v8 txBytes ** (teerType ↦ₘ typeOld) ** (teerInnerOff ↦ₘ innerOld)))
      (((.x1 ↦ᵣ (teerB + 164)) ** ((regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion v8 txBytes) **
       (fun h =>
         ((.x10 ↦ᵣ (teerTxTypeDispatch txBytes).1) **
           (teerType ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
           (teerInnerOff ↦ₘ (teerTxTypeDispatch txBytes).2.2)) h))) **
        ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9))) := by
  have hbody := cpsTripleWithin_extend_code teer_mono
    (teer_body_entry_spec v8 v9 v10o v11o v12o v13o)
  have hbodyF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion v8 txBytes ** (teerType ↦ₘ typeOld) ** (teerInnerOff ↦ₘ innerOld))
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hbody
  have hcallF := cpsTripleWithin_frameR ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_txtype_call_spec txd htxd v8 v9 raIn t0Old t1Old typeOld innerOld txBytes
      hlen halign hover hvalid)
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hbodyF hcallF

/-! ## Post-call parse-failure dispatch (instruction 41)

    `bne a0, zero` at `teerB + 164`.  TAKEN (dispatch status `sv ≠ 0`, a parse
    failure) branches to the far epilogue at `teerB + 2856` (the rolled-back
    return path); NOT-TAKEN (`sv = 0`, success) falls through to `teerB + 168`,
    the type==4 check.  This is the "error exit → far epilogue teerB+2856"
    dispatch that ends the first call group. -/
set_option maxRecDepth 8000 in
theorem teer_txtype_bne_spec (sv : Word) :
    cpsBranchWithin 1 (teerB + 164) fullCode
      ((.x10 ↦ᵣ sv) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x10 ↦ᵣ sv) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜sv ≠ (0 : Word)⌝)
      (teerB + 168) ((.x10 ↦ᵣ sv) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜sv = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x10 .x0 (2692 : BitVec 13) sv (0 : Word) (teerB + 164)
  rw [show (teerB + 164) + signExtend13 (2692 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2692 : BitVec 13) = (2692 : Word) from by decide]; bv_omega,
      show (teerB + 164) + 4 = teerB + 168 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 164) teerProg 41
    (.BNE .x10 .x0 (2692 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
