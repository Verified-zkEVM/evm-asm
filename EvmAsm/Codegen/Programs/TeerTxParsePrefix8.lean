/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix8

  PASS 6 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  Introduces the ambient frame `teerPrefixExtra` — the union of registers and
  `.bss` cells that the tx-parse WALK CHAIN (`teerB + 216 → 712`) touches but
  the dispatch / type==4 / cursor-setup FRONT (`teerB + 136 → 216`) does not.
  Concretely:

    * the callee-saved / scratch registers `x23..x31` (regOwn): the loop
      counter `x23`/`x24`, the capture temporaries `x25`/`x26`/`x27`, and the
      walk-callee scratch `t3..t6` (`x28..x31`) which each `rlp_walk_*` call
      consumes as `t3Old..t6Old`;
    * the four prefix `.bss` out-cells (memOwn): `teer_recipient_ptr`,
      `teer_recipient_len`, `teer_value_nonzero`, `teer_auth_count`.

  The frame is threaded from the body-entry PC `teerB + 136` by framing the
  proven front branch (`teer_prefix_to_cursor_spec`, module 7,
  `teerB + 136 → {2856 teerFail, 216}`) with `teerPrefixExtra` via
  `cpsBranchWithin_frameR`; the taken (parse-failure) exit collapses back to
  the shared `teerFail`.  The resulting `teer_prefix_to_cursor_extra_spec` is
  the entry point of the walk-chain composition: its `teerB + 216` not-taken
  exit carries BOTH the established inner-payload cursor AND the full ambient
  frame the `jal rlp_walk_init`@54 needs (notably the `t3..t6` scratch).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix7

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## The walk-chain ambient frame -/

/-- The union of registers / `.bss` cells the walk chain (`teerB + 216 → 712`)
    touches but the dispatch/type==4/cursor-setup front does not: the
    callee-saved / scratch registers `x23..x31` (owned) plus the four prefix
    `.bss` out-cells (owned).  Carried as an ambient frame from `teerB + 136`. -/
def teerPrefixExtra : Assertion :=
  regOwn .x23 ** regOwn .x24 ** regOwn .x25 ** regOwn .x26 ** regOwn .x27 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  memOwn teerRecipientPtr ** memOwn teerRecipientLen **
  memOwn teerValueNonzero ** memOwn teerAuthCount

/-- `teerPrefixExtra` is `pcFree` (a union of `regOwn`/`memOwn`). -/
theorem teerPrefixExtra_pcFree : teerPrefixExtra.pcFree := by
  unfold teerPrefixExtra
  repeat' first
    | exact pcFree_regOwn | exact pcFree_memOwn | apply pcFree_sepConj

set_option maxRecDepth 8000 in
/-- **Front join to cursor setup, with the walk-chain ambient frame**
    (`teerB + 136 → {2856, 216}`).

    Frames the proven front branch (`teer_prefix_to_cursor_spec`, module 7)
    with `teerPrefixExtra` and collapses the taken (parse-failure) exit back to
    `teerFail`.  The `teerB + 216` not-taken exit carries the established
    cursor plus the full ambient frame the `jal rlp_walk_init`@54 needs. -/
theorem teer_prefix_to_cursor_extra_spec (txd : TxTypeDispatchAssumed fullCode)
    (htxd : txd.entry = BitVec.ofNat 64 GuestAddrs.tx_type_dispatch)
    (v8 v9 v10o v11o v12o v13o raIn t0Old t1Old typeOld innerOld v7 v21o v22o : Word)
    (txBytes : List (BitVec 8))
    (hlen : v9 = BitVec.ofNat 64 txBytes.length)
    (halign : v8.toNat % 8 = 0)
    (hover : v8.toNat + txBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < txBytes.length →
      isValidByteAccess (v8 + BitVec.ofNat 64 k) = true) :
    cpsBranchWithin ((((6 + (1 + nTxTypeDispatchSteps)) + 1) + 5) + 7) (teerB + 136) fullCode
      ((((((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10o) ** (.x11 ↦ᵣ v11o) **
        (.x12 ↦ᵣ v12o) ** (.x13 ↦ᵣ v13o)) **
       ((.x1 ↦ᵣ raIn) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion v8 txBytes ** (teerType ↦ₘ typeOld) ** (teerInnerOff ↦ₘ innerOld))) **
       (.x7 ↦ᵣ v7)) **
       ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o))) ** teerPrefixExtra)
      (teerB + 2856) teerFail
      (teerB + 216)
      ((((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ teerInnerOff) **
          (.x6 ↦ᵣ (teerTxTypeDispatch txBytes).2.2) **
          (.x10 ↦ᵣ (v8 + (teerTxTypeDispatch txBytes).2.2)) **
          (.x11 ↦ᵣ (v9 - (teerTxTypeDispatch txBytes).2.2)) **
          (.x21 ↦ᵣ (v8 + (teerTxTypeDispatch txBytes).2.2)) **
          (.x22 ↦ᵣ (v9 - (teerTxTypeDispatch txBytes).2.2)) **
          (teerInnerOff ↦ₘ (teerTxTypeDispatch txBytes).2.2)) **
        teerCursorRest v8 txBytes) ** teerPrefixExtra) := by
  have hbr := cpsBranchWithin_frameR teerPrefixExtra teerPrefixExtra_pcFree
    (teer_prefix_to_cursor_spec txd htxd v8 v9 v10o v11o v12o v13o raIn
      t0Old t1Old typeOld innerOld v7 v21o v22o txBytes hlen halign hover hvalid)
  exact cpsBranchWithin_weaken (fun _ hp => hp) (fun _ _ => trivial) (fun _ hq => hq) hbr

/-! ## Loop-head reach: `rlp_walk_init`@176 dispatch ;; loop init (`teerB + 708 → 724`)

    The disjunction-free TAIL of the tx-parse prefix.  Composes the
    authorization-list `rlp_walk_init` parse-shape dispatch
    (`teer_walkinit177_bne_spec`, `teerB + 708 → {2856, 712}`) into the per-auth
    loop counter/cursor init (`teer_loop_init_spec`, `teerB + 712 → 724`, lifted
    to `fullCode`), producing the loop-head-reaching branch
    `teerB + 708 → {far epilogue 2856, loop head 724}`.  The not-taken exit
    establishes the initial loop state (`x21 = list cursor`, `x22 = list end`,
    `x24 = i = 0`) — the register core of the `LoopInv 0` / `TxParseOk` witness
    at the per-auth loop head.  The walk-init parse-shape failure (`a2 ≠ 0`)
    collapses to the shared `teerFail`. -/
set_option maxRecDepth 8000 in
theorem teer_loophead_reach_spec (v10 v11 v21o v22o v24o a2 : Word) :
    cpsBranchWithin (1 + 3) (teerB + 708) fullCode
      (((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) **
          (.x24 ↦ᵣ v24o)))
      (teerB + 2856) teerFail
      (teerB + 724)
      (((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v10) ** (.x22 ↦ᵣ v11) **
          (.x24 ↦ᵣ (0 : Word))) **
        ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a2 = (0 : Word)⌝)) := by
  have h1 := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) ** (.x24 ↦ᵣ v24o))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walkinit177_bne_spec a2)
  have h2 := cpsTripleWithin_frameR ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a2 = (0 : Word)⌝)
    (by repeat' first | exact pcFree_regIs | exact pcFree_pure | apply pcFree_sepConj)
    (cpsTripleWithin_extend_code teer_mono (teer_loop_init_spec v10 v11 v21o v22o v24o))
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1
    (fun h hq => by xperm_hyp hq)
    h2
    (fun h hq => to_teerFail _ h hq)

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
