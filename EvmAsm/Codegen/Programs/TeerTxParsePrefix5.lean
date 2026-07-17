/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix5

  PASS 3 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  Begins COMPOSING the tx-parse prefix call groups + BNEs into a single
  `cpsBranchWithin` chain (mirroring `teer_prologue_spec`), toward the eventual
  `teer_txparse_prefix_spec` reaching the per-auth loop head (`teerB + 724`).

  This module lands the first `call ;; BNE` join — the `tx_type_dispatch`
  dispatch (instrs 34..41), which is the CLEANEST such join because
  `tx_type_dispatch`'s contract publishes a single (non-disjunctive) result:
  the status `(teerTxTypeDispatch txBytes).1` into `a0`.  The post-call
  `bne a0, 0` routes a parse failure (status ≠ 0) to the far epilogue
  `teerB + 2856` and the success (status = 0) to the type==4 check `teerB + 168`.

  The join recipe (reused by every later group): frame the status `BNE` with
  the call group's remaining footprint (`REST`) via `cpsBranchWithin_frameR`,
  then `cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr` with an `xperm_hyp`
  midpoint permutation (which strips the callee's lambda-wrapped result post).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix4

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-- The `tx_type_dispatch` call group's footprint OUTSIDE the dispatch-status
    `BNE` — everything the `bne a0, 0` at instruction 41 does NOT read.  Framed
    around the guard so both exits retain the full post-call state. -/
def teerTxdRest (v8 v9 : Word) (txBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ (teerB + 164)) ** regOwn .x5 ** regOwn .x6 **
  bytesRegion v8 txBytes **
  (teerType ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
  (teerInnerOff ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
  (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9)

set_option maxRecDepth 8000 in
/-- **`tx_type_dispatch` dispatch** (instrs 34..41, `teerB + 136 →` branch).

    Chains the `tx_type_dispatch` call GROUP (`teer_txtype_group_spec`,
    `teerB + 136 → teerB + 164`) into the parse-failure `bne a0, 0`
    (`teer_txtype_bne_spec`, instr 41).  TAKEN (status ≠ 0) → far epilogue
    `teerB + 2856`; NOT-TAKEN (status = 0) → type==4 check `teerB + 168`.  Both
    exits carry the dispatch result (`teerTxdRest`) plus the decided status. -/
theorem teer_txtype_dispatch_spec (txd : TxTypeDispatchAssumed fullCode)
    (htxd : txd.entry = BitVec.ofNat 64 GuestAddrs.tx_type_dispatch)
    (v8 v9 v10o v11o v12o v13o raIn t0Old t1Old typeOld innerOld : Word)
    (txBytes : List (BitVec 8))
    (hlen : v9 = BitVec.ofNat 64 txBytes.length)
    (halign : v8.toNat % 8 = 0)
    (hover : v8.toNat + txBytes.length ≤ 2 ^ 64)
    (hvalid : ∀ k, k < txBytes.length →
      isValidByteAccess (v8 + BitVec.ofNat 64 k) = true) :
    cpsBranchWithin ((6 + (1 + nTxTypeDispatchSteps)) + 1) (teerB + 136) fullCode
      (((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10o) ** (.x11 ↦ᵣ v11o) **
        (.x12 ↦ᵣ v12o) ** (.x13 ↦ᵣ v13o)) **
       ((.x1 ↦ᵣ raIn) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion v8 txBytes ** (teerType ↦ₘ typeOld) ** (teerInnerOff ↦ₘ innerOld)))
      (teerB + 2856)
      (((.x10 ↦ᵣ (teerTxTypeDispatch txBytes).1) ** (.x0 ↦ᵣ (0 : Word)) **
         ⌜(teerTxTypeDispatch txBytes).1 ≠ (0 : Word)⌝) ** teerTxdRest v8 v9 txBytes)
      (teerB + 168)
      (((.x10 ↦ᵣ (teerTxTypeDispatch txBytes).1) ** (.x0 ↦ᵣ (0 : Word)) **
         ⌜(teerTxTypeDispatch txBytes).1 = (0 : Word)⌝) ** teerTxdRest v8 v9 txBytes) := by
  have hgroup := teer_txtype_group_spec txd htxd v8 v9 v10o v11o v12o v13o raIn
    t0Old t1Old typeOld innerOld txBytes hlen halign hover hvalid
  have hbneF := cpsBranchWithin_frameR (teerTxdRest v8 v9 txBytes)
    (by unfold teerTxdRest; pcFree)
    (teer_txtype_bne_spec (teerTxTypeDispatch txBytes).1)
  exact cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by unfold teerTxdRest; xperm_hyp hp) hgroup hbneF

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
