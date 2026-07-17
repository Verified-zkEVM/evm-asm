/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix7

  PASS 6 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  Extends the front `cpsBranchWithin` chain past the per-auth-loop-blocking
  footing fix (assumed-callee posts now leave the arg regs `x11/x12/x13` OWNED,
  so the inner-payload cursor setup can consume them).  This module lands the
  FIRST forward join beyond `teerB + 188`:

    * `teer_cursor_setup_spec'` — the inner-payload cursor/len setup
      (`teer_cursor_setup_spec`, instrs 47..53) restated with the callee-
      clobbered `x11` exposed as `regOwn` (its inbound value is dead: instr 53
      overwrites it with `a1 = x22`), via `cpsTripleWithin_of_forall_regIs_to_regOwn`;
    * `teer_prefix_to_cursor_spec` — chains the proven front branch
      (`teer_prefix_dispatch_type4_spec`, `teerB + 136 → {2856, 188}`) into the
      cursor setup (`teerB + 188 → 216`) via
      `cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr`, producing a single
      parse-failure-routing branch `teerB + 136 → {far epilogue 2856, walk_init
      entry 216}`.

  **Frame union** (hard piece 1): the cursor setup needs the callee-saved
  `x21`/`x22` (the inner-payload cursor/end registers), which the dispatch /
  type==4 front does NOT touch; they are carried from `teerB + 136` in an
  ambient frame `((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o))`, threaded through the front
  branch by `cpsBranchWithin_frameR` and reconciled at the join by `xperm_hyp`.
  The dispatch-result footprint the cursor setup does not read (`x7`, the
  `teer_type` cell, the two decided-status pures, `x0`, `ra`, the now-owned
  `x12`/`x13`, the tx bytes) frames the cursor setup as `teerCursorRest`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix6

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000 in
/-- **Inner-payload cursor/len setup** (instrs 47..53, `teerB + 188 → 216`) with
    the callee-clobbered `x11` exposed as `regOwn`.  Instruction 53
    (`mv a1, x22`) overwrites `x11`, so its inbound value is irrelevant; this
    restatement lets the dispatch contract's now-owned `x11` feed the setup
    directly.  Derived from `teer_cursor_setup_spec` by
    `cpsTripleWithin_of_forall_regIs_to_regOwn`. -/
theorem teer_cursor_setup_spec' (v8 v9 v5 v6 v10o v21o v22o ioff : Word) :
    cpsTripleWithin 7 (teerB + 188) (teerB + 216) teerCode
      (((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x10 ↦ᵣ v10o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) **
        (teerInnerOff ↦ₘ ioff)) ** regOwn .x11)
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ teerInnerOff) ** (.x6 ↦ᵣ ioff) **
        (.x10 ↦ᵣ (v8 + ioff)) ** (.x11 ↦ᵣ (v9 - ioff)) **
        (.x21 ↦ᵣ (v8 + ioff)) ** (.x22 ↦ᵣ (v9 - ioff)) **
        (teerInnerOff ↦ₘ ioff)) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v11o
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (teer_cursor_setup_spec v8 v9 v5 v6 v10o v11o v21o v22o ioff)

/-- The dispatch-result footprint the cursor setup does NOT read: `x7 = 4`, the
    `teer_type` cell, the two decided-status pures, `x0`, `ra`, the now-owned
    `x12`/`x13`, and the tx bytes.  Framed around the cursor setup so the join
    carries the full post-dispatch state to `teerB + 216`. -/
def teerCursorRest (v8 : Word) (txBytes : List (BitVec 8)) : Assertion :=
  (.x7 ↦ᵣ (4 : Word)) ** (teerType ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
  ⌜(teerTxTypeDispatch txBytes).2.1 = (4 : Word)⌝ ** (.x0 ↦ᵣ (0 : Word)) **
  ⌜(teerTxTypeDispatch txBytes).1 = (0 : Word)⌝ ** (.x1 ↦ᵣ (teerB + 164)) **
  regOwn .x12 ** regOwn .x13 ** bytesRegion v8 txBytes

set_option maxRecDepth 8000 in
/-- **Front join to cursor setup** (`teerB + 136 → {2856, 216}`).

    Chains the proven front branch (`teer_prefix_dispatch_type4_spec`,
    `teerB + 136 → {2856, 188}`) into the inner-payload cursor setup
    (`teer_cursor_setup_spec'`, `teerB + 188 → 216`, lifted to `fullCode`).  The
    ntaken exit at `teerB + 216` holds the established cursor (`x21 = x10 =
    txPtr + inner_off`, `x22 = x11 = txLen - inner_off`), ready for the
    `jal rlp_walk_init` at instruction 54.  The taken (parse-failure) exit
    collapses to `teerFail`. -/
theorem teer_prefix_to_cursor_spec (txd : TxTypeDispatchAssumed fullCode)
    (htxd : txd.entry = BitVec.ofNat 64 GuestAddrs.tx_type_dispatch)
    (v8 v9 v10o v11o v12o v13o raIn t0Old t1Old typeOld innerOld v7 v21o v22o : Word)
    (txBytes : List (BitVec 8))
    (hlen : v9 = BitVec.ofNat 64 txBytes.length)
    (halign : v8.toNat % 8 = 0)
    (hover : v8.toNat + txBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < txBytes.length →
      isValidByteAccess (v8 + BitVec.ofNat 64 k) = true) :
    cpsBranchWithin ((((6 + (1 + nTxTypeDispatchSteps)) + 1) + 5) + 7) (teerB + 136) fullCode
      (((((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10o) ** (.x11 ↦ᵣ v11o) **
        (.x12 ↦ᵣ v12o) ** (.x13 ↦ᵣ v13o)) **
       ((.x1 ↦ᵣ raIn) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion v8 txBytes ** (teerType ↦ₘ typeOld) ** (teerInnerOff ↦ₘ innerOld))) **
       (.x7 ↦ᵣ v7)) **
       ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o)))
      (teerB + 2856) teerFail
      (teerB + 216)
      (((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ teerInnerOff) **
          (.x6 ↦ᵣ (teerTxTypeDispatch txBytes).2.2) **
          (.x10 ↦ᵣ (v8 + (teerTxTypeDispatch txBytes).2.2)) **
          (.x11 ↦ᵣ (v9 - (teerTxTypeDispatch txBytes).2.2)) **
          (.x21 ↦ᵣ (v8 + (teerTxTypeDispatch txBytes).2.2)) **
          (.x22 ↦ᵣ (v9 - (teerTxTypeDispatch txBytes).2.2)) **
          (teerInnerOff ↦ₘ (teerTxTypeDispatch txBytes).2.2)) **
        teerCursorRest v8 txBytes) := by
  have hfront := teer_prefix_dispatch_type4_spec txd htxd v8 v9 v10o v11o v12o v13o raIn
    t0Old t1Old typeOld innerOld v7 txBytes hlen halign hover hvalid
  have hfrontF := cpsBranchWithin_frameR ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o))
    (by pcFree) hfront
  have hcur := cpsTripleWithin_extend_code teer_mono
    (teer_cursor_setup_spec' v8 v9 teerType (teerTxTypeDispatch txBytes).2.1
      (teerTxTypeDispatch txBytes).1 v21o v22o (teerTxTypeDispatch txBytes).2.2)
  have hcurF := cpsTripleWithin_frameR (teerCursorRest v8 txBytes)
    (by unfold teerCursorRest; repeat' first
        | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _ | exact pcFree_pure | apply pcFree_sepConj) hcur
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    hfrontF
    (fun h hp => by unfold teerType4Rest teerCursorRest at *; xperm_hyp hp)
    hcurF
    (fun h hq => to_teerFail _ h hq)

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
