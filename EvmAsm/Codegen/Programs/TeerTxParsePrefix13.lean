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

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
