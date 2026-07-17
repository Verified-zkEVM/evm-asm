/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix16

  PASS 11 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The **walk-next cursor-pinning bridge** — the `rlp_walk_next` analogue of
  `teer_walkinit_group_pin` (module 13).

  Each `rlp_walk_next` dispatch group's fall-through post (module 10) carries the
  callee success predicate `rlpWalkNextOk cursor endc srcBytes srcOff`, which
  unfolds to the EXISTENTIAL

      ∃ next len, (x10 ↦ next) ** (x11 ↦ 0) ** (x12 ↦ len) **
                    ⌜rlpItemDecode srcBytes srcOff cursor endc next len⌝

  The downstream MV-shuffle glue reads a single CONCRETE advanced cursor in
  `x10`, so before the join the existential `next` must collapse to one forward
  cursor `C`.

  `teer_walknext_group_pin` performs exactly this collapse: under the PER-WALK
  concrete-RLP hypothesis `hc : ∀ next len, rlpItemDecode … next len → next = C`
  (the forward-cursor fact that a later concrete-RLP pass discharges — here
  supplied as a theorem arg, so the whole prefix stays CONDITIONAL), it strips
  the `⌜rlpItemDecode⌝` conjunct, rewrites `x10 ↦ next → x10 ↦ C`, and drops the
  now-irrelevant `next` binder, leaving the concrete-cursor fall post

      (x1 ↦ midPC) ** (F ** ∃ len, (x10 ↦ C) ** (x11 ↦ 0) ** (x12 ↦ len))

  The reported content length `len` is retained (the recipient-capture /
  value-nonzero blocks consume `x12 = len` as a free parameter, so the residual
  `∃ len` is absorbed downstream via `cpsBranchWithin_exists_pre`).  The frame
  `F` (walk-callee scratch `regOwn` + the single physical `bytesRegion`) and the
  far-epilogue `teerFail` taken exit are carried through unchanged.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix15

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## The walk-next cursor-pinning bridge -/

set_option maxRecDepth 8000 in
/-- **Walk-next cursor-pinning.**  Collapses a walk-next dispatch group's
    fall post `rlpWalkNextOk cursor endc srcBytes srcOff` (i.e.
    `∃ next len, x10 ↦ next ** x11 ↦ 0 ** x12 ↦ len ** ⌜rlpItemDecode …⌝`) to the
    concrete-cursor form `∃ len, x10 ↦ C ** x11 ↦ 0 ** x12 ↦ len`, given the
    per-walk concrete-RLP fact `hc : ∀ next len, rlpItemDecode … → next = C`.
    The frame `F` and the `teerFail` taken exit are carried through unchanged. -/
theorem teer_walknext_group_pin
    (nSteps : Nat) (callPC fallPC midPC C endc cursor : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (P F : Assertion)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff cursor endc next len → next = C)
    (hgrp : cpsBranchWithin nSteps callPC fullCode P
      (teerB + 2856) teerFail
      fallPC
      ((.x1 ↦ᵣ midPC) **
        (F ** EvmAsm.Rv64.RLP.rlpWalkNextOk cursor endc srcBytes srcOff))) :
    cpsBranchWithin nSteps callPC fullCode P
      (teerB + 2856) teerFail
      fallPC
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ midPC) **
          (F ** ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) := by
  refine cpsBranchWithin_weaken (fun _ hp => hp) (fun _ hq => hq) (fun h hq => ?_) hgrp
  obtain ⟨s1, s2, hd, hu, hx1, hrest⟩ := hq
  obtain ⟨s3, s4, hd2, hu2, hF, hok⟩ := hrest
  obtain ⟨next, len, hbody⟩ := hok
  have hdec : EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff cursor endc next len :=
    sepConj_extract_pure_end3 s4 hbody
  have hstrip := sepConj_strip_pure_end3 s4 hbody
  rw [hc next len hdec] at hstrip
  exact ⟨len, s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hF, hstrip⟩

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
