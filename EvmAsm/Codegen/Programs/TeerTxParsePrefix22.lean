/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix22

  PASS 11 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The **`value` walk + `value ≠ 0` flag join** (`teerB + 388 → {2856, 412}`).
  Chains the past-`to` `rlp_walk_next`@97 dispatch group + cursor pin (the
  `value` field walk) onto the `value ≠ 0` straight-line block
  (`teer_value_nonzero_spec`, module 2, `teerB + 396 → 412`), which records
  `teer_value_nonzero = (value content length > 0)`.

  As with the recipient-capture join (module 21) this is a "new-shape" boundary:
  the `value ≠ 0` block consumes two of the walk-callee scratch registers
  concretely — `x5` (the `la` temporary) and `x30` (the `sltu` target) — so the
  join unbundles `teerWalkScratch` (`cpsTripleWithin_of_forall_regIs_to_regOwn2`)
  and frames the `teer_value_nonzero` `.bss` cell (peeled off `teerPrefixExtra`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix21

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## `rlp_walk_next`@97 (`value`) dispatch group + cursor pin (`teerB + 388 → {2856, 396}`) -/

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@97 group + pin (`teerB + 388 → {2856, 396}`).  The past-`to`
    (`value`) walk; mirrors `teer_walknext85_pin_spec`. -/
theorem teer_walknext97_pin_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 388) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 396)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 392)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 388) (teerB + 396) (teerB + 392)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext97_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

/-! ## The `value` walk ;; `value ≠ 0` flag join (`teerB + 388 → {2856, 412}`) -/

set_option maxRecDepth 8000 in
/-- **`value` walk group+pin ;; `value ≠ 0` flag** (`teerB + 388 → {2856, 412}`).
    Composes the pinned `rlp_walk_next`@97 group with the `value ≠ 0` block,
    unbundling `teerWalkScratch` for the two scratch registers the block
    consumes (`x5`/`x30`) and framing the `teer_value_nonzero` `.bss` cell. -/
theorem teer_walknext97_value_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (vno : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 4) (teerB + 388) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        (teerValueNonzero ↦ₘ vno))
      (teerB + 2856) teerFail
      (teerB + 412)
      (fun h => ∃ len : Word,
        (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            (.x30 ↦ᵣ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
            (.x5 ↦ᵣ teerValueNonzero)) **
          ((.x1 ↦ᵣ (teerB + 392)) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
            bytesRegion srcBase srcBytes) **
          (teerValueNonzero ↦ₘ (if BitVec.ult (0 : Word) len then (1 : Word) else 0))) h) := by
  -- Block 1: the pinned walk-97 group, framed with the value cell.
  have h1 := cpsBranchWithin_frameR (teerValueNonzero ↦ₘ vno)
    (by exact pcFree_memIs)
    (teer_walknext97_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  -- Block 2: value-nonzero, unbundling `teerWalkScratch` for `x5`/`x30`.
  have h2 : cpsTripleWithin 4 (teerB + 396) (teerB + 412) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 392)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          (teerValueNonzero ↦ₘ vno)) h)
      (fun h => ∃ len : Word,
        (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            (.x30 ↦ᵣ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
            (.x5 ↦ᵣ teerValueNonzero)) **
          ((.x1 ↦ᵣ (teerB + 392)) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
            bytesRegion srcBase srcBytes) **
          (teerValueNonzero ↦ₘ (if BitVec.ult (0 : Word) len then (1 : Word) else 0))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have hval : cpsTripleWithin 4 (teerB + 396) (teerB + 412) fullCode
        ((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (teerValueNonzero ↦ₘ vno)) **
          ((.x1 ↦ᵣ (teerB + 392)) ** (.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
            bytesRegion srcBase srcBytes)) **
          regOwn .x30 ** regOwn .x5)
        (fun h =>
          (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
              (.x30 ↦ᵣ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
              (.x5 ↦ᵣ teerValueNonzero)) **
            ((.x1 ↦ᵣ (teerB + 392)) **
              regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
              bytesRegion srcBase srcBytes) **
            (teerValueNonzero ↦ₘ (if BitVec.ult (0 : Word) len then (1 : Word) else 0))) h) := by
      apply cpsTripleWithin_of_forall_regIs_to_regOwn2
      intro v30o v5o
      exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
        (cpsTripleWithin_frameR
          ((.x1 ↦ᵣ (teerB + 392)) ** (.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
            bytesRegion srcBase srcBytes)
          (by repeat' first
              | exact pcFree_regIs | exact pcFree_regOwn | exact bytesRegion_pcFree _ _
              | apply pcFree_sepConj)
          (cpsTripleWithin_extend_code teer_mono
            (teer_value_nonzero_spec len v30o v5o vno)))
    exact cpsTripleWithin_weaken
      (fun h hp => by simp only [teerWalkScratch] at hp; xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩)
      hval
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
