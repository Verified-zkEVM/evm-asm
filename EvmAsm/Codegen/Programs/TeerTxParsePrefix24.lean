/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix24

  PASS 11 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The auth-list-walk `walknextNN ;; alglueK` pinned-group compositions (sites
  116/121/…/156, the x21/x22 analogue of the `to`-walk `walknext ;; toglue`
  blocks in module 19) and the final `walknext161 ;; authlist_setup` boundary
  (`teerB + 644 → {2856, 676}`).

  The `authlist_setup` block touches no walk-callee scratch, so its join is a
  clean frame-through: it stages the authorization-list content ptr/len
  (`x21 = a0 - a2`, `x22 = a2`) and materialises `&teer_auth_count` into `a2`
  for the `rlp_list_count_items` call at `teerB + 676`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix23

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## `walknextNN ;; alglueK` compositions (sites 116/…/156) -/

set_option maxRecDepth 8000 in
theorem teer_walknext116_alglue1_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 464) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22)))
      (teerB + 2856) teerFail (teerB + 484)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 468)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext116_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 472) (teerB + 484) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 468)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 468)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 468)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_alglue1_spec C (0 : Word) v21o v22))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

set_option maxRecDepth 8000 in
theorem teer_walknext121_alglue2_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 484) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22)))
      (teerB + 2856) teerFail (teerB + 504)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 488)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext121_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 492) (teerB + 504) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 488)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 488)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 488)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_alglue2_spec C (0 : Word) v21o v22))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

set_option maxRecDepth 8000 in
theorem teer_walknext126_alglue3_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 504) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22)))
      (teerB + 2856) teerFail (teerB + 524)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 508)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext126_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 512) (teerB + 524) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 508)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 508)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 508)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_alglue3_spec C (0 : Word) v21o v22))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

set_option maxRecDepth 8000 in
theorem teer_walknext131_alglue4_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 524) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22)))
      (teerB + 2856) teerFail (teerB + 544)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 528)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext131_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 532) (teerB + 544) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 528)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 528)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 528)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_alglue4_spec C (0 : Word) v21o v22))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

set_option maxRecDepth 8000 in
theorem teer_walknext136_alglue5_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 544) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22)))
      (teerB + 2856) teerFail (teerB + 564)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 548)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext136_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 552) (teerB + 564) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 548)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 548)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 548)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_alglue5_spec C (0 : Word) v21o v22))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

set_option maxRecDepth 8000 in
theorem teer_walknext141_alglue6_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 564) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22)))
      (teerB + 2856) teerFail (teerB + 584)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 568)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext141_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 572) (teerB + 584) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 568)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 568)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 568)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_alglue6_spec C (0 : Word) v21o v22))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

set_option maxRecDepth 8000 in
theorem teer_walknext146_alglue7_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 584) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22)))
      (teerB + 2856) teerFail (teerB + 604)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 588)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext146_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 592) (teerB + 604) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 588)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 588)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 588)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_alglue7_spec C (0 : Word) v21o v22))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

set_option maxRecDepth 8000 in
theorem teer_walknext151_alglue8_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 604) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22)))
      (teerB + 2856) teerFail (teerB + 624)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 608)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext151_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 612) (teerB + 624) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 608)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 608)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 608)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_alglue8_spec C (0 : Word) v21o v22))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

set_option maxRecDepth 8000 in
theorem teer_walknext156_alglue9_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 624) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22)))
      (teerB + 2856) teerFail (teerB + 644)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 628)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext156_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 632) (teerB + 644) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 628)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ v22)) **
          ((.x1 ↦ᵣ (teerB + 628)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 628)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_alglue9_spec C (0 : Word) v21o v22))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

/-! ## `walknext161 ;; authlist_setup` (`teerB + 644 → {2856, 676}`) -/

set_option maxRecDepth 8000 in
/-- The final auth-list-walk boundary: the pinned `rlp_walk_next`@161 group
    followed by the `authlist_setup` block, which stages the content ptr/len
    (`x21 = a0 - a2`, `x22 = a2`) and materialises `&teer_auth_count` into `a2`.
    `authlist_setup` touches no walk-callee scratch, so it frames through. -/
theorem teer_walknext161_authlist_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22o : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 6) (teerB + 644) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o)))
      (teerB + 2856) teerFail (teerB + 676)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ (C - len)) ** (.x11 ↦ᵣ len) ** (.x12 ↦ᵣ teerAuthCount) **
            (.x21 ↦ᵣ (C - len)) ** (.x22 ↦ᵣ len)) **
          ((.x1 ↦ᵣ (teerB + 648)) ** teerWalkScratch srcBase srcBytes)) h) := by
  have h1 := cpsBranchWithin_frameR ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext161_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 6 (teerB + 652) (teerB + 676) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 648)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ (C - len)) ** (.x11 ↦ᵣ len) ** (.x12 ↦ᵣ teerAuthCount) **
            (.x21 ↦ᵣ (C - len)) ** (.x22 ↦ᵣ len)) **
          ((.x1 ↦ᵣ (teerB + 648)) ** teerWalkScratch srcBase srcBytes)) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 648)) ** teerWalkScratch srcBase srcBytes)
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono
        (teer_authlist_setup_spec C (0 : Word) len v21o v22o))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
