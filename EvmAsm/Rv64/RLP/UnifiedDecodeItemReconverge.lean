/-
  EvmAsm.Rv64.RLP.UnifiedDecodeItemReconverge

  EL.3 — reconvergence of the unified single-item decoder's class exits.

  `rlp_decode_single_item_spec_within` (UnifiedDecodeItem.lean) reaches five
  different exit PCs with five different postconditions. A per-item RLP *list*
  loop needs all classes to reconverge to ONE common PC with a UNIFORM
  postcondition, so it can advance to the next item (`x13 += x11`) and iterate.

  This file does the **flat classes** (`singleByte` / `shortBytes` / `shortList`
  — no memory, no `x12`/`x14` clobber). Each class handler runs to its own exit,
  then an unconditional `JAL x0` jumps to a common `joinPC`; the uniform post
  exposes the decoded payload length (`x11`) and payload pointer (`x13`) via
  `classifyPrefix`-dispatched helpers. The long classes (memory + `x12`/`x14` +
  variable steps) are a follow-up.
-/

import EvmAsm.Rv64.RLP.UnifiedDecodeItem
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

-- ============================================================================
-- Uniform-post helpers (classifyPrefix-dispatched)
-- ============================================================================

/-- The cascade-constant residue left in `x10` per flat class. -/
def itemCascadeResidue (pfx : Byte) : Word :=
  match classifyPrefix pfx with
  | .singleByte => (0 : Word) + signExtend12 (0x80 : BitVec 12)
  | .shortBytes => (0 : Word) + signExtend12 (0xB8 : BitVec 12)
  | .shortList  => (0 : Word) + signExtend12 (0xF8 : BitVec 12)
  | _ => 0

/-- The decoded payload length left in `x11` per flat class. -/
def itemPayloadLen (pfx : Byte) : Word :=
  match classifyPrefix pfx with
  | .singleByte => 1
  | .shortBytes => BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx)
  | .shortList  => BitVec.ofNat 64 (rlpPrefixShortListPayloadLen pfx)
  | _ => 0

/-- The payload pointer left in `x13` per flat class (single byte is its own
    payload, so the pointer is unchanged; short forms advance past the prefix). -/
def itemPayloadPtr (pfx : Byte) (v13 : Word) : Word :=
  match classifyPrefix pfx with
  | .singleByte => v13
  | .shortBytes => v13 + signExtend12 (1 : BitVec 12)
  | .shortList  => v13 + signExtend12 (1 : BitVec 12)
  | _ => v13

-- ============================================================================
-- Generic reconvergence arm: handler ∘ JAL, lifted to the shared code `cr`
-- ============================================================================

/-- A class handler reaching `eC` (with uniform pre `P`, uniform post `R`),
    followed by an unconditional `JAL x0` to `joinPC`, lifted into the shared
    decoder code `cr` and to the common step bound `11`. -/
private theorem reconverge_arm
    {sC : Nat} (hsC : sC + 1 ≤ 11)
    {base eC joinPC : Word} {cr handlerCR : CodeReq} {joff : BitVec 21}
    {P R : Assertion} (hRpc : R.pcFree)
    (handler : cpsTripleWithin sC base eC handlerCR P R)
    (hjoin : eC + signExtend21 joff = joinPC)
    (hd_jal : handlerCR.Disjoint (CodeReq.singleton eC (.JAL .x0 joff)))
    (hsub : ∀ a i,
      (handlerCR.union (CodeReq.singleton eC (.JAL .x0 joff))) a = some i → cr a = some i) :
    cpsTripleWithin 11 base joinPC cr P R := by
  have jal := jal_x0_spec_gen_within joff eC
  rw [hjoin] at jal
  -- Frame `R` onto the JAL (its emp pre/post pass `R` through unchanged).
  have jalR : cpsTripleWithin 1 eC joinPC
      (CodeReq.singleton eC (.JAL .x0 joff)) R R := by
    have hf := cpsTripleWithin_frameR R hRpc jal
    rwa [sepConj_emp_left'] at hf
  have seq := cpsTripleWithin_seq hd_jal handler jalR
  have ext := cpsTripleWithin_extend_code hsub seq
  exact cpsTripleWithin_mono_nSteps hsC ext

-- ============================================================================
-- Reconverged flat single-item decode (singleByte / shortBytes / shortList)
-- ============================================================================

/-- **Reconverged flat single-item decode.** For any flat prefix (`singleByte` /
    `shortBytes` / `shortList`), the decoder runs from `base`, and an
    unconditional `JAL x0` at the class exit jumps to the common `joinPC`. The
    uniform postcondition exposes the cascade residue (`x10`), the decoded
    payload length (`x11`), and the payload pointer (`x13`) via the
    `classifyPrefix`-dispatched helpers — so a list loop can advance uniformly by
    `x13 += x11`. The shared decoder code is the parameter `cr`; each class's
    handler+JAL code is a sub-CR of it (`hsub_*`). -/
theorem rlp_decode_single_item_reconverged_flat
    (pfx : Byte) (v10 v11Old v13 : Word)
    (off1 off2 off3 off4 : BitVec 13) (joff1 joff2 joff4 : BitVec 21)
    (base e1_target e2_target e4_target joinPC : Word) (cr : CodeReq)
    (hflat : classifyPrefix pfx = .singleByte ∨ classifyPrefix pfx = .shortBytes
              ∨ classifyPrefix pfx = .shortList)
    (htarget1 : (base + 4) + signExtend13 off1 = e1_target)
    (htarget2 : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (htarget4 : (base + 24 + 4) + signExtend13 off4 = e4_target)
    (hjoin1 : (e1_target + 4) + signExtend21 joff1 = joinPC)
    (hjoin2 : (e2_target + 8) + signExtend21 joff2 = joinPC)
    (hjoin4 : (e4_target + 8) + signExtend21 joff4 = joinPC)
    (hd_e1 : (rlp_phase1_step_code 0x80 off1 base).Disjoint
              (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog))
    (hd_e2 : ((rlp_phase1_step_code 0x80 off1 base).union
                (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
              (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_e4 : (((rlp_phase1_step_code 0x80 off1 base).union
              ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                  (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
              (CodeReq.ofProg e4_target rlp_phase3_short_list_prog))
    (hd_jal1 : ((rlp_phase1_step_code 0x80 off1 base).union
                  (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog)).Disjoint
                (CodeReq.singleton (e1_target + 4) (.JAL .x0 joff1)))
    (hd_jal2 : (((rlp_phase1_step_code 0x80 off1 base).union
                  (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                  (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
                (CodeReq.singleton (e2_target + 8) (.JAL .x0 joff2)))
    (hd_jal4 : (((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                      (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
                  (CodeReq.ofProg e4_target rlp_phase3_short_list_prog)).Disjoint
                (CodeReq.singleton (e4_target + 8) (.JAL .x0 joff4)))
    (hsub_e1 : ∀ a i, (((rlp_phase1_step_code 0x80 off1 base).union
                  (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog)).union
                  (CodeReq.singleton (e1_target + 4) (.JAL .x0 joff1))) a = some i → cr a = some i)
    (hsub_e2 : ∀ a i, ((((rlp_phase1_step_code 0x80 off1 base).union
                  (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                  (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                  (CodeReq.singleton (e2_target + 8) (.JAL .x0 joff2))) a = some i → cr a = some i)
    (hsub_e4 : ∀ a i, ((((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                      (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
                  (CodeReq.ofProg e4_target rlp_phase3_short_list_prog)).union
                (CodeReq.singleton (e4_target + 8) (.JAL .x0 joff4))) a = some i → cr a = some i) :
    cpsTripleWithin 11 base joinPC cr
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
       (.x13 ↦ᵣ itemPayloadPtr pfx v13)) := by
  rcases hflat with h | h | h
  · -- singleByte: frame x13 onto the (x13-free) handler, then reconverge.
    have handler := rlp_phase1_e1_single_byte_of_class_spec_within pfx v10 v11Old off1 base
      e1_target htarget1 h hd_e1
    have handler' : cpsTripleWithin 3 base (e1_target + 4)
        ((rlp_phase1_step_code 0x80 off1 base).union
          (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
         (.x13 ↦ᵣ itemPayloadPtr pfx v13)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemCascadeResidue, itemPayloadLen, itemPayloadPtr, h]
          xperm_hyp hp)
        (cpsTripleWithin_frameR (.x13 ↦ᵣ v13) (by pcFree) handler)
    exact reconverge_arm (by omega) (by pcFree) handler' hjoin1 hd_jal1 hsub_e1
  · -- shortBytes.
    have handler := rlp_phase1_e2_full_path_payload_len_of_class_spec_within pfx v10 v11Old v13
      off1 off2 base e2_target htarget2 h hd_e2
    have handler' : cpsTripleWithin 6 base (e2_target + 8)
        (((rlp_phase1_step_code 0x80 off1 base).union
            (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
          (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
         (.x13 ↦ᵣ itemPayloadPtr pfx v13)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemCascadeResidue, itemPayloadLen, itemPayloadPtr, h]
          xperm_hyp hp) handler
    exact reconverge_arm (by omega) (by pcFree) handler' hjoin2 hd_jal2 hsub_e2
  · -- shortList.
    have handler := rlp_phase1_e4_full_path_payload_len_of_class_spec_within pfx v10 v11Old v13
      off1 off2 off3 off4 base e4_target htarget4 h hd_e4
    have handler' : cpsTripleWithin 10 base (e4_target + 8)
        (((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
              (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
          (CodeReq.ofProg e4_target rlp_phase3_short_list_prog))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
         (.x13 ↦ᵣ itemPayloadPtr pfx v13)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemCascadeResidue, itemPayloadLen, itemPayloadPtr, h]
          xperm_hyp hp) handler
    exact reconverge_arm (by omega) (by pcFree) handler' hjoin4 hd_jal4 hsub_e4

-- Sanity: the uniform-post helpers compute the spec-correct per-class values.
example : itemPayloadLen (0x00 : Byte) = (1 : Word) := by decide
example : itemPayloadLen (0x83 : Byte) = BitVec.ofNat 64 3 := by decide
example : itemCascadeResidue (0xC5 : Byte) = (0 : Word) + signExtend12 (0xF8 : BitVec 12) := by
  rw [itemCascadeResidue, show classifyPrefix (0xC5 : Byte) = .shortList from by decide]
example (v13 : Word) : itemPayloadPtr (0x00 : Byte) v13 = v13 := by
  rw [itemPayloadPtr, show classifyPrefix (0x00 : Byte) = .singleByte from by decide]
example (v13 : Word) :
    itemPayloadPtr (0x83 : Byte) v13 = v13 + signExtend12 (1 : BitVec 12) := by
  rw [itemPayloadPtr, show classifyPrefix (0x83 : Byte) = .shortBytes from by decide]

end EvmAsm.Rv64.RLP
