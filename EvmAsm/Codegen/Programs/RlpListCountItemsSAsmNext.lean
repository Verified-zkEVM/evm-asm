import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmLoop

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

def nextCommon (listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  (.x1 ↦ᵣ (B + 60)) ** bytesRegion listBase bytes

def nextOutcome (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off : Nat) : Assertion := fun h =>
  rlpWalkNextOk (listBase + BitVec.ofNat 64 off) endPtr bytes off h ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (2 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 off) endPtr = true⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (3 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode bytes off
      (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (4 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode bytes off
      (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (5 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode bytes off
      (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (6 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode bytes off
      (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h)

/-- The wrapper's `mv a1,s2` followed by its embedded strict-next call. -/
theorem nextCallBlock (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off listLen : Nat) (v5 v6 v7 v11 v12 v28 v29 v30 v31 oldRa : Word)
    (F : Assertion) (h_F : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_off : off ≤ listLen) :
    cpsTripleWithin 89 (B + 52) (B + 60) code
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** (.x18 ↦ᵣ endPtr) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ oldRa) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** F)
      ((nextCommon listBase bytes ** nextOutcome listBase endPtr bytes off) **
       ((.x18 ↦ᵣ endPtr) ** F)) := by
  have h_offb : off < bytes.length := by omega
  have hmv0 := mv_spec_gen_within .x11 .x18 endPtr v11 (B + 52) (by decide)
  rw [show B + 52 + 4 = B + 56 from by bv_omega] at hmv0
  have hmv := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub B (B + 52) rlpListCountItems_prog
      [.MV .x11 .x18] 13 (by bv_omega) rfl
      (by rw [total_length]; norm_num) (by rw [total_length]; norm_num)) hmv0
  have hwn := rlp_walk_next_spec_within WN listBase endPtr (B + 60) v12
    v5 v6 v7 v28 v29 v30 v31 bytes off h_align h_offb (by omega)
    (h_valid off h_offb)
    (fun _ _ => ⟨by omega, by omega, h_valid _ (by omega)⟩)
    (fun hb8 hc0 => by
      have h_lo : ((bytes[off]'h_offb).zeroExtend 64 - (0xb7 : Word)).toNat ≤ 8 := by
        simp only [BitVec.ult, decide_eq_true_eq] at hb8 hc0
        bv_omega
      exact ⟨by omega, by omega, fun k hk => h_valid _ (by omega)⟩)
    (fun hf8 => by
      have h_lo : ((bytes[off]'h_offb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        simp only [BitVec.ult, decide_eq_true_eq] at hf8
        have h3 := (bytes[off]'h_offb).isLt
        bv_omega
      exact ⟨by omega, by omega, fun k hk => h_valid _ (by omega)⟩)
  have hwn' := cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) hwn
    (P' := (.x1 ↦ᵣ (B + 60)) **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes))
  have hcall := callWalkNext (n := 87) oldRa (by pcf) hwn'
  have hmvF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x12 ↦ᵣ v12) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
     (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ oldRa) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** F) (by pcf; exact h_F) hmv
  have hcallF := cpsTripleWithin_frameR ((.x18 ↦ᵣ endPtr) ** F)
    (by pcf; exact h_F) hcall
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hmvF hcallF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by unfold nextCommon nextOutcome; exact hp) hc

#print axioms nextCallBlock

end EvmAsm.Codegen.RlpListCountItemsSAsm
