/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainF

  Nonce-station boundary assertions for `bal_account_nonstorage_finals`.
  The station occupies slots 88--134 and returns at `B + 540`, or rejects
  at the shared body exit `B + 736`.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainC
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainC2

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- Successful nonce-station exit.  `G` is the already-materialised balance
    footprint; keeping it abstract makes preservation across nonce rejection
    explicit without duplicating `balStationPost`'s two arms. -/
def nonceStationPost (aB newSp oB : Word) (aLen fOff fSpanN : Nat)
    (n4 : Word) (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion :=
  fun h =>
    -- EMPTY arm: the prologue's zeroed nonce and code fields are unchanged.
    ((G **
      ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) **
      ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      memOwn (newSp + 64) ** memOwn (newSp + 72) **
      ((.x2 : Reg) ↦ᵣ newSp) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) **
      regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
      regOwn .x19 ** regOwn .x20 **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     ⌜FieldFinal acctBytes aB fOff fSpanN none⌝) h ∨
    -- FOUND arm: rlp_content_to_u64 returns the big-endian scalar in a0.
    (∃ vNext vLen : Word,
      let image := BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
        ((acctBytes.drop (vNext - vLen - aB).toNat).take vLen.toNat))
      ((G **
        ((oB + 40) ↦ₘ (1 : Word)) ** ((oB + 48) ↦ₘ image) **
        ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) **
        ((newSp + 48) ↦ₘ n4) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x19 ** regOwn .x20 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F) **
       ⌜FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen)) ∧
        vLen.toNat ≤ 8⌝) h)

/-- Shared-reject exit from station 2.  In particular, `G` and every out-block
    cell remain owned, so an earlier balance result cannot be forgotten. -/
def nonceStationRej (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion :=
  G ** memOwn (oB + 40) ** memOwn (oB + 48) **
  ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
  ((oB + 72) ↦ₘ (0 : Word)) **
  memOwn (newSp + 48) ** memOwn (newSp + 56) **
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  ((.x2 : Reg) ↦ᵣ newSp) **
  ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
  ((.x18 : Reg) ↦ᵣ oB) **
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x11 ** regOwn .x12 **
  regOwn .x19 ** regOwn .x20 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
  bytesRegion aB acctBytes ** F

/-- The value decode supplies every account-buffer side condition needed by
    `rlp_content_to_u64_spec_within`.  Keeping this bridge separate prevents
    the capture continuation from exposing a field-local bounds hypothesis. -/
theorem bansf_nonceCapture_callee_bounds (aB : Word) (aLen tEnd off : Nat)
    (vNext vLen : Word) (acctBytes : List (BitVec 8))
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen) (hoffle : off ≤ tEnd)
    (hdec : rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
      (aB + BitVec.ofNat 64 tEnd) vNext vLen) :
    let srcOff := (vNext - vLen - aB).toNat
    vLen.toNat < 2 ^ 64 ∧
    srcOff + vLen.toNat ≤ acctBytes.length ∧
    aB.toNat + (srcOff + vLen.toNat) ≤ 2 ^ 64 ∧
    ∀ k, k < vLen.toNat →
      isValidByteAccess (aB + BitVec.ofNat 64 (srcOff + k)) = true := by
  dsimp only
  have hover9 : aB.toNat + tEnd + 9 < 2 ^ 64 := by omega
  obtain ⟨_, _, hspan⟩ := rlpItemDecode_spanStart hdec hoffle hover9
  have hsrcLen : (vNext - vLen - aB).toNat + vLen.toNat ≤ acctBytes.length := by
    omega
  refine ⟨vLen.isLt, hsrcLen, by omega, ?_⟩
  intro k hk
  exact hvalid ((vNext - vLen - aB).toNat + k) (by omega)

#print axioms bansf_nonceCapture_callee_bounds

/-- Status-zero tail of the nonce capture (slots 131--134): fall through the
    status check, store the scalar, and set `has_nonce`. -/
theorem bansf_nonceCapture_successTail_spec (oB image : Word) :
    cpsTripleWithin 4 (B + 524) (B + 540) bansfCR
      (((.x10 : Reg) ↦ᵣ image) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x5 **
       ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x10 : Reg) ↦ᵣ image) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
       ((oB + 40) ↦ₘ (1 : Word)) ** ((oB + 48) ↦ₘ image) **
       ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  have hbne := bne_spec_gen_within .x11 .x0 (208 : BitVec 13)
    (0 : Word) (0 : Word) (B + 524)
  rw [show (B + 524) + 4 = B + 528 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 524) bansfProg 131
        (.BNE .x11 .x0 (208 : BitVec 13))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    hbne
  have hfall := cpsBranchWithin_ntakenPath hbneL
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
  have hfallF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ image) ** ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x5 **
     ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)))
    (by pcf) hfall
  have hsd48 := sd_spec_gen_within .x18 .x10 oB image (0 : Word)
    (48 : BitVec 12) (B + 528)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide,
      show (B + 528) + 4 = B + 532 from by bv_omega] at hsd48
  have hsd48L := liftCode (cr' := bansfCR) hsd48
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 528) bansfProg 132
        (.SD .x18 .x10 (48 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hli : cpsTripleWithin 1 (B + 532) (B + 536) bansfCR
      (regOwn .x5) ((.x5 : Reg) ↦ᵣ (1 : Word)) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn_single (fun vOld => ?_)
    have h := li_spec_gen_within .x5 vOld (1 : Word) (B + 532) (by decide)
    rw [show (B + 532) + 4 = B + 536 from by bv_omega] at h
    exact liftCode (cr' := bansfCR) h
      (fun a i hh => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 532) bansfProg 133 (.LI .x5 (1 : Word))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i hh))
  have hsd40 := sd_spec_gen_within .x18 .x5 oB (1 : Word) (0 : Word)
    (40 : BitVec 12) (B + 536)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide,
      show (B + 536) + 4 = B + 540 from by bv_omega] at hsd40
  have hsd40L := liftCode (cr' := bansfCR) hsd40
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 536) bansfProg 134
        (.SD .x18 .x5 (40 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hsd48F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
     ((oB + 40) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hsd48L
  have hliF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ image) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
     ((.x18 : Reg) ↦ᵣ oB) ** ((oB + 40) ↦ₘ (0 : Word)) **
     ((oB + 48) ↦ₘ image) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hli
  have hsd40F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ image) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
     ((oB + 48) ↦ₘ image) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hsd40L
  have h1 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2)
    hfallF hsd48F
  have h2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1 hliF
  have h3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h2 hsd40F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) h3

#print axioms bansf_nonceCapture_successTail_spec

/-- Nonzero-status route from the nonce parser check (slot 131) through the
    shared reject stub (slot 183). -/
theorem bansf_nonceCapture_rejectRoute_spec (st oldA0 : Word) (P : Assertion)
    (hst : st ≠ 0) (hP : P.pcFree) :
    cpsTripleWithin 2 (B + 524) (B + 736) bansfCR
      (((.x11 : Reg) ↦ᵣ st) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x10 : Reg) ↦ᵣ oldA0) ** P)
      (((.x11 : Reg) ↦ᵣ st) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x10 : Reg) ↦ᵣ (1 : Word)) ** P) := by
  have hbne := bne_spec_gen_within .x11 .x0 (208 : BitVec 13)
    st (0 : Word) (B + 524)
  rw [show (B + 524) + signExtend13 (208 : BitVec 13) = B + 732 from by
        rw [show signExtend13 (208 : BitVec 13) = (208 : Word) from by decide]
        bv_omega,
      show (B + 524) + 4 = B + 528 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 524) bansfProg 131
        (.BNE .x11 .x0 (208 : BitVec 13))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    hbne
  have hbneF := cpsBranchWithin_frameR (((.x10 : Reg) ↦ᵣ oldA0) ** P)
    (by pcf; exact hP) hbneL
  have htaken := cpsBranchWithin_takenPath hbneF
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact hst (((sepConj_pure_right _).1 h_pure).2))
  have hrej := liftCode (cr' := bansfCR)
    (bansf_rejectTail_spec B oldA0 (by decide))
    (fun a i h => CodeReq.union_mono_left a i h)
  have hrejF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ st) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** P)
    (by pcf; exact hP) hrej
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2)
    htaken hrejF
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hchain

#print axioms bansf_nonceCapture_rejectRoute_spec

/-- Exact four-way post exported by the nonce parser at slot 130. -/
@[irreducible] def nonceParserPost (aB : Word) (srcOff len : Nat)
    (acctBytes : List (BitVec 8)) : Assertion :=
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
   ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
   bytesRegion aB acctBytes) **
  (fun h =>
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (2 : Word)) **
      ⌜8 < len⌝) h ∨
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ⌜len = 0⌝) h ∨
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (3 : Word)) **
      ⌜0 < len ∧ len ≤ 8 ∧ getByteAt acctBytes srcOff = 0⌝) h ∨
    (((.x10 : Reg) ↦ᵣ BitVec.ofNat 64
        (EL.RLP.Nat.fromBytesBE ((acctBytes.drop srcOff).take len))) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ⌜0 < len ∧ len ≤ 8 ∧ getByteAt acctBytes srcOff ≠ 0⌝) h)

/-- Slots 128--130: form the value-content window and invoke the unified u64
    parser.  The result is left in its exact four-way post for the two tails. -/
theorem bansf_nonceCapture_call_spec (aB : Word) (aLen tEnd off : Nat)
    (vNext vLen vStatus v5 v6 v7 v28 vRa : Word)
    (acctBytes : List (BitVec 8)) (P : Assertion)
    (hP : P.pcFree) (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen) (hoffle : off ≤ tEnd)
    (hdec : rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
      (aB + BitVec.ofNat 64 tEnd) vNext vLen) :
    cpsTripleWithin (7 * vLen.toNat + 14) (B + 512) (B + 524) bansfCR
      (((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ vStatus) **
       ((.x12 : Reg) ↦ᵣ vLen) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** P)
      (nonceParserPost aB (vNext - vLen - aB).toNat vLen.toNat acctBytes **
       ((.x12 : Reg) ↦ᵣ vLen) ** P) := by
  obtain ⟨hlen64, hslen, hsover, hsvalid⟩ :=
    bansf_nonceCapture_callee_bounds aB aLen tEnd off vNext vLen acctBytes
      hslack hover hvalid htEnd hoffle hdec
  have hover9 : aB.toNat + tEnd + 9 < 2 ^ 64 := by omega
  obtain ⟨hrepS, _, _⟩ := rlpItemDecode_spanStart hdec hoffle hover9
  have h128 := sub_spec_gen_rd_eq_rs1_within .x10 .x12 vNext vLen
    (B + 512) (by decide)
  rw [hrepS, show (B + 512) + 4 = B + 516 from by bv_omega] at h128
  have h128L := liftCode (cr' := bansfCR) h128
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 512) bansfProg 128 (.SUB .x10 .x10 .x12)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have h129 := mv_spec_gen_within .x11 .x12 vLen vStatus
    (B + 516) (by decide)
  rw [show (B + 516) + 4 = B + 520 from by bv_omega] at h129
  have h129L := liftCode (cr' := bansfCR) h129
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 516) bansfProg 129 (.MV .x11 .x12)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have h128F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ vStatus) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
     ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** P)
    (by pcf; exact hP) h128L
  have h129F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (vNext - vLen - aB).toNat)) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
     ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** P)
    (by pcf; exact hP) h129L
  have hsetup := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h128F h129F
  have hcallee := rlp_content_to_u64_spec_within C6 aB (B + 524)
    v5 v6 v7 v28 acctBytes (vNext - vLen - aB).toNat vLen.toNat
    hlen64 hsalign hslen hsover hsvalid
  have hlenrep : vLen = BitVec.ofNat 64 vLen.toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [← hlenrep] at hcallee
  have hPrest :
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (vNext - vLen - aB).toNat)) **
       ((.x11 : Reg) ↦ᵣ vLen) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes).pcFree := by
    pcf
  have hcallee' := cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hcallee
    (P' := ((.x1 : Reg) ↦ᵣ (B + 524)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (vNext - vLen - aB).toNat)) **
       ((.x11 : Reg) ↦ᵣ vLen) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes))
  have hcall := bansf_callSite130_content_to_u64 (n := 7 * vLen.toNat + 11)
    vRa hPrest hcallee'
  have hcallF := cpsTripleWithin_frameR (((.x12 : Reg) ↦ᵣ vLen) ** P)
    (by pcf; exact hP) hcall
  have hfull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hsetup hcallF
  rw [show B + 520 + 4 = B + 524 from by bv_omega] at hfull
  rw [nonceParserPost]
  rw [show 7 * vLen.toNat + 14 = 1 + 1 + (1 + (7 * vLen.toNat + 11)) from by omega]
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hfull

#print axioms bansf_nonceCapture_call_spec

/-- The `8 < len` arm of the unified nonce parser is routed to rejection. -/
theorem bansf_nonceCapture_tooLong_spec (aB oB vLen : Word) (len : Nat)
    (acctBytes : List (BitVec 8)) (P : Assertion) (hP : P.pcFree) :
    cpsTripleWithin 2 (B + 524) (B + 736) bansfCR
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
          bytesRegion aB acctBytes) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (2 : Word)) **
         ⌜8 < len⌝)) **
        ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
        ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
      (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ (2 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
       bytesRegion aB acctBytes ** ((.x12 : Reg) ↦ᵣ vLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((oB + 40) ↦ₘ (0 : Word)) **
       ((oB + 48) ↦ₘ (0 : Word)) ** P) := by
  have hr := bansf_nonceCapture_rejectRoute_spec (2 : Word) (0 : Word)
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
     ((.x1 : Reg) ↦ᵣ (B + 524)) ** bytesRegion aB acctBytes **
     ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
     ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
    (by decide) (by pcf; exact hP)
  exact cpsTripleWithin_weaken
    (fun h hp => by
      let R : Assertion :=
        ((.x11 : Reg) ↦ᵣ (2 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
         ((.x1 : Reg) ↦ᵣ (B + 524)) ** bytesRegion aB acctBytes **
         ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
         ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
      have hp2 : (R ** ⌜8 < len⌝) h := by
        dsimp only [R]
        xperm_hyp hp
      exact ((sepConj_pure_right h).1 hp2).1)
    (fun h hq => by xperm_hyp hq) hr

#print axioms bansf_nonceCapture_tooLong_spec

/-- The empty-content success arm stores scalar zero and sets the nonce flag. -/
theorem bansf_nonceCapture_empty_spec (aB oB vLen : Word) (len : Nat)
    (acctBytes : List (BitVec 8)) (P : Assertion) (hP : P.pcFree) :
    cpsTripleWithin 4 (B + 524) (B + 540) bansfCR
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
          bytesRegion aB acctBytes) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
         ⌜len = 0⌝)) **
       ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
       ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
       bytesRegion aB acctBytes ** ((.x12 : Reg) ↦ᵣ vLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((oB + 40) ↦ₘ (1 : Word)) **
       ((oB + 48) ↦ₘ (0 : Word)) ** ⌜len = 0⌝ ** P) := by
  have ht := bansf_nonceCapture_successTail_spec oB (0 : Word)
  have htF := cpsTripleWithin_frameR
    (regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
     ((.x1 : Reg) ↦ᵣ (B + 524)) ** bytesRegion aB acctBytes **
     ((.x12 : Reg) ↦ᵣ vLen) ** ⌜len = 0⌝ ** P)
    (by pcf; exact hP) ht
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) htF

#print axioms bansf_nonceCapture_empty_spec

/-- The leading-zero noncanonical arm is routed to rejection. -/
theorem bansf_nonceCapture_noncanonical_spec (aB oB vLen : Word)
    (srcOff len : Nat) (acctBytes : List (BitVec 8))
    (P : Assertion) (hP : P.pcFree) :
    cpsTripleWithin 2 (B + 524) (B + 736) bansfCR
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
          bytesRegion aB acctBytes) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (3 : Word)) **
         ⌜0 < len ∧ len ≤ 8 ∧ getByteAt acctBytes srcOff = 0⌝)) **
       ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
       ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
      (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ (3 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
       bytesRegion aB acctBytes ** ((.x12 : Reg) ↦ᵣ vLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((oB + 40) ↦ₘ (0 : Word)) **
       ((oB + 48) ↦ₘ (0 : Word)) ** P) := by
  have hr := bansf_nonceCapture_rejectRoute_spec (3 : Word) (0 : Word)
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
     ((.x1 : Reg) ↦ᵣ (B + 524)) ** bytesRegion aB acctBytes **
     ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
     ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
    (by decide) (by pcf; exact hP)
  exact cpsTripleWithin_weaken
    (fun h hp => by
      let R : Assertion :=
        ((.x11 : Reg) ↦ᵣ (3 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
         ((.x1 : Reg) ↦ᵣ (B + 524)) ** bytesRegion aB acctBytes **
         ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
         ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
      have hp2 : (R ** ⌜0 < len ∧ len ≤ 8 ∧ getByteAt acctBytes srcOff = 0⌝) h := by
        dsimp only [R]
        xperm_hyp hp
      exact ((sepConj_pure_right h).1 hp2).1)
    (fun h hq => by xperm_hyp hq) hr

#print axioms bansf_nonceCapture_noncanonical_spec

/-- The canonical status-zero arm stores the decoded scalar and sets the flag.
    The caller supplies the static length bound from its pre-call case split. -/
theorem bansf_nonceCapture_canonical_spec (aB oB vLen image : Word)
    (srcOff len : Nat) (acctBytes : List (BitVec 8))
    (P : Assertion) (hP : P.pcFree) (hlen8 : len ≤ 8) :
    cpsTripleWithin 4 (B + 524) (B + 540) bansfCR
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
          bytesRegion aB acctBytes) **
        (((.x10 : Reg) ↦ᵣ image) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
         ⌜0 < len ∧ len ≤ 8 ∧ getByteAt acctBytes srcOff ≠ 0⌝)) **
       ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
       ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
      ((((.x10 : Reg) ↦ᵣ image) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
         ((.x5 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
         bytesRegion aB acctBytes ** ((.x12 : Reg) ↦ᵣ vLen) **
         ((.x18 : Reg) ↦ᵣ oB) ** ((oB + 40) ↦ₘ (1 : Word)) **
         ((oB + 48) ↦ₘ image) ** P) ** ⌜len ≤ 8⌝) := by
  have ht := bansf_nonceCapture_successTail_spec oB image
  have htF := cpsTripleWithin_frameR
    (regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
     ((.x1 : Reg) ↦ᵣ (B + 524)) ** bytesRegion aB acctBytes **
     ((.x12 : Reg) ↦ᵣ vLen) **
     ⌜0 < len ∧ len ≤ 8 ∧ getByteAt acctBytes srcOff ≠ 0⌝ ** P)
    (by pcf; exact hP) ht
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) htF
  let R : Assertion :=
    ((.x10 : Reg) ↦ᵣ image) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
    ((.x5 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
    bytesRegion aB acctBytes ** ((.x12 : Reg) ↦ᵣ vLen) **
    ((.x18 : Reg) ↦ᵣ oB) ** ((oB + 40) ↦ₘ (1 : Word)) **
    ((oB + 48) ↦ₘ image) ** P
  have hq2 : (R ** ⌜0 < len ∧ len ≤ 8 ∧ getByteAt acctBytes srcOff ≠ 0⌝) h := by
    dsimp only [R]
    xperm_hyp hq
  exact (sepConj_pure_right h).2 ⟨((sepConj_pure_right h).1 hq2).1, hlen8⟩

#print axioms bansf_nonceCapture_canonical_spec

def nonceCaptureRejectPost (aB oB vLen : Word)
    (acctBytes : List (BitVec 8)) (P : Assertion) : Assertion :=
  fun h =>
    ((((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ (2 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
       bytesRegion aB acctBytes ** ((.x12 : Reg) ↦ᵣ vLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((oB + 40) ↦ₘ (0 : Word)) **
       ((oB + 48) ↦ₘ (0 : Word)) ** P) h) ∨
    ((((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ (3 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
       bytesRegion aB acctBytes ** ((.x12 : Reg) ↦ᵣ vLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((oB + 40) ↦ₘ (0 : Word)) **
       ((oB + 48) ↦ₘ (0 : Word)) ** P) h)

def nonceCaptureFoundPost (aB oB vLen image : Word)
    (len : Nat) (acctBytes : List (BitVec 8)) (P : Assertion) : Assertion :=
  fun h =>
    ((((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
       bytesRegion aB acctBytes ** ((.x12 : Reg) ↦ᵣ vLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((oB + 40) ↦ₘ (1 : Word)) **
       ((oB + 48) ↦ₘ (0 : Word)) ** ⌜len = 0⌝ ** P) h) ∨
    (((((.x10 : Reg) ↦ᵣ image) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
        bytesRegion aB acctBytes ** ((.x12 : Reg) ↦ᵣ vLen) **
        ((.x18 : Reg) ↦ᵣ oB) ** ((oB + 40) ↦ₘ (1 : Word)) **
        ((oB + 48) ↦ₘ image) ** P) ** ⌜len ≤ 8⌝) h)

def nonceCaptureTooLongPre (aB oB vLen : Word) (len : Nat)
    (acctBytes : List (BitVec 8)) (P : Assertion) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
      bytesRegion aB acctBytes) **
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (2 : Word)) ** ⌜8 < len⌝)) **
  ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
  ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P

def nonceCaptureEmptyPre (aB oB vLen : Word) (len : Nat)
    (acctBytes : List (BitVec 8)) (P : Assertion) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
      bytesRegion aB acctBytes) **
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ⌜len = 0⌝)) **
  ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
  ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P

def nonceCaptureNoncanonicalPre (aB oB vLen : Word) (srcOff len : Nat)
    (acctBytes : List (BitVec 8)) (P : Assertion) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
      bytesRegion aB acctBytes) **
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (3 : Word)) **
      ⌜0 < len ∧ len ≤ 8 ∧ getByteAt acctBytes srcOff = 0⌝)) **
  ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
  ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P

def nonceCaptureCanonicalPre (aB oB vLen image : Word) (srcOff len : Nat)
    (acctBytes : List (BitVec 8)) (P : Assertion) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
      bytesRegion aB acctBytes) **
    (((.x10 : Reg) ↦ᵣ image) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ⌜0 < len ∧ len ≤ 8 ∧ getByteAt acctBytes srcOff ≠ 0⌝)) **
  ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
  ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P

/-- Four parser arms merged to the common reject/found capture exits. -/
theorem bansf_nonceCapture_dispatch_spec (aB oB vLen image : Word)
    (srcOff len : Nat) (acctBytes : List (BitVec 8))
    (P : Assertion) (hP : P.pcFree) (hlen8 : len ≤ 8) :
    cpsBranchWithin 4 (B + 524) bansfCR
      (fun h => nonceCaptureTooLongPre aB oB vLen len acctBytes P h ∨
        (nonceCaptureEmptyPre aB oB vLen len acctBytes P h ∨
          (nonceCaptureNoncanonicalPre aB oB vLen srcOff len acctBytes P h ∨
           nonceCaptureCanonicalPre aB oB vLen image srcOff len acctBytes P h)))
      (B + 736) (nonceCaptureRejectPost aB oB vLen acctBytes P)
      (B + 540) (nonceCaptureFoundPost aB oB vLen image len acctBytes P) := by
  have htl0 := bansf_nonceCapture_tooLong_spec aB oB vLen len acctBytes P hP
  have htl := cpsBranchWithin_weaken
    (P' := nonceCaptureTooLongPre aB oB vLen len acctBytes P)
    (Q_t' := nonceCaptureRejectPost aB oB vLen acctBytes P)
    (Q_f' := nonceCaptureFoundPost aB oB vLen image len acctBytes P)
    (fun _ hp => hp)
    (fun _ hq => Or.inl hq) (fun _ hq => hq)
    (cpsTripleWithin_as_cpsBranchWithin_left (B + 540)
      (nonceCaptureFoundPost aB oB vLen image len acctBytes P)
      (cpsTripleWithin_mono_nSteps (nSteps' := 4) (by omega) htl0))
  have he0 := bansf_nonceCapture_empty_spec aB oB vLen len acctBytes P hP
  have he := cpsBranchWithin_weaken
    (P' := nonceCaptureEmptyPre aB oB vLen len acctBytes P)
    (Q_t' := nonceCaptureRejectPost aB oB vLen acctBytes P)
    (Q_f' := nonceCaptureFoundPost aB oB vLen image len acctBytes P)
    (fun _ hp => hp)
    (fun _ hq => hq)
    (fun _ hq => Or.inl hq)
    (cpsTripleWithin_as_cpsBranchWithin_right (B + 736)
      (nonceCaptureRejectPost aB oB vLen acctBytes P) he0)
  have hnc0 := bansf_nonceCapture_noncanonical_spec aB oB vLen srcOff len acctBytes P hP
  have hnc := cpsBranchWithin_weaken
    (P' := nonceCaptureNoncanonicalPre aB oB vLen srcOff len acctBytes P)
    (Q_t' := nonceCaptureRejectPost aB oB vLen acctBytes P)
    (Q_f' := nonceCaptureFoundPost aB oB vLen image len acctBytes P)
    (fun _ hp => hp)
    (fun _ hq => Or.inr hq) (fun _ hq => hq)
    (cpsTripleWithin_as_cpsBranchWithin_left (B + 540)
      (nonceCaptureFoundPost aB oB vLen image len acctBytes P)
      (cpsTripleWithin_mono_nSteps (nSteps' := 4) (by omega) hnc0))
  have hc0 := bansf_nonceCapture_canonical_spec aB oB vLen image srcOff len
    acctBytes P hP hlen8
  have hc := cpsBranchWithin_weaken
    (P' := nonceCaptureCanonicalPre aB oB vLen image srcOff len acctBytes P)
    (Q_t' := nonceCaptureRejectPost aB oB vLen acctBytes P)
    (Q_f' := nonceCaptureFoundPost aB oB vLen image len acctBytes P)
    (fun _ hp => hp)
    (fun _ hq => hq)
    (fun _ hq => Or.inr hq)
    (cpsTripleWithin_as_cpsBranchWithin_right (B + 736)
      (nonceCaptureRejectPost aB oB vLen acctBytes P) hc0)
  exact cpsBranchWithin_pre_or htl
    (cpsBranchWithin_pre_or he (cpsBranchWithin_pre_or hnc hc))

#print axioms bansf_nonceCapture_dispatch_spec

/-- Distribute the station frame into the parser's four-way post for the
    nonce-capture dispatch theorem. -/
theorem nonceParserPost_to_dispatchPre (aB oB vLen image : Word)
    (srcOff len : Nat) (acctBytes : List (BitVec 8)) (P : Assertion)
    (himage : image = BitVec.ofNat 64
      (EL.RLP.Nat.fromBytesBE ((acctBytes.drop srcOff).take len))) :
    ∀ h,
      (nonceParserPost aB srcOff len acctBytes **
       ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
       ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P) h →
      (nonceCaptureTooLongPre aB oB vLen len acctBytes P h ∨
       (nonceCaptureEmptyPre aB oB vLen len acctBytes P h ∨
        (nonceCaptureNoncanonicalPre aB oB vLen srcOff len acctBytes P h ∨
         nonceCaptureCanonicalPre aB oB vLen image srcOff len acctBytes P h))) := by
  intro h hp
  let F : Assertion :=
    ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
    ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P
  have hp0 : (nonceParserPost aB srcOff len acctBytes ** F) h := by
    dsimp only [F]
    xperm_hyp hp
  obtain ⟨g1, g2, hd, hu, hnp, hF⟩ := hp0
  unfold nonceParserPost at hnp
  obtain ⟨b1, b2, hdb, hub, hbase, harms⟩ := hnp
  rcases harms with htl | he | hnc | hc
  · left
    unfold nonceCaptureTooLongPre
    exact ⟨g1, g2, hd, hu, ⟨b1, b2, hdb, hub, hbase, htl⟩, hF⟩
  · right; left
    unfold nonceCaptureEmptyPre
    exact ⟨g1, g2, hd, hu, ⟨b1, b2, hdb, hub, hbase, he⟩, hF⟩
  · right; right; left
    unfold nonceCaptureNoncanonicalPre
    exact ⟨g1, g2, hd, hu, ⟨b1, b2, hdb, hub, hbase, hnc⟩, hF⟩
  · right; right; right
    unfold nonceCaptureCanonicalPre
    rw [himage]
    exact ⟨g1, g2, hd, hu, ⟨b1, b2, hdb, hub, hbase, hc⟩, hF⟩

#print axioms nonceParserPost_to_dispatchPre

/-- Slots 128--130 on the statically too-long path, using the precise public
    per-case u64 callee contract. -/
theorem bansf_nonceCapture_tooLongCall_spec (aB oB : Word)
    (vNext vLen vStatus v5 v6 v7 v28 vRa : Word) (len : Nat)
    (acctBytes : List (BitVec 8)) (P : Assertion) (hP : P.pcFree)
    (hlen : vLen.toNat = len) (htl : 8 < len)
    (hrepS : vNext - vLen = aB + BitVec.ofNat 64 (vNext - vLen - aB).toNat) :
    cpsTripleWithin 8 (B + 512) (B + 524) bansfCR
      (((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ vStatus) **
       ((.x12 : Reg) ↦ᵣ vLen) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** ((.x18 : Reg) ↦ᵣ oB) **
       ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
      (nonceCaptureTooLongPre aB oB vLen len acctBytes P) := by
  have h128 := sub_spec_gen_rd_eq_rs1_within .x10 .x12 vNext vLen
    (B + 512) (by decide)
  rw [hrepS, show (B + 512) + 4 = B + 516 from by bv_omega] at h128
  have h128L := liftCode (cr' := bansfCR) h128
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 512) bansfProg 128 (.SUB .x10 .x10 .x12)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have h129 := mv_spec_gen_within .x11 .x12 vLen vStatus (B + 516) (by decide)
  rw [show (B + 516) + 4 = B + 520 from by bv_omega] at h129
  have h129L := liftCode (cr' := bansfCR) h129
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 516) bansfProg 129 (.MV .x11 .x12)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have h128F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ vStatus) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
     ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** ((.x18 : Reg) ↦ᵣ oB) **
     ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
    (by pcf; exact hP) h128L
  have h129F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (vNext - vLen - aB).toNat)) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
     ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** ((.x18 : Reg) ↦ᵣ oB) **
     ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
    (by pcf; exact hP) h129L
  have hsetup := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h128F h129F
  have hult : BitVec.ult (8 : Word) vLen := by
    simp only [BitVec.ult, decide_eq_true_eq]
    have h8 : (8 : Word).toNat = 8 := by decide
    rw [h8, hlen]
    exact htl
  have hc := rlp_content_to_u64_too_long_spec_within C6
    (aB + BitVec.ofNat 64 (vNext - vLen - aB).toNat) vLen v5 (B + 524) hult
  have hc' := cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) hc
    (P' := ((.x1 : Reg) ↦ᵣ (B + 524)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (vNext - vLen - aB).toNat)) **
       ((.x11 : Reg) ↦ᵣ vLen) ** ((.x5 : Reg) ↦ᵣ v5) **
       ((.x0 : Reg) ↦ᵣ (0 : Word))))
  have hcall := bansf_callSite130_content_to_u64 (n := 5) vRa (by pcf) hc'
  have hcallF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion aB acctBytes **
     ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
     ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
    (by pcf; exact hP) hcall
  have hfull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hsetup hcallF
  rw [show B + 520 + 4 = B + 524 from by bv_omega] at hfull
  unfold nonceCaptureTooLongPre
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      have hq2 : (((.x5 : Reg) ↦ᵣ (8 : Word)) **
          ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
          ((.x28 : Reg) ↦ᵣ v28) **
          (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (2 : Word)) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
           bytesRegion aB acctBytes ** ((.x12 : Reg) ↦ᵣ vLen) **
           ((.x18 : Reg) ↦ᵣ oB) ** ((oB + 40) ↦ₘ (0 : Word)) **
           ((oB + 48) ↦ₘ (0 : Word)) ** P)) h := by
        xperm_hyp hq
      have hq3 := sepConj_mono (regIs_implies_regOwn .x5)
        (sepConj_mono (regIs_implies_regOwn .x6)
          (sepConj_mono (regIs_implies_regOwn .x7)
            (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x)))) h hq2
      let R : Assertion :=
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
         bytesRegion aB acctBytes) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (2 : Word))) **
        ((.x12 : Reg) ↦ᵣ vLen) ** ((.x18 : Reg) ↦ᵣ oB) **
        ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P
      have hR : R h := by dsimp only [R]; xperm_hyp hq3
      have hRp : (R ** ⌜8 < len⌝) h := (sepConj_pure_right h).2 ⟨hR, htl⟩
      dsimp only [R] at hRp
      xperm_hyp hRp) hfull

#print axioms bansf_nonceCapture_tooLongCall_spec

/-- Complete nonce-value capture (slots 128--134), with reject/found exits. -/
theorem bansf_nonceCapture_spec (aB oB : Word) (aLen tEnd off : Nat)
    (vNext vLen vStatus v5 v6 v7 v28 vRa : Word)
    (acctBytes : List (BitVec 8)) (P : Assertion)
    (hP : P.pcFree) (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen) (hoffle : off ≤ tEnd)
    (hdec : rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
      (aB + BitVec.ofNat 64 tEnd) vNext vLen) :
    cpsBranchWithin (7 * vLen.toNat + 18) (B + 512) bansfCR
      (((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ vStatus) **
       ((.x12 : Reg) ↦ᵣ vLen) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** ((.x18 : Reg) ↦ᵣ oB) **
       ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** P)
      (B + 736) (nonceCaptureRejectPost aB oB vLen acctBytes P)
      (B + 540) (nonceCaptureFoundPost aB oB vLen
        (BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
          ((acctBytes.drop (vNext - vLen - aB).toNat).take vLen.toNat)))
        vLen.toNat acctBytes P) := by
  have hover9 : aB.toNat + tEnd + 9 < 2 ^ 64 := by omega
  obtain ⟨hrepS, _, _⟩ := rlpItemDecode_spanStart hdec hoffle hover9
  by_cases htl : 8 < vLen.toNat
  · have hc := bansf_nonceCapture_tooLongCall_spec aB oB
      vNext vLen vStatus v5 v6 v7 v28 vRa vLen.toNat acctBytes P hP rfl htl hrepS
    have ht := bansf_nonceCapture_tooLong_spec aB oB vLen vLen.toNat acctBytes P hP
    have hfull := cpsTripleWithin_seq_same_cr hc ht
    have hfull' := cpsTripleWithin_weaken
      (Q' := nonceCaptureRejectPost aB oB vLen acctBytes P) (fun _ hp => hp)
      (fun _ hq => Or.inl hq) hfull
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_left (B + 540)
        (nonceCaptureFoundPost aB oB vLen
          (BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
            ((acctBytes.drop (vNext - vLen - aB).toNat).take vLen.toNat)))
          vLen.toNat acctBytes P) hfull')
  · have hlen8 : vLen.toNat ≤ 8 := by omega
    let PF : Assertion :=
      ((.x18 : Reg) ↦ᵣ oB) ** ((oB + 40) ↦ₘ (0 : Word)) **
      ((oB + 48) ↦ₘ (0 : Word)) ** P
    have hPF : PF.pcFree := by dsimp only [PF]; pcf; exact hP
    have hc := bansf_nonceCapture_call_spec aB aLen tEnd off
      vNext vLen vStatus v5 v6 v7 v28 vRa acctBytes PF hPF hsalign
      hslack hover hvalid htEnd hoffle hdec
    have hd := bansf_nonceCapture_dispatch_spec aB oB vLen
      (BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
        ((acctBytes.drop (vNext - vLen - aB).toNat).take vLen.toNat)))
      (vNext - vLen - aB).toNat vLen.toNat acctBytes P hP hlen8
    have hfull := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (nonceParserPost_to_dispatchPre aB oB vLen
        (BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
          ((acctBytes.drop (vNext - vLen - aB).toNat).take vLen.toNat)))
        (vNext - vLen - aB).toNat vLen.toNat acctBytes P rfl)
      hc hd
    dsimp only [PF] at hfull
    exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hfull

#print axioms bansf_nonceCapture_spec

/-- Reframe either nonce-parser rejection status as the station reject post. -/
theorem nonceCaptureReject_to_stationRej (aB newSp oB n4 vLen : Word)
    (aLen : Nat) (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      nonceCaptureRejectPost aB oB vLen acctBytes
        (G **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) **
         ((newSp + 48) ↦ₘ n4) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         memOwn (newSp + 64) ** memOwn (newSp + 72) **
         ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
         ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         regOwn .x19 ** regOwn .x20 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** F) h →
      nonceStationRej aB newSp oB aLen acctBytes G F h := by
  intro h hq
  unfold nonceCaptureRejectPost at hq
  rcases hq with hq | hq
  · have hq2 :
        ((((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ (2 : Word)) **
          ((.x12 : Reg) ↦ᵣ vLen) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
          ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
          ((newSp + 48) ↦ₘ n4) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen))) **
         (G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
          ((oB + 72) ↦ₘ (0 : Word)) **
          memOwn (newSp + 64) ** memOwn (newSp + 72) **
          ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
          ((.x18 : Reg) ↦ᵣ oB) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x19 ** regOwn .x20 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hq
    have hq3 := sepConj_mono
      (sepConj_mono (fun _ hx => hx)
       (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
         (sepConj_mono (regIs_implies_regOwn .x1)
          (sepConj_mono memIs_implies_memOwn
           (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)))))))
      (fun _ x => x) h hq2
    unfold nonceStationRej
    xperm_hyp hq3
  · have hq2 :
        ((((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ (3 : Word)) **
          ((.x12 : Reg) ↦ᵣ vLen) ** ((.x1 : Reg) ↦ᵣ (B + 524)) **
          ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
          ((newSp + 48) ↦ₘ n4) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen))) **
         (G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
          ((oB + 72) ↦ₘ (0 : Word)) **
          memOwn (newSp + 64) ** memOwn (newSp + 72) **
          ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
          ((.x18 : Reg) ↦ᵣ oB) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x19 ** regOwn .x20 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hq
    have hq3 := sepConj_mono
      (sepConj_mono (fun _ hx => hx)
       (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
         (sepConj_mono (regIs_implies_regOwn .x1)
          (sepConj_mono memIs_implies_memOwn
           (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)))))))
      (fun _ x => x) h hq2
    unfold nonceStationRej
    xperm_hyp hq3

#print axioms nonceCaptureReject_to_stationRej

/-- Reframe either successful nonce-parser arm as the station found post. -/
theorem nonceCaptureFound_to_stationPost (aB newSp oB n4 vNext vLen : Word)
    (aLen fOff fSpanN : Nat) (acctBytes : List (BitVec 8))
    (G F : Assertion)
    (hFF : FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    ∀ h,
      nonceCaptureFoundPost aB oB vLen
        (BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
          ((acctBytes.drop (vNext - vLen - aB).toNat).take vLen.toNat)))
        vLen.toNat acctBytes
        (G **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) **
         ((newSp + 48) ↦ₘ n4) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         memOwn (newSp + 64) ** memOwn (newSp + 72) **
         ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
         ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         regOwn .x19 ** regOwn .x20 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** F) h →
      nonceStationPost aB newSp oB aLen fOff fSpanN n4 acctBytes G F h := by
  intro h hq
  unfold nonceCaptureFoundPost at hq
  unfold nonceStationPost
  refine Or.inr ⟨vNext, vLen, ?_⟩
  let image : Word := BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
    ((acctBytes.drop (vNext - vLen - aB).toNat).take vLen.toNat))
  rcases hq with he | hc
  · let R : Assertion :=
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ vLen) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
      ((.x1 : Reg) ↦ᵣ (B + 524)) **
      (G ** ((oB + 40) ↦ₘ (1 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) **
       ((newSp + 48) ↦ₘ n4) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       memOwn (newSp + 64) ** memOwn (newSp + 72) **
       ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
       ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x19 ** regOwn .x20 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F)
    have he2 : (R ** ⌜vLen.toNat = 0⌝) h := by
      dsimp only [R]
      xperm_hyp he
    obtain ⟨hR, hzero⟩ := (sepConj_pure_right h).1 he2
    have himage0 : image = (0 : Word) := by
      dsimp only [image]
      rw [hzero]
      rfl
    let S : Assertion :=
      G ** ((oB + 40) ↦ₘ (1 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      memOwn (newSp + 64) ** memOwn (newSp + 72) **
      ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
      ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x19 ** regOwn .x20 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F
    let T : Assertion := ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ vLen) **
      ((.x5 : Reg) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524))
    have hR2 : (T ** S) h := by
      dsimp only [T, S]
      xperm_hyp hR
    dsimp only [T] at hR2
    have hR' := sepConj_mono
      (sepConj_mono (regIs_implies_regOwn .x10)
       (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
         (sepConj_mono (regIs_implies_regOwn .x5) (regIs_implies_regOwn .x1)))))
      (fun _ x => x) h hR2
    refine (sepConj_pure_right h).2 ⟨?_, ⟨hFF, by omega⟩⟩
    dsimp only [image] at himage0
    rw [himage0]
    xperm_hyp hR'
  · let R : Assertion :=
      ((.x10 : Reg) ↦ᵣ image) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ vLen) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
      ((.x1 : Reg) ↦ᵣ (B + 524)) **
      (G ** ((oB + 40) ↦ₘ (1 : Word)) ** ((oB + 48) ↦ₘ image) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) **
       ((newSp + 48) ↦ₘ n4) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       memOwn (newSp + 64) ** memOwn (newSp + 72) **
       ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
       ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x19 ** regOwn .x20 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F)
    have hc2 : (R ** ⌜vLen.toNat ≤ 8⌝) h := by
      dsimp only [R, image]
      xperm_hyp hc
    obtain ⟨hR, hlen8⟩ := (sepConj_pure_right h).1 hc2
    let S : Assertion :=
      G ** ((oB + 40) ↦ₘ (1 : Word)) ** ((oB + 48) ↦ₘ image) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      memOwn (newSp + 64) ** memOwn (newSp + 72) **
      ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
      ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x19 ** regOwn .x20 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F
    let T : Assertion := ((.x10 : Reg) ↦ᵣ image) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ vLen) **
      ((.x5 : Reg) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 524))
    have hR2 : (T ** S) h := by
      dsimp only [T, S]
      xperm_hyp hR
    dsimp only [T] at hR2
    have hR' := sepConj_mono
      (sepConj_mono (regIs_implies_regOwn .x10)
       (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
         (sepConj_mono (regIs_implies_regOwn .x5) (regIs_implies_regOwn .x1)))))
      (fun _ x => x) h hR2
    refine (sepConj_pure_right h).2 ⟨?_, ⟨hFF, hlen8⟩⟩
    dsimp only [image] at hR' ⊢
    xperm_hyp hR'

#print axioms nonceCaptureFound_to_stationPost

theorem cpsBranchWithin_of_forall_regIs_to_regOwn5
    {n : Nat} {entry : Word} {r1 r2 r3 r4 r5 : Reg}
    {P : Assertion} {e1 : Word} {Q1 : Assertion} {e2 : Word} {Q2 : Assertion}
    {cr : CodeReq}
    (h : ∀ v1 v2 v3 v4 v5, cpsBranchWithin n entry cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) **
       (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5)) e1 Q1 e2 Q2) :
    cpsBranchWithin n entry cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5)
      e1 Q1 e2 Q2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, ⟨v5, hv5⟩⟩ := hO4
  exact h v1 v2 v3 v4 v5 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, g4, g5, d3, u3,
       hv2, g6, g7, d4, u4, hv3, g8, g9, d5, u5, hv4, hv5⟩, hRb⟩ hpc

#print axioms cpsBranchWithin_of_forall_regIs_to_regOwn5

/-- Continuation at `B + 512` (the nonce value item decoded): run the scalar
    capture and route both exits to the nonce-station boundary assertions. -/
theorem bansf_nonceStationCont512_spec (aB newSp oB : Word)
    (aLen tEnd offV fOff fSpanN : Nat) (n4 : Word)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen) (hoffle : offV ≤ tEnd)
    (hFF : ∀ vNext vLen : Word,
      rlpItemDecode acctBytes offV (aB + BitVec.ofNat 64 offV)
        (aB + BitVec.ofNat 64 tEnd) vNext vLen →
      FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    cpsBranchWithin (7 * acctBytes.length + 18) (B + 512) bansfCR
      (fun h => ∃ vNext vLen : Word,
        (((((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
           ((.x12 : Reg) ↦ᵣ vLen) **
           ((.x2 : Reg) ↦ᵣ newSp) **
           ((newSp + 48) ↦ₘ n4) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           memOwn (newSp + 64) ** memOwn (newSp + 72) **
           ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
           ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
           ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
           ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
           ((oB + 72) ↦ₘ (0 : Word)) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** G **
           regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** F) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x1) **
         ⌜rlpItemDecode acctBytes offV (aB + BitVec.ofNat 64 offV)
           (aB + BitVec.ofNat 64 tEnd) vNext vLen⌝) h)
      (B + 736) (nonceStationRej aB newSp oB aLen acctBytes G F)
      (B + 540)
        (nonceStationPost aB newSp oB aLen fOff fSpanN n4 acctBytes G F) := by
  refine cpsBranchWithin_exists_pre (fun vNext => ?_)
  refine cpsBranchWithin_exists_pre (fun vLen => ?_)
  refine cpsBranchWithin_pure_pre_right (fun hdecV => ?_)
  refine cpsBranchWithin_of_forall_regIs_to_regOwn5
    (fun v5 v6 v7 v28 vRa => ?_)
  let P : Assertion :=
    G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    memOwn (newSp + 64) ** memOwn (newSp + 72) **
    ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
    ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
    regOwn .x19 ** regOwn .x20 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** F
  have hP : P.pcFree := by dsimp only [P]; pcf; exact hG; pcf; exact hF
  have hc := bansf_nonceCapture_spec aB oB aLen tEnd offV
    vNext vLen 0 v5 v6 v7 v28 vRa acctBytes P hP hsalign hslack
    hover hvalid htEnd hoffle hdecV
  obtain ⟨_, hsrcLen, _, _⟩ := bansf_nonceCapture_callee_bounds aB aLen tEnd
    offV vNext vLen acctBytes hslack hover hvalid htEnd hoffle hdecV
  refine cpsBranchWithin_weaken (fun h hp => by dsimp only [P]; xperm_hyp hp)
    (fun h hq => nonceCaptureReject_to_stationRej
      aB newSp oB n4 vLen aLen acctBytes G F h hq)
    (fun h hq => nonceCaptureFound_to_stationPost
      aB newSp oB n4 vNext vLen aLen fOff fSpanN acctBytes G F
      (hFF vNext vLen hdecV) h hq)
    (cpsBranchWithin_mono_nSteps (by omega) hc)

#print axioms bansf_nonceStationCont512_spec

/-- A rejected nonce value-item unit carries enough untouched station frame to
    establish the shared nonce-station reject assertion. -/
theorem nonceTupleReject_to_stationRej (aB newSp oB n4 : Word)
    (aLen : Nat) (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      (tupleRej aB newSp acctBytes F **
        (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)) h →
      nonceStationRej aB newSp oB aLen acctBytes G F h := by
  intro h hq
  unfold tupleRej at hq
  have hq2 :
      ((((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
        ((newSp + 48) ↦ₘ n4) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x10 : Reg) ↦ᵣ (1 : Word))) **
       (G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F)) h := by
    xperm_hyp hq
  have hq3 := sepConj_mono
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn (fun _ hx => hx)))))
    (fun _ x => x) h hq2
  unfold nonceStationRej
  xperm_hyp hq3

#print axioms nonceTupleReject_to_stationRej

@[irreducible]
def nonceCont512Pre (aB newSp oB n4 : Word) (aLen tEnd off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion :=
  fun h => ∃ vNext vLen : Word,
    (((((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ vLen) ** ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 48) ↦ₘ n4) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       memOwn (newSp + 64) ** memOwn (newSp + 72) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
       ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion aB acctBytes ** G ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31 ** F) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x1) **
     ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
       (aB + BitVec.ofNat 64 tEnd) vNext vLen⌝) h

/-- Folded success adapter from the nonce value-item post to the capture
    continuation precondition. -/
theorem nonceTupleValOk_to_cont512Pre (aB newSp oB n4 : Word)
    (aLen tEnd off : Nat) (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      (tupleValOk aB newSp tEnd off acctBytes F **
        (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)) h →
      nonceCont512Pre aB newSp oB n4 aLen tEnd off acctBytes G F h := by
  intro h hp
  unfold tupleValOk at hp
  obtain ⟨g1, g2, gd, gu, hVal, hfr⟩ := hp
  obtain ⟨vNext, vLen, hVal2⟩ := hVal
  obtain ⟨hregs, hdec⟩ := (sepConj_pure_right g1).1 hVal2
  have hR := (⟨g1, g2, gd, gu, hregs, hfr⟩ :
    (((((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ vLen) ** ((.x2 : Reg) ↦ᵣ newSp) **
      memOwn (newSp + 64) ** memOwn (newSp + 72) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)) h))
  delta nonceCont512Pre
  refine ⟨vNext, vLen, (sepConj_pure_right h).2 ⟨?_, hdec⟩⟩
  let L : Assertion :=
    (((((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ vLen) ** ((.x2 : Reg) ↦ᵣ newSp) **
      memOwn (newSp + 64) ** memOwn (newSp + 72) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)))
  let R : Assertion :=
    (((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ vLen) ** ((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      memOwn (newSp + 64) ** memOwn (newSp + 72) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
      ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion aB acctBytes ** G ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** F) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x1
  have hL : L h := by dsimp only [L]; exact hR
  have heq : L = R := by dsimp only [L, R]; xperm
  change R h
  exact (congrFun heq h).mp hL

#print axioms nonceTupleValOk_to_cont512Pre

/-- Continuation at `B + 496`: decode the tuple value item, then run the
    nonce scalar capture at `B + 512`. -/
theorem bansf_nonceStationCont496_spec (aB newSp oB : Word)
    (aLen tEnd offI fOff fSpanN : Nat) (n4 : Word)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen) (hoffleI : offI ≤ tEnd)
    (hFF2 : ∀ iNext iLen vNext vLen : Word,
      rlpItemDecode acctBytes offI (aB + BitVec.ofNat 64 offI)
        (aB + BitVec.ofNat 64 tEnd) iNext iLen →
      rlpItemDecode acctBytes ((iNext - aB).toNat) iNext
        (aB + BitVec.ofNat 64 tEnd) vNext vLen →
      FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    cpsBranchWithin (7 * acctBytes.length + 110) (B + 496) bansfCR
      (fun h => ∃ next len : Word,
        (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
           ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
           ((newSp + 64) ↦ₘ next) **
           ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
           ((newSp + 48) ↦ₘ n4) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
           ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
           ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
           ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
           ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion aB acctBytes ** G ** F) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
         ⌜rlpItemDecode acctBytes offI (aB + BitVec.ofNat 64 offI)
           (aB + BitVec.ofNat 64 tEnd) next len⌝) h)
      (B + 736) (nonceStationRej aB newSp oB aLen acctBytes G F)
      (B + 540)
        (nonceStationPost aB newSp oB aLen fOff fSpanN n4 acctBytes G F) := by
  refine cpsBranchWithin_exists_pre (fun next => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_pure_pre_right (fun hdecI => ?_)
  obtain ⟨hrepI, _, hleI⟩ := rlpItemDecode_advance hdecI hoffleI (by omega)
  set offN := (next - aB).toNat with hoffN
  rw [hrepI]
  refine cpsBranchWithin_of_forall_regIs_to_regOwn8
    (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
  have hti := bansf_nonceTupleItem1_spec aB newSp aLen tEnd offN acctBytes
    v5 v6 v7 (aB + BitVec.ofNat 64 offN) 0 len v28 v29 v30 v31 vRa F hF
    hsalign hslack hover hvalid htEnd hleI
  let H : Assertion :=
    G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
    ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
    ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20
  have hHF : H.pcFree := by dsimp only [H]; pcf; exact hG; pcf
  have htiF := cpsBranchWithin_frameR H hHF hti
  have hc512 := bansf_nonceStationCont512_spec aB newSp oB aLen tEnd offN
    fOff fSpanN n4 acctBytes G F hG hF hsalign hslack hover hvalid htEnd hleI
    (fun vNext vLen hdecV =>
      hFF2 next len vNext vLen hdecI (by rw [← hoffN, hrepI]; exact hdecV))
  have hc512F := cpsBranchWithin_weaken
    (P' := nonceCont512Pre aB newSp oB n4 aLen tEnd offN acctBytes G F)
    (fun _ hp => by delta nonceCont512Pre at hp; exact hp)
    (fun _ hq => hq) (fun _ hq => hq) hc512
  have hc512' := cpsBranchWithin_weaken
    (nonceTupleValOk_to_cont512Pre aB newSp oB n4 aLen tEnd offN acctBytes G F)
    (fun _ hq => hq) (fun _ hq => hq) hc512F
  have htiW := cpsBranchWithin_weaken
    (Q_t' := nonceStationRej aB newSp oB aLen acctBytes G F)
    (fun _ hp => hp)
    (fun h hq => nonceTupleReject_to_stationRej
      aB newSp oB n4 aLen acctBytes G F h (by dsimp only [H] at hq; exact hq))
    (fun _ hq => hq) htiF
  have hchain := cpsBranchWithin_chain_snd htiW hc512'
  exact cpsBranchWithin_weaken (fun h hp => by dsimp only [H]; xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_mono_nSteps (by omega) hchain)

#print axioms bansf_nonceStationCont496_spec

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
