/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainF

  Nonce-station boundary assertions for `bal_account_nonstorage_finals`.
  The station occupies slots 88--134 and returns at `B + 540`, or rejects
  at the shared body exit `B + 736`.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainE

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
     assertPure (FieldFinal acctBytes aB fOff fSpanN none) empAssertion) h ∨
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
       assertPure (FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen)) ∧
        vLen.toNat ≤ 8) empAssertion) h)

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
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
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
      ⌜0 < len ∧ getByteAt acctBytes srcOff = 0⌝) h ∨
    (((.x10 : Reg) ↦ᵣ BitVec.ofNat 64
        (EL.RLP.Nat.fromBytesBE ((acctBytes.drop srcOff).take len))) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ⌜0 < len ∧ getByteAt acctBytes srcOff ≠ 0⌝) h)

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

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
