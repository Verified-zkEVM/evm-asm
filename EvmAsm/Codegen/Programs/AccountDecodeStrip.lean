/-
  Leading-zero strip loops of `accountDecode_prog` (GH #11523): after each of
  field 0 / field 1 loads its content cursor, a top-tested scan drops prefix
  zero bytes so the subsequent bound check is on *significant* length
  (u64 / u256 value bounds), matching `witness_state.py:112-118` `int.from_bytes`.

  Nonce strip [30]-[35] (`AB+120 → AB+144`):
    BEQ x6,x0,+24 ; LBU ; BNE x29,x0,+16 ; ADDI x28,1 ; ADDI x6,-1 ; JAL -20
  Balance strip [63]-[68] (`AB+252 → AB+276`): identical shape at the field-1 PCs.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeSpec
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000

local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

local macro "adMemF" k:term ", " A:term ", " ins:term : term =>
  `((fun a i h => ad_mono a i
      (CodeReq.ofProg_mem_at AB $A accountDecode_prog $k $ins (by bv_omega)
        (by rw [ad_length]; omega) rfl (by rw [ad_length]; norm_num) a i h)))

/-! ## Pure helpers bridging strip ghost state to `significantLen` -/

/-- Recursive leading-zero count over a bounded window — matches the strip loop. -/
def nlzWin (bs : List (BitVec 8)) (off : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if h : off < bs.length then
        if bs[off]'h = (0 : BitVec 8) then nlzWin bs (off + 1) n + 1 else 0
      else 0

theorem nlzWin_le (bs : List (BitVec 8)) (off n : Nat) : nlzWin bs off n ≤ n := by
  induction n generalizing off with
  | zero => simp [nlzWin]
  | succ n ih =>
    simp only [nlzWin]
    split
    · split
      · have := ih (off + 1); omega
      · omega
    · omega

private theorem ads_drop_take_cons (bs : List (BitVec 8)) (off n : Nat)
    (hoff : off < bs.length) :
    (bs.drop off).take (n + 1) = bs[off]'hoff :: (bs.drop (off + 1)).take n := by
  have hdrop : bs.drop off = bs[off]'hoff :: bs.drop (off + 1) :=
    List.drop_eq_getElem_cons hoff
  rw [hdrop]; rfl

theorem nlzWin_eq_numLeadingZerosBE (bs : List (BitVec 8)) (off n : Nat)
    (hbound : off + n ≤ bs.length) :
    nlzWin bs off n = numLeadingZerosBE ((bs.drop off).take n) := by
  induction n generalizing off with
  | zero => simp [nlzWin, numLeadingZerosBE]
  | succ n ih =>
    have hoff : off < bs.length := by omega
    have hdrop := ads_drop_take_cons bs off n hoff
    simp only [nlzWin, hoff, ↓reduceDIte]
    by_cases hz : bs[off]'hoff = (0 : BitVec 8)
    · simp only [hz, ↓reduceIte]
      rw [hdrop, numLeadingZerosBE, hz]
      have hpos : ((0 : BitVec 8) == 0) = true := by decide
      simp only [hpos, List.takeWhile_cons, ↓reduceIte, List.length_cons]
      exact congrArg Nat.succ (ih (off + 1) (by omega))
    · simp only [hz, ↓reduceIte]
      rw [hdrop, numLeadingZerosBE]
      have hne : (bs[off]'hoff == (0 : BitVec 8)) = false := by
        simp only [beq_eq_false_iff_ne]; exact hz
      rw [List.takeWhile_cons, hne]
      rfl

theorem significantLen_eq_nlzWin (bs : List (BitVec 8)) (off n : Nat)
    (hbound : off + n ≤ bs.length) :
    significantLen ((bs.drop off).take n) = n - nlzWin bs off n := by
  rw [significantLen, nlzWin_eq_numLeadingZerosBE bs off n hbound]
  have hlen : ((bs.drop off).take n).length = n := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left]
    omega
  omega

private theorem ads_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem ads_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

private theorem ads_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

private theorem ads_toNat_zext_byte (b : BitVec 8) :
    (b.zeroExtend 64 : Word).toNat = b.toNat := by
  have hb := b.isLt
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth]
  omega

private theorem ads_byte_ne_zero_of_zext (b : BitVec 8) (hnz : b ≠ 0) :
    (b.zeroExtend 64 : Word) ≠ (0 : Word) := by
  intro hc
  have h1 := ads_toNat_zext_byte b
  have : b.toNat = 0 := by
    have hz : (0 : Word).toNat = 0 := rfl
    rw [← hc, h1] at hz; exact hz
  exact hnz (BitVec.eq_of_toNat_eq (by simp [this]))

/-! ## Nonce strip body steps -/

private theorem adNonceStripZeroStep (accBase : Word) (bytes : List (BitVec 8))
    (o0 i k : Nat) (v29 : Word)
    (halign : accBase.toNat % 8 = 0)
    (hlt : o0 + i < bytes.length)
    (hz : bytes[o0 + i]'hlt = (0 : BitVec 8))
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 5 (AB + 124) (AB + 120) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 k) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes) := by
  have h31 := bytesRegion_lbu_within .x29 .x28 accBase v29 (AB + 124) bytes (o0 + i)
    (by decide) halign hlt (by omega) (hvalid (o0 + i) hlt)
  rw [show (AB + 124 : Word) + 4 = AB + 128 from by bv_omega, hz,
      show ((0 : BitVec 8).zeroExtend 64 : Word) = 0 from by decide] at h31
  have e31 := cpsTripleWithin_extend_code
    (adMemF 31, (AB + 124), (.LBU .x29 .x28 (0 : BitVec 12))) h31
  have f31 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcFreeR) e31
  have hbne := bne_spec_gen_within .x29 .x0 (16 : BitVec 13) (0 : Word) (0 : Word) (AB + 128)
  rw [show (AB + 128 : Word) + signExtend13 (16 : BitVec 13) = AB + 144 from by
      rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (AB + 128 : Word) + 4 = AB + 132 from by bv_omega] at hbne
  have ebne := cpsBranchWithin_extend_code
    (adMemF 32, (AB + 128), (.BNE .x29 .x0 (16 : BitVec 13))) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 ebne (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 rfl)
  have fnt := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
     bytesRegion accBase bytes)
    (by pcFreeR) hnt
  have h33 := addi_spec_gen_same_within .x28 (accBase + BitVec.ofNat 64 (o0 + i))
    (1 : BitVec 12) (AB + 132) (by decide)
  rw [ads_advance accBase (o0 + i),
      show o0 + i + 1 = o0 + (i + 1) from by omega,
      show (AB + 132 : Word) + 4 = AB + 136 from by bv_omega] at h33
  have e33 := cpsTripleWithin_extend_code
    (adMemF 33, (AB + 132), (.ADDI .x28 .x28 (1 : BitVec 12))) h33
  have f33 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
     ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion accBase bytes)
    (by pcFreeR) e33
  have h34 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (k + 1)) (-1 : BitVec 12)
    (AB + 136) (by decide)
  rw [ads_succ_dec k, show (AB + 136 : Word) + 4 = AB + 140 from by bv_omega] at h34
  have e34 := cpsTripleWithin_extend_code
    (adMemF 34, (AB + 136), (.ADDI .x6 .x6 (-1 : BitVec 12))) h34
  have f34 := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion accBase bytes)
    (by pcFreeR) e34
  have h35 := jal_x0_spec_gen_within (-20 : BitVec 21) (AB + 140)
  rw [show AB + 140 + signExtend21 (-20 : BitVec 21) = AB + 120 from by
      rw [show signExtend21 (-20 : BitVec 21) = (-20 : Word) from by decide]; bv_omega] at h35
  have e35 := cpsTripleWithin_extend_code
    (adMemF 35, (AB + 140), (.JAL .x0 (-20 : BitVec 21))) h35
  have f35 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 k) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion accBase bytes)
    (by pcFreeR) e35
  rw [sepConj_emp_left'] at f35
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f31 fnt
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f33
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 f34
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 f35
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s4)

private theorem adNonceStripBreak (accBase : Word) (bytes : List (BitVec 8))
    (o0 i n : Nat) (v29 : Word)
    (halign : accBase.toNat % 8 = 0)
    (hlt : o0 + i < bytes.length)
    (hnz : bytes[o0 + i]'hlt ≠ (0 : BitVec 8))
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 2 (AB + 124) (AB + 144) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ ((bytes[o0 + i]'hlt).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes) := by
  have h31 := bytesRegion_lbu_within .x29 .x28 accBase v29 (AB + 124) bytes (o0 + i)
    (by decide) halign hlt (by omega) (hvalid (o0 + i) hlt)
  rw [show (AB + 124 : Word) + 4 = AB + 128 from by bv_omega] at h31
  have e31 := cpsTripleWithin_extend_code
    (adMemF 31, (AB + 124), (.LBU .x29 .x28 (0 : BitVec 12))) h31
  have f31 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcFreeR) e31
  have hbne := bne_spec_gen_within .x29 .x0 (16 : BitVec 13)
    ((bytes[o0 + i]'hlt).zeroExtend 64) (0 : Word) (AB + 128)
  rw [show (AB + 128 : Word) + signExtend13 (16 : BitVec 13) = AB + 144 from by
      rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (AB + 128 : Word) + 4 = AB + 132 from by bv_omega] at hbne
  have ebne := cpsBranchWithin_extend_code
    (adMemF 32, (AB + 128), (.BNE .x29 .x0 (16 : BitVec 13))) hbne
  have ht := cpsBranchWithin_takenStripPure2 ebne (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ads_byte_ne_zero_of_zext _ hnz ((sepConj_pure_right _).1 hQ).2)
  have ft := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
     bytesRegion accBase bytes)
    (by pcFreeR) ht
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f31 ft
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s)

/-- **Nonce strip loop** [30]-[35] (`AB+120 → AB+144`).

    Ghost state: remaining window length `n` at absolute content index `o0+i`.
    Post: `x6 = n - nlzWin`, `x28` advanced by `nlzWin` bytes. -/
theorem adNonceStrip (accBase : Word) (bytes : List (BitVec 8))
    (o0 n i : Nat) (v29 : Word)
    (halign : accBase.toNat % 8 = 0)
    (hbound : o0 + i + n ≤ bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (6 * n + 1) (AB + 120) (AB + 144) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - nlzWin bytes (o0 + i) n)) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i + nlzWin bytes (o0 + i) n))) **
       regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes) := by
  have hbeq : (AB + 120 : Word) + signExtend13 (24 : BitVec 13) = AB + 144 := by
    rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]; bv_omega
  induction n generalizing i v29 with
  | zero =>
    have hb := beq_spec_gen_within .x6 .x0 (24 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (AB + 120)
    rw [hbeq] at hb
    have hbe := cpsBranchWithin_extend_code
      (adMemF 30, (AB + 120), (.BEQ .x6 .x0 (24 : BitVec 13))) hb
    have htaken := cpsBranchWithin_takenStripPure2 hbe (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion accBase bytes)
      (by pcFreeR) htaken
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          have hnlz : nlzWin bytes (o0 + i) 0 = 0 := by simp [nlzWin]
          simp only [hnlz, Nat.sub_zero, Nat.add_zero]
          -- taken BEQ leaves x6 = BitVec.ofNat 64 0 (= ofNat 64 (0-0))
          have hq2 : (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
              ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
              ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion accBase bytes) sState := by xperm_chunked hq
          exact sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x29))) _ hq2) htf)
  | succ k ih =>
    have hb := beq_spec_gen_within .x6 .x0 (24 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (AB + 120)
    rw [hbeq] at hb
    have hbe := cpsBranchWithin_extend_code
      (adMemF 30, (AB + 120), (.BEQ .x6 .x0 (24 : BitVec 13))) hb
    have hnt := cpsBranchWithin_ntakenStripPure2 hbe (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ads_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion accBase bytes)
      (by pcFreeR) hnt
    have hlt : o0 + i < bytes.length := by omega
    by_cases hz : bytes[o0 + i]'hlt = (0 : BitVec 8)
    · have hbody := adNonceStripZeroStep accBase bytes o0 i k v29 halign hlt hz hover hvalid
      have hih := ih (i + 1) (0 : Word) (by omega)
      have s1 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_chunked hp) hntf hbody
      have sfull := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_chunked hp) s1 hih
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
          (fun _ hq => by
            have hnlz : nlzWin bytes (o0 + i) (k + 1) =
                nlzWin bytes (o0 + (i + 1)) k + 1 := by
              simp only [nlzWin, hlt, ↓reduceDIte, hz, ↓reduceIte]
              ac_rfl
            have hsub : (k + 1) - nlzWin bytes (o0 + i) (k + 1) =
                k - nlzWin bytes (o0 + (i + 1)) k := by
              rw [hnlz]; omega
            have hadd : o0 + i + nlzWin bytes (o0 + i) (k + 1) =
                o0 + (i + 1) + nlzWin bytes (o0 + (i + 1)) k := by
              rw [hnlz]; omega
            simp only [hsub, hadd] at hq ⊢
            exact hq) sfull)
    · have hbr := adNonceStripBreak accBase bytes o0 i (k + 1) v29 halign hlt hz hover hvalid
      have s1 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_chunked hp) hntf hbr
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
          (fun sState hq => by
            have hnlz : nlzWin bytes (o0 + i) (k + 1) = 0 := by
              simp only [nlzWin, hlt, ↓reduceDIte, hz, ↓reduceIte]
            simp only [hnlz, Nat.sub_zero, Nat.add_zero]
            have hq2 : (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
                ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
                ((.x29 : Reg) ↦ᵣ ((bytes[o0 + i]'hlt).zeroExtend 64)) **
                ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                bytesRegion accBase bytes) sState := by xperm_chunked hq
            have hq3 := sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (regIs_implies_regOwn .x29))) _ hq2
            exact hq3) s1)

#print axioms adNonceStrip

/-! ## Balance strip — same shape at field-1 PCs -/

private theorem adBalStripZeroStep (accBase : Word) (bytes : List (BitVec 8))
    (o0 i k : Nat) (v29 : Word)
    (halign : accBase.toNat % 8 = 0)
    (hlt : o0 + i < bytes.length)
    (hz : bytes[o0 + i]'hlt = (0 : BitVec 8))
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 5 (AB + 256) (AB + 252) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 k) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes) := by
  have h64 := bytesRegion_lbu_within .x29 .x28 accBase v29 (AB + 256) bytes (o0 + i)
    (by decide) halign hlt (by omega) (hvalid (o0 + i) hlt)
  rw [show (AB + 256 : Word) + 4 = AB + 260 from by bv_omega, hz,
      show ((0 : BitVec 8).zeroExtend 64 : Word) = 0 from by decide] at h64
  have e64 := cpsTripleWithin_extend_code
    (adMemF 64, (AB + 256), (.LBU .x29 .x28 (0 : BitVec 12))) h64
  have f64 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcFreeR) e64
  have hbne := bne_spec_gen_within .x29 .x0 (16 : BitVec 13) (0 : Word) (0 : Word) (AB + 260)
  rw [show (AB + 260 : Word) + signExtend13 (16 : BitVec 13) = AB + 276 from by
      rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (AB + 260 : Word) + 4 = AB + 264 from by bv_omega] at hbne
  have ebne := cpsBranchWithin_extend_code
    (adMemF 65, (AB + 260), (.BNE .x29 .x0 (16 : BitVec 13))) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 ebne (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 rfl)
  have fnt := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
     bytesRegion accBase bytes)
    (by pcFreeR) hnt
  have h66 := addi_spec_gen_same_within .x28 (accBase + BitVec.ofNat 64 (o0 + i))
    (1 : BitVec 12) (AB + 264) (by decide)
  rw [ads_advance accBase (o0 + i),
      show o0 + i + 1 = o0 + (i + 1) from by omega,
      show (AB + 264 : Word) + 4 = AB + 268 from by bv_omega] at h66
  have e66 := cpsTripleWithin_extend_code
    (adMemF 66, (AB + 264), (.ADDI .x28 .x28 (1 : BitVec 12))) h66
  have f66 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
     ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion accBase bytes)
    (by pcFreeR) e66
  have h67 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (k + 1)) (-1 : BitVec 12)
    (AB + 268) (by decide)
  rw [ads_succ_dec k, show (AB + 268 : Word) + 4 = AB + 272 from by bv_omega] at h67
  have e67 := cpsTripleWithin_extend_code
    (adMemF 67, (AB + 268), (.ADDI .x6 .x6 (-1 : BitVec 12))) h67
  have f67 := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion accBase bytes)
    (by pcFreeR) e67
  have h68 := jal_x0_spec_gen_within (-20 : BitVec 21) (AB + 272)
  rw [show AB + 272 + signExtend21 (-20 : BitVec 21) = AB + 252 from by
      rw [show signExtend21 (-20 : BitVec 21) = (-20 : Word) from by decide]; bv_omega] at h68
  have e68 := cpsTripleWithin_extend_code
    (adMemF 68, (AB + 272), (.JAL .x0 (-20 : BitVec 21))) h68
  have f68 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 k) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion accBase bytes)
    (by pcFreeR) e68
  rw [sepConj_emp_left'] at f68
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f64 fnt
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f66
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 f67
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 f68
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s4)

private theorem adBalStripBreak (accBase : Word) (bytes : List (BitVec 8))
    (o0 i n : Nat) (v29 : Word)
    (halign : accBase.toNat % 8 = 0)
    (hlt : o0 + i < bytes.length)
    (hnz : bytes[o0 + i]'hlt ≠ (0 : BitVec 8))
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 2 (AB + 256) (AB + 276) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ ((bytes[o0 + i]'hlt).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes) := by
  have h64 := bytesRegion_lbu_within .x29 .x28 accBase v29 (AB + 256) bytes (o0 + i)
    (by decide) halign hlt (by omega) (hvalid (o0 + i) hlt)
  rw [show (AB + 256 : Word) + 4 = AB + 260 from by bv_omega] at h64
  have e64 := cpsTripleWithin_extend_code
    (adMemF 64, (AB + 256), (.LBU .x29 .x28 (0 : BitVec 12))) h64
  have f64 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcFreeR) e64
  have hbne := bne_spec_gen_within .x29 .x0 (16 : BitVec 13)
    ((bytes[o0 + i]'hlt).zeroExtend 64) (0 : Word) (AB + 260)
  rw [show (AB + 260 : Word) + signExtend13 (16 : BitVec 13) = AB + 276 from by
      rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (AB + 260 : Word) + 4 = AB + 264 from by bv_omega] at hbne
  have ebne := cpsBranchWithin_extend_code
    (adMemF 65, (AB + 260), (.BNE .x29 .x0 (16 : BitVec 13))) hbne
  have ht := cpsBranchWithin_takenStripPure2 ebne (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ads_byte_ne_zero_of_zext _ hnz ((sepConj_pure_right _).1 hQ).2)
  have ft := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
     bytesRegion accBase bytes)
    (by pcFreeR) ht
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f64 ft
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s)

theorem adBalStrip (accBase : Word) (bytes : List (BitVec 8))
    (o0 n i : Nat) (v29 : Word)
    (halign : accBase.toNat % 8 = 0)
    (hbound : o0 + i + n ≤ bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (6 * n + 1) (AB + 252) (AB + 276) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - nlzWin bytes (o0 + i) n)) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i + nlzWin bytes (o0 + i) n))) **
       regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes) := by
  have hbeq : (AB + 252 : Word) + signExtend13 (24 : BitVec 13) = AB + 276 := by
    rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]; bv_omega
  induction n generalizing i v29 with
  | zero =>
    have hb := beq_spec_gen_within .x6 .x0 (24 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (AB + 252)
    rw [hbeq] at hb
    have hbe := cpsBranchWithin_extend_code
      (adMemF 63, (AB + 252), (.BEQ .x6 .x0 (24 : BitVec 13))) hb
    have htaken := cpsBranchWithin_takenStripPure2 hbe (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion accBase bytes)
      (by pcFreeR) htaken
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          have hnlz : nlzWin bytes (o0 + i) 0 = 0 := by simp [nlzWin]
          simp only [hnlz, Nat.sub_zero, Nat.add_zero]
          have hq2 : (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
              ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
              ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion accBase bytes) sState := by xperm_chunked hq
          exact sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x29))) _ hq2) htf)
  | succ k ih =>
    have hb := beq_spec_gen_within .x6 .x0 (24 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (AB + 252)
    rw [hbeq] at hb
    have hbe := cpsBranchWithin_extend_code
      (adMemF 63, (AB + 252), (.BEQ .x6 .x0 (24 : BitVec 13))) hb
    have hnt := cpsBranchWithin_ntakenStripPure2 hbe (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ads_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion accBase bytes)
      (by pcFreeR) hnt
    have hlt : o0 + i < bytes.length := by omega
    by_cases hz : bytes[o0 + i]'hlt = (0 : BitVec 8)
    · have hbody := adBalStripZeroStep accBase bytes o0 i k v29 halign hlt hz hover hvalid
      have hih := ih (i + 1) (0 : Word) (by omega)
      have s1 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_chunked hp) hntf hbody
      have sfull := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_chunked hp) s1 hih
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
          (fun _ hq => by
            have hnlz : nlzWin bytes (o0 + i) (k + 1) =
                nlzWin bytes (o0 + (i + 1)) k + 1 := by
              simp only [nlzWin, hlt, ↓reduceDIte, hz, ↓reduceIte]
              ac_rfl
            have hsub : (k + 1) - nlzWin bytes (o0 + i) (k + 1) =
                k - nlzWin bytes (o0 + (i + 1)) k := by
              rw [hnlz]; omega
            have hadd : o0 + i + nlzWin bytes (o0 + i) (k + 1) =
                o0 + (i + 1) + nlzWin bytes (o0 + (i + 1)) k := by
              rw [hnlz]; omega
            simp only [hsub, hadd] at hq ⊢
            exact hq) sfull)
    · have hbr := adBalStripBreak accBase bytes o0 i (k + 1) v29 halign hlt hz hover hvalid
      have s1 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_chunked hp) hntf hbr
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
          (fun sState hq => by
            have hnlz : nlzWin bytes (o0 + i) (k + 1) = 0 := by
              simp only [nlzWin, hlt, ↓reduceDIte, hz, ↓reduceIte]
            simp only [hnlz, Nat.sub_zero, Nat.add_zero]
            have hq2 : (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
                ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
                ((.x29 : Reg) ↦ᵣ ((bytes[o0 + i]'hlt).zeroExtend 64)) **
                ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                bytesRegion accBase bytes) sState := by xperm_chunked hq
            have hq3 := sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (regIs_implies_regOwn .x29))) _ hq2
            exact hq3) s1)

#print axioms adBalStrip

end EvmAsm.Codegen.AccountDecodeSpec
