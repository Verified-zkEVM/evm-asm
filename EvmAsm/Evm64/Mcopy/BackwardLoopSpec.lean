/-
  EvmAsm.Evm64.Mcopy.BackwardLoopSpec

  The backward (high→low) copy loop of `MCOPY` (`base+28 → base+84`, program
  indices [7..13]).  This is the genuinely new loop shape for the codebase: the
  runtime enters it only for the forward-overlap case `srcOff < destOff <
  srcOff+len`, walking from the high end down so the still-unread source bytes
  are never clobbered.  Each iteration decrements both pointers FIRST, then
  reads/stores/decrements the counter.

  The read at source index `srcOff+len-1-k` still returns the ORIGINAL byte
  (`mcopyBwdContent_getElem_src`, valid because `srcOff ≤ destOff`), and the
  store advances the suffix window (`mcopyBwdContent_set`).  The loop closes by
  induction on the remaining count `n`, landing on `mcopyBwdContent … len`
  (= `mcopyResult`).
-/

import EvmAsm.Evm64.Mcopy.ForwardLoopSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Mcopy

open EvmAsm.Rv64

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-- General counter decrement: `x - 1` as words, for `x ≥ 1`. -/
theorem cc_word_dec (x : Nat) (h : 1 ≤ x) :
    BitVec.ofNat 64 x + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `signExtend12 (-1)` is the all-ones word `-1`. Hoisted to a named lemma so the
    (slow, negative-sign-extension) `decide` runs once here instead of inline in
    every pointer-decrement rewrite. -/
theorem cc_sE12_neg1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [hs]; rfl

/-- Pointer decrement: `base + ofNat (Y+1) + (-1) = base + ofNat Y`, proved by
    reassociation + the fast `toNat`-based `cc_word_dec` (NOT `bv_omega`, which
    bit-blasts the symbolic `ofNat` and dominated the backward-body elaboration
    at ~12 s per call — see the profiler note in the PR). -/
theorem ptr_dec (base : Word) (Y : Nat) :
    base + BitVec.ofNat 64 (Y + 1) + signExtend12 (-1 : BitVec 12) = base + BitVec.ofNat 64 Y := by
  rw [BitVec.add_assoc base (BitVec.ofNat 64 (Y + 1)) (signExtend12 (-1 : BitVec 12)),
      cc_word_dec (Y + 1) (by omega), Nat.add_sub_cancel]

/-! ## One backward iteration -/

/-- One iteration of the backward copy loop (`base+32 → base+52`, indices
    [8..12]): decrement both pointers, read the source byte `copied[len-1-k]`
    from the shared slab, store it at destination index `len-1-k`, decrement the
    counter.  `k` is the number of bytes already copied (from the high end). -/
theorem mcopy_bwd_body_spec_within
    (base memBase : Word) (destOff srcOff len k : Nat)
    (copied memBytes : List (BitVec 8)) (scratchOld : Word)
    (h_k : k < len)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_clen : copied.length = len)
    (h_copied : copied = (memBytes.drop srcOff).take len)
    (h_win : destOff + len ≤ memBytes.length)
    (h_sfits : srcOff + len ≤ memBytes.length)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true)
    (h_bwd : srcOff ≤ destOff) :
    cpsTripleWithin 5 (base + 32) (base + 52)
      (evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base)
      (((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (len - k)))) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + (len - k)))) **
       ((.x19 : Reg) ↦ᵣ scratchOld) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 (len - k)) **
       bytesRegion memBase (mcopyBwdContent memBytes copied destOff len k))
      (((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (len - (k + 1))))) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + (len - (k + 1))))) **
       ((.x19 : Reg) ↦ᵣ ((copied[len - 1 - k]'(by omega)).zeroExtend 64)) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 (len - (k + 1))) **
       bytesRegion memBase (mcopyBwdContent memBytes copied destOff len (k + 1))) := by
  have hlen : (mcopyBwdContent memBytes copied destOff len k).length = memBytes.length :=
    mcopyBwdContent_length memBytes copied destOff len k (by omega) h_clen (by omega)
  -- The source byte read equals `copied[len-1-k]`.
  have hread : (mcopyBwdContent memBytes copied destOff len k)[srcOff + len - 1 - k]'(by
        rw [hlen]; omega)
      = copied[len - 1 - k]'(by omega) := by
    rw [mcopyBwdContent_getElem_src memBytes copied destOff srcOff len k h_k h_clen
          (by omega) (by omega) h_bwd]
    have hidx : srcOff + len - 1 - k = srcOff + (len - 1 - k) := by omega
    simp only [hidx, h_copied]
    exact (sourceSlice_getElem memBytes srcOff len (len - 1 - k) (by omega) (by omega)).symm
  have hset : (mcopyBwdContent memBytes copied destOff len k).set (destOff + len - 1 - k)
        (((copied[len - 1 - k]'(by omega)).zeroExtend 64).truncate 8)
      = mcopyBwdContent memBytes copied destOff len (k + 1) := by
    rw [cc_trunc_zeroExtend]
    exact mcopyBwdContent_set memBytes copied destOff len k (copied[len - 1 - k]'(by omega))
      h_k h_clen (by omega) rfl
  set dstP := memBase + BitVec.ofNat 64 (destOff + (len - k)) with hdstP
  set srcP := memBase + BitVec.ofNat 64 (srcOff + (len - k)) with hsrcP
  -- [8] ADDI x17 x17 -1 : dstPtr := destOff + (len-(k+1)).
  have h8 := addi_spec_gen_same_within .x17 dstP (-1 : BitVec 12) (base + 32) (by decide)
  rw [show dstP + signExtend12 (-1 : BitVec 12)
        = memBase + BitVec.ofNat 64 (destOff + (len - (k + 1))) from by
        rw [hdstP, show destOff + (len - k) = destOff + (len - (k + 1)) + 1 from by omega]
        exact ptr_dec memBase (destOff + (len - (k + 1)))] at h8
  -- [9] ADDI x18 x18 -1 : srcPtr := srcOff + (len-(k+1)).
  have h9 := addi_spec_gen_same_within .x18 srcP (-1 : BitVec 12) (base + 36) (by decide)
  rw [show srcP + signExtend12 (-1 : BitVec 12)
        = memBase + BitVec.ofNat 64 (srcOff + (len - (k + 1))) from by
        rw [hsrcP, show srcOff + (len - k) = srcOff + (len - (k + 1)) + 1 from by omega]
        exact ptr_dec memBase (srcOff + (len - (k + 1)))] at h9
  -- [10] LBU x19 x18 0 : x19 := copied[len-1-k].zeroExtend 64.
  have h10 := bytesRegion_lbu_within .x19 .x18 memBase scratchOld (base + 40)
    (mcopyBwdContent memBytes copied destOff len k) (srcOff + len - 1 - k) (by decide) h_mem_align
    (by rw [hlen]; omega) (by omega) (h_mem_valid (srcOff + len - 1 - k) (by omega))
  rw [show memBase + BitVec.ofNat 64 (srcOff + len - 1 - k)
        = memBase + BitVec.ofNat 64 (srcOff + (len - (k + 1))) from by
        rw [show srcOff + len - 1 - k = srcOff + (len - (k + 1)) from by omega], hread] at h10
  -- [11] SB x17 x19 0 : store at destination index len-1-k.
  have h11 := bytesRegion_sb_within .x17 .x19 memBase ((copied[len - 1 - k]'(by omega)).zeroExtend 64)
    (base + 44) (mcopyBwdContent memBytes copied destOff len k) (destOff + len - 1 - k) h_mem_align
    (by rw [hlen]; omega) (by omega) (h_mem_valid (destOff + len - 1 - k) (by omega))
  rw [show memBase + BitVec.ofNat 64 (destOff + len - 1 - k)
        = memBase + BitVec.ofNat 64 (destOff + (len - (k + 1))) from by
        rw [show destOff + len - 1 - k = destOff + (len - (k + 1)) from by omega], hset] at h11
  -- [12] ADDI x16 x16 -1.
  have h12 := addi_spec_gen_same_within .x16 (BitVec.ofNat 64 (len - k)) (-1 : BitVec 12)
    (base + 48) (by decide)
  rw [cc_word_dec (len - k) (by omega),
      show (len - k) - 1 = len - (k + 1) from by omega] at h12
  -- Code-monotonicity for each index.
  have m8 : ∀ a i, CodeReq.singleton (base + 32) (.ADDI .x17 .x17 (-1 : BitVec 12)) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 8
      (base + 32) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have m9 : ∀ a i, CodeReq.singleton (base + 36) (.ADDI .x18 .x18 (-1 : BitVec 12)) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 9
      (base + 36) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have m10 : ∀ a i, CodeReq.singleton (base + 40) (.LBU .x19 .x18 0) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 10
      (base + 40) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have m11 : ∀ a i, CodeReq.singleton (base + 44) (.SB .x17 .x19 0) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 11
      (base + 44) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have m12 : ∀ a i, CodeReq.singleton (base + 48) (.ADDI .x16 .x16 (-1 : BitVec 12)) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 12
      (base + 48) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have h8e := cpsTripleWithin_extend_code m8 h8
  have h9e := cpsTripleWithin_extend_code m9 h9
  have h10e := cpsTripleWithin_extend_code m10 h10
  have h11e := cpsTripleWithin_extend_code m11 h11
  have h12e := cpsTripleWithin_extend_code m12 h12
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at h8e
  rw [show (base + 36 : Word) + 4 = base + 40 from by bv_omega] at h9e
  rw [show (base + 40 : Word) + 4 = base + 44 from by bv_omega] at h10e
  rw [show (base + 44 : Word) + 4 = base + 48 from by bv_omega] at h11e
  rw [show (base + 48 : Word) + 4 = base + 52 from by bv_omega] at h12e
  -- Frame each instruction with its complementary heap, sequence them.
  have f8 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ srcP) ** ((.x19 : Reg) ↦ᵣ scratchOld) **
     ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 (len - k)) **
     bytesRegion memBase (mcopyBwdContent memBytes copied destOff len k)) (by pcFreeR) h8e
  have f9 := cpsTripleWithin_frameR
    (((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (len - (k + 1))))) **
     ((.x19 : Reg) ↦ᵣ scratchOld) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 (len - k)) **
     bytesRegion memBase (mcopyBwdContent memBytes copied destOff len k)) (by pcFreeR) h9e
  have f10 := cpsTripleWithin_frameR
    (((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (len - (k + 1))))) **
     ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 (len - k))) (by pcFreeR) h10e
  have f11 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + (len - (k + 1))))) **
     ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 (len - k))) (by pcFreeR) h11e
  have f12 := cpsTripleWithin_frameR
    (((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (len - (k + 1))))) **
     ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + (len - (k + 1))))) **
     ((.x19 : Reg) ↦ᵣ ((copied[len - 1 - k]'(by omega)).zeroExtend 64)) **
     bytesRegion memBase (mcopyBwdContent memBytes copied destOff len (k + 1))) (by pcFreeR) h12e
  simp only [sepConj_assoc'] at f8 f9 f10 f11 f12
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f8 f9
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f10
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 f11
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 f12
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s4

/-! ## The backward loop closure -/

/-- The backward copy loop (`base+28 → base+84`, indices [7..13]) by induction on
    the remaining count `n` (with `k` bytes already copied, `k + n = len`).
    Landing state: window fully copied (`mcopyBwdContent … len`), counter zero. -/
theorem mcopy_bwd_loop_spec_within
    (base memBase : Word) (destOff srcOff len k n : Nat)
    (copied memBytes : List (BitVec 8)) (scratchV : Word)
    (h_kn : k + n = len)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_clen : copied.length = len)
    (h_copied : copied = (memBytes.drop srcOff).take len)
    (h_win : destOff + len ≤ memBytes.length)
    (h_sfits : srcOff + len ≤ memBytes.length)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true)
    (h_bwd : srcOff ≤ destOff) :
    cpsTripleWithin (7 * n + 1) (base + 28) (base + 84)
      (evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base)
      (((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + n))) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + n))) **
       ((.x19 : Reg) ↦ᵣ scratchV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (mcopyBwdContent memBytes copied destOff len k))
      (((.x16 : Reg) ↦ᵣ (0 : Word)) **
       ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) **
       regOwn .x19 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (mcopyBwdContent memBytes copied destOff len len)) := by
  have hmono7 : ∀ a i, CodeReq.singleton (base + 28) (.BEQ .x16 .x0 (BitVec.ofNat 13 56)) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 7
      (base + 28) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have hmono13 : ∀ a i, CodeReq.singleton (base + 52) (.JAL .x0 (-24 : BitVec 21)) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 13
      (base + 52) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have ha_t : (base + 28) + signExtend13 (BitVec.ofNat 13 56) = base + 84 := by
    rw [show signExtend13 (BitVec.ofNat 13 56) = (56 : Word) from by decide]; bv_omega
  have ha_f : (base + 28 : Word) + 4 = base + 32 := by bv_omega
  have ha_back : (base + 52) + signExtend21 (-24 : BitVec 21) = base + 28 := by
    rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega
  induction n generalizing k scratchV with
  | zero =>
    rw [show k = len from by omega]
    have hbeq := beq_spec_gen_within .x16 .x0 (BitVec.ofNat 13 56) (BitVec.ofNat 64 0)
      (0 : Word) (base + 28)
    rw [ha_t, ha_f] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono7 hbeq
    have htaken := cpsBranchWithin_takenStripPure2 hbeqe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) **
       ((.x19 : Reg) ↦ᵣ scratchV) **
       bytesRegion memBase (mcopyBwdContent memBytes copied destOff len len)) (by pcFreeR) htaken
    simp only [sepConj_assoc'] at htf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by
        simp only [Nat.add_zero] at hp; xperm_chunked hp)
        (fun sState hq => by
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          have hq2 : (((.x19 : Reg) ↦ᵣ scratchV) **
              ((.x16 : Reg) ↦ᵣ (0 : Word)) **
              ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
              ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion memBase (mcopyBwdContent memBytes copied destOff len len)) sState := by
            xperm_chunked hq
          have hq3 := sepConj_mono_left (regIs_implies_regOwn .x19) _ hq2
          xperm_chunked hq3) htf)
  | succ m ih =>
    have hk_lt : k < len := by omega
    have e1 : len - (k + 1) = m := by omega
    have e2 : len - 1 - k = m := by omega
    have e3 : len - k = m + 1 := by omega
    have hbeq := beq_spec_gen_within .x16 .x0 (BitVec.ofNat 13 56) (BitVec.ofNat 64 (m + 1))
      (0 : Word) (base + 28)
    rw [ha_t, ha_f] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono7 hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact cc_word_succ_ne_zero m (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (m + 1)))) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + (m + 1)))) **
       ((.x19 : Reg) ↦ᵣ scratchV) **
       bytesRegion memBase (mcopyBwdContent memBytes copied destOff len k)) (by pcFreeR) hnt
    have hbody := mcopy_bwd_body_spec_within base memBase destOff srcOff len k
      copied memBytes scratchV hk_lt h_mem_align h_clen h_copied h_win h_sfits
      h_mem_over h_mem_valid h_bwd
    -- Reconcile the body's `len-k`, `len-(k+1)`, `len-1-k` indices with the ih's `m`.
    simp only [e1, e2, e3] at hbody
    have hbodyf := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcFreeR) hbody
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 52)
    rw [ha_back] at hjal
    have hjale := cpsTripleWithin_extend_code hmono13 hjal
    have hih := ih (k + 1) ((copied[m]'(by omega)).zeroExtend 64) (by omega)
    simp only [sepConj_assoc'] at hntf hbodyf
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf hbodyf
    have hjalf := cpsTripleWithin_frameR
      (((.x19 : Reg) ↦ᵣ ((copied[m]'(by omega)).zeroExtend 64)) **
       ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + m))) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + m))) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 m) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (mcopyBwdContent memBytes copied destOff len (k + 1))) (by pcFreeR) hjale
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left']; xperm_chunked hp) s1 hjalf
    have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left'] at hp; xperm_chunked hp) s2 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hp => by xperm_chunked hp) s3)

end Mcopy
end EvmAsm.Evm64
