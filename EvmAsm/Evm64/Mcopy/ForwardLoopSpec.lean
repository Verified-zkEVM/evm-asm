/-
  EvmAsm.Evm64.Mcopy.ForwardLoopSpec

  The forward (low→high) copy loop of `MCOPY` (`base+56 → base+84`, program
  indices [14..20]).  Structurally the CALLDATACOPY copy loop, but with the
  out-of-bounds/zero arm removed (every MCOPY byte is in bounds after memory
  expansion) and — crucially — the source byte is read from the SAME
  `bytesRegion memBase` slab that the loop writes to.  The read still returns the
  ORIGINAL source byte because, in the forward direction, the runtime only
  chooses it when `destOff ≤ srcOff` or the ranges are disjoint
  (`mcopyFwdContent_getElem_src`).

  `mcopy_fwd_body_spec_within` is one iteration's straight-line body
  (`base+60 → base+80`: LBU, SB, ADDI×3); `mcopy_fwd_loop_spec_within` closes the
  loop by induction on the byte countdown `n = len - i`, landing on
  `mcopyFwdContent … len` (= `mcopyResult`).
-/

import EvmAsm.Evm64.Mcopy.Program
import EvmAsm.Evm64.Mcopy.Result
import EvmAsm.Evm64.StateAssertions
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPermChunked

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

/-! ## Counter arithmetic (shared with the backward loop) -/

/-- `(n+1) - 1 = n` as words (loop counter decrement). -/
theorem cc_word_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A successor counter `< 2^64` is nonzero as a word. -/
theorem cc_word_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

/-- The low byte of a zero-extended byte is that byte. -/
theorem cc_trunc_zeroExtend (b : BitVec 8) : (b.zeroExtend 64).truncate 8 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## One forward iteration -/

/-- One iteration of the forward copy loop (`base+60 → base+80`, indices
    [15..19]): read the source byte `copied[i]` from the shared memory slab,
    store it at destination index `i`, advance both pointers and the counter. -/
theorem mcopy_fwd_body_spec_within
    (base memBase : Word) (destOff srcOff len i : Nat)
    (copied memBytes : List (BitVec 8)) (cntV scratchOld : Word)
    (h_i : i < len)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_clen : copied.length = len)
    (h_copied : copied = (memBytes.drop srcOff).take len)
    (h_win : destOff + len ≤ memBytes.length)
    (h_sfits : srcOff + len ≤ memBytes.length)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true)
    (h_fwd : destOff ≤ srcOff ∨ srcOff + len ≤ destOff) :
    cpsTripleWithin 5 (base + 60) (base + 80)
      (evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base)
      (((.x19 : Reg) ↦ᵣ scratchOld) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x16 : Reg) ↦ᵣ cntV) **
       bytesRegion memBase (mcopyFwdContent memBytes copied destOff i))
      (((.x19 : Reg) ↦ᵣ ((copied[i]'(by omega)).zeroExtend 64)) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (i + 1)))) **
       ((.x16 : Reg) ↦ᵣ (cntV + signExtend12 (-1 : BitVec 12))) **
       bytesRegion memBase (mcopyFwdContent memBytes copied destOff (i + 1))) := by
  have hlen : (mcopyFwdContent memBytes copied destOff i).length = memBytes.length :=
    mcopyFwdContent_length memBytes copied destOff i (by omega) (by omega)
  -- The source byte read equals `copied[i]`.
  have hread : (mcopyFwdContent memBytes copied destOff i)[srcOff + i]'(by rw [hlen]; omega)
      = copied[i]'(by omega) := by
    rw [mcopyFwdContent_getElem_src memBytes copied destOff srcOff len i h_i h_clen
          (by omega) (by omega) h_fwd]
    simp only [h_copied]
    exact (sourceSlice_getElem memBytes srcOff len i h_i (by omega)).symm
  have hset : (mcopyFwdContent memBytes copied destOff i).set (destOff + i)
        (((copied[i]'(by omega)).zeroExtend 64).truncate 8)
      = mcopyFwdContent memBytes copied destOff (i + 1) := by
    rw [cc_trunc_zeroExtend]
    exact mcopyFwdContent_set memBytes copied destOff i (copied[i]'(by omega)) (by omega)
      (by omega) rfl
  set srcP := memBase + BitVec.ofNat 64 (srcOff + i) with hsrcP
  set destP := memBase + BitVec.ofNat 64 (destOff + i) with hdestP
  -- [15] LBU x19 x18 0 : x19 := copied[i].zeroExtend 64.
  have h15 := bytesRegion_lbu_within .x19 .x18 memBase scratchOld (base + 60)
    (mcopyFwdContent memBytes copied destOff i) (srcOff + i) (by decide) h_mem_align
    (by rw [hlen]; omega) (by omega) (h_mem_valid (srcOff + i) (by omega))
  rw [← hsrcP, hread] at h15
  -- [16] SB x17 x19 0 : store the byte at destination index i.
  have h16 := bytesRegion_sb_within .x17 .x19 memBase ((copied[i]'(by omega)).zeroExtend 64)
    (base + 64) (mcopyFwdContent memBytes copied destOff i) (destOff + i) h_mem_align
    (by rw [hlen]; omega) (by omega) (h_mem_valid (destOff + i) (by omega))
  rw [← hdestP, hset] at h16
  -- [17] ADDI x18 x18 1
  have h17 := addi_spec_gen_same_within .x18 srcP (1 : BitVec 12) (base + 68) (by decide)
  rw [show srcP + signExtend12 (1 : BitVec 12) = memBase + BitVec.ofNat 64 (srcOff + (i + 1)) from by
        rw [hsrcP, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at h17
  -- [18] ADDI x17 x17 1
  have h18 := addi_spec_gen_same_within .x17 destP (1 : BitVec 12) (base + 72) (by decide)
  rw [show destP + signExtend12 (1 : BitVec 12) = memBase + BitVec.ofNat 64 (destOff + (i + 1)) from by
        rw [hdestP, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at h18
  -- [19] ADDI x16 x16 -1
  have h19 := addi_spec_gen_same_within .x16 cntV (-1 : BitVec 12) (base + 76) (by decide)
  -- Code-monotonicity for each index.
  have m15 : ∀ a i, CodeReq.singleton (base + 60) (.LBU .x19 .x18 0) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 15
      (base + 60) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have m16 : ∀ a i, CodeReq.singleton (base + 64) (.SB .x17 .x19 0) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 16
      (base + 64) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have m17 : ∀ a i, CodeReq.singleton (base + 68) (.ADDI .x18 .x18 1) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 17
      (base + 68) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have m18 : ∀ a i, CodeReq.singleton (base + 72) (.ADDI .x17 .x17 1) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 18
      (base + 72) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have m19 : ∀ a i, CodeReq.singleton (base + 76) (.ADDI .x16 .x16 (-1 : BitVec 12)) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 19
      (base + 76) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have h15e := cpsTripleWithin_extend_code m15 h15
  have h16e := cpsTripleWithin_extend_code m16 h16
  have h17e := cpsTripleWithin_extend_code m17 h17
  have h18e := cpsTripleWithin_extend_code m18 h18
  have h19e := cpsTripleWithin_extend_code m19 h19
  rw [show (base + 60 : Word) + 4 = base + 64 from by bv_omega] at h15e
  rw [show (base + 64 : Word) + 4 = base + 68 from by bv_omega] at h16e
  rw [show (base + 68 : Word) + 4 = base + 72 from by bv_omega] at h17e
  rw [show (base + 72 : Word) + 4 = base + 76 from by bv_omega] at h18e
  rw [show (base + 76 : Word) + 4 = base + 80 from by bv_omega] at h19e
  -- Frame each instruction with its complementary heap and sequence them.
  have f15 := cpsTripleWithin_frameR
    (((.x17 : Reg) ↦ᵣ destP) ** ((.x16 : Reg) ↦ᵣ cntV)) (by pcFreeR) h15e
  have f16 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + i))) **
     ((.x16 : Reg) ↦ᵣ cntV)) (by pcFreeR) h16e
  have f17 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ ((copied[i]'(by omega)).zeroExtend 64)) **
     ((.x17 : Reg) ↦ᵣ destP) **
     ((.x16 : Reg) ↦ᵣ cntV) **
     bytesRegion memBase (mcopyFwdContent memBytes copied destOff (i + 1))) (by pcFreeR) h17e
  have f18 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ ((copied[i]'(by omega)).zeroExtend 64)) **
     ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x16 : Reg) ↦ᵣ cntV) **
     bytesRegion memBase (mcopyFwdContent memBytes copied destOff (i + 1))) (by pcFreeR) h18e
  have f19 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ ((copied[i]'(by omega)).zeroExtend 64)) **
     ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (i + 1)))) **
     bytesRegion memBase (mcopyFwdContent memBytes copied destOff (i + 1))) (by pcFreeR) h19e
  simp only [sepConj_assoc'] at f15 f16 f17 f18 f19
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f15 f16
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f17
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 f18
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 f19
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s4

/-! ## The forward loop closure -/

/-- The forward copy loop (`base+56 → base+84`, indices [14..20]) by induction on
    the byte countdown `n = len - i`.  Landing state: window fully copied
    (`mcopyFwdContent … len`), counter zero, scratch shed to ownership. -/
theorem mcopy_fwd_loop_spec_within
    (base memBase : Word) (destOff srcOff len n i : Nat)
    (copied memBytes : List (BitVec 8)) (scratchV : Word)
    (h_ni : i + n = len)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_clen : copied.length = len)
    (h_copied : copied = (memBytes.drop srcOff).take len)
    (h_win : destOff + len ≤ memBytes.length)
    (h_sfits : srcOff + len ≤ memBytes.length)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true)
    (h_fwd : destOff ≤ srcOff ∨ srcOff + len ≤ destOff) :
    cpsTripleWithin (7 * n + 1) (base + 56) (base + 84)
      (evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base)
      (((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x19 : Reg) ↦ᵣ scratchV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (mcopyFwdContent memBytes copied destOff i))
      (((.x16 : Reg) ↦ᵣ (0 : Word)) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + len))) **
       ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + len))) **
       regOwn .x19 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (mcopyFwdContent memBytes copied destOff len)) := by
  have hmono14 : ∀ a i, CodeReq.singleton (base + 56) (.BEQ .x16 .x0 (BitVec.ofNat 13 28)) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 14
      (base + 56) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have hmono20 : ∀ a i, CodeReq.singleton (base + 80) (.JAL .x0 (-24 : BitVec 21)) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 20
      (base + 80) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have ha_t : (base + 56) + signExtend13 (BitVec.ofNat 13 28) = base + 84 := by
    rw [show signExtend13 (BitVec.ofNat 13 28) = (28 : Word) from by decide]; bv_omega
  have ha_f : (base + 56 : Word) + 4 = base + 60 := by bv_omega
  have ha_back : (base + 80) + signExtend21 (-24 : BitVec 21) = base + 56 := by
    rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega
  induction n generalizing i scratchV with
  | zero =>
    have hilen : len = i := by omega
    subst hilen
    have hbeq := beq_spec_gen_within .x16 .x0 (BitVec.ofNat 13 28) (BitVec.ofNat 64 0)
      (0 : Word) (base + 56)
    rw [ha_t, ha_f] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono14 hbeq
    have htaken := cpsBranchWithin_takenStripPure2 hbeqe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + len))) **
       ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + len))) **
       ((.x19 : Reg) ↦ᵣ scratchV) **
       bytesRegion memBase (mcopyFwdContent memBytes copied destOff len)) (by pcFreeR) htaken
    simp only [sepConj_assoc'] at htf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          have hq2 : (((.x19 : Reg) ↦ᵣ scratchV) **
              ((.x16 : Reg) ↦ᵣ (0 : Word)) **
              ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + len))) **
              ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + len))) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion memBase (mcopyFwdContent memBytes copied destOff len)) sState := by
            xperm_chunked hq
          have hq3 := sepConj_mono_left (regIs_implies_regOwn .x19) _ hq2
          xperm_chunked hq3) htf)
  | succ k ih =>
    have hi_lt : i < len := by omega
    have hbeq := beq_spec_gen_within .x16 .x0 (BitVec.ofNat 13 28) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (base + 56)
    rw [ha_t, ha_f] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono14 hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact cc_word_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x19 : Reg) ↦ᵣ scratchV) **
       bytesRegion memBase (mcopyFwdContent memBytes copied destOff i)) (by pcFreeR) hnt
    have hbody := mcopy_fwd_body_spec_within base memBase destOff srcOff len i
      copied memBytes (BitVec.ofNat 64 (k + 1)) scratchV hi_lt h_mem_align h_clen h_copied
      h_win h_sfits h_mem_over h_mem_valid h_fwd
    rw [cc_word_succ_dec k] at hbody
    have hbodyf := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcFreeR) hbody
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 80)
    rw [ha_back] at hjal
    have hjale := cpsTripleWithin_extend_code hmono20 hjal
    have hih := ih (i + 1) ((copied[i]'(by omega)).zeroExtend 64) (by omega)
    simp only [sepConj_assoc'] at hntf hbodyf
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf hbodyf
    have hjalf := cpsTripleWithin_frameR
      (((.x19 : Reg) ↦ᵣ ((copied[i]'(by omega)).zeroExtend 64)) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (i + 1)))) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (mcopyFwdContent memBytes copied destOff (i + 1))) (by pcFreeR) hjale
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left']; xperm_chunked hp) s1 hjalf
    have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left'] at hp; xperm_chunked hp) s2 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hp => by xperm_chunked hp) s3)

end Mcopy
end EvmAsm.Evm64
