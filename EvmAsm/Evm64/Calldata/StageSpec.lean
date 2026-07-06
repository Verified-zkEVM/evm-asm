/-
  EvmAsm.Evm64.Calldata.StageSpec

  The verified staging step for the ARENA-FREE CALLDATALOAD (bead
  evm-asm-t1iqb, phase B): the ≤32-byte copy-with-zero-fill loop that
  materializes the CALLDATALOAD window into the aligned staging buffer.
  This is the copy-loop verification the CALLDATACOPY slice deferred
  (`CopySpec.lean` proved only the preamble).

  Option-1 source model (unaligned aliased calldata): the calldata is a
  byte-slice of the aligned parent-memory / input arena.  The precondition
  carries `bytesRegion memBase memBytes` with `memBase % 8 = 0`, the calldata
  pointer `cdp = memBase + cdByteOff`, and the calldata bytes are
  `data = (memBytes.drop cdByteOff).take len`.  The loop reads calldata byte
  `pos` at aligned index `cdByteOff + pos` and writes the aligned staging
  buffer `bytesRegion buf …`, so both memory accesses are 8-aligned dword
  cells even though `cdp` itself is unaligned.
-/

import EvmAsm.Evm64.Calldata.StageProgram
import EvmAsm.Evm64.Calldata.StageWindow
import EvmAsm.Evm64.Calldata.LoadDispatch
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPermChunked

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64
open EvmAsm.Evm64.EvmEnv (callDataPtrOff callDataLenOff)

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves (the base `pcFree`
    tactic handles only register atoms). -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-- The byte the loop copies at window index `i`: the real calldata byte at
    the normalized source position, or zero out of bounds. -/
theorem stage_copy_byte_eq
    (data memBytes : List (BitVec 8)) (cdByteOff normOff len i : Nat)
    (h_fits : cdByteOff + len ≤ memBytes.length)
    (h_data : data = (memBytes.drop cdByteOff).take len)
    (h_i : normOff + i < len) :
    (memBytes[cdByteOff + normOff + i]'(by omega)) =
      callDataByte data (normOff + i) := by
  subst h_data
  rw [callDataByte_of_lt (by rw [List.length_take, List.length_drop]; omega),
      List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- Buffer content after `i` window bytes have been copied: the copied prefix
    of `copyBytes` followed by the still-original suffix of the buffer. -/
def stageBufContent (copyBytes origBuf : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  copyBytes.take i ++ origBuf.drop i

theorem stageBufContent_length (copyBytes origBuf : List (BitVec 8)) (i : Nat)
    (h_cb : copyBytes.length = 32) (h_ob : origBuf.length = 64) (h_i : i ≤ 32) :
    (stageBufContent copyBytes origBuf i).length = 64 := by
  simp only [stageBufContent, List.length_append, List.length_take,
    List.length_drop, h_cb, h_ob]
  omega

/-- Writing `copyBytes[i]` at index `i` advances the buffer content from the
    `i`-prefix to the `(i+1)`-prefix. -/
theorem stageBufContent_set (copyBytes origBuf : List (BitVec 8)) (i : Nat)
    (v : BitVec 8) (h_i : i < copyBytes.length) (h_i2 : i < origBuf.length)
    (h_v : v = copyBytes[i]) :
    (stageBufContent copyBytes origBuf i).set i v
      = stageBufContent copyBytes origBuf (i + 1) := by
  apply List.ext_getElem
  · simp only [stageBufContent, List.length_set, List.length_append,
      List.length_take, List.length_drop]
    omega
  · intro j hj1 _
    have hlen : (stageBufContent copyBytes origBuf i).length = origBuf.length := by
      simp only [stageBufContent, List.length_append, List.length_take,
        List.length_drop]; omega
    rw [List.length_set, hlen] at hj1
    by_cases h_eq : j = i
    · subst h_eq
      rw [List.getElem_set_self]
      simp only [stageBufContent]
      rw [List.getElem_append_left (by rw [List.length_take]; omega),
          List.getElem_take]
      exact h_v
    · rw [List.getElem_set_ne (Ne.symm h_eq)]
      -- both sides agree away from i
      simp only [stageBufContent]
      by_cases h_lt : j < i
      · rw [List.getElem_append_left (by rw [List.length_take]; omega),
            List.getElem_append_left (by rw [List.length_take]; omega),
            List.getElem_take, List.getElem_take]
      · have h_gt : i < j := by omega
        have ht1 : (List.take i copyBytes).length = i := by
          rw [List.length_take]; omega
        have ht2 : (List.take (i + 1) copyBytes).length = i + 1 := by
          rw [List.length_take]; omega
        rw [List.getElem_append_right (by rw [ht1]; omega),
            List.getElem_append_right (by rw [ht2]; omega),
            List.getElem_drop, List.getElem_drop]
        congr 1
        omega

/-- Peel a pure `⌜fact⌝` from the right of the precondition into an ambient
    hypothesis (same as `LoadSpec.cpsTripleWithin_of_pure_imp`). -/
private theorem cpsTripleWithin_of_pure_imp
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {fact : Prop}
    (h : fact → cpsTripleWithin nSteps entry exit_ cr P Q) :
    cpsTripleWithin nSteps entry exit_ cr (P ** ⌜fact⌝) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, hpq⟩ := hPR
  obtain ⟨h1, h2, hd, hunion, hPF, hR_⟩ := hpq
  have hpf := (sepConj_pure_right h1).1 hPF
  exact h hpf.2 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hunion, hpf.1, hR_⟩ hpc

/-- `BitVec.ult` of two `memBase`-relative pointers reflects the `Nat` order of
    their offsets, when neither addition wraps. -/
theorem stage_ult_offsets (memBase : Word) (a b : Nat)
    (ha : memBase.toNat + a < 2 ^ 64) (hb : memBase.toNat + b < 2 ^ 64)
    (ha' : a < 2 ^ 64) (hb' : b < 2 ^ 64) :
    BitVec.ult (memBase + BitVec.ofNat 64 a) (memBase + BitVec.ofNat 64 b)
      = decide (a < b) := by
  have hx : (memBase + BitVec.ofNat 64 a).toNat = memBase.toNat + a := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha',
        Nat.mod_eq_of_lt ha]
  have hy : (memBase + BitVec.ofNat 64 b).toNat = memBase.toNat + b := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb',
        Nat.mod_eq_of_lt hb]
  simp only [BitVec.ult, hx, hy]
  exact decide_eq_decide.mpr (by omega)

/-- One iteration of the staging copy loop (`base+72 → base+100`, indices
    [18..24]): default the byte to zero, load the calldata byte when in bounds,
    store it into the buffer, and advance the source/destination pointers and
    the counter.  The inner `BGEU` out-of-bounds branch merges: in both arms the
    stored byte is `copyBytes[i]` (the real byte in bounds, zero past the end),
    so the buffer content advances from the `i`-prefix to the `(i+1)`-prefix. -/
theorem stage_body_spec_within
    (base memBase buf : Word) (cdByteOff normOff len i : Nat)
    (data memBytes origBuf : List (BitVec 8)) (cntV x28Old : Word)
    (h_i : i < 32)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_buf_align : buf.toNat % 8 = 0)
    (h_fits : cdByteOff + len ≤ memBytes.length)
    (h_data : data = (memBytes.drop cdByteOff).take len)
    (h_normOff_le : normOff ≤ len)
    (h_mem_over : memBase.toNat + memBytes.length + 32 ≤ 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true)
    (h_buf_over : buf.toNat + 64 < 2 ^ 64)
    (h_buf_valid : ∀ k, k < 64 → isValidByteAccess (buf + BitVec.ofNat 64 k) = true)
    (h_origBuf_len : origBuf.length = 64)
    (h_cb : (callDataCopyBytes data normOff 32)[i]'(by
      simp only [callDataCopyBytes_length]; omega) = cbi) :
    cpsTripleWithin 7 (base + 72) (base + 100) (evm_calldataload_staged_code base)
      ((.x28 ↦ᵣ x28Old) **
       (.x30 ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + normOff + i))) **
       (.x6 ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + len))) **
       (.x31 ↦ᵣ (buf + BitVec.ofNat 64 i)) **
       (.x29 ↦ᵣ cntV) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion buf (stageBufContent (callDataCopyBytes data normOff 32) origBuf i) **
       bytesRegion memBase memBytes)
      ((.x28 ↦ᵣ (cbi.zeroExtend 64)) **
       (.x30 ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + normOff + (i + 1)))) **
       (.x6 ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + len))) **
       (.x31 ↦ᵣ (buf + BitVec.ofNat 64 (i + 1))) **
       (.x29 ↦ᵣ (cntV + signExtend12 (-1 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion buf (stageBufContent (callDataCopyBytes data normOff 32) origBuf (i + 1)) **
       bytesRegion memBase memBytes) := by
  set copyBytes := callDataCopyBytes data normOff 32 with hcb_def
  -- Bounds for the pointer arithmetic / branch comparison.
  have hmemlen_lt : memBytes.length < 2 ^ 64 := by omega
  have hk_lt : cdByteOff + normOff + i < 2 ^ 64 := by omega
  have hend_lt : cdByteOff + len < 2 ^ 64 := by omega
  have h_mem_k : memBase.toNat + (cdByteOff + normOff + i) < 2 ^ 64 := by omega
  have h_mem_end : memBase.toNat + (cdByteOff + len) < 2 ^ 64 := by omega
  -- The window byte the loop stores at index `i`.
  have hcbi_val : cbi = callDataByte data (normOff + i) := by
    rw [← h_cb]; exact callDataCopyBytes_get h_i
  have hbuf_i_lt : i < (stageBufContent copyBytes origBuf i).length := by
    rw [stageBufContent_length copyBytes origBuf i (by simp [hcb_def]) h_origBuf_len
      (by omega)]; omega
  have hcb_len : copyBytes.length = 32 := by simp [hcb_def]
  -- Branch condition: srcPtr ≥ end  ⟺  normOff + i ≥ len.
  have hult := stage_ult_offsets memBase (cdByteOff + normOff + i) (cdByteOff + len)
    h_mem_k h_mem_end hk_lt hend_lt
  -- The buffer content after this write.
  have hset : (stageBufContent copyBytes origBuf i).set i cbi
      = stageBufContent copyBytes origBuf (i + 1) :=
    stageBufContent_set copyBytes origBuf i cbi (by omega) (by omega) h_cb.symm
  -- Abbreviations for the pointers threaded through the branch/segment
  -- (declared BEFORE h18 so `runBlock` is not followed by a `set` token,
  -- which its variadic argument parser would otherwise consume).
  set srcP := memBase + BitVec.ofNat 64 (cdByteOff + normOff + i) with hsrcP
  set endP := memBase + BitVec.ofNat 64 (cdByteOff + len) with hendP
  set dstP := buf + BitVec.ofNat 64 i with hdstP
  have hbuf_align' : buf.toNat % 8 = 0 := h_buf_align
  -- [18] base+72 → base+76 : x28 := 0.
  have h18 : cpsTripleWithin 1 (base + 72) (base + 76)
      (evm_calldataload_staged_code base)
      ((.x0 ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ x28Old))
      ((.x0 ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ (0 : Word))) := by
    have h := addi_spec_gen_within .x28 .x0 x28Old (0 : Word) (0 : BitVec 12)
      (base + 72) (by decide)
    rw [show (0 : Word) + signExtend12 (0 : BitVec 12) = 0 from by
      rw [signExtend12_0]; bv_omega] at h
    runBlock h
  -- [19] BGEU x30 x6 : base+76 → taken base+84 (¬ult), ntaken base+80 (ult).
  have hbgeu0 := bgeu_spec_gen_within .x30 .x6 (8 : BitVec 13) srcP endP (base + 76)
  rw [show (base + 76) + signExtend13 (8 : BitVec 13) = base + 84 from by
        rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]; bv_omega,
      show (base + 76 : Word) + 4 = base + 80 from by bv_omega] at hbgeu0
  have hmono19 : ∀ a i, CodeReq.singleton (base + 76) (.BGEU .x30 .x6 (8 : BitVec 13)) a = some i
      → evm_calldataload_staged_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base evm_calldataload_staged 19
      (base + 76) (by rw [evm_calldataload_staged_length]; norm_num)
      (by rw [evm_calldataload_staged_length]; norm_num) (by rfl))
  -- Extend the (unframed) branch to the full staged code.
  have hbgeu0e := cpsBranchWithin_extend_code hmono19 hbgeu0
  -- x28 = cbi.zeroExtend 64, whichever branch is taken.
  have htrunc : (cbi.zeroExtend 64).truncate 8 = cbi := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have := cbi.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hpre_sb : cpsTripleWithin 2 (base + 76) (base + 84)
      (evm_calldataload_staged_code base)
      (((.x30 : Reg) ↦ᵣ srcP) ** ((.x6 : Reg) ↦ᵣ endP) ** ((.x28 : Reg) ↦ᵣ (0 : Word)) **
       ((.x31 : Reg) ↦ᵣ dstP) ** ((.x29 : Reg) ↦ᵣ cntV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion buf (stageBufContent copyBytes origBuf i) ** bytesRegion memBase memBytes)
      (((.x28 : Reg) ↦ᵣ (cbi.zeroExtend 64)) ** ((.x30 : Reg) ↦ᵣ srcP) **
       ((.x6 : Reg) ↦ᵣ endP) ** ((.x31 : Reg) ↦ᵣ dstP) ** ((.x29 : Reg) ↦ᵣ cntV) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion buf (stageBufContent copyBytes origBuf i) ** bytesRegion memBase memBytes) := by
    by_cases h_ib : normOff + i < len
    · -- in-bounds: bgeu NOT taken; LBU loads memBytes[cdByteOff+normOff+i] = cbi.
      have hnt := cpsBranchWithin_ntakenStripPure2 hbgeu0e (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        have hnu := ((sepConj_pure_right _).1 hQ).2
        rw [hult] at hnu
        exact hnu (by simp only [decide_eq_true_eq]; omega))
      have hntf := cpsTripleWithin_frameR
        (((.x28 : Reg) ↦ᵣ (0 : Word)) ** ((.x31 : Reg) ↦ᵣ dstP) **
         ((.x29 : Reg) ↦ᵣ cntV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion buf (stageBufContent copyBytes origBuf i) ** bytesRegion memBase memBytes)
        (by pcFreeR) hnt
      have hlbu := bytesRegion_lbu_within .x28 .x30 memBase (0 : Word) (base + 80)
        memBytes (cdByteOff + normOff + i) (by decide) h_mem_align (by omega) (by omega)
        (h_mem_valid (cdByteOff + normOff + i) (by omega))
      have hmemk : memBytes[cdByteOff + normOff + i]'(by omega) = cbi := by
        rw [hcbi_val]
        exact stage_copy_byte_eq data memBytes cdByteOff normOff len i h_fits h_data h_ib
      rw [← hsrcP] at hlbu
      rw [show memBytes[cdByteOff + normOff + i]'(by omega) = cbi from hmemk,
          show (base + 80 : Word) + 4 = base + 84 from by bv_omega] at hlbu
      have hmono20 : ∀ a i, CodeReq.singleton (base + 80) (.LBU .x28 .x30 0) a = some i
          → evm_calldataload_staged_code base a = some i :=
        CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base evm_calldataload_staged 20
          (base + 80) (by rw [evm_calldataload_staged_length]; norm_num)
          (by rw [evm_calldataload_staged_length]; norm_num) (by rfl))
      have hlbu := cpsTripleWithin_extend_code hmono20 hlbu
      have hlbuf := cpsTripleWithin_frameR
        (((.x6 : Reg) ↦ᵣ endP) ** ((.x31 : Reg) ↦ᵣ dstP) ** ((.x29 : Reg) ↦ᵣ cntV) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion buf (stageBufContent copyBytes origBuf i)) (by pcFreeR) hlbu
      simp only [sepConj_assoc'] at hntf hlbuf
      have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf hlbuf
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hp => by xperm_chunked hp) hseq
    · -- out of bounds: bgeu taken; x28 stays 0 = cbi.zeroExtend 64.
      have hcbi0 : cbi = 0 := by
        rw [hcbi_val]; apply callDataByte_of_ge
        rw [h_data, List.length_take, List.length_drop]; omega
      have ht := cpsBranchWithin_takenStripPure2 hbgeu0e (fun hp hQf => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQf
        have hu := ((sepConj_pure_right _).1 hQ).2
        rw [hult] at hu; rw [decide_eq_true_eq] at hu; omega)
      have htf := cpsTripleWithin_frameR
        (((.x28 : Reg) ↦ᵣ (0 : Word)) ** ((.x31 : Reg) ↦ᵣ dstP) **
         ((.x29 : Reg) ↦ᵣ cntV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion buf (stageBufContent copyBytes origBuf i) ** bytesRegion memBase memBytes)
        (by pcFreeR) ht
      simp only [sepConj_assoc'] at htf
      refine cpsTripleWithin_mono_nSteps (by decide)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => ?_) htf)
      rw [hcbi0, show BitVec.zeroExtend 64 (0 : BitVec 8) = 0 from by decide]
      xperm_chunked hq
  -- hshared : base+84 → base+100 : store cbi, advance src/dst/cnt.
  have hshared : cpsTripleWithin 4 (base + 84) (base + 100)
      (evm_calldataload_staged_code base)
      (((.x28 : Reg) ↦ᵣ (cbi.zeroExtend 64)) ** ((.x30 : Reg) ↦ᵣ srcP) **
       ((.x6 : Reg) ↦ᵣ endP) ** ((.x31 : Reg) ↦ᵣ dstP) ** ((.x29 : Reg) ↦ᵣ cntV) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion buf (stageBufContent copyBytes origBuf i) ** bytesRegion memBase memBytes)
      (((.x28 : Reg) ↦ᵣ (cbi.zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + normOff + (i + 1)))) **
       ((.x6 : Reg) ↦ᵣ endP) ** ((.x31 : Reg) ↦ᵣ (buf + BitVec.ofNat 64 (i + 1))) **
       ((.x29 : Reg) ↦ᵣ (cntV + signExtend12 (-1 : BitVec 12))) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion buf (stageBufContent copyBytes origBuf (i + 1)) **
       bytesRegion memBase memBytes) := by
    -- [21] SB x31 x28 0
    have h21 := bytesRegion_sb_within .x31 .x28 buf (cbi.zeroExtend 64) (base + 84)
      (stageBufContent copyBytes origBuf i) i hbuf_align' hbuf_i_lt
      (by omega) (h_buf_valid i (by omega))
    rw [← hdstP, htrunc, hset] at h21
    -- [22] ADDI x30 x30 1
    have h22 := addi_spec_gen_same_within .x30 srcP (1 : BitVec 12) (base + 88) (by decide)
    rw [show srcP + signExtend12 (1 : BitVec 12)
        = memBase + BitVec.ofNat 64 (cdByteOff + normOff + (i + 1)) from by
          rw [hsrcP, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
          bv_omega] at h22
    -- [23] ADDI x31 x31 1
    have h23 := addi_spec_gen_same_within .x31 dstP (1 : BitVec 12) (base + 92) (by decide)
    rw [show dstP + signExtend12 (1 : BitVec 12)
        = buf + BitVec.ofNat 64 (i + 1) from by
          rw [hdstP, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
          bv_omega] at h23
    -- [24] ADDI x29 x29 -1
    have h24 := addi_spec_gen_same_within .x29 cntV (-1 : BitVec 12) (base + 96) (by decide)
    have m21 : ∀ a i, CodeReq.singleton (base + 84) (.SB .x31 .x28 0) a = some i
        → evm_calldataload_staged_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base evm_calldataload_staged 21
        (base + 84) (by rw [evm_calldataload_staged_length]; norm_num)
        (by rw [evm_calldataload_staged_length]; norm_num) (by rfl))
    have h21 := cpsTripleWithin_extend_code m21 h21
    have m22 : ∀ a i, CodeReq.singleton (base + 88) (.ADDI .x30 .x30 1) a = some i
        → evm_calldataload_staged_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base evm_calldataload_staged 22
        (base + 88) (by rw [evm_calldataload_staged_length]; norm_num)
        (by rw [evm_calldataload_staged_length]; norm_num) (by rfl))
    have h22 := cpsTripleWithin_extend_code m22 h22
    have m23 : ∀ a i, CodeReq.singleton (base + 92) (.ADDI .x31 .x31 1) a = some i
        → evm_calldataload_staged_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base evm_calldataload_staged 23
        (base + 92) (by rw [evm_calldataload_staged_length]; norm_num)
        (by rw [evm_calldataload_staged_length]; norm_num) (by rfl))
    have h23 := cpsTripleWithin_extend_code m23 h23
    have m24 : ∀ a i, CodeReq.singleton (base + 96) (.ADDI .x29 .x29 (-1 : BitVec 12)) a = some i
        → evm_calldataload_staged_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base evm_calldataload_staged 24
        (base + 96) (by rw [evm_calldataload_staged_length]; norm_num)
        (by rw [evm_calldataload_staged_length]; norm_num) (by rfl))
    have h24 := cpsTripleWithin_extend_code m24 h24
    rw [show (base + 84 : Word) + 4 = base + 88 from by bv_omega] at h21
    rw [show (base + 88 : Word) + 4 = base + 92 from by bv_omega] at h22
    rw [show (base + 92 : Word) + 4 = base + 96 from by bv_omega] at h23
    rw [show (base + 96 : Word) + 4 = base + 100 from by bv_omega] at h24
    have fh21 := cpsTripleWithin_frameR
      (((.x30 : Reg) ↦ᵣ srcP) ** ((.x6 : Reg) ↦ᵣ endP) ** ((.x29 : Reg) ↦ᵣ cntV) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion memBase memBytes) (by pcFreeR) h21
    have fh22 := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (cbi.zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ endP) **
       ((.x31 : Reg) ↦ᵣ dstP) ** ((.x29 : Reg) ↦ᵣ cntV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion buf (stageBufContent copyBytes origBuf (i + 1)) **
       bytesRegion memBase memBytes) (by pcFreeR) h22
    have fh23 := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (cbi.zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + normOff + (i + 1)))) **
       ((.x6 : Reg) ↦ᵣ endP) ** ((.x29 : Reg) ↦ᵣ cntV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion buf (stageBufContent copyBytes origBuf (i + 1)) **
       bytesRegion memBase memBytes) (by pcFreeR) h23
    have fh24 := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (cbi.zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + normOff + (i + 1)))) **
       ((.x6 : Reg) ↦ᵣ endP) ** ((.x31 : Reg) ↦ᵣ (buf + BitVec.ofNat 64 (i + 1))) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion buf (stageBufContent copyBytes origBuf (i + 1)) **
       bytesRegion memBase memBytes) (by pcFreeR) h24
    simp only [sepConj_assoc'] at fh21 fh22 fh23 fh24
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) fh21 fh22
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 fh23
    have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 fh24
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) s3
  -- Compose: [18] ; (branch→base+84) ; [21..24].
  have hbody := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hpre_sb hshared
  have hfull := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    (cpsTripleWithin_frameR
      (((.x30 : Reg) ↦ᵣ srcP) ** ((.x6 : Reg) ↦ᵣ endP) ** ((.x31 : Reg) ↦ᵣ dstP) **
       ((.x29 : Reg) ↦ᵣ cntV) **
       bytesRegion buf (stageBufContent copyBytes origBuf i) ** bytesRegion memBase memBytes)
      (by pcFreeR) h18) hbody
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hp => by xperm_chunked hp)
    hfull

/-- `(n+1) - 1 = n` as words (loop counter decrement). -/
private theorem word_ofNat_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A successor counter `< 2^64` is nonzero as a word. -/
private theorem word_ofNat_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

/-- The staging copy loop closure (`base+68 → base+104`, indices [17..25]) by
    induction on the countdown `n = 32 - i`. -/
theorem stage_copy_loop_spec_within
    (base memBase buf : Word) (cdByteOff normOff len : Nat)
    (data memBytes origBuf : List (BitVec 8)) (n i : Nat) (x28v : Word)
    (h_ni : i + n = 32)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_buf_align : buf.toNat % 8 = 0)
    (h_fits : cdByteOff + len ≤ memBytes.length)
    (h_data : data = (memBytes.drop cdByteOff).take len)
    (h_normOff_le : normOff ≤ len)
    (h_mem_over : memBase.toNat + memBytes.length + 32 ≤ 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true)
    (h_buf_over : buf.toNat + 64 < 2 ^ 64)
    (h_buf_valid : ∀ k, k < 64 → isValidByteAccess (buf + BitVec.ofNat 64 k) = true)
    (h_origBuf_len : origBuf.length = 64) :
    cpsTripleWithin (9 * n + 1) (base + 68) (base + 104)
      (evm_calldataload_staged_code base)
      (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x30 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + normOff + i))) **
       ((.x6 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + len))) **
       ((.x31 : Reg) ↦ᵣ (buf + BitVec.ofNat 64 i)) **
       ((.x28 : Reg) ↦ᵣ x28v) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion buf (stageBufContent (callDataCopyBytes data normOff 32) origBuf i) **
       bytesRegion memBase memBytes)
      (((.x29 : Reg) ↦ᵣ (0 : Word)) **
       ((.x30 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + normOff + 32))) **
       ((.x6 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + len))) **
       ((.x31 : Reg) ↦ᵣ (buf + BitVec.ofNat 64 32)) **
       regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion buf (stageBufContent (callDataCopyBytes data normOff 32) origBuf 32) **
       bytesRegion memBase memBytes) := by
  set copyBytes := callDataCopyBytes data normOff 32 with hcb_def
  have hmono17 : ∀ a i, CodeReq.singleton (base + 68) (.BEQ .x29 .x0 (36 : BitVec 13)) a = some i
      → evm_calldataload_staged_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base evm_calldataload_staged 17
      (base + 68) (by rw [evm_calldataload_staged_length]; norm_num)
      (by rw [evm_calldataload_staged_length]; norm_num) (by rfl))
  have hmono25 : ∀ a i, CodeReq.singleton (base + 100) (.JAL .x0 (-32 : BitVec 21)) a = some i
      → evm_calldataload_staged_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base evm_calldataload_staged 25
      (base + 100) (by rw [evm_calldataload_staged_length]; norm_num)
      (by rw [evm_calldataload_staged_length]; norm_num) (by rfl))
  have ha_t : (base + 68) + signExtend13 (36 : BitVec 13) = base + 104 := by
    rw [show signExtend13 (36 : BitVec 13) = (36 : Word) from by decide]; bv_omega
  have ha_f : (base + 68 : Word) + 4 = base + 72 := by bv_omega
  have ha_back : (base + 100) + signExtend21 (-32 : BitVec 21) = base + 68 := by
    rw [show signExtend21 (-32 : BitVec 21) = (-32 : Word) from by decide]; bv_omega
  induction n generalizing i x28v with
  | zero =>
    have hi32 : i = 32 := by omega
    subst hi32
    have hbeq := beq_spec_gen_within .x29 .x0 (36 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (base + 68)
    rw [ha_t, ha_f] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono17 hbeq
    have htaken := cpsBranchWithin_takenStripPure2 hbeqe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x30 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + normOff + 32))) **
       ((.x6 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + len))) **
       ((.x31 : Reg) ↦ᵣ (buf + BitVec.ofNat 64 32)) ** ((.x28 : Reg) ↦ᵣ x28v) **
       bytesRegion buf (stageBufContent copyBytes origBuf 32) **
       bytesRegion memBase memBytes) (by pcFreeR) htaken
    simp only [sepConj_assoc'] at htf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          have hq2 : (((.x28 : Reg) ↦ᵣ x28v) **
              ((.x29 : Reg) ↦ᵣ (0 : Word)) **
              ((.x30 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + normOff + 32))) **
              ((.x6 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + len))) **
              ((.x31 : Reg) ↦ᵣ (buf + BitVec.ofNat 64 32)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion buf (stageBufContent copyBytes origBuf 32) **
              bytesRegion memBase memBytes) sState := by xperm_chunked hq
          have hq3 := sepConj_mono_left (regIs_implies_regOwn .x28) _ hq2
          xperm_chunked hq3) htf)
  | succ k ih =>
    have hi_lt : i < 32 := by omega
    have hbeq := beq_spec_gen_within .x29 .x0 (36 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (base + 68)
    rw [ha_t, ha_f] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono17 hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact word_ofNat_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x30 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + normOff + i))) **
       ((.x6 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + len))) **
       ((.x31 : Reg) ↦ᵣ (buf + BitVec.ofNat 64 i)) ** ((.x28 : Reg) ↦ᵣ x28v) **
       bytesRegion buf (stageBufContent copyBytes origBuf i) **
       bytesRegion memBase memBytes) (by pcFreeR) hnt
    have hbody := stage_body_spec_within base memBase buf cdByteOff normOff len i data
      memBytes origBuf (BitVec.ofNat 64 (k + 1)) x28v hi_lt h_mem_align h_buf_align
      h_fits h_data h_normOff_le h_mem_over h_mem_valid h_buf_over h_buf_valid
      h_origBuf_len rfl
    rw [word_ofNat_succ_dec k] at hbody
    have hjal := jal_x0_spec_gen_within (-32 : BitVec 21) (base + 100)
    rw [ha_back] at hjal
    have hjale := cpsTripleWithin_extend_code hmono25 hjal
    have hih := ih (i + 1) ((copyBytes[i]'(by rw [hcb_def, callDataCopyBytes_length]; omega)).zeroExtend 64) (by omega)
    -- Compose guard ; body ; jal ; IH.
    simp only [sepConj_assoc'] at hntf
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf hbody
    have hjalf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ ((copyBytes[i]'(by rw [hcb_def, callDataCopyBytes_length]; omega)).zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + normOff + (i + 1)))) **
       ((.x6 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (cdByteOff + len))) **
       ((.x31 : Reg) ↦ᵣ (buf + BitVec.ofNat 64 (i + 1))) **
       ((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion buf (stageBufContent copyBytes origBuf (i + 1)) **
       bytesRegion memBase memBytes) (by pcFreeR) hjale
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left']; xperm_chunked hp) s1 hjalf
    have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left'] at hp; xperm_chunked hp) s2 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hp => by xperm_chunked hp) s3)


/-- The normalized source offset: `offLo` in bounds, `len` (all-OOB) on the
    skip path. -/
def stageNormW (offsetWord : EvmWord) (lenW : Word) : Word :=
  if calldataload_oobFlag offsetWord lenW = 0 then offsetWord.getLimbN 0 else lenW

/-- The staging setup preamble ([0..16], `base → base+68`). -/
theorem evm_calldataload_stage_setup_spec_within
    (base envAddr sp cdp lenW buf : Word) (offsetWord : EvmWord)
    (x5o x6o x7o x28o x29o x30o x31o : Word) :
    cpsTripleWithin 17 base (base + 68) (evm_calldataload_staged_code base)
      (((.x20 : Reg) ↦ᵣ envAddr) ** ((.x12 : Reg) ↦ᵣ sp) ** ((.x14 : Reg) ↦ᵣ buf) **
       ((.x5 : Reg) ↦ᵣ x5o) ** ((.x6 : Reg) ↦ᵣ x6o) ** ((.x7 : Reg) ↦ᵣ x7o) **
       ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) ** ((.x30 : Reg) ↦ᵣ x30o) **
       ((.x31 : Reg) ↦ᵣ x31o) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ cdp) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ lenW) **
       (sp ↦ₘ offsetWord.getLimbN 0) ** ((sp + 8) ↦ₘ offsetWord.getLimbN 1) **
       ((sp + 16) ↦ₘ offsetWord.getLimbN 2) ** ((sp + 24) ↦ₘ offsetWord.getLimbN 3))
      (((.x20 : Reg) ↦ᵣ envAddr) ** ((.x12 : Reg) ↦ᵣ sp) ** ((.x14 : Reg) ↦ᵣ buf) **
       ((.x5 : Reg) ↦ᵣ cdp) ** ((.x6 : Reg) ↦ᵣ (cdp + lenW)) **
       ((.x7 : Reg) ↦ᵣ stageNormW offsetWord lenW) **
       ((.x28 : Reg) ↦ᵣ calldataload_oobFlag offsetWord lenW) **
       ((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 32) **
       ((.x30 : Reg) ↦ᵣ (cdp + stageNormW offsetWord lenW)) **
       ((.x31 : Reg) ↦ᵣ buf) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ cdp) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ lenW) **
       (sp ↦ₘ offsetWord.getLimbN 0) ** ((sp + 8) ↦ₘ offsetWord.getLimbN 1) **
       ((sp + 16) ↦ₘ offsetWord.getLimbN 2) ** ((sp + 24) ↦ₘ offsetWord.getLimbN 3)) := by
  set l0 := offsetWord.getLimbN 0 with hl0
  set l1 := offsetWord.getLimbN 1 with hl1
  set l2 := offsetWord.getLimbN 2 with hl2
  set l3 := offsetWord.getLimbN 3 with hl3
  -- Straight prefix [0..10]: base → base+44.
  have hpre : cpsTripleWithin 11 base (base + 44) (evm_calldataload_staged_code base)
      (((.x20 : Reg) ↦ᵣ envAddr) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((.x5 : Reg) ↦ᵣ x5o) ** ((.x6 : Reg) ↦ᵣ x6o) ** ((.x7 : Reg) ↦ᵣ x7o) **
       ((.x28 : Reg) ↦ᵣ x28o) ** ((.x30 : Reg) ↦ᵣ x30o) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ cdp) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ lenW) **
       (sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) ** ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3))
      (((.x20 : Reg) ↦ᵣ envAddr) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((.x5 : Reg) ↦ᵣ cdp) ** ((.x6 : Reg) ↦ᵣ lenW) ** ((.x7 : Reg) ↦ᵣ l0) **
       ((.x28 : Reg) ↦ᵣ calldataload_oobFlag offsetWord lenW) **
       ((.x30 : Reg) ↦ᵣ calldataload_oobBit l0 lenW) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ cdp) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ lenW) **
       (sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) ** ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3)) := by
    have h0 := ld_spec_gen_within .x5 .x20 envAddr x5o cdp (BitVec.ofNat 12 callDataPtrOff) base (by decide)
    simp only [signExtend12_callDataPtrOff] at h0
    have h1 := ld_spec_gen_within .x6 .x20 envAddr x6o lenW (BitVec.ofNat 12 callDataLenOff) (base + 4) (by decide)
    simp only [signExtend12_callDataLenOff] at h1
    have h2 := ld_spec_gen_within .x7 .x12 sp x7o l0 (0 : BitVec 12) (base + 8) (by decide)
    simp only [signExtend12_0] at h2
    have h3 := ld_spec_gen_within .x28 .x12 sp x28o l1 (8 : BitVec 12) (base + 12) (by decide)
    simp only [signExtend12_8] at h3
    have h4 := ld_spec_gen_within .x30 .x12 sp x30o l2 (16 : BitVec 12) (base + 16) (by decide)
    simp only [signExtend12_16] at h4
    have h5 := or_spec_gen_rd_eq_rs1_within .x28 .x30 l1 l2 (base + 20) (by decide)
    have h6 := ld_spec_gen_within .x30 .x12 sp l2 l3 (24 : BitVec 12) (base + 24) (by decide)
    simp only [signExtend12_24] at h6
    have h7 := or_spec_gen_rd_eq_rs1_within .x28 .x30 (l1 ||| l2) l3 (base + 28) (by decide)
    have h8 := sltu_spec_gen_within .x30 .x7 .x6 l3 l0 lenW (base + 32) (by decide)
    have h9 := sltiu_spec_gen_same_within .x30
      (if BitVec.ult l0 lenW then (1 : Word) else 0) (1 : BitVec 12) (base + 36) (by decide)
    rw [calldataload_sltiu_seqz_eq l0 lenW] at h9
    have h10 := or_spec_gen_rd_eq_rs1_within .x28 .x30 ((l1 ||| l2) ||| l3)
      (calldataload_oobBit l0 lenW) (base + 40) (by decide)
    rw [show ((l1 ||| l2) ||| l3) ||| calldataload_oobBit l0 lenW
        = calldataload_oobFlag offsetWord lenW from by
      unfold calldataload_oobFlag calldataload_oobFlagW
      rw [← hl0, ← hl1, ← hl2, ← hl3, BitVec.or_assoc]] at h10
    runBlock h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmono11 : ∀ a i, CodeReq.singleton (base + 44) (.BEQ .x28 .x0 (8 : BitVec 13)) a = some i
      → evm_calldataload_staged_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base evm_calldataload_staged 11
      (base + 44) (by rw [evm_calldataload_staged_length]; norm_num)
      (by rw [evm_calldataload_staged_length]; norm_num) (by rfl))
  -- Normalize branch [11][12]: base+44 → base+52, x7 := stageNormW.
  have hbr : cpsTripleWithin 2 (base + 44) (base + 52) (evm_calldataload_staged_code base)
      (((.x28 : Reg) ↦ᵣ calldataload_oobFlag offsetWord lenW) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x7 : Reg) ↦ᵣ l0) ** ((.x6 : Reg) ↦ᵣ lenW))
      (((.x28 : Reg) ↦ᵣ calldataload_oobFlag offsetWord lenW) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x7 : Reg) ↦ᵣ stageNormW offsetWord lenW) ** ((.x6 : Reg) ↦ᵣ lenW)) := by
    have hbeq := beq_spec_gen_within .x28 .x0 (8 : BitVec 13)
      (calldataload_oobFlag offsetWord lenW) (0 : Word) (base + 44)
    rw [show (base + 44) + signExtend13 (8 : BitVec 13) = base + 52 from by
          rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]; bv_omega,
        show (base + 44 : Word) + 4 = base + 48 from by bv_omega] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono11 hbeq
    by_cases hflag : calldataload_oobFlag offsetWord lenW = 0
    · -- taken: x7 stays l0 = stageNormW.
      have ht := cpsBranchWithin_takenStripPure2 hbeqe (fun hp hQf => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQf
        exact ((sepConj_pure_right _).1 hQ).2 hflag)
      have htf := cpsTripleWithin_frameR (((.x7 : Reg) ↦ᵣ l0) ** ((.x6 : Reg) ↦ᵣ lenW))
        (by pcFreeR) ht
      rw [show stageNormW offsetWord lenW = l0 from by
        unfold stageNormW; rw [if_pos hflag, ← hl0]]
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
          (fun _ hp => by xperm_chunked hp) htf)
    · -- not taken: [12] sets x7 := lenW = stageNormW.
      have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        exact hflag ((sepConj_pure_right _).1 hQ).2)
      have hntf := cpsTripleWithin_frameR (((.x7 : Reg) ↦ᵣ l0) ** ((.x6 : Reg) ↦ᵣ lenW))
        (by pcFreeR) hnt
      have h12 := addi_spec_gen_within .x7 .x6 l0 lenW (0 : BitVec 12) (base + 48) (by decide)
      rw [show lenW + signExtend12 (0 : BitVec 12) = lenW from by
            rw [signExtend12_0]; bv_omega,
          show (base + 48 : Word) + 4 = base + 52 from by bv_omega] at h12
      have h12e := cpsTripleWithin_extend_code
        (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base evm_calldataload_staged 12
          (base + 48) (by rw [evm_calldataload_staged_length]; norm_num)
          (by rw [evm_calldataload_staged_length]; norm_num) (by rfl))) h12
      rw [show stageNormW offsetWord lenW = lenW from by
        unfold stageNormW; rw [if_neg hflag]]
      have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf
        (cpsTripleWithin_frameR (((.x28 : Reg) ↦ᵣ calldataload_oobFlag offsetWord lenW) **
          ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcFreeR) h12e)
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hp => by xperm_chunked hp) hseq
  -- Pointer setup [13..16]: base+52 → base+68.
  have hp3 : cpsTripleWithin 4 (base + 52) (base + 68) (evm_calldataload_staged_code base)
      (((.x5 : Reg) ↦ᵣ cdp) ** ((.x7 : Reg) ↦ᵣ stageNormW offsetWord lenW) **
       ((.x14 : Reg) ↦ᵣ buf) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ lenW) **
       ((.x30 : Reg) ↦ᵣ calldataload_oobBit l0 lenW) ** ((.x31 : Reg) ↦ᵣ x31o) **
       ((.x29 : Reg) ↦ᵣ x29o))
      (((.x5 : Reg) ↦ᵣ cdp) ** ((.x7 : Reg) ↦ᵣ stageNormW offsetWord lenW) **
       ((.x14 : Reg) ↦ᵣ buf) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ (cdp + lenW)) **
       ((.x30 : Reg) ↦ᵣ (cdp + stageNormW offsetWord lenW)) ** ((.x31 : Reg) ↦ᵣ buf) **
       ((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 32)) := by
    have h13 := add_spec_gen_within .x30 .x5 .x7 cdp (stageNormW offsetWord lenW)
      (calldataload_oobBit l0 lenW) (base + 52) (by decide)
    have h14 := add_spec_gen_rd_eq_rs2_within .x6 .x5 cdp lenW (base + 56) (by decide)
    have h15 := addi_spec_gen_within .x31 .x14 x31o buf (0 : BitVec 12) (base + 60) (by decide)
    rw [show buf + signExtend12 (0 : BitVec 12) = buf from by rw [signExtend12_0]; bv_omega] at h15
    have h16 := addi_spec_gen_within .x29 .x0 x29o (0 : Word) (BitVec.ofNat 12 32) (base + 64) (by decide)
    rw [show (0 : Word) + signExtend12 (BitVec.ofNat 12 32) = BitVec.ofNat 64 32 from by
      rw [signExtend12_ofNat_small (by decide)]; bv_omega] at h16
    runBlock h13 h14 h15 h16
  -- Compose hpre ; hbr ; hp3.
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    (cpsTripleWithin_frameR (((.x14 : Reg) ↦ᵣ buf) ** ((.x29 : Reg) ↦ᵣ x29o) **
      ((.x31 : Reg) ↦ᵣ x31o) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcFreeR) hpre)
    (cpsTripleWithin_frameR (((.x20 : Reg) ↦ᵣ envAddr) ** ((.x12 : Reg) ↦ᵣ sp) **
      ((.x5 : Reg) ↦ᵣ cdp) ** ((.x14 : Reg) ↦ᵣ buf) ** ((.x29 : Reg) ↦ᵣ x29o) **
      ((.x30 : Reg) ↦ᵣ calldataload_oobBit l0 lenW) ** ((.x31 : Reg) ↦ᵣ x31o) **
      ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ cdp) ** ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ lenW) ** (sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) ** ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3)) (by pcFreeR) hbr)
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1
    (cpsTripleWithin_frameR (((.x20 : Reg) ↦ᵣ envAddr) ** ((.x12 : Reg) ↦ᵣ sp) **
      ((.x28 : Reg) ↦ᵣ calldataload_oobFlag offsetWord lenW) ** ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ cdp) ** ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ lenW) ** (sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) ** ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3))
      (by pcFreeR) hp3)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s2

/-- The normalized copy content equals the CALLDATALOAD window content at the
    true 256-bit offset: in bounds `normW = offLo = offsetWord.toNat`; on the
    skip path both sides are all-zero (offset past the calldata end). -/
theorem stageNormW_copyBytes (data : List (BitVec 8)) (offsetWord : EvmWord)
    (lenW : Word) (h_len : data.length = lenW.toNat) :
    callDataCopyBytes data (stageNormW offsetWord lenW).toNat 32
      = stagedWindowBytes data offsetWord.toNat := by
  rw [stagedWindowBytes]
  apply List.ext_getElem
  · simp only [callDataCopyBytes_length]
  · intro j hj1 _
    have hj : j < 32 := by simpa [callDataCopyBytes_length] using hj1
    rw [callDataCopyBytes_get hj, callDataCopyBytes_get hj]
    unfold stageNormW
    by_cases hflag : calldataload_oobFlag offsetWord lenW = 0
    · rw [if_pos hflag, calldataload_oobFlag] at *
      obtain ⟨h_upper, _⟩ := calldataload_oobFlagW_eq_zero_iff.mp hflag
      rw [toNat_eq_getLimbN0_toNat_of_upper_or_zero h_upper]
    · rw [if_neg hflag]
      have h_off_ge : data.length ≤ offsetWord.toNat := by
        by_cases h_up : offsetWord.getLimbN 1 ||| offsetWord.getLimbN 2 |||
            offsetWord.getLimbN 3 = 0
        · rw [toNat_eq_getLimbN0_toNat_of_upper_or_zero h_up, h_len]
          have hoob : calldataload_oobBit (offsetWord.getLimbN 0) lenW ≠ 0 := by
            intro hb
            exact hflag (by rw [calldataload_oobFlag, calldataload_oobFlagW, h_up, hb]; decide)
          have hnlt : ¬ (offsetWord.getLimbN 0 < lenW) := fun h =>
            hoob (calldataload_oobBit_eq_zero_iff.mpr h)
          rw [BitVec.lt_def] at hnlt; omega
        · have h2 := two_pow_64_le_toNat_of_upper_or_ne_zero h_up
          have hl := lenW.isLt
          omega
      rw [callDataByte_of_ge (by omega : data.length ≤ lenW.toNat + j),
          callDataByte_of_ge (by omega : data.length ≤ offsetWord.toNat + j)]

/-- The finalize store [26] (`base+104 → base+108`): `SD x12 x0 0` zeroes the
    low operand cell so the window prologue reads `offLo = 0` from the buffer. -/
theorem evm_calldataload_stage_finalize_spec_within (base sp gL0 : Word) :
    cpsTripleWithin 1 (base + 104) (base + 108) (evm_calldataload_staged_code base)
      (((.x12 : Reg) ↦ᵣ sp) ** (sp ↦ₘ gL0))
      (((.x12 : Reg) ↦ᵣ sp) ** (sp ↦ₘ (0 : Word))) := by
  have h := sd_x0_spec_gen_within .x12 sp gL0 (0 : BitVec 12) (base + 104)
  rw [show sp + signExtend12 (0 : BitVec 12) = sp from by rw [signExtend12_0]; bv_omega,
      show (base + 104 : Word) + 4 = base + 108 from by bv_omega] at h
  exact cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base evm_calldataload_staged 26
      (base + 104) (by rw [evm_calldataload_staged_length]; norm_num)
      (by rw [evm_calldataload_staged_length]; norm_num) (by rfl))) h

/-- The window ladder [27..120] (`base+108 → base+484`) transported onto the
    staged program code: re-run the verified in-bounds window arm over the
    staging buffer `buf` at offset 0. -/
theorem stage_window_spec_within
    (base sp buf offOld addrOld byteOld accOld l1 l2 l3 : Word)
    (windowBytes : List (BitVec 8))
    (h_wf : CalldataRegionWf buf windowBytes)
    (h_off : (0 : Word).toNat < windowBytes.length) :
    cpsTripleWithin 94 (base + 108) (base + 484)
      (evm_calldataload_staged_code base)
      (calldataloadWindowArmPre .x15 .x16 .x17 .x18 .x14
        sp buf 0 offOld addrOld byteOld accOld l1 l2 l3 windowBytes)
      (calldataloadWindowArmPost .x15 .x16 .x17 .x18 .x14
        sp buf 0 windowBytes) := by
  have h_core := calldataload_window_arm_core_spec_within
    .x15 .x16 .x17 .x18 .x14 sp buf 0 offOld addrOld byteOld accOld l1 l2 l3
    windowBytes (base + 108) (by decide) (by decide) (by decide) (by decide)
    h_wf h_off
  have hmono : ∀ a i,
      evm_calldataload_window_code .x15 .x16 .x17 .x18 .x14 (base + 108) a = some i →
      evm_calldataload_staged_code base a = some i :=
    CodeReq.ofProg_mono_sub base (base + 108) evm_calldataload_staged
      (evm_calldataload_window .x15 .x16 .x17 .x18 .x14) 27
      (by bv_omega)
      (by rfl)
      (by rw [evm_calldataload_staged_length,
              evm_calldataload_window_program_length])
      (by rw [evm_calldataload_staged_length]; decide)
  have h_staged := cpsTripleWithin_extend_code hmono h_core
  rwa [show (base + 108 : Word) + 376 = base + 484 from by bv_omega] at h_staged


end Calldata
end EvmAsm.Evm64
