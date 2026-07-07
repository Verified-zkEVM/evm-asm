/-
  EvmAsm.Evm64.Code.CopyLoopSpec

  The verified CODECOPY copy loop: the ≤`size`-byte copy-with-zero-fill loop
  of `evm_codecopy` (`Code/CopyProgram.lean`, indices [8..17]) that writes
  `Code.copyBytes code codeOffset size` into the EVM-memory destination
  window `[destByteOff, destByteOff + size)`, zero-filling positions past
  `len(code)` — plus the public CODECOPY stack spec.

  This is the sibling of `Calldata/CopyLoopSpec.lean`; the loop body is
  byte-for-byte the same instruction sequence, shifted down by one preamble
  instruction (the CODECOPY preamble is 8 instructions, CALLDATACOPY's is 9)
  and with the register remap end `x18 → x17`, byte `x19 → x18` (the code
  base rides in the preserved dispatcher register `x21`).  Option-1 source
  model (unaligned aliased running code): the code is a byte-slice of the
  aligned source region `bytesRegion srcBase srcBytes` with
  `codeBase = srcBase + cbByteOff`; the destination is the aligned
  EVM-memory region `bytesRegion memBase memBytes` with
  `dest = memBase + destByteOff`.

  The destination-window content function `copyDestContent` and the pure
  copied-bytes function are reused from the Calldata modules —
  `Code.copyBytes` is definitionally `Calldata.callDataCopyBytes`
  (`copyBytes_eq_callDataCopyBytes`), so all its get/length lemmas apply.
-/

import EvmAsm.Evm64.Code.CopySpec
import EvmAsm.Evm64.Calldata.CopyLoopSpec
import EvmAsm.Evm64.Calldata.StageSpec
import EvmAsm.Evm64.StateAssertions
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPermChunked

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Code

open EvmAsm.Rv64
open EvmAsm.Evm64.Calldata

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-- `Code.copyBytes` *is* `Calldata.callDataCopyBytes`: both read `size`
    bytes at increasing source offsets, producing zero past the end of the
    buffer (`Code.byte` and `callDataByte` are the same function).  This
    bridge lets the CODECOPY loop reuse the whole Calldata pure-lemma kit. -/
theorem copyBytes_eq_callDataCopyBytes
    (code : List (BitVec 8)) (codeOffset size : Nat) :
    copyBytes code codeOffset size = callDataCopyBytes code codeOffset size :=
  rfl

/-! ## The copy-loop body (one iteration)

Registers are fixed to the emitted CODECOPY handler instantiation
(`EvmCodeHandlers`, `evm_codecopy .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18`):
`x14 = destReg`, `x15 = srcReg`, `x16 = cntReg`, `x17 = endReg`,
`x18 = byteReg`.  The destination EVM-memory region is `bytesRegion memBase …`;
the source code region is the aligned `bytesRegion srcBase srcBytes` with
`codeBase = srcBase + cbByteOff` (Option-1). -/

/-- One iteration of the CODECOPY copy loop (`base+36 → base+68`, indices
    [9..16]): select `copied[i]` (source byte in bounds, else zero), store it
    at the destination window index `i`, advance src/dest, decrement the
    counter. -/
theorem evm_codecopy_body_spec_within
    (base memBase srcBase : Word)
    (cbByteOff dataOff len destByteOff size i : Nat)
    (data srcBytes memBytes : List (BitVec 8)) (cntV byteOld : Word)
    (h_i : i < size)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_fits : cbByteOff + len ≤ srcBytes.length)
    (h_data : data = (srcBytes.drop cbByteOff).take len)
    (h_win : destByteOff + size ≤ memBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true)
    (h_src_nowrap : srcBase.toNat + cbByteOff + dataOff + size ≤ 2 ^ 64)
    (h_cb : (callDataCopyBytes data dataOff size)[i]'(by
      simp only [callDataCopyBytes_length]; omega) = cbi) :
    cpsTripleWithin 7 (base + 36) (base + 68)
      (evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base)
      (((.x18 : Reg) ↦ᵣ byteOld) **
       ((.x15 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + i))) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + len))) **
       ((.x14 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destByteOff + i))) **
       ((.x16 : Reg) ↦ᵣ cntV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (copyDestContent memBytes (callDataCopyBytes data dataOff size) destByteOff i) **
       bytesRegion srcBase srcBytes)
      (((.x18 : Reg) ↦ᵣ (cbi.zeroExtend 64)) **
       ((.x15 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + (i + 1)))) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + len))) **
       ((.x14 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destByteOff + (i + 1)))) **
       ((.x16 : Reg) ↦ᵣ (cntV + signExtend12 (-1 : BitVec 12))) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (copyDestContent memBytes (callDataCopyBytes data dataOff size) destByteOff (i + 1)) **
       bytesRegion srcBase srcBytes) := by
  set copied := callDataCopyBytes data dataOff size with hcopied_def
  have hcopied_len : copied.length = size := by simp [hcopied_def]
  -- Bounds.
  have hsrclen_lt : srcBytes.length < 2 ^ 64 := by omega
  have hmemlen_lt : memBytes.length < 2 ^ 64 := by omega
  have h_src_idx : cbByteOff + dataOff + i < 2 ^ 64 := by omega
  have h_end_idx : cbByteOff + len < 2 ^ 64 := by omega
  have h_src_k : srcBase.toNat + (cbByteOff + dataOff + i) < 2 ^ 64 := by omega
  have h_src_end : srcBase.toNat + (cbByteOff + len) < 2 ^ 64 := by omega
  -- The window byte stored at index `i`.
  have hcbi_val : cbi = callDataByte data (dataOff + i) := by
    rw [← h_cb]; exact callDataCopyBytes_get h_i
  have hdest_len : (copyDestContent memBytes copied destByteOff i).length = memBytes.length :=
    copyDestContent_length memBytes copied destByteOff i (by rw [hcopied_len]; omega) (by omega)
  have hdest_i_lt : destByteOff + i < (copyDestContent memBytes copied destByteOff i).length := by
    rw [hdest_len]; omega
  -- Branch: src ≥ end ⟺ dataOff + i ≥ len.
  have hult := stage_ult_offsets srcBase (cbByteOff + dataOff + i) (cbByteOff + len)
    h_src_k h_src_end h_src_idx h_end_idx
  -- The window content after this write.
  have hset : (copyDestContent memBytes copied destByteOff i).set (destByteOff + i) cbi
      = copyDestContent memBytes copied destByteOff (i + 1) :=
    copyDestContent_set memBytes copied destByteOff i cbi (by omega)
      (by rw [hcopied_len]; omega) h_cb.symm
  have htrunc : (cbi.zeroExtend 64).truncate 8 = cbi := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have := cbi.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  set srcP := srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + i) with hsrcP
  set endP := srcBase + BitVec.ofNat 64 (cbByteOff + len) with hendP
  set destP := memBase + BitVec.ofNat 64 (destByteOff + i) with hdestP
  -- BGEU [9] base+36: taken base+48 (¬ult), ntaken base+40 (ult).
  have hbgeu := bgeu_spec_gen_within .x15 .x17 (BitVec.ofNat 13 12) srcP endP (base + 36)
  rw [show (base + 36) + signExtend13 (BitVec.ofNat 13 12) = base + 48 from by
        rw [show signExtend13 (BitVec.ofNat 13 12) = (12 : Word) from by decide]; bv_omega,
      show (base + 36 : Word) + 4 = base + 40 from by bv_omega] at hbgeu
  have hmono9 : ∀ a i, CodeReq.singleton (base + 36) (.BGEU .x15 .x17 (BitVec.ofNat 13 12)) a = some i
      → evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_codecopy .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18) 9
      (base + 36) (by rw [evm_codecopy_length]; norm_num)
      (by rw [evm_codecopy_length]; norm_num) (by rfl))
  have hbgeue := cpsBranchWithin_extend_code hmono9 hbgeu
  -- hpre_sb : base+36 → base+52 : byteReg := cbi.zeroExtend 64.
  have hpre_sb : cpsTripleWithin 3 (base + 36) (base + 52)
      (evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base)
      (((.x15 : Reg) ↦ᵣ srcP) ** ((.x17 : Reg) ↦ᵣ endP) ** ((.x18 : Reg) ↦ᵣ byteOld) **
       ((.x14 : Reg) ↦ᵣ destP) ** ((.x16 : Reg) ↦ᵣ cntV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (copyDestContent memBytes copied destByteOff i) **
       bytesRegion srcBase srcBytes)
      (((.x18 : Reg) ↦ᵣ (cbi.zeroExtend 64)) ** ((.x15 : Reg) ↦ᵣ srcP) **
       ((.x17 : Reg) ↦ᵣ endP) ** ((.x14 : Reg) ↦ᵣ destP) ** ((.x16 : Reg) ↦ᵣ cntV) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (copyDestContent memBytes copied destByteOff i) **
       bytesRegion srcBase srcBytes) := by
    by_cases h_ib : dataOff + i < len
    · -- in-bounds: BGEU not taken → LBU (byteReg := src byte = cbi) → JAL skip.
      have hnt := cpsBranchWithin_ntakenStripPure2 hbgeue (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        have hu := ((sepConj_pure_right _).1 hQ).2
        rw [hult] at hu; rw [decide_eq_true_eq] at hu; omega)
      have hntf := cpsTripleWithin_frameR
        (((.x18 : Reg) ↦ᵣ byteOld) ** ((.x14 : Reg) ↦ᵣ destP) ** ((.x16 : Reg) ↦ᵣ cntV) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion memBase (copyDestContent memBytes copied destByteOff i) **
         bytesRegion srcBase srcBytes) (by pcFreeR) hnt
      -- LBU [10] base+40 → base+44.
      have hlbu := bytesRegion_lbu_within .x18 .x15 srcBase byteOld (base + 40)
        srcBytes (cbByteOff + dataOff + i) (by decide) h_src_align (by omega) (by omega)
        (h_src_valid (cbByteOff + dataOff + i) (by omega))
      have hsrck : srcBytes[cbByteOff + dataOff + i]'(by omega) = cbi := by
        rw [hcbi_val]
        exact stage_copy_byte_eq data srcBytes cbByteOff dataOff len i h_fits h_data h_ib
      rw [← hsrcP,
          show srcBytes[cbByteOff + dataOff + i]'(by omega) = cbi from hsrck,
          show (base + 40 : Word) + 4 = base + 44 from by bv_omega] at hlbu
      have hmono10 : ∀ a i, CodeReq.singleton (base + 40) (.LBU .x18 .x15 0) a = some i
          → evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base a = some i :=
        CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
          (evm_codecopy .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18) 10
          (base + 40) (by rw [evm_codecopy_length]; norm_num)
          (by rw [evm_codecopy_length]; norm_num) (by rfl))
      have hlbue := cpsTripleWithin_extend_code hmono10 hlbu
      have hlbuf := cpsTripleWithin_frameR
        (((.x17 : Reg) ↦ᵣ endP) ** ((.x14 : Reg) ↦ᵣ destP) ** ((.x16 : Reg) ↦ᵣ cntV) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion memBase (copyDestContent memBytes copied destByteOff i)) (by pcFreeR) hlbue
      -- JAL [11] base+44 → base+52 (skip the oob fill).
      have hjal := jal_x0_spec_gen_within (BitVec.ofNat 21 8) (base + 44)
      rw [show (base + 44) + signExtend21 (BitVec.ofNat 21 8) = base + 52 from by
        rw [show signExtend21 (BitVec.ofNat 21 8) = (8 : Word) from by decide]; bv_omega] at hjal
      have hmono11 : ∀ a i, CodeReq.singleton (base + 44) (.JAL .x0 (BitVec.ofNat 21 8)) a = some i
          → evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base a = some i :=
        CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
          (evm_codecopy .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18) 11
          (base + 44) (by rw [evm_codecopy_length]; norm_num)
          (by rw [evm_codecopy_length]; norm_num) (by rfl))
      have hjale := cpsTripleWithin_extend_code hmono11 hjal
      have hjalf := cpsTripleWithin_frameR
        (((.x18 : Reg) ↦ᵣ (cbi.zeroExtend 64)) ** ((.x15 : Reg) ↦ᵣ srcP) **
         ((.x17 : Reg) ↦ᵣ endP) ** ((.x14 : Reg) ↦ᵣ destP) ** ((.x16 : Reg) ↦ᵣ cntV) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion memBase (copyDestContent memBytes copied destByteOff i) **
         bytesRegion srcBase srcBytes) (by pcFreeR) hjale
      simp only [sepConj_assoc', sepConj_emp_left'] at hntf hlbuf hjalf
      have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf hlbuf
      have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hjalf
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hp => by xperm_chunked hp) s2
    · -- out-of-bounds: BGEU taken → ADDI byteReg 0 (= cbi).
      have hcbi0 : cbi = 0 := by
        rw [hcbi_val]; apply callDataByte_of_ge
        rw [h_data, List.length_take, List.length_drop]; omega
      have ht := cpsBranchWithin_takenStripPure2 hbgeue (fun hp hQf => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQf
        have hu := ((sepConj_pure_right _).1 hQ).2
        rw [hult] at hu; rw [decide_eq_true_eq] at hu; omega)
      have htf := cpsTripleWithin_frameR
        (((.x18 : Reg) ↦ᵣ byteOld) ** ((.x14 : Reg) ↦ᵣ destP) ** ((.x16 : Reg) ↦ᵣ cntV) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion memBase (copyDestContent memBytes copied destByteOff i) **
         bytesRegion srcBase srcBytes) (by pcFreeR) ht
      -- ADDI [12] base+48 → base+52 : byteReg := 0.
      have haddi := addi_spec_gen_within .x18 .x0 byteOld (0 : Word) (0 : BitVec 12)
        (base + 48) (by decide)
      rw [show (0 : Word) + signExtend12 (0 : BitVec 12) = 0 from by
            rw [signExtend12_0]; bv_omega,
          show (base + 48 : Word) + 4 = base + 52 from by bv_omega] at haddi
      have hmono12 : ∀ a i, CodeReq.singleton (base + 48) (.ADDI .x18 .x0 0) a = some i
          → evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base a = some i :=
        CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
          (evm_codecopy .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18) 12
          (base + 48) (by rw [evm_codecopy_length]; norm_num)
          (by rw [evm_codecopy_length]; norm_num) (by rfl))
      have haddie := cpsTripleWithin_extend_code hmono12 haddi
      have haddif := cpsTripleWithin_frameR
        (((.x15 : Reg) ↦ᵣ srcP) ** ((.x17 : Reg) ↦ᵣ endP) ** ((.x14 : Reg) ↦ᵣ destP) **
         ((.x16 : Reg) ↦ᵣ cntV) **
         bytesRegion memBase (copyDestContent memBytes copied destByteOff i) **
         bytesRegion srcBase srcBytes) (by pcFreeR) haddie
      simp only [sepConj_assoc'] at htf haddif
      have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) htf haddif
      refine cpsTripleWithin_mono_nSteps (by decide)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => ?_) hseq)
      rw [hcbi0, show BitVec.zeroExtend 64 (0 : BitVec 8) = 0 from by decide]
      xperm_chunked hq
  -- hshared : base+52 → base+68 : store byte, advance src/dest, decrement cnt.
  have hshared : cpsTripleWithin 4 (base + 52) (base + 68)
      (evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base)
      (((.x18 : Reg) ↦ᵣ (cbi.zeroExtend 64)) ** ((.x15 : Reg) ↦ᵣ srcP) **
       ((.x17 : Reg) ↦ᵣ endP) ** ((.x14 : Reg) ↦ᵣ destP) ** ((.x16 : Reg) ↦ᵣ cntV) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (copyDestContent memBytes copied destByteOff i) **
       bytesRegion srcBase srcBytes)
      (((.x18 : Reg) ↦ᵣ (cbi.zeroExtend 64)) **
       ((.x15 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + (i + 1)))) **
       ((.x17 : Reg) ↦ᵣ endP) **
       ((.x14 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destByteOff + (i + 1)))) **
       ((.x16 : Reg) ↦ᵣ (cntV + signExtend12 (-1 : BitVec 12))) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (copyDestContent memBytes copied destByteOff (i + 1)) **
       bytesRegion srcBase srcBytes) := by
    -- [13] SB x14 x18 0
    have h13 := bytesRegion_sb_within .x14 .x18 memBase (cbi.zeroExtend 64) (base + 52)
      (copyDestContent memBytes copied destByteOff i) (destByteOff + i) h_mem_align hdest_i_lt
      (by omega) (h_mem_valid (destByteOff + i) (by rw [hdest_len] at hdest_i_lt; omega))
    rw [← hdestP, htrunc, hset] at h13
    -- [14] ADDI x15 x15 1
    have h14 := addi_spec_gen_same_within .x15 srcP (1 : BitVec 12) (base + 56) (by decide)
    rw [show srcP + signExtend12 (1 : BitVec 12)
        = srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + (i + 1)) from by
          rw [hsrcP, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at h14
    -- [15] ADDI x14 x14 1
    have h15 := addi_spec_gen_same_within .x14 destP (1 : BitVec 12) (base + 60) (by decide)
    rw [show destP + signExtend12 (1 : BitVec 12)
        = memBase + BitVec.ofNat 64 (destByteOff + (i + 1)) from by
          rw [hdestP, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at h15
    -- [16] ADDI x16 x16 -1
    have h16 := addi_spec_gen_same_within .x16 cntV (-1 : BitVec 12) (base + 64) (by decide)
    have m13 : ∀ a i, CodeReq.singleton (base + 52) (.SB .x14 .x18 0) a = some i
        → evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
        (evm_codecopy .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18) 13
        (base + 52) (by rw [evm_codecopy_length]; norm_num)
        (by rw [evm_codecopy_length]; norm_num) (by rfl))
    have h13e := cpsTripleWithin_extend_code m13 h13
    have m14 : ∀ a i, CodeReq.singleton (base + 56) (.ADDI .x15 .x15 1) a = some i
        → evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
        (evm_codecopy .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18) 14
        (base + 56) (by rw [evm_codecopy_length]; norm_num)
        (by rw [evm_codecopy_length]; norm_num) (by rfl))
    have h14e := cpsTripleWithin_extend_code m14 h14
    have m15 : ∀ a i, CodeReq.singleton (base + 60) (.ADDI .x14 .x14 1) a = some i
        → evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
        (evm_codecopy .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18) 15
        (base + 60) (by rw [evm_codecopy_length]; norm_num)
        (by rw [evm_codecopy_length]; norm_num) (by rfl))
    have h15e := cpsTripleWithin_extend_code m15 h15
    have m16 : ∀ a i, CodeReq.singleton (base + 64) (.ADDI .x16 .x16 (-1 : BitVec 12)) a = some i
        → evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
        (evm_codecopy .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18) 16
        (base + 64) (by rw [evm_codecopy_length]; norm_num)
        (by rw [evm_codecopy_length]; norm_num) (by rfl))
    have h16e := cpsTripleWithin_extend_code m16 h16
    rw [show (base + 52 : Word) + 4 = base + 56 from by bv_omega] at h13e
    rw [show (base + 56 : Word) + 4 = base + 60 from by bv_omega] at h14e
    rw [show (base + 60 : Word) + 4 = base + 64 from by bv_omega] at h15e
    rw [show (base + 64 : Word) + 4 = base + 68 from by bv_omega] at h16e
    have fh13 := cpsTripleWithin_frameR
      (((.x15 : Reg) ↦ᵣ srcP) ** ((.x17 : Reg) ↦ᵣ endP) ** ((.x16 : Reg) ↦ᵣ cntV) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) (by pcFreeR) h13e
    have fh14 := cpsTripleWithin_frameR
      (((.x18 : Reg) ↦ᵣ (cbi.zeroExtend 64)) ** ((.x17 : Reg) ↦ᵣ endP) **
       ((.x14 : Reg) ↦ᵣ destP) ** ((.x16 : Reg) ↦ᵣ cntV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (copyDestContent memBytes copied destByteOff (i + 1)) **
       bytesRegion srcBase srcBytes) (by pcFreeR) h14e
    have fh15 := cpsTripleWithin_frameR
      (((.x18 : Reg) ↦ᵣ (cbi.zeroExtend 64)) **
       ((.x15 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + (i + 1)))) **
       ((.x17 : Reg) ↦ᵣ endP) ** ((.x16 : Reg) ↦ᵣ cntV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (copyDestContent memBytes copied destByteOff (i + 1)) **
       bytesRegion srcBase srcBytes) (by pcFreeR) h15e
    have fh16 := cpsTripleWithin_frameR
      (((.x18 : Reg) ↦ᵣ (cbi.zeroExtend 64)) **
       ((.x15 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + (i + 1)))) **
       ((.x17 : Reg) ↦ᵣ endP) **
       ((.x14 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destByteOff + (i + 1)))) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (copyDestContent memBytes copied destByteOff (i + 1)) **
       bytesRegion srcBase srcBytes) (by pcFreeR) h16e
    simp only [sepConj_assoc'] at fh13 fh14 fh15 fh16
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) fh13 fh14
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 fh15
    have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 fh16
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) s3
  -- Compose hpre_sb ; hshared.
  have hbody := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hpre_sb hshared
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) hbody

/-- `(n+1) - 1 = n` as words (loop counter decrement). -/
private theorem ccp_word_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A successor counter `< 2^64` is nonzero as a word. -/
private theorem ccp_word_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

/-- The CODECOPY copy-loop closure (`base+32 → base+72`, indices [8..17]) by
    induction on the byte countdown `n = size - i`. -/
theorem evm_codecopy_loop_spec_within
    (base memBase srcBase : Word)
    (cbByteOff dataOff len destByteOff size n i : Nat)
    (data srcBytes memBytes : List (BitVec 8)) (byteV : Word)
    (h_ni : i + n = size)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_fits : cbByteOff + len ≤ srcBytes.length)
    (h_data : data = (srcBytes.drop cbByteOff).take len)
    (h_win : destByteOff + size ≤ memBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true)
    (h_src_nowrap : srcBase.toNat + cbByteOff + dataOff + size ≤ 2 ^ 64) :
    cpsTripleWithin (9 * n + 1) (base + 32) (base + 72)
      (evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base)
      (((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x15 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + i))) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + len))) **
       ((.x14 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destByteOff + i))) **
       ((.x18 : Reg) ↦ᵣ byteV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (copyDestContent memBytes (callDataCopyBytes data dataOff size) destByteOff i) **
       bytesRegion srcBase srcBytes)
      (((.x16 : Reg) ↦ᵣ (0 : Word)) **
       ((.x15 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + size))) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + len))) **
       ((.x14 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destByteOff + size))) **
       regOwn .x18 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (copyDestContent memBytes (callDataCopyBytes data dataOff size) destByteOff size) **
       bytesRegion srcBase srcBytes) := by
  set copied := callDataCopyBytes data dataOff size with hcopied_def
  have hmono8 : ∀ a i, CodeReq.singleton (base + 32) (.BEQ .x16 .x0 (BitVec.ofNat 13 40)) a = some i
      → evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_codecopy .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18) 8
      (base + 32) (by rw [evm_codecopy_length]; norm_num)
      (by rw [evm_codecopy_length]; norm_num) (by rfl))
  have hmono17 : ∀ a i, CodeReq.singleton (base + 68) (.JAL .x0 (-36 : BitVec 21)) a = some i
      → evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_codecopy .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18) 17
      (base + 68) (by rw [evm_codecopy_length]; norm_num)
      (by rw [evm_codecopy_length]; norm_num) (by rfl))
  have ha_t : (base + 32) + signExtend13 (BitVec.ofNat 13 40) = base + 72 := by
    rw [show signExtend13 (BitVec.ofNat 13 40) = (40 : Word) from by decide]; bv_omega
  have ha_f : (base + 32 : Word) + 4 = base + 36 := by bv_omega
  have ha_back : (base + 68) + signExtend21 (-36 : BitVec 21) = base + 32 := by
    rw [show signExtend21 (-36 : BitVec 21) = (-36 : Word) from by decide]; bv_omega
  induction n generalizing i byteV with
  | zero =>
    have hisize : size = i := by omega
    subst hisize
    have hbeq := beq_spec_gen_within .x16 .x0 (BitVec.ofNat 13 40) (BitVec.ofNat 64 0)
      (0 : Word) (base + 32)
    rw [ha_t, ha_f] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono8 hbeq
    have htaken := cpsBranchWithin_takenStripPure2 hbeqe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x15 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + size))) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + len))) **
       ((.x14 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destByteOff + size))) **
       ((.x18 : Reg) ↦ᵣ byteV) **
       bytesRegion memBase (copyDestContent memBytes copied destByteOff size) **
       bytesRegion srcBase srcBytes) (by pcFreeR) htaken
    simp only [sepConj_assoc'] at htf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          have hq2 : (((.x18 : Reg) ↦ᵣ byteV) **
              ((.x16 : Reg) ↦ᵣ (0 : Word)) **
              ((.x15 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + size))) **
              ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + len))) **
              ((.x14 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destByteOff + size))) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion memBase (copyDestContent memBytes copied destByteOff size) **
              bytesRegion srcBase srcBytes) sState := by xperm_chunked hq
          have hq3 := sepConj_mono_left (regIs_implies_regOwn .x18) _ hq2
          xperm_chunked hq3) htf)
  | succ k ih =>
    have hi_lt : i < size := by omega
    have hbeq := beq_spec_gen_within .x16 .x0 (BitVec.ofNat 13 40) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (base + 32)
    rw [ha_t, ha_f] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono8 hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ccp_word_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x15 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + i))) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + len))) **
       ((.x14 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destByteOff + i))) **
       ((.x18 : Reg) ↦ᵣ byteV) **
       bytesRegion memBase (copyDestContent memBytes copied destByteOff i) **
       bytesRegion srcBase srcBytes) (by pcFreeR) hnt
    have hbody := evm_codecopy_body_spec_within base memBase srcBase cbByteOff
      dataOff len destByteOff size i data srcBytes memBytes (BitVec.ofNat 64 (k + 1)) byteV
      hi_lt h_src_align h_mem_align h_fits h_data h_win h_src_over h_src_valid
      h_mem_over h_mem_valid h_src_nowrap rfl
    rw [ccp_word_succ_dec k] at hbody
    have hjal := jal_x0_spec_gen_within (-36 : BitVec 21) (base + 68)
    rw [ha_back] at hjal
    have hjale := cpsTripleWithin_extend_code hmono17 hjal
    have hih := ih (i + 1)
      ((copied[i]'(by rw [hcopied_def, callDataCopyBytes_length]; omega)).zeroExtend 64)
      (by omega)
    simp only [sepConj_assoc'] at hntf
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf hbody
    have hjalf := cpsTripleWithin_frameR
      (((.x18 : Reg) ↦ᵣ ((copied[i]'(by rw [hcopied_def, callDataCopyBytes_length]; omega)).zeroExtend 64)) **
       ((.x15 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + (i + 1)))) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (cbByteOff + len))) **
       ((.x14 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destByteOff + (i + 1)))) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (copyDestContent memBytes copied destByteOff (i + 1)) **
       bytesRegion srcBase srcBytes) (by pcFreeR) hjale
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left']; xperm_chunked hp) s1 hjalf
    have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left'] at hp; xperm_chunked hp) s2 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hp => by xperm_chunked hp) s3)

/-! ## The public CODECOPY stack spec -/

/-- Shed the four loop scratch registers (`x14 x15 x16 x17`) to ownership at
    the tail of the CODECOPY postcondition. -/
private theorem ccp_shed4 (F : Assertion) (v14 v15 v16 v17 : Word) :
    ∀ ps,
      (F ** (((.x14 : Reg) ↦ᵣ v14) ** ((.x15 : Reg) ↦ᵣ v15) **
        ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ v17))) ps →
      (F ** (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17)) ps := by
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono (regIs_implies_regOwn _)
  exact regIs_implies_regOwn _

/-- **The public CODECOPY stack spec** (`0x39`) over the full `evm_codecopy`
    program (entry `base`, exit `base + 72`): pops `[destOffset, dataOffset,
    size]`, writes `Code.copyBytes data dataOffset size` into the EVM-memory
    window `[destOffset, destOffset + size)` (zero-filling positions past
    `len(code)`), for **every** operand.  Pad-free: the code region needs no
    zero tail (the loop zero-fills at copy time).  Option-1 source model: the
    running code is a slice of the aligned region `bytesRegion srcBase
    srcBytes` with `codeBase = srcBase + cbByteOff`; the running-code length
    is the dispatcher-seeded `codeSizeIs` cell (`env + 496`).  The destination
    is the EVM memory `evmMemoryIs memBase capacity memBytes`.  All scratch
    shed to ownership.  This is the CODECOPY `.proven` registry witness.

    Axiom audit (`#print axioms evm_codecopy_stack_spec_within`):
    `[propext, Classical.choice, Quot.sound]` — kernel-checked, classical-3
    only (same for `evm_codecopy_body_spec_within` and
    `evm_codecopy_loop_spec_within`). -/
theorem evm_codecopy_stack_spec_within
    (base sp envAddr memBase codeBase srcBase : Word)
    (cbByteOff len capacity : Nat) (codeSizeW : Word)
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord)
    (data srcBytes memBytes : List (BitVec 8))
    (destOld srcOld cntOld endOld byteOld : Word)
    (h_cbase : codeBase = srcBase + BitVec.ofNat 64 cbByteOff)
    (h_len : len = codeSizeW.toNat)
    (h_data : data = (srcBytes.drop cbByteOff).take len)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_fits : cbByteOff + len ≤ srcBytes.length)
    (h_win : (destOffset.getLimbN 0).toNat + (size.getLimbN 0).toNat ≤ memBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true)
    (h_src_nowrap :
      srcBase.toNat + cbByteOff + (dataOffset.getLimbN 0).toNat + (size.getLimbN 0).toNat ≤ 2 ^ 64)
    (h_cap : memBytes.length = capacity) :
    cpsTripleWithin (9 * (size.getLimbN 0).toNat + 9) base (base + 72)
      (evm_codecopy_code .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 base)
      (((.x12 : Reg) ↦ᵣ sp) ** ((.x20 : Reg) ↦ᵣ envAddr) **
       ((.x13 : Reg) ↦ᵣ memBase) ** ((.x21 : Reg) ↦ᵣ codeBase) **
       ((.x14 : Reg) ↦ᵣ destOld) ** ((.x15 : Reg) ↦ᵣ srcOld) **
       ((.x16 : Reg) ↦ᵣ cntOld) ** ((.x17 : Reg) ↦ᵣ endOld) **
       ((.x18 : Reg) ↦ᵣ byteOld) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest ** codeSizeIs envAddr codeSizeW **
       evmMemoryIs memBase capacity memBytes ** bytesRegion srcBase srcBytes)
      (((.x12 : Reg) ↦ᵣ (sp + 96)) ** ((.x20 : Reg) ↦ᵣ envAddr) **
       ((.x13 : Reg) ↦ᵣ memBase) ** ((.x21 : Reg) ↦ᵣ codeBase) **
       regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** regOwn .x18 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest ** codeSizeIs envAddr codeSizeW **
       evmMemoryIs memBase capacity
         (copyDestContent memBytes (copyBytes data (dataOffset.getLimbN 0).toNat
           (size.getLimbN 0).toNat) (destOffset.getLimbN 0).toNat (size.getLimbN 0).toNat) **
       bytesRegion srcBase srcBytes) := by
  rw [copyBytes_eq_callDataCopyBytes]
  set dataOff := (dataOffset.getLimbN 0).toNat with hdataOff
  set destByteOff := (destOffset.getLimbN 0).toNat with hdestByteOff
  set sz := (size.getLimbN 0).toNat with hsz
  set copied := callDataCopyBytes data dataOff sz with hcopied
  -- Preamble (base → base+32), framed with the untouched x0/x18 and the two regions.
  have hpre := evm_codecopy_full_code_preamble_stack_spec_within
    .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18 (by decide) (by decide) (by decide)
    (by decide) sp base envAddr memBase codeBase destOld srcOld cntOld endOld
    codeSizeW destOffset dataOffset size rest
  have hpref := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ byteOld) **
     evmMemoryIs memBase capacity memBytes ** bytesRegion srcBase srcBytes)
    (by
      refine pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree)
        (pcFree_sepConj pcFree_evmMemoryIs (bytesRegion_pcFree _ _)))) hpre
  -- Loop (base+32 → base+72) at i = 0, n = sz.
  have hbytes : evmMemoryIs memBase capacity memBytes
      = bytesRegion memBase memBytes := evmMemoryIs_eq_bytesRegion h_cap
  have hloop := evm_codecopy_loop_spec_within base memBase srcBase cbByteOff
    dataOff len destByteOff sz sz 0 data srcBytes memBytes byteOld
    (by omega) h_src_align h_mem_align h_fits h_data h_win
    h_src_over h_src_valid h_mem_over h_mem_valid (by omega)
  have hloopf := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ (sp + 96)) ** ((.x20 : Reg) ↦ᵣ envAddr) **
     ((.x13 : Reg) ↦ᵣ memBase) ** ((.x21 : Reg) ↦ᵣ codeBase) **
     evmStackIs sp [destOffset, dataOffset, size] **
     evmStackIs (sp + 96) rest ** codeSizeIs envAddr codeSizeW)
    (by
      refine pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree)
        (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree)
          (pcFree_sepConj pcFree_evmStackIs (pcFree_sepConj pcFree_evmStackIs
            pcFree_codeSizeIs))))) ) hloop
  -- Value bridges connecting the preamble post to the loop entry.
  have e_src : codeBase + dataOffset.getLimbN 0
      = srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + 0) := by
    rw [h_cbase, hdataOff]; bv_omega
  have e_end : codeSizeW + codeBase
      = srcBase + BitVec.ofNat 64 (cbByteOff + len) := by
    rw [h_cbase, h_len]; bv_omega
  have e_dest : memBase + destOffset.getLimbN 0
      = memBase + BitVec.ofNat 64 (destByteOff + 0) := by
    rw [hdestByteOff]; bv_omega
  have e_cnt : size.getLimbN 0 = BitVec.ofNat 64 sz := by rw [hsz]; bv_omega
  have e_mem : bytesRegion memBase memBytes
      = bytesRegion memBase (copyDestContent memBytes copied destByteOff 0) := by
    rw [copyDestContent_zero]
  -- Compose preamble ; loop, rewriting the midpoint into the loop entry shape.
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      rw [← e_src, ← e_end, ← e_dest, ← e_cnt, ← e_mem, ← hbytes]
      simp only [sepConj_assoc'] at hp ⊢; xperm_chunked hp) hpref hloopf
  -- Reshape endpoints and lift the destination region to evmMemoryIs.
  have hcdc_len : (copyDestContent memBytes copied destByteOff sz).length = capacity := by
    rw [copyDestContent_length memBytes copied destByteOff sz
      (by rw [hcopied, callDataCopyBytes_length]; omega)
      (by rw [hcopied, callDataCopyBytes_length])]
    exact h_cap
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hcomp)
  · simp only [sepConj_assoc'] at hp ⊢; xperm_chunked hp
  · rw [← evmMemoryIs_eq_bytesRegion hcdc_len] at hq
    have hshed := ccp_shed4
      (((.x12 : Reg) ↦ᵣ (sp + 96)) ** ((.x20 : Reg) ↦ᵣ envAddr) **
       ((.x13 : Reg) ↦ᵣ memBase) ** ((.x21 : Reg) ↦ᵣ codeBase) **
       regOwn .x18 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest ** codeSizeIs envAddr codeSizeW **
       evmMemoryIs memBase capacity (copyDestContent memBytes copied destByteOff sz) **
       bytesRegion srcBase srcBytes)
      (memBase + BitVec.ofNat 64 (destByteOff + sz))
      (srcBase + BitVec.ofNat 64 (cbByteOff + dataOff + sz))
      (0 : Word) (srcBase + BitVec.ofNat 64 (cbByteOff + len)) _
      (by simp only [sepConj_assoc'] at hq ⊢; xperm_chunked hq)
    simp only [sepConj_assoc'] at hshed ⊢; xperm_chunked hshed

end Code
end EvmAsm.Evm64
