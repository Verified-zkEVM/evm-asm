/-
  EvmAsm.Rv64.RLP.UnifiedBytesFieldDecode

  EL.3 / Phase 5 — full byte-array field decode-and-copy. From `x13 = regionBase + ofNat O`
  (a `.bytes data` field, `data.length ≤ 55` — covers 20-byte addresses, 32-byte hashes),
  decode the item header then byte-copy the `data.length` payload bytes into the output
  struct region at byte offset `di0`. Composes `unified_list_header_descend` (→ x13 =
  payload pointer, x11 = length) with `unified_field_bytes_copy`, the byte-array analog of
  `unified_scalar_field_decode_and_store`. Coincides with `decode (bs.drop O) = some
  (.bytes data, tail)`.
-/

import EvmAsm.Rv64.RLP.UnifiedFieldBytesCopy
import EvmAsm.Rv64.RLP.UnifiedScalarFieldDecode
import EvmAsm.Rv64.RLP.UnifiedListDescendConcrete

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- `copyRangeGen` only reads `src` through `[s, s+N)`; agreeing windows give equal results. -/
theorem copyRangeGen_congr (dst src1 src2 : List (BitVec 8)) (s1 s2 di0 N : Nat)
    (h : ∀ k, k < N → getByteAt src1 (s1 + k) = getByteAt src2 (s2 + k)) :
    copyRangeGen dst src1 s1 di0 N = copyRangeGen dst src2 s2 di0 N := by
  induction N generalizing dst s1 s2 di0 with
  | zero => rfl
  | succ n ih =>
    have h0 : getByteAt src1 s1 = getByteAt src2 s2 := by
      have := h 0 (by omega); simpa using this
    simp only [copyRangeGen, h0]
    exact ih (dst.set di0 (getByteAt src2 s2)) (s1 + 1) (s2 + 1) (di0 + 1)
      (fun k hk => by
        have := h (k + 1) (by omega)
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this)

/-- The copy chain maps to `none` outside its slots `{bw + 4*j : j < 5*N}`. -/
theorem byteCopyChainCR_none (bw a : Word) (N : Nat)
    (h : ∀ j, j < 5 * N → a ≠ bw + BitVec.ofNat 64 (4 * j)) :
    byteCopyChainCR bw N a = none := by
  induction N generalizing bw with
  | zero => rfl
  | succ k ih =>
    have h1 : copyIterCR bw a = none := copyIterCR_none bw a (fun s hs => h s (by omega))
    have h2 : byteCopyChainCR (bw + 20) k a = none := ih (bw + 20) (fun j hj => by
      have := h (5 + j) (by omega)
      rwa [show bw + BitVec.ofNat 64 (4 * (5 + j)) = (bw + 20) + BitVec.ofNat 64 (4 * j)
        from by bv_omega] at this)
    simp only [byteCopyChainCR, CodeReq.union, h1, h2]

set_option maxRecDepth 8000 in
/-- **Full byte-array field decode-and-copy.** Decode the `.bytes data` field at `x13 =
    regionBase + ofNat O` and copy its payload into the output struct region at byte
    offset `di0`; the output region's `[di0, di0 + data.length)` becomes `data`. -/
theorem unified_bytes_field_decode_and_copy
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hlen1 : 1 ≤ data.length) (hlen55 : data.length ≤ 55)
    (hsize : (encode (.bytes data)).length < 256 ^ 8)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hdst : di0 + data.length ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + (148 + 4 + 20 * data.length) < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    cpsTripleWithin (61 + (1 + 5 * data.length)) base (base + 148 + 4 + BitVec.ofNat 64 (20 * data.length))
      (((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        ((CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm)).union
          (byteCopyChainCR (base + 148 + 4) data.length)))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + data.length))) ** (regOwn .x15) **
        (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
        bytesRegion outBase (copyRangeGen outBytes data 0 di0 data.length)) **
       (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11))
    ∧ decode (bs.drop O) = some (.bytes data, tail) := by
  -- Window connection: locate the payload (offset `payloadOff`, pointer / length facts).
  have hbs0 : O < bs.length := by
    have h := congrArg List.length hdrop
    rw [List.length_drop, List.length_append] at h
    have := encode_nonempty (RLPItem.bytes data); omega
  have hbs_head : bs[O]'hbs0 = (encode (.bytes data))[0]'(encode_nonempty (RLPItem.bytes data)) := by
    have key : (bs.drop O)[0]'(by rw [List.length_drop]; omega)
        = (encode (.bytes data))[0]'(encode_nonempty (RLPItem.bytes data)) :=
      (List.getElem_of_eq hdrop _).trans (List.getElem_append_left (encode_nonempty _))
    rw [← key]; simp
  obtain ⟨payloadOff, hptr, hlen, hpay⟩ :=
    bytes_item_payload_window data tail regionBase O bs hdrop hlen55
  rw [show ((encode (.bytes data))[0]'(encode_nonempty (RLPItem.bytes data)))
        = (bs[O]'hbs0) from hbs_head.symm] at hptr hlen
  have hpaylen : payloadOff + data.length ≤ bs.length := by
    have e1 := congrArg List.length hpay
    rw [List.length_drop, List.length_append] at e1; omega
  have hstride : payloadOff + data.length = O + (encode (.bytes data)).length := by
    have e1 := congrArg List.length hpay
    have e2 := congrArg List.length hdrop
    simp only [List.length_drop, List.length_append] at e1 e2; omega
  have hwindow0 : regionLongWindow regionBase bs O hbs0 :=
    regionLongWindow_of_split regionBase bs (.bytes data) tail O hbs0 hbs_head hdrop
      (by simpa [itemPayloadCount] using (show data.length < 256 ^ 8 by omega)) hwin
  -- Header decode (base .. base+148): x13 = payload pointer, x11 = length.
  have hdesc := unified_list_header_descend base regionBase bs O hbs0 v5Old v10 v11Old v12Old
    v14Old v15Old halign hover (hwin O hbs0) hwindow0
  rw [hptr] at hdesc
  -- Frame the output region + pointer through the header descend.
  have hdesc' := cpsTripleWithin_frameR ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)
    (by exact pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) hdesc
  -- The leaf byte-array copy (base+148 ..): copies data.length payload bytes to di0.
  have hcopy := unified_field_bytes_copy (base + 148) regionBase rOut outBase fieldImm bs outBytes
    payloadOff di0 data.length (itemX12Region (bs[O]'hbs0) bs O v12Old) (itemX14 (bs[O]'hbs0) v14Old)
    v15Old halign hdalign hover hwin hpaylen hdst hdov hdval
    (by have h148 : (base + 148).toNat = base.toNat + 148 := by bv_omega
        omega) hImm
  -- Frame the header-leftover registers (x5/x0/x10/x11) through the copy.
  have hcopy' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (bs[O]'hbs0).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x10 ↦ᵣ itemResidue (bs[O]'hbs0)) ** (.x11 ↦ᵣ itemLenRegion (bs[O]'hbs0) bs O))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs pcFree_regIs))) hcopy
  -- Disjointness: header CR ⊥ copy CR.
  have hd : ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).Disjoint
      ((CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm)).union
        (byteCopyChainCR (base + 148 + 4) data.length)) := by
    refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton (by bv_omega)) ?_
      exact singleton_disjoint_byteCopyChainCR base (base + 148 + 4) _ data.length
        (by have : (base + 148 + 4).toNat = base.toNat + 152 := by bv_omega
            omega)
        (by have : (base + 148 + 4).toNat = base.toNat + 152 := by bv_omega
            omega)
    · refine CodeReq.Disjoint.union_right ?_ ?_
      · exact CodeReq.Disjoint.ofProg_singleton
          (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 (base + 148)
            unified_decoder_prog_length (by intro k hk; bv_omega))
      · -- decoder ofProg ⊥ copy chain (decoder ⊆ [base+4, base+144], chain ≥ base+152).
        intro a
        by_cases hdec : ∀ k, k < 36 → a ≠ (base + 4) + BitVec.ofNat 64 (4 * k)
        · exact Or.inl (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 a
            unified_decoder_prog_length hdec)
        · push Not at hdec
          obtain ⟨k, hk, rfl⟩ := hdec
          exact Or.inr (byteCopyChainCR_none (base + 148 + 4) _ data.length
            (fun j hj => by bv_omega))
  -- The pure decode coincidence.
  have hpure : decode (bs.drop O) = some (.bytes data, tail) := by
    rw [hdrop]; exact decode_encode_append (.bytes data) tail hsize
  refine ⟨?_, hpure⟩
  -- copyRangeGen over `bs` at payloadOff equals over `data` at 0 (windows agree via hpay).
  have hcongr : copyRangeGen outBytes bs payloadOff di0 data.length
      = copyRangeGen outBytes data 0 di0 data.length := by
    apply copyRangeGen_congr
    intro k hk
    have hk' : payloadOff + k < bs.length := by omega
    have hdk : bs[payloadOff + k]'hk' = data[k]'hk := by
      have h1 := List.getElem_of_eq hpay (i := k) (by rw [List.length_drop]; omega)
      rw [List.getElem_drop] at h1
      rw [h1, List.getElem_append_left hk]
    unfold getByteAt
    rw [dif_pos hk', show (0 + k) = k from Nat.zero_add k, dif_pos hk, hdk]
  rw [hcongr] at hcopy'
  -- Weaken the header-leftover regs to `regOwn` in the copy's framed post.
  have hF2 : ∀ hh, ((.x5 ↦ᵣ (bs[O]'hbs0).zeroExtend 64) ** (.x0 ↦ᵣ (0:Word)) **
        (.x10 ↦ᵣ itemResidue (bs[O]'hbs0)) ** (.x11 ↦ᵣ itemLenRegion (bs[O]'hbs0) bs O)) hh →
      (regOwn .x5 ** (.x0 ↦ᵣ (0:Word)) ** regOwn .x10 ** regOwn .x11) hh :=
    fun hh hf =>
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (regIs_implies_regOwn .x11)))) hh
        ((sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10)))) hh
          ((sepConj_mono_left (regIs_implies_regOwn .x5)) hh hf))
  have hcopy'' := cpsTripleWithin_weaken (fun _ h => h)
    (fun _ hp => sepConj_mono_right hF2 _ hp) hcopy'
  -- Compose: header descend ⨾ copy, reconciling the framed intermediate state.
  rw [show O + (encode (.bytes data)).length = payloadOff + data.length from hstride.symm]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq hd
      (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) hdesc')
      hcopy'')

end EvmAsm.Rv64.RLP
