/-
  EvmAsm.Rv64.RLP.UnifiedEmptyBytesField

  EL.3 / Phase 5 — the EMPTY (`n=0`) byte-array field. An empty byte string (`to` on contract
  creation) RLP-encodes as `[0x80]`; the non-empty byte-array unit
  (`unified_bytes_field_decode_and_copy`) requires `1 ≤ data.length` (its `payloadOff ≤ bs.length`
  step uses it via `omega`), so it cannot decode an empty field into the schema engine's output.

  The header descent on `0x80` leaves `x13` at the next field (empty payload), so there is nothing
  to copy: descend, then the byte-copy leaf with `N = 0` (`ADDI x14, rOut, fieldImm` + empty copy
  chain) — the output region is unchanged (`copyRangeGen out [] 0 di 0 = out`). `fieldSize = 152`
  (the byte-array formula at length 0). Coincides with `decode (bs.drop O) = some (.bytes [], tail)`.
-/

import EvmAsm.Rv64.RLP.UnifiedBytesFieldDecode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **Empty (`n=0`) byte-array field decode-and-copy.** From `x13 = regionBase + ofNat O` pointing
    at the empty byte string `[0x80]`, descend the header (advancing `x13` to the next field) and
    run the byte-copy leaf with `N = 0` — the output region is unchanged. Same statement shape as
    `unified_bytes_field_decode_and_copy` at `data = []`; coincides with
    `decode (bs.drop O) = some (.bytes [], tail)`. -/
theorem unified_empty_bytes_field_decode_and_copy
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hdst : di0 + ([] : List Byte).length ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + (148 + 4 + 20 * ([] : List Byte).length) < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes ([] : List Byte)) ++ tail) :
    cpsTripleWithin (61 + (1 + 5 * ([] : List Byte).length)) base
        (base + 148 + 4 + BitVec.ofNat 64 (20 * ([] : List Byte).length))
      (((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        ((CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm)).union
          (byteCopyChainCR (base + 148 + 4) ([] : List Byte).length)))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x12) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes ([] : List Byte))).length))) **
        (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + ([] : List Byte).length))) ** (regOwn .x15) **
        (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
        bytesRegion outBase (copyRangeGen outBytes ([] : List Byte) 0 di0 ([] : List Byte).length)) **
       (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11))
    ∧ decode (bs.drop O) = some (.bytes ([] : List Byte), tail) := by
  -- `encode (.bytes []) = [0x80]`, length 1.
  have henc_len : (encode (.bytes ([] : List Byte))).length = 1 := by
    simp [encode, encodeBytes_nil]
  have hbs0 : O < bs.length := by
    have h := congrArg List.length hdrop
    rw [List.length_drop, List.length_append] at h
    have := encode_nonempty (RLPItem.bytes ([] : List Byte)); omega
  have hbs_head : bs[O]'hbs0
      = (encode (.bytes ([] : List Byte)))[0]'(encode_nonempty (RLPItem.bytes ([] : List Byte))) := by
    have key : (bs.drop O)[0]'(by rw [List.length_drop]; omega)
        = (encode (.bytes ([] : List Byte)))[0]'(encode_nonempty (RLPItem.bytes ([] : List Byte))) :=
      (List.getElem_of_eq hdrop _).trans (List.getElem_append_left (encode_nonempty _))
    rw [← key]; simp
  have hhead80 : bs[O]'hbs0 = (BitVec.ofNat 8 0x80 : Byte) := by
    rw [hbs_head]; simp [encode, encodeBytes_nil]
  have hcls : classifyPrefix (bs[O]'hbs0) = .shortBytes := by rw [hhead80]; decide
  have hptr : itemPtrRegion (bs[O]'hbs0) regionBase O = regionBase + BitVec.ofNat 64 (O + 1) := by
    simp only [itemPtrRegion, hcls]
  have hpay : bs.drop (O + 1) = ([] : List Byte) ++ tail := by
    have hd1 : bs.drop (O + 1) = (bs.drop O).drop 1 := by rw [List.drop_drop]
    rw [hd1, hdrop]; simp [encode, encodeBytes_nil]
  have hpaylen : (O + 1) + ([] : List Byte).length ≤ bs.length := by simp; omega
  have hwindow0 : regionLongWindow regionBase bs O hbs0 :=
    regionLongWindow_of_split regionBase bs (.bytes ([] : List Byte)) tail O hbs0 hbs_head hdrop
      (by simp [itemPayloadCount]) hwin
  -- Header decode (base .. base+148): x13 = payload pointer (= O+1, empty payload).
  have hdesc := unified_list_header_descend base regionBase bs O hbs0 v5Old v10 v11Old v12Old
    v14Old v15Old halign hover (hwin O hbs0) hwindow0
  rw [hptr] at hdesc
  -- Frame the output region + pointer through the header descend.
  have hdesc' := cpsTripleWithin_frameR ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)
    (by exact pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) hdesc
  -- The leaf byte-array copy (base+148 ..) with N = 0: copies nothing.
  have hcopy := unified_field_bytes_copy (base + 148) regionBase rOut outBase fieldImm bs outBytes
    (O + 1) di0 ([] : List Byte).length (itemX12Region (bs[O]'hbs0) bs O v12Old)
    (itemX14 (bs[O]'hbs0) v14Old) v15Old halign hdalign hover hwin hpaylen hdst hdov hdval
    (by have h148 : (base + 148).toNat = base.toNat + 148 := by bv_omega
        omega) hImm
  -- Frame the header-leftover registers (x5/x0/x10/x11) through the copy.
  have hcopy' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (bs[O]'hbs0).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x10 ↦ᵣ itemResidue (bs[O]'hbs0)) ** (.x11 ↦ᵣ itemLenRegion (bs[O]'hbs0) bs O))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs pcFree_regIs))) hcopy
  -- Disjointness: header CR ⊥ copy CR (identical to the non-empty bytes unit).
  have hd : ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).Disjoint
      ((CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm)).union
        (byteCopyChainCR (base + 148 + 4) ([] : List Byte).length)) := by
    refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton (by bv_omega)) ?_
      exact singleton_disjoint_byteCopyChainCR base (base + 148 + 4) _ ([] : List Byte).length
        (by have : (base + 148 + 4).toNat = base.toNat + 152 := by bv_omega
            omega)
        (by have : (base + 148 + 4).toNat = base.toNat + 152 := by bv_omega
            omega)
    · refine CodeReq.Disjoint.union_right ?_ ?_
      · exact CodeReq.Disjoint.ofProg_singleton
          (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 (base + 148)
            unified_decoder_prog_length (by intro k hk; bv_omega))
      · intro a
        by_cases hdec : ∀ k, k < 36 → a ≠ (base + 4) + BitVec.ofNat 64 (4 * k)
        · exact Or.inl (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 a
            unified_decoder_prog_length hdec)
        · push Not at hdec
          obtain ⟨k, hk, rfl⟩ := hdec
          exact Or.inr (byteCopyChainCR_none (base + 148 + 4) _ ([] : List Byte).length
            (fun j hj => by bv_omega))
  -- The pure decode coincidence.
  have hpure : decode (bs.drop O) = some (.bytes ([] : List Byte), tail) := by
    rw [hdrop]; exact decode_encode_append (.bytes ([] : List Byte)) tail (by rw [henc_len]; norm_num)
  refine ⟨?_, hpure⟩
  -- copyRangeGen over `bs` at O+1 equals over `[]` at 0 (both reduce to outBytes for N=0).
  have hcongr : copyRangeGen outBytes bs (O + 1) di0 ([] : List Byte).length
      = copyRangeGen outBytes ([] : List Byte) 0 di0 ([] : List Byte).length := rfl
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
  rw [show O + (encode (.bytes ([] : List Byte))).length = (O + 1) + ([] : List Byte).length
      from by simp [henc_len]]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq hd
      (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) hdesc')
      hcopy'')

end EvmAsm.Rv64.RLP
