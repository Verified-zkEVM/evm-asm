/-
  EvmAsm.Rv64.RLP.UnifiedScalarFieldRegion

  EL.3 / Phase 5 — full scalar field decode-and-store INTO THE OUTPUT REGION. Decode a
  `.bytes data` scalar field (`1 ≤ data.length ≤ 8`) at `x13 = regionBase + ofNat O` and
  write its u64 value little-endian into the unified output-struct `bytesRegion` at byte
  offset `di0`. The region analog of `unified_scalar_field_decode_and_store` (which used
  `SD` to a separate `↦ₘ` cell) and the scalar counterpart of
  `unified_bytes_field_decode_and_copy` — so scalar and byte-array fields share one
  whole-struct output region. Coincides with `decodeScalar (bs.drop O) = some (value, tail)`.

  Composition: `unified_scalar_field_decode` (→ x11 = value) ⨾ `unified_field_scalar_store_region`
  (peeling the decode's `regOwn x14`).
-/

import EvmAsm.Rv64.RLP.UnifiedFieldScalarStoreRegion
import EvmAsm.Rv64.RLP.UnifiedScalarFieldDecode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- The spill chain maps to `none` outside its slots `{bw + 4*j : j < 3*N}`. -/
theorem spillChainCR_none (bw a : Word) (N : Nat)
    (h : ∀ j, j < 3 * N → a ≠ bw + BitVec.ofNat 64 (4 * j)) :
    spillChainCR bw N a = none := by
  induction N generalizing bw with
  | zero => rfl
  | succ k ih =>
    have h1 : spillIterCR bw a = none := spillIterCR_none bw a (fun s hs => h s (by omega))
    have h2 : spillChainCR (bw + 12) k a = none := ih (bw + 12) (fun j hj => by
      have := h (3 + j) (by omega)
      rwa [show bw + BitVec.ofNat 64 (4 * (3 + j)) = (bw + 12) + BitVec.ofNat 64 (4 * j)
        from by bv_omega] at this)
    simp only [spillChainCR, CodeReq.union, h1, h2]

/-- Full non-empty scalar field decode-and-store into region. Decode the byte-string scalar at
    x13 = regionBase + ofNat O, read its non-empty big-endian payload into x11, and spill that
    u64 value little-endian into the output struct region at byte offset di0. The guard
    data.headD 1 != 0 is the scalar canonicality condition enforced by decodeScalar. -/
theorem unified_scalar_field_decode_and_store_region
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hlen1 : 1 ≤ data.length) (hlen8 : data.length ≤ 8) (hhead : data.headD 1 ≠ 0)
    (hsize : (encode (.bytes data)).length < 256 ^ 8)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hdst : di0 + 8 ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + 280 < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    cpsTripleWithin ((61 + (2 + 6 * data.length)) + (1 + 3 * 8)) base
      (base + 180 + 4 + BitVec.ofNat 64 (12 * 8))
      (((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        ((((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
            (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
            (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20)))).union
          ((CodeReq.singleton (base + 180) (.ADDI .x14 rOut fieldImm)).union
            (spillChainCR (base + 180 + 4) 8))))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x11) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + 8))) ** (rOut ↦ᵣ outBase) **
        bytesRegion outBase
          (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE data)) di0 8)) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old)))
    ∧ decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail) := by
  have hlen55 : data.length ≤ 55 := by omega
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
    rw [List.length_drop, List.length_append] at e1
    omega
  have hstride : payloadOff + data.length = O + (encode (.bytes data)).length := by
    have e1 := congrArg List.length hpay
    have e2 := congrArg List.length hdrop
    simp only [List.length_drop, List.length_append] at e1 e2; omega
  have htake : (bs.drop payloadOff).take data.length = data := by
    rw [hpay, List.take_left' rfl]
  have hwindow0 : regionLongWindow regionBase bs O hbs0 :=
    regionLongWindow_of_split regionBase bs (.bytes data) tail O hbs0 hbs_head hdrop
      (by simpa [itemPayloadCount] using (show data.length < 256 ^ 8 by omega)) hwin
  have hdesc := unified_list_header_descend base regionBase bs O hbs0 v5Old v10 v11Old v12Old
    v14Old v15Old halign hover (hwin O hbs0) hwindow0
  rw [hptr, hlen] at hdesc
  have hread := unified_field_scalar_read (base + 148) regionBase bs payloadOff data.length
    (itemX12Region (bs[O]'hbs0) bs O v12Old) (itemX14 (bs[O]'hbs0) v14Old)
    hlen1 hlen8 halign hover
    (fun i hi => ⟨by omega, hwin (payloadOff + i) (by omega)⟩)
  rw [show (base + 148) + 32 = base + 180 from by bv_omega,
      show (base + 148) + 4 = base + 152 from by bv_omega,
      show (base + 148) + 8 = base + 156 from by bv_omega, htake] at hread
  have hreadF := cpsTripleWithin_frameR
    (regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old) **
      ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
    (by pcFree) hread
  have hstore := unified_field_scalar_store_region (base + 180) rOut outBase fieldImm outBytes di0 8
    (BitVec.ofNat 64 (Nat.fromBytesBE data)) (0 : Word)
    hdalign hdst hdov hdval
    (by have h180 : (base + 180).toNat = base.toNat + 180 := by bv_omega
        omega) hImm
  have hstoreF := cpsTripleWithin_frameR
    ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (payloadOff + data.length))) **
      regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
      regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old))
    (by pcFree) hstore
  have hd_desc_read : ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).Disjoint
      (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
          (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
          (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20)))) := by
    refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_right ?_ ?_
      · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton (by bv_omega)) ?_
        exact CodeReq.Disjoint.singleton (by bv_omega)
      · exact CodeReq.Disjoint.singleton_ofProg
          (CodeReq.ofProg_none_range_len (base + 156) (rlp_phase2_long_loop_body_prog (-20)) 6 base
            (by rfl) (by intro k hk; bv_omega))
    · refine CodeReq.Disjoint.union_right ?_ ?_
      · refine CodeReq.Disjoint.union_right ?_ ?_
        · exact CodeReq.Disjoint.ofProg_singleton
            (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 (base + 148)
              unified_decoder_prog_length (by intro k hk; bv_omega))
        · exact CodeReq.Disjoint.ofProg_singleton
            (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 (base + 152)
              unified_decoder_prog_length (by intro k hk; bv_omega))
      · intro a
        by_cases hdec : ∀ k, k < 36 → a ≠ (base + 4) + BitVec.ofNat 64 (4 * k)
        · exact Or.inl (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 a
            unified_decoder_prog_length hdec)
        · push Not at hdec
          obtain ⟨k, hk, rfl⟩ := hdec
          exact Or.inr (CodeReq.ofProg_none_range_len (base + 156)
            (rlp_phase2_long_loop_body_prog (-20)) 6 _ (by rfl) (by intro j hj; bv_omega))
  have hd_read_store : (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
          (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
          (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20)))).Disjoint
      ((CodeReq.singleton (base + 180) (.ADDI .x14 rOut fieldImm)).union
        (spillChainCR (base + 180 + 4) 8)) := by
    refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_left ?_ ?_
      · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton (by bv_omega)) ?_
        exact singleton_disjoint_spillChainCR (base + 148) (base + 180 + 4)
          (.ADDI .x14 .x11 0) 8 (by bv_omega) (by bv_omega)
      · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton (by bv_omega)) ?_
        exact singleton_disjoint_spillChainCR (base + 152) (base + 180 + 4)
          (.ADDI .x11 .x0 0) 8 (by bv_omega) (by bv_omega)
    · refine CodeReq.Disjoint.union_right ?_ ?_
      · exact CodeReq.Disjoint.ofProg_singleton
          (CodeReq.ofProg_none_range_len (base + 156) (rlp_phase2_long_loop_body_prog (-20)) 6
            (base + 180) (by rfl) (by intro k hk; bv_omega))
      · intro a
        by_cases hloop : ∀ k, k < 6 → a ≠ (base + 156) + BitVec.ofNat 64 (4 * k)
        · exact Or.inl (CodeReq.ofProg_none_range_len (base + 156)
            (rlp_phase2_long_loop_body_prog (-20)) 6 a (by rfl) hloop)
        · push Not at hloop
          obtain ⟨k, hk, rfl⟩ := hloop
          exact Or.inr (spillChainCR_none (base + 180 + 4) _ 8 (fun j hj => by bv_omega))
  have hd_desc_store : ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).Disjoint
      ((CodeReq.singleton (base + 180) (.ADDI .x14 rOut fieldImm)).union
        (spillChainCR (base + 180 + 4) 8)) := by
    refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton (by bv_omega)) ?_
      exact singleton_disjoint_spillChainCR base (base + 180 + 4) (.LBU .x5 .x13 0) 8
        (by bv_omega) (by bv_omega)
    · refine CodeReq.Disjoint.union_right ?_ ?_
      · exact CodeReq.Disjoint.ofProg_singleton
          (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 (base + 180)
            unified_decoder_prog_length (by intro k hk; bv_omega))
      · intro a
        by_cases hdec : ∀ k, k < 36 → a ≠ (base + 4) + BitVec.ofNat 64 (4 * k)
        · exact Or.inl (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 a
            unified_decoder_prog_length hdec)
        · push Not at hdec
          obtain ⟨k, hk, rfl⟩ := hdec
          exact Or.inr (spillChainCR_none (base + 180 + 4) _ 8 (fun j hj => by bv_omega))
  have hd_desc_tail : ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).Disjoint
      ((((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
          (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
          (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20)))).union
        ((CodeReq.singleton (base + 180) (.ADDI .x14 rOut fieldImm)).union
          (spillChainCR (base + 180 + 4) 8))) :=
    CodeReq.Disjoint.union_right hd_desc_read hd_desc_store
  have hreadForStore : cpsTripleWithin (2 + 6 * data.length) (base + 148) (base + 180)
      (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
          (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
        (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20))))
      (((.x11 ↦ᵣ BitVec.ofNat 64 data.length) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 payloadOff)) **
          (.x14 ↦ᵣ itemX14 (bs[O]'hbs0) v14Old) **
          (.x12 ↦ᵣ itemX12Region (bs[O]'hbs0) bs O v12Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) **
        regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old) **
        (rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)
      (((.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE data)) **
          (.x14 ↦ᵣ (0 : Word)) ** (rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (payloadOff + data.length))) **
        regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hp => by
      have htmp : ((.x12 ↦ᵣ (bs.getD (payloadOff + (data.length - 1)) 0).zeroExtend 64) **
          ((.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE data)) **
           (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (payloadOff + data.length))) **
           (.x14 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
           regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old) **
           ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))) h := by
        xperm_hyp hp
      have hx12 : (regOwn .x12 **
          ((.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE data)) **
           (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (payloadOff + data.length))) **
           (.x14 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
           regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old) **
           ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))) h :=
        sepConj_mono_left (regIs_implies_regOwn .x12) h htmp
      xperm_hyp hx12) hreadF
  have hread_then_store := cpsTripleWithin_seq hd_read_store hreadForStore hstoreF
  have hdescForRead : cpsTripleWithin 61 base (base + 148)
      ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((.x11 ↦ᵣ BitVec.ofNat 64 data.length) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 payloadOff)) **
          (.x14 ↦ᵣ itemX14 (bs[O]'hbs0) v14Old) **
          (.x12 ↦ᵣ itemX12Region (bs[O]'hbs0) bs O v12Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) **
        regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old) **
        (rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hp => by
      have htmp : (((.x5 ↦ᵣ (bs[O]'hbs0).zeroExtend 64) ** (.x10 ↦ᵣ itemResidue (bs[O]'hbs0))) **
          ((.x11 ↦ᵣ BitVec.ofNat 64 data.length) **
           (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 payloadOff)) **
           (.x14 ↦ᵣ itemX14 (bs[O]'hbs0) v14Old) **
           (.x12 ↦ᵣ itemX12Region (bs[O]'hbs0) bs O v12Old) **
           (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
           (.x15 ↦ᵣ v15Old) ** ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))) h := by
        xperm_hyp hp
      have htmp' : ((regOwn .x5 ** regOwn .x10) **
          ((.x11 ↦ᵣ BitVec.ofNat 64 data.length) **
           (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 payloadOff)) **
           (.x14 ↦ᵣ itemX14 (bs[O]'hbs0) v14Old) **
           (.x12 ↦ᵣ itemX12Region (bs[O]'hbs0) bs O v12Old) **
           (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
           (.x15 ↦ᵣ v15Old) ** ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))) h :=
        sepConj_mono_left
          (sepConj_mono (regIs_implies_regOwn .x5) (regIs_implies_regOwn .x10)) h htmp
      xperm_hyp htmp')
      (cpsTripleWithin_frameR ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)
        (by exact pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) hdesc)
  have all := cpsTripleWithin_seq hd_desc_tail hdescForRead hread_then_store
  refine ⟨?_, ?_⟩
  · rw [show O + (encode (.bytes data)).length = payloadOff + data.length from hstride.symm]
    rw [show (61 + (2 + 6 * data.length)) + (1 + 3 * 8)
        = 61 + (2 + 6 * data.length) + (1 + 3 * 8) by ring]
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) all
  · unfold decodeScalar
    have hpure : decode (bs.drop O) = some (.bytes data, tail) := by
      rw [hdrop]; exact decode_encode_append (.bytes data) tail hsize
    rw [hpure]
    simp only [Option.bind_eq_bind, Option.bind_some, hhead, ↓reduceIte]

end EvmAsm.Rv64.RLP
