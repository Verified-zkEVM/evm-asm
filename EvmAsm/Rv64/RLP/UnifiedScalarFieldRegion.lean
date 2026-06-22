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

set_option maxRecDepth 8000 in
/-- **Full scalar field decode-and-store into region.** Decode the `.bytes data` scalar
    field at `x13 = regionBase + ofNat O` and spill its u64 value (little-endian) into the
    output region at byte offset `di0`; `output[di0 .. di0+8)` becomes the value's LE bytes. -/
theorem unified_scalar_field_decode_and_store_region
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hlen1 : 1 ≤ data.length) (hlen8 : data.length ≤ 8)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail)
    (hdalign : outBase.toNat % 8 = 0) (hdst : di0 + 8 ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hcode : base.toNat + (180 + 4 + 12 * 8) < 2 ^ 64) :
    cpsTripleWithin ((61 + (2 + 6 * data.length)) + (1 + 3 * 8)) base
        (base + 180 + 4 + BitVec.ofNat 64 (12 * 8))
      ((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
          (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
              (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
              (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20))))).union
        ((CodeReq.singleton (base + 180) (.ADDI .x14 rOut fieldImm)).union
          (spillChainCR (base + 180 + 4) 8)))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x11) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + 8))) ** (rOut ↦ᵣ outBase) **
        bytesRegion outBase (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE data)) di0 8)) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old)))
    ∧ decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail) := by
  obtain ⟨t_dec, hpure⟩ := unified_scalar_field_decode base regionBase bs O data tail
    v5Old v10 v11Old v12Old v14Old v15Old hlen1 hlen8 halign hover hwin hdrop
  -- Frame the output region + pointer through the decode.
  have t_dec' := cpsTripleWithin_frameR ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)
    (by exact pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) t_dec
  -- Leaf scalar store at base+180, accepting the decode's `regOwn x14` (peeled).
  have store : cpsTripleWithin (1 + 3 * 8) (base + 180) (base + 180 + 4 + BitVec.ofNat 64 (12 * 8))
      ((CodeReq.singleton (base + 180) (.ADDI .x14 rOut fieldImm)).union (spillChainCR (base + 180 + 4) 8))
      ((.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE data)) ** (regOwn .x14) ** (rOut ↦ᵣ outBase) **
       bytesRegion outBase outBytes)
      ((regOwn .x11) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + 8))) ** (rOut ↦ᵣ outBase) **
       bytesRegion outBase (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE data)) di0 8)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x14)
        (P := (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE data)) ** (rOut ↦ᵣ outBase) **
          bytesRegion outBase outBytes)
        (fun v14 => ?_))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (unified_field_scalar_store_region (base + 180) rOut outBase fieldImm outBytes di0 8
        (BitVec.ofNat 64 (Nat.fromBytesBE data)) v14 hdalign hdst hdov hdval
        (by have h180 : (base + 180).toNat = base.toNat + 180 := by bv_omega
            omega) hImm)
  -- Frame the decode-leftover registers / input region through the store.
  have store' := cpsTripleWithin_frameR
    ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
     regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
     regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regOwn (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (bytesRegion_pcFree _ _) (pcFree_sepConj pcFree_regOwn
        (pcFree_sepConj pcFree_regOwn pcFree_regIs)))))) store
  -- Disjointness: decode CR ⊥ store CR.
  have hd : ((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
            (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
            (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20)))))).Disjoint
      ((CodeReq.singleton (base + 180) (.ADDI .x14 rOut fieldImm)).union
        (spillChainCR (base + 180 + 4) 8)) := by
    refine CodeReq.Disjoint.union_left (CodeReq.Disjoint.union_left ?_ ?_)
      (CodeReq.Disjoint.union_left (CodeReq.Disjoint.union_left ?_ ?_) ?_) <;>
      · refine CodeReq.Disjoint.union_right ?_ ?_
        · first
            | exact CodeReq.Disjoint.singleton (by bv_omega)
            | exact CodeReq.Disjoint.ofProg_singleton
                (CodeReq.ofProg_none_range_len _ _ 36 _ unified_decoder_prog_length
                  (by intro k hk; bv_omega))
            | exact CodeReq.Disjoint.ofProg_singleton
                (CodeReq.ofProg_none_range_len _ _ 6 _ (by rfl) (by intro k hk; bv_omega))
        · intro a'
          by_cases hh : ∀ j, j < 3 * 8 → a' ≠ (base + 180 + 4) + BitVec.ofNat 64 (4 * j)
          · exact Or.inr (spillChainCR_none (base + 180 + 4) a' 8 hh)
          · push Not at hh; obtain ⟨j, hj, rfl⟩ := hh
            first
              | exact Or.inl (CodeReq.singleton_miss (by bv_omega))
              | exact Or.inl (CodeReq.ofProg_none_range_len _ _ 36 _ unified_decoder_prog_length
                  (by intro k hk; bv_omega))
              | exact Or.inl (CodeReq.ofProg_none_range_len _ _ 6 _ (by rfl)
                  (by intro k hk; bv_omega))
  refine ⟨?_, hpure⟩
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq hd
      (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) t_dec')
      store')

end EvmAsm.Rv64.RLP
