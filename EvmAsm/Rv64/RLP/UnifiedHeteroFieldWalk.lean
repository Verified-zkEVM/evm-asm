/-
  EvmAsm.Rv64.RLP.UnifiedHeteroFieldWalk

  EL.3 / Phase 5 — the first HETEROGENEOUS multi-field walk: a scalar field followed by a
  byte-array field, both decoded into ONE shared whole-struct output `bytesRegion`. This is
  the keystone that ties the two field-type decoders together — real STF schemas (legacy
  tx, block header) interleave u64 scalars (`nonce`, `gas`) with fixed byte arrays
  (20-byte `address`, 32-byte hash).

  Field A (scalar, `1 ≤ len ≤ 8`) is decoded by `unified_scalar_field_decode_and_store_region`
  (concrete scratch pre), which spills its u64 value little-endian into the output region at
  byte offset `diA` and advances `x13` to the next field. Field B (byte array, `1 ≤ len ≤ 55`)
  is decoded by `unified_bytes_field_decode_and_copy_at_regOwn` (the `regOwn`-pre variant,
  callable after A clobbered the scratch), which copies its payload into the output region at
  byte offset `diB`. A's `x13` feeds B's payload pointer with no glue; the output region is
  threaded directly (A's `spillRange` is B's input `bytesRegion`), so the final region holds
  both fields. Coincides with the scalar peel for A and the item-decode peel for B.

  Layout (program base `base`; aligned `regionBase`/`bs`, output `outBase`/`outBytes`):
      base       < scalar field A : decode + spill into region >   (base .. base+280)
      base+280   < byte field  B : decode + copy  into region >    (base+280 .. base+432+20·|dataB|)
-/

import EvmAsm.Rv64.RLP.UnifiedScalarFieldRegion
import EvmAsm.Rv64.RLP.UnifiedBytesFieldRegOwn

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- Spilling preserves the destination list's length (it is a sequence of `List.set`s). -/
theorem spillRange_length (dst : List Byte) (v : Word) (di0 N : Nat) :
    (spillRange dst v di0 N).length = dst.length := by
  induction N generalizing dst v di0 with
  | zero => rfl
  | succ n ih => rw [spillRange, ih, List.length_set]

set_option maxRecDepth 8000 in
/-- **Heterogeneous two-field walk (scalar ⨾ byte-array, shared output region).** Decode
    scalar field A at buffer offset `OA` and spill its u64 value into the output region at
    byte offset `diA`; then decode byte-array field B (at `OA + len(A)`) and copy its payload
    into the same region at byte offset `diB`. The output region is threaded directly, so it
    ends holding both fields: `copyRangeGen (spillRange outBytes valueA diA 8) dataB 0 diB
    |dataB|`. Coincides with the scalar decode of A and the item decode of B. -/
theorem unified_hetero_field_walk
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (offA offB : BitVec 12)
    (bs : List Byte) (OA : Nat) (dataA dataB tail : List Byte) (outBytes : List Byte)
    (diA diB : Nat) (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hlenA1 : 1 ≤ dataA.length) (hlenA8 : dataA.length ≤ 8)
    (hlenB1 : 1 ≤ dataB.length) (hlenB55 : dataB.length ≤ 55)
    (hsizeB : (encode (.bytes dataB)).length < 256 ^ 8)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hImmA : signExtend12 offA = BitVec.ofNat 64 diA)
    (hImmB : signExtend12 offB = BitVec.ofNat 64 diB)
    (hdstA : diA + 8 ≤ outBytes.length)
    (hdstB : diB + dataB.length ≤ outBytes.length)
    (hcode : base.toNat + (280 + (148 + 4 + 20 * dataB.length)) < 2 ^ 64)
    (hdrop : bs.drop OA = encode (.bytes dataA) ++ encode (.bytes dataB) ++ tail) :
    cpsTripleWithin
        (((61 + (2 + 6 * dataA.length)) + (1 + 3 * 8)) + (61 + (1 + 5 * dataB.length))) base
        (base + 432 + BitVec.ofNat 64 (20 * dataB.length))
      (((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
            (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
                (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
                (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20))))).union
          ((CodeReq.singleton (base + 180) (.ADDI .x14 rOut offA)).union
            (spillChainCR (base + 180 + 4) 8))).union
        ((((CodeReq.singleton (base + 280) (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 280 + 4) unified_decoder_prog)).union
          ((CodeReq.singleton (base + 280 + 148) (.ADDI .x14 rOut offB)).union
            (byteCopyChainCR (base + 280 + 148 + 4) dataB.length)))))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 OA)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64
            ((OA + (encode (.bytes dataA)).length) + (encode (.bytes dataB)).length))) **
        (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (diB + dataB.length))) ** (regOwn .x15) **
        (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
        bytesRegion outBase (copyRangeGen
          (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE dataA)) diA 8)
          dataB 0 diB dataB.length)) **
       (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11))
    ∧ decodeScalar (bs.drop OA) = some (Nat.fromBytesBE dataA, encode (.bytes dataB) ++ tail)
    ∧ decode (bs.drop (OA + (encode (.bytes dataA)).length)) = some (.bytes dataB, tail) := by
  -- Field A's payload is followed by field B's encoding (re-associate the append).
  have hdropA : bs.drop OA = encode (.bytes dataA) ++ (encode (.bytes dataB) ++ tail) := by
    rw [hdrop, List.append_assoc]
  -- Field B starts exactly after field A's encoding.
  have hdropB : bs.drop (OA + (encode (.bytes dataA)).length) = encode (.bytes dataB) ++ tail := by
    rw [← List.drop_drop, hdropA, List.drop_append_length]
  -- Scalar field A: decode + spill into the output region (concrete scratch pre).
  obtain ⟨tA, hpureA⟩ := unified_scalar_field_decode_and_store_region base regionBase rOut outBase
    offA bs OA dataA (encode (.bytes dataB) ++ tail) outBytes diA
    v5Old v10 v11Old v12Old v14Old v15Old hlenA1 hlenA8 halign hover hwin hdropA hdalign hdstA
    hdov hdval hImmA (by omega)
  rw [show base + 180 + 4 + BitVec.ofNat 64 (12 * 8) = base + 280 from by bv_omega] at tA
  -- Byte-array field B: decode + copy into the (now spilled) region (regOwn scratch pre).
  obtain ⟨tB, hpureB⟩ := unified_bytes_field_decode_and_copy_at_regOwn (base + 280) regionBase rOut
    outBase offB bs (OA + (encode (.bytes dataA)).length) dataB tail
    (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE dataA)) diA 8) diB
    (outBase + BitVec.ofNat 64 (diA + 8)) v15Old hlenB1 hlenB55 hsizeB halign hdalign hover hwin
    hImmB (by rw [spillRange_length]; exact hdstB)
    (by rw [spillRange_length]; exact hdov)
    (by intro i hi; rw [spillRange_length] at hi; exact hdval i hi)
    (by have h280 : (base + 280).toNat = base.toNat + 280 := by bv_omega
        omega) hdropB
  rw [show base + 280 + 148 + 4 + BitVec.ofNat 64 (20 * dataB.length)
      = base + 432 + BitVec.ofNat 64 (20 * dataB.length) from by bv_omega] at tB
  -- Disjointness: field A's code (base .. base+280) ⊥ field B's code (≥ base+280), by range.
  have hd : (((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
            (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
            (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20))))).union
        ((CodeReq.singleton (base + 180) (.ADDI .x14 rOut offA)).union
          (spillChainCR (base + 180 + 4) 8)))).Disjoint
      ((((CodeReq.singleton (base + 280) (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 280 + 4) unified_decoder_prog)).union
        ((CodeReq.singleton (base + 280 + 148) (.ADDI .x14 rOut offB)).union
          (byteCopyChainCR (base + 280 + 148 + 4) dataB.length)))) := by
    intro a
    by_cases hlo : a.toNat < base.toNat + 280
    · -- `a` is in field A's range ⇒ every field-B slot (≥ base+280) misses `a`.
      refine Or.inr ?_
      have hm1 : CodeReq.singleton (base + 280) (.LBU .x5 .x13 0) a = none :=
        CodeReq.singleton_miss (by bv_omega)
      have hm2 : CodeReq.ofProg (base + 280 + 4) unified_decoder_prog a = none :=
        CodeReq.ofProg_none_range_len _ _ 36 a unified_decoder_prog_length (fun k hk => by bv_omega)
      have hm3 : CodeReq.singleton (base + 280 + 148) (.ADDI .x14 rOut offB) a = none :=
        CodeReq.singleton_miss (by bv_omega)
      have hm4 : byteCopyChainCR (base + 280 + 148 + 4) dataB.length a = none :=
        byteCopyChainCR_none _ a dataB.length (fun j hj => by bv_omega)
      simp only [CodeReq.union, hm1, hm2, hm3, hm4]
    · -- `a` is past field A's range ⇒ every field-A slot (< base+280) misses `a`.
      refine Or.inl ?_
      have hl1 : CodeReq.singleton base (.LBU .x5 .x13 0) a = none :=
        CodeReq.singleton_miss (by bv_omega)
      have hl2 : CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
        CodeReq.ofProg_none_range_len _ _ 36 a unified_decoder_prog_length (fun k hk => by bv_omega)
      have hl3 : CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0) a = none :=
        CodeReq.singleton_miss (by bv_omega)
      have hl4 : CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0) a = none :=
        CodeReq.singleton_miss (by bv_omega)
      have hl5 : CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20)) a = none :=
        CodeReq.ofProg_none_range_len _ _ 6 a (by rfl) (fun k hk => by bv_omega)
      have hl6 : CodeReq.singleton (base + 180) (.ADDI .x14 rOut offA) a = none :=
        CodeReq.singleton_miss (by bv_omega)
      have hl7 : spillChainCR (base + 180 + 4) 8 a = none :=
        spillChainCR_none _ a 8 (fun j hj => by bv_omega)
      simp only [CodeReq.union, hl1, hl2, hl3, hl4, hl5, hl6, hl7]
  refine ⟨?_, hpureA, hpureB⟩
  exact cpsTripleWithin_seq hd
    (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) tA) tB

end EvmAsm.Rv64.RLP
