/-
  EvmAsm.Rv64.RLP.ValidatingBytesCopy

  SINGLE-PASS validated fixed-length BYTE-ARRAY field copy (T2/T3 building block of #9373). The
  byte-array analog of `rlp_decode_shortBytes_scalar_store_at`: composes the offset-general
  validating shortBytes decoder with the existing byte-copy engine (`unified_field_bytes_copy`) on
  the decoder's SUCCESS exit. The validating arm leaves the payload pointer in `x13` and payload
  length in `x11`; the copy then streams the `N` payload bytes straight into a fixed slot of an
  output struct — validated and copied in one forward sweep, no reparse.

  Used for `withdrawal_decode`'s 20-byte `address` field (and the header hash fields). `rOut` is a
  callee-saved register holding the output base; `N` (= the validated payload length) is the field's
  fixed width — the surrounding decoder supplies the runtime width check that pins `payloadLen = N`.

  SUCCESS: the output region's slot `[di0, di0+N)` holds the payload bytes, carrying the verdict
  `decode (pfx :: rest) = some (.bytes (rest.take N), rest.drop N)`. FAIL: the decoder's abort exit.
-/

import EvmAsm.Rv64.RLP.UnifiedDecodeItemShortBytesValidatedAt
import EvmAsm.Rv64.RLP.UnifiedFieldBytesCopy
import EvmAsm.Rv64.RLP.ValidatingFieldWalk

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- The validating arm leaves `x13` at `(regionBase + O) + signExtend12 1`; that is the payload
    pointer `regionBase + (O+1)` the byte copy consumes. -/
private theorem bytescopy_ptr_eq (regionBase : Word) (O : Nat) :
    (regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12)
    = regionBase + BitVec.ofNat 64 (O + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Sequence a branch onto the TAKEN exit of a branch, converging the follow-on branch's TAKEN exit
    with the first branch's fall exit onto a shared fail exit `exitF`. Used to bolt a length-equality
    check onto a validating decode's success so that *both* a malformed field (the decoder's bound
    failure) and a wrong-length field converge on the one `a0 ≠ 0` exit. -/
theorem cpsBranchWithin_seq_cpsBranchWithin_taken_conv {n1 n2 : Nat}
    {entry mid succ exitF : Word} {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q_t1 Q_f1 Q_t2 Q_succ Q_f : Assertion}
    (h1 : cpsBranchWithin n1 entry cr1 P mid Q_t1 exitF Q_f1)
    (h2 : cpsBranchWithin n2 mid cr2 Q_t1 exitF Q_t2 succ Q_succ)
    (hf1 : ∀ h, Q_f1 h → Q_f h) (hf2 : ∀ h, Q_t2 h → Q_f h) :
    cpsBranchWithin (n1 + n2) entry (cr1.union cr2) P succ Q_succ exitF Q_f := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, hk1, s1, hstep1, hbranch1⟩ := h1 R hR s hcr1 hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · have hcr2' := CodeReq.SatisfiedBy_preserved hstep1 hcr2
    obtain ⟨k2, hk2, s2, hstep2, hbranch2⟩ := h2 R hR s1 hcr2' hQ_t1R hpc_t1
    rcases hbranch2 with ⟨hpc_t2, hQ_t2R⟩ | ⟨hpc_f2, hQ_succR⟩
    · exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
        Or.inr ⟨hpc_t2, by
          obtain ⟨hp, hcompat, hpq⟩ := hQ_t2R
          exact ⟨hp, hcompat, sepConj_mono_left hf2 hp hpq⟩⟩⟩
    · exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
        Or.inl ⟨hpc_f2, hQ_succR⟩⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1, hstep1,
      Or.inr ⟨hpc_f1, by
        obtain ⟨hp, hcompat, hpq⟩ := hQ_f1R
        exact ⟨hp, hcompat, sepConj_mono_left hf1 hp hpq⟩⟩⟩

set_option linter.unusedVariables false in
/-- **Single-pass validated fixed-length byte-array copy** at byte offset `O`: validate the
    shortBytes field, then stream its `N`-byte payload into the output slot `outBase + di0`. -/
theorem rlp_decode_shortBytes_bytescopy_at
    (pfx : Byte) (rest : List Byte) (bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (outBytes : List Byte) (di0 : Nat)
    (off1 off2 succOff : BitVec 13) (base e2_target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (hLfit : (pfx :: rest).length < 2 ^ 64)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (hsuccPC : (e2_target + 8) + signExtend13 succOff = succPC)
    (hsalign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hsover : regionBase.toNat + bs.length < 2 ^ 64)
    (hsvalid : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsrc : (O + 1) + rlpPrefixShortBytesPayloadLen pfx ≤ bs.length)
    (hdst : di0 + rlpPrefixShortBytesPayloadLen pfx ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : succPC.toNat + (4 + 20 * rlpPrefixShortBytesPayloadLen pfx) < 2 ^ 64)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hd_copy : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               ((CodeReq.singleton succPC (.ADDI .x14 rOut fieldImm)).union
                 (byteCopyChainCR (succPC + 4) (rlpPrefixShortBytesPayloadLen pfx)))) :
    cpsBranchWithin (7 + (1 + 5 * rlpPrefixShortBytesPayloadLen pfx)) base
      (((((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
        (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).union
        ((CodeReq.singleton succPC (.ADDI .x14 rOut fieldImm)).union
          (byteCopyChainCR (succPC + 4) (rlpPrefixShortBytesPayloadLen pfx))))
      (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      -- SUCCESS (taken): the payload is copied into the output slot.
      (succPC + 4 + BitVec.ofNat 64 (20 * rlpPrefixShortBytesPayloadLen pfx))
        ((((regOwn .x12) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + rlpPrefixShortBytesPayloadLen pfx))) **
          (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + rlpPrefixShortBytesPayloadLen pfx))) **
          (regOwn .x15) ** (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
          bytesRegion outBase
            (copyRangeGen outBytes bs (O + 1) di0 (rlpPrefixShortBytesPayloadLen pfx))) **
         ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          ⌜decode (pfx :: rest)
            = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                    rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)))
      -- FAIL (fall): the decoder's abort exit, output untouched.
      (e2_target + 12)
        (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + 1))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest) = none⌝) **
         ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)) := by
  set N := rlpPrefixShortBytesPayloadLen pfx with hN
  -- The validating decoder at offset O; rewrite x13 (both exits) to the payload pointer.
  have decAt := rlp_decode_shortBytes_validated_at pfx rest bs O v10 v11Old v12Old v14Old
    regionBase off1 off2 succOff base e2_target h_class hns hLfit htarget hd_phase3 hd_bltu
  rw [hsuccPC] at decAt
  simp only [bytescopy_ptr_eq] at decAt
  -- Frame the output pointer + region onto both exits.
  have decAtF := cpsBranchWithin_frameR
    ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)
    (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) decAt
  -- The byte copy at succPC, off = O+1, copying N payload bytes into outBase+di0; framed with the
  -- arm's extra atoms (x5/x10/x11 and the pure verdict) and reordered to decAtF's taken post.
  have copyRaw := unified_field_bytes_copy succPC regionBase rOut outBase fieldImm bs outBytes
    (O + 1) di0 N v12Old v14Old (BitVec.ofNat 64 (pfx :: rest).length)
    hsalign hdalign hsover hsvalid hsrc hdst hdov hdval hcode hImm
  have copyF : cpsTripleWithin (1 + 5 * N) succPC (succPC + 4 + BitVec.ofNat 64 (20 * N))
      ((CodeReq.singleton succPC (.ADDI .x14 rOut fieldImm)).union (byteCopyChainCR (succPC + 4) N))
      (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 N)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + 1))) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
        ⌜decode (pfx :: rest) = some (.bytes (rest.take N), rest.drop N)⌝) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      ((((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + N))) **
          (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + N))) ** (regOwn .x15) **
          (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
          bytesRegion outBase (copyRangeGen outBytes bs (O + 1) di0 N)) **
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 N)) **
          ⌜decode (pfx :: rest) = some (.bytes (rest.take N), rest.drop N)⌝))) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 N)) **
          ⌜decode (pfx :: rest) = some (.bytes (rest.take N), rest.drop N)⌝)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs pcFree_pure))))
        copyRaw)
  exact cpsBranchWithin_seq_cpsTripleWithin_taken hd_copy decAtF copyF

end EvmAsm.Rv64.RLP
