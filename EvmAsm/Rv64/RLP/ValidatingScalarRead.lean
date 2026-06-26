/-
  EvmAsm.Rv64.RLP.ValidatingScalarRead

  SINGLE-PASS validated scalar-field extraction (T1 core of #9373). Composes the offset-general
  validating shortBytes decoder (`rlp_decode_shortBytes_validated_at`) with the existing big-endian
  value read (`unified_field_scalar_read`) on the decoder's SUCCESS exit. The validating arm leaves
  exactly the register convention the value read consumes — payload pointer in `x13`, payload length
  in `x11` — so a `≤8`-byte scalar field is **validated and its value extracted in one forward
  sweep**, with no second pass over the input (per the maintainer's direction on #9461).

  SUCCESS: `x11 = Nat.fromBytesBE payload`, `x13` advanced to the next field, and the verdict
  `decodeScalar (bs.drop O) = some (that value, …)` (via `decodeScalar_of_decode_bytes`). FAIL is the
  decoder's abort exit (`decode = none`) unchanged.
-/

import EvmAsm.Rv64.RLP.ValidatingFieldWalk
import EvmAsm.Rv64.RLP.UnifiedFieldScalarRead
import EvmAsm.Rv64.RLP.SchemaScalarValues

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- The validating arm leaves `x13` at `(regionBase + O) + signExtend12 1`; that is the payload
    pointer `regionBase + (O+1)` the scalar read consumes. -/
private theorem payload_ptr_eq (regionBase : Word) (O : Nat) :
    (regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12)
    = regionBase + BitVec.ofNat 64 (O + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]

set_option linter.unusedVariables false in
/-- **Single-pass validated scalar read** at byte offset `O`. Runs the validating shortBytes decoder
    then, on SUCCESS, the big-endian value read — one descent, value extracted. Requires the field be
    a non-empty `≤8`-byte payload (`1 ≤ payloadLen ≤ 8`); the surrounding decoder supplies the
    runtime `payloadLen ≤ 8` check that discharges this. -/
theorem rlp_decode_shortBytes_scalar_at
    (pfx : Byte) (rest : List Byte) (bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word)
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
    (hdrop : bs.drop O = pfx :: rest)
    (hn1 : 1 ≤ rlpPrefixShortBytesPayloadLen pfx)
    (hn8 : rlpPrefixShortBytesPayloadLen pfx ≤ 8)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < rlpPrefixShortBytesPayloadLen pfx →
        (O + 1) + i < bs.length
        ∧ isValidByteAccess (regionBase + BitVec.ofNat 64 ((O + 1) + i)) = true)
    (hd_read : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               (((CodeReq.singleton succPC (.ADDI .x14 .x11 0)).union
                   (CodeReq.singleton (succPC + 4) (.ADDI .x11 .x0 0))).union
                   (CodeReq.ofProg (succPC + 8) (rlp_phase2_long_loop_body_prog (-20))))) :
    cpsBranchWithin (7 + (2 + 6 * rlpPrefixShortBytesPayloadLen pfx)) base
      (((((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
        (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).union
        (((CodeReq.singleton succPC (.ADDI .x14 .x11 0)).union
            (CodeReq.singleton (succPC + 4) (.ADDI .x11 .x0 0))).union
            (CodeReq.ofProg (succPC + 8) (rlp_phase2_long_loop_body_prog (-20)))))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs)
      -- SUCCESS (taken): the scalar value is in x11; x13 advanced to the next field.
      (succPC + 32)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64
            (Nat.fromBytesBE (rest.take (rlpPrefixShortBytesPayloadLen pfx))))) **
          (.x12 ↦ᵣ (bs.getD ((O + 1) + (rlpPrefixShortBytesPayloadLen pfx - 1)) 0).zeroExtend 64) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + rlpPrefixShortBytesPayloadLen pfx))) **
          (.x14 ↦ᵣ (0 : Word)) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
          ⌜decodeScalar (bs.drop O)
            = some (Nat.fromBytesBE (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                    rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)
      -- FAIL (fall): the decoder's abort exit, unchanged.
      (e2_target + 12)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + 1))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest) = none⌝) := by
  set pl := rlpPrefixShortBytesPayloadLen pfx with hpl
  have hdrop1 : bs.drop (O + 1) = rest := by
    rw [← List.drop_drop, hdrop]; rfl
  -- The validating decoder at offset O (taken = success). Rewrite `x13` in both exits to the payload
  -- pointer `regionBase + (O+1)` the scalar read consumes.
  have decAt := rlp_decode_shortBytes_validated_at pfx rest bs O v10 v11Old v12Old v14Old
    regionBase off1 off2 succOff base e2_target h_class hns hLfit htarget hd_phase3 hd_bltu
  rw [hsuccPC] at decAt
  simp only [payload_ptr_eq] at decAt
  -- The big-endian value read at succPC, off = O+1, n = payloadLen, framed with the 4 atoms the read
  -- doesn't mention (x5, x10, x15, and the pure decode verdict) and reordered to decAt''s post.
  have readRaw := unified_field_scalar_read succPC regionBase bs (O + 1) pl v12Old v14Old
    hn1 hn8 halign hover hwin
  have readF : cpsTripleWithin (2 + 6 * pl) succPC (succPC + 32)
      (((CodeReq.singleton succPC (.ADDI .x14 .x11 0)).union
          (CodeReq.singleton (succPC + 4) (.ADDI .x11 .x0 0))).union
          (CodeReq.ofProg (succPC + 8) (rlp_phase2_long_loop_body_prog (-20))))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 pl)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + 1))) **
        (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
        bytesRegion regionBase bs **
        ⌜decode (pfx :: rest) = some (.bytes (rest.take pl), rest.drop pl)⌝)
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop (O + 1)).take pl)))) **
        (.x12 ↦ᵣ (bs.getD ((O + 1) + (pl - 1)) 0).zeroExtend 64) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + pl))) **
        (.x14 ↦ᵣ (0 : Word)) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
        bytesRegion regionBase bs **
        ⌜decode (pfx :: rest) = some (.bytes (rest.take pl), rest.drop pl)⌝) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx.zeroExtend 64) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          ⌜decode (pfx :: rest) = some (.bytes (rest.take pl), rest.drop pl)⌝)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs pcFree_pure)))
        readRaw)
  -- Sequence the read onto the decoder's SUCCESS (taken) exit.
  have composed := cpsBranchWithin_seq_cpsTripleWithin_taken hd_read decAt readF
  -- Final post weaken: x11 value `bs.drop (O+1) → rest`, and `⌜decode …⌝ → ⌜decodeScalar (bs.drop O) …⌝`.
  refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ (fun _ hp => hp) composed
  intro _ hp
  rw [hdrop1] at hp
  have hdecode : decode (pfx :: rest) = some (.bytes (rest.take pl), rest.drop pl) := by
    have hp2 := hp
    extract_pure hp2
    obtain ⟨hdec, _⟩ := hp2
    exact hdec
  have hscalar : decodeScalar (bs.drop O)
      = some (Nat.fromBytesBE (rest.take pl), rest.drop pl) := by
    rw [hdrop]; exact decodeScalar_of_decode_bytes hdecode
  -- Both verdicts hold, so the carried pure assertion equals the decodeScalar one (propext).
  rw [propext (iff_of_true hdecode hscalar)] at hp
  exact hp

end EvmAsm.Rv64.RLP
