/-
  EvmAsm.Rv64.RLP.ValidatingScalarStore

  SINGLE-PASS validated scalar-field decode-AND-STORE (T1/T2 building block of #9373). Composes the
  single-pass validated scalar read (`rlp_decode_shortBytes_scalar_at`) with one `SD` that writes the
  decoded value to a fixed slot of an output struct (`outBase + offset`). One forward sweep:
  validate → read value → store to output, with no second pass over the input.

  SUCCESS: the output cell holds `Nat.fromBytesBE payload` and the verdict
  `decodeScalar (bs.drop O) = some (that value, …)` holds. FAIL: the decoder's abort exit, unchanged.
  This is the per-field operation a fixed-schema scalar decoder (`rlp_field_to_u64`,
  `withdrawal_decode`) repeats; `rOut` is a callee-saved register holding the output base (set up by
  the LP64 wrapper), distinct from the decoder's `x5/x10..x15` working set.
-/

import EvmAsm.Rv64.RLP.ValidatingScalarRead

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option linter.unusedVariables false in
/-- **Single-pass validated scalar decode-and-store** at byte offset `O`: validate the shortBytes
    field, read its `≤8`-byte big-endian value, and `SD` it to `outBase + offset` — one sweep. -/
theorem rlp_decode_shortBytes_scalar_store_at
    (pfx : Byte) (rest : List Byte) (bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word) (rOut : Reg) (outBase memOld : Word) (offset : BitVec 12)
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
                   (CodeReq.ofProg (succPC + 8) (rlp_phase2_long_loop_body_prog (-20)))))
    (hd_sd : (((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).union
               (((CodeReq.singleton succPC (.ADDI .x14 .x11 0)).union
                   (CodeReq.singleton (succPC + 4) (.ADDI .x11 .x0 0))).union
                   (CodeReq.ofProg (succPC + 8) (rlp_phase2_long_loop_body_prog (-20))))).Disjoint
               (CodeReq.singleton (succPC + 32) (.SD rOut .x11 offset))) :
    cpsBranchWithin ((7 + (2 + 6 * rlpPrefixShortBytesPayloadLen pfx)) + 1) base
      ((((((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
        (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).union
        (((CodeReq.singleton succPC (.ADDI .x14 .x11 0)).union
            (CodeReq.singleton (succPC + 4) (.ADDI .x11 .x0 0))).union
            (CodeReq.ofProg (succPC + 8) (rlp_phase2_long_loop_body_prog (-20))))).union
        (CodeReq.singleton (succPC + 32) (.SD rOut .x11 offset)))
      (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld)))
      -- SUCCESS (taken): the value is stored in the output slot.
      (succPC + 32 + 4)
        (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64
            (Nat.fromBytesBE (rest.take (rlpPrefixShortBytesPayloadLen pfx))))) **
          (.x12 ↦ᵣ (bs.getD ((O + 1) + (rlpPrefixShortBytesPayloadLen pfx - 1)) 0).zeroExtend 64) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + rlpPrefixShortBytesPayloadLen pfx))) **
          (.x14 ↦ᵣ (0 : Word)) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
          ⌜decodeScalar (bs.drop O)
            = some (Nat.fromBytesBE (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                    rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝) **
         ((rOut ↦ᵣ outBase) **
          ((outBase + signExtend12 offset) ↦ₘ
            BitVec.ofNat 64 (Nat.fromBytesBE (rest.take (rlpPrefixShortBytesPayloadLen pfx))))))
      -- FAIL (fall): the decoder's abort exit, with the output slot untouched.
      (e2_target + 12)
        (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + 1))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest) = none⌝) **
         ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld))) := by
  set pl := rlpPrefixShortBytesPayloadLen pfx with hpl
  -- The single-pass validated scalar read (branch), framed with the output pointer + slot.
  have scalarAt := rlp_decode_shortBytes_scalar_at pfx rest bs O v10 v11Old v12Old v14Old
    regionBase off1 off2 succOff base e2_target h_class hns hLfit htarget hd_phase3 hd_bltu
    succPC hsuccPC hdrop hn1 hn8 halign hover hwin hd_read
  have scalarAtF := cpsBranchWithin_frameR
    ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld))
    (pcFree_sepConj pcFree_regIs pcFree_memIs) scalarAt
  -- The store: SD rOut, x11, offset — writes the decoded value to the output slot.
  have sd_raw := sd_spec_within rOut .x11 outBase
    (BitVec.ofNat 64 (Nat.fromBytesBE (rest.take pl))) memOld offset (succPC + 32)
  -- Frame the rest of the success state (all but rOut/x11/cell) around the store, reordered to the
  -- read's success post.
  have sdF : cpsTripleWithin 1 (succPC + 32) (succPC + 32 + 4)
      (CodeReq.singleton (succPC + 32) (.SD rOut .x11 offset))
      (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (Nat.fromBytesBE (rest.take pl)))) **
        (.x12 ↦ᵣ (bs.getD ((O + 1) + (pl - 1)) 0).zeroExtend 64) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + pl))) **
        (.x14 ↦ᵣ (0 : Word)) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
        ⌜decodeScalar (bs.drop O) = some (Nat.fromBytesBE (rest.take pl), rest.drop pl)⌝) **
       ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld)))
      (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (Nat.fromBytesBE (rest.take pl)))) **
        (.x12 ↦ᵣ (bs.getD ((O + 1) + (pl - 1)) 0).zeroExtend 64) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + pl))) **
        (.x14 ↦ᵣ (0 : Word)) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
        ⌜decodeScalar (bs.drop O) = some (Nat.fromBytesBE (rest.take pl), rest.drop pl)⌝) **
       ((rOut ↦ᵣ outBase) **
        ((outBase + signExtend12 offset) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE (rest.take pl))))) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x12 ↦ᵣ (bs.getD ((O + 1) + (pl - 1)) 0).zeroExtend 64) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + pl))) **
          (.x14 ↦ᵣ (0 : Word)) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
          ⌜decodeScalar (bs.drop O) = some (Nat.fromBytesBE (rest.take pl), rest.drop pl)⌝)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_pure))))))))
        sd_raw)
  exact cpsBranchWithin_seq_cpsTripleWithin_taken hd_sd scalarAtF sdF

end EvmAsm.Rv64.RLP
