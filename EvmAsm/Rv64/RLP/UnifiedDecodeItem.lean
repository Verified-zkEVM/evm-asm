/-
  EvmAsm.Rv64.RLP.UnifiedDecodeItem

  EL.3 capstone: a single unified single-item decode theorem over an arbitrary
  RLP prefix byte. Each of the five `classifyPrefix` classes already has a
  proven full `base → decode` path; this packages them into one theorem whose
  conclusion is a `match classifyPrefix pfx`, dispatching to the right handler.

  Mirrors the pure-spec dispatch shape `decodeAux_cons_eq_classifyPrefix_match`
  (`EvmAsm/EL/RLP/PrefixDecode.lean`): for any prefix the RV64 decoder reaches
  the class-appropriate exit with the spec-correct decoded length
  (`1` / `rlpPrefixShort{Bytes,List}PayloadLen` / `Nat.fromBytesBE …`).

  The long-form-only proof hypotheses (per-byte window `hwin`, loop back-edge
  `hback`) are carried in a `match`-typed hypothesis `hlong`, so flat-class
  callers need not supply them.
-/

import EvmAsm.Rv64.RLP.Phase1ToPhase3SingleByte
import EvmAsm.Rv64.RLP.Phase1E2FullPath
import EvmAsm.Rv64.RLP.Phase1E3LongBytesFull
import EvmAsm.Rv64.RLP.Phase1E4FullPath
import EvmAsm.Rv64.RLP.Phase1E5LongListFull

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- Long-form-only proof obligations (per-byte memory window + loop back-edge),
    gated on the class so flat callers needn't provide them. -/
def rlpDecodeLongHyps (pfx : EvmAsm.EL.RLP.Byte)
    (v13 dwordAddr base : Word) (back : BitVec 13) (e3_target : Word) : Prop :=
  match classifyPrefix pfx with
  | .longBytes =>
      (∀ i, i < rlpPrefixLongBytesLenOfLen pfx →
          alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 i) = dwordAddr
          ∧ isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 i) = true)
        ∧ ((e3_target + 12) + 20) + signExtend13 back = (e3_target + 12)
  | .longList =>
      (∀ i, i < rlpPrefixLongListLenOfLen pfx →
          alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 i) = dwordAddr
          ∧ isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 i) = true)
        ∧ ((base + 44) + 20) + signExtend13 back = (base + 44)
  | _ => True

/-- **Unified single-item decode.** For any prefix byte `pfx`, executing the RLP
    decoder from `base` reaches the class-appropriate exit with the spec-correct
    decoded length. The conclusion dispatches on `classifyPrefix pfx`, each
    branch being the proven per-class full-path handler. -/
theorem rlp_decode_single_item_spec_within
    (pfx : EvmAsm.EL.RLP.Byte)
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 off4 back : BitVec 13)
    (base e1_target e2_target e3_target e4_target : Word)
    (htarget1 : (base + 4) + signExtend13 off1 = e1_target)
    (htarget2 : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (htarget3 : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (htarget4 : (base + 24 + 4) + signExtend13 off4 = e4_target)
    (hlong : rlpDecodeLongHyps pfx v13 dwordAddr base back e3_target)
    (hd_e1 : (rlp_phase1_step_code 0x80 off1 base).Disjoint
              (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog))
    (hd_e2 : ((rlp_phase1_step_code 0x80 off1 base).union
                (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
              (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_e3_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_e3_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
    (hd_e4 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg e4_target rlp_phase3_short_list_prog))
    (hd_e5_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_e5_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))) :
    match classifyPrefix pfx with
    | .singleByte =>
        cpsTripleWithin 3 base (e1_target + 4)
          ((rlp_phase1_step_code 0x80 off1 base).union
             (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog))
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
            (.x11 ↦ᵣ v11Old))
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
            (.x11 ↦ᵣ (1 : Word)))
    | .shortBytes =>
        cpsTripleWithin 6 base (e2_target + 8)
          (((rlp_phase1_step_code 0x80 off1 base).union
              (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
             (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
            (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
            (.x11 ↦ᵣ
              (BitVec.ofNat 64 (EvmAsm.EL.RLP.rlpPrefixShortBytesPayloadLen pfx) : Word)) **
            (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))))
    | .longBytes =>
        cpsTripleWithin (9 + 6 * rlpPrefixLongBytesLenOfLen pfx) base
          ((e3_target + 12) + 24)
          (((((rlp_phase1_step_code 0x80 off1 base).union
              ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
              (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
              (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
          ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x10 ↦ᵣ v10) **
            (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
            (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
          ((.x5 ↦ᵣ pfx.zeroExtend 64) **
            (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
            (.x11 ↦ᵣ BitVec.ofNat 64
              (Nat.fromBytesBE (rlpLoopByteList wordVal (v13 + signExtend12 (1 : BitVec 12))
                (rlpPrefixLongBytesLenOfLen pfx)))) **
            (.x13 ↦ᵣ ((v13 + signExtend12 (1 : BitVec 12))
              + BitVec.ofNat 64 (rlpPrefixLongBytesLenOfLen pfx))) ** (.x14 ↦ᵣ (0 : Word)) **
            (.x12 ↦ᵣ (extractByte wordVal (byteOffset ((v13 + signExtend12 (1 : BitVec 12))
              + BitVec.ofNat 64 (rlpPrefixLongBytesLenOfLen pfx - 1)))).zeroExtend 64) **
            (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
    | .shortList =>
        cpsTripleWithin 10 base (e4_target + 8)
          (((rlp_phase1_step_code 0x80 off1 base).union
            ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
              ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
            (CodeReq.ofProg e4_target rlp_phase3_short_list_prog))
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
            (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
            (.x11 ↦ᵣ
              (BitVec.ofNat 64 (EvmAsm.EL.RLP.rlpPrefixShortListPayloadLen pfx) : Word)) **
            (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))))
    | .longList =>
        cpsTripleWithin (11 + 6 * rlpPrefixLongListLenOfLen pfx) base
          ((base + 44) + 24)
          (((((rlp_phase1_step_code 0x80 off1 base).union
            ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
              ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
            (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
            (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
          ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x10 ↦ᵣ v10) **
            (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
            (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
          ((.x5 ↦ᵣ pfx.zeroExtend 64) **
            (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
            (.x11 ↦ᵣ BitVec.ofNat 64
              (Nat.fromBytesBE (rlpLoopByteList wordVal (v13 + signExtend12 (1 : BitVec 12))
                (rlpPrefixLongListLenOfLen pfx)))) **
            (.x13 ↦ᵣ ((v13 + signExtend12 (1 : BitVec 12))
              + BitVec.ofNat 64 (rlpPrefixLongListLenOfLen pfx))) ** (.x14 ↦ᵣ (0 : Word)) **
            (.x12 ↦ᵣ (extractByte wordVal (byteOffset ((v13 + signExtend12 (1 : BitVec 12))
              + BitVec.ofNat 64 (rlpPrefixLongListLenOfLen pfx - 1)))).zeroExtend 64) **
            (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  unfold rlpDecodeLongHyps at hlong
  cases h : classifyPrefix pfx with
  | singleByte =>
    exact rlp_phase1_e1_single_byte_of_class_spec_within pfx v10 v11Old off1 base
      e1_target htarget1 h hd_e1
  | shortBytes =>
    exact rlp_phase1_e2_full_path_payload_len_of_class_spec_within pfx v10 v11Old v13
      off1 off2 base e2_target htarget2 h hd_e2
  | longBytes =>
    simp only [h] at hlong
    obtain ⟨hwin, hback⟩ := hlong
    exact rlp_phase1_e3_longBytes_full_spec_within pfx v10 v11Old v12Old v13 v14Old
      wordVal dwordAddr off1 off2 off3 back base e3_target htarget3 h hwin hback
      hd_e3_phase3 hd_e3_loop
  | shortList =>
    exact rlp_phase1_e4_full_path_payload_len_of_class_spec_within pfx v10 v11Old v13
      off1 off2 off3 off4 base e4_target htarget4 h hd_e4
  | longList =>
    simp only [h] at hlong
    obtain ⟨hwin, hback⟩ := hlong
    exact rlp_phase1_e5_longList_full_spec_within pfx v10 v11Old v12Old v13 v14Old
      wordVal dwordAddr off1 off2 off3 off4 back base h hwin hback
      hd_e5_phase3 hd_e5_loop

-- Sanity: a representative prefix per class selects the expected branch.
example : classifyPrefix (0x00 : EvmAsm.EL.RLP.Byte) = .singleByte := by decide
example : classifyPrefix (0x83 : EvmAsm.EL.RLP.Byte) = .shortBytes := by decide
example : classifyPrefix (0xBA : EvmAsm.EL.RLP.Byte) = .longBytes := by decide
example : classifyPrefix (0xC5 : EvmAsm.EL.RLP.Byte) = .shortList := by decide
example : classifyPrefix (0xFA : EvmAsm.EL.RLP.Byte) = .longList := by decide

end EvmAsm.Rv64.RLP
