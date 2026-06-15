/-
  EvmAsm.Rv64.RLP.Phase1E3LongStringFromBytesBE

  End-to-end spec-correctness restatements of the long byte-string (e3)
  full paths: the decoder's output length register `x11` equals the value the
  pure RLP spec decodes, `BitVec.ofNat 64 (Nat.fromBytesBE [e0, …, e_{N-1}])`,
  where `ei = extractByte wordVal (byteOffset (ptr + i))`.

  Each theorem wraps the corresponding `rlp_phase1_e3_0x…_…_byte_length_spec_within`
  full path and rewrites the raw big-endian accumulation in `x11` to the
  `Nat.fromBytesBE` form via the bridge lemmas in `Phase2LongLengthBridge.lean`.
  Proof shape (per N ≥ 2): rewrite the *goal* backwards
  (`← rlp_be_len_N`, `← …_post_unfold`) into the closure's `_post`, then close
  with the underlying full path. The `lenLen = 1` path (`0xB8`) collapses the
  accumulation to a single byte, so it uses `rlp_be_byte_eq_fromBytesBE`.
-/

import EvmAsm.Rv64.RLP.Phase1E3LongStringOne
import EvmAsm.Rv64.RLP.Phase1E3LongStringTwo
import EvmAsm.Rv64.RLP.Phase1E3LongStringThree
import EvmAsm.Rv64.RLP.Phase1E3LongStringFour
import EvmAsm.Rv64.RLP.Phase1E3LongStringFive
import EvmAsm.Rv64.RLP.Phase1E3LongStringSix
import EvmAsm.Rv64.RLP.Phase1E3LongStringSeven
import EvmAsm.Rv64.RLP.Phase1E3LongStringEight
import EvmAsm.Rv64.RLP.Phase2LongLengthBridge

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- `0xB8` long string (`lenLen = 1`): `x11 = ofNat (fromBytesBE [e0])`. -/
theorem rlp_phase1_e3_0xB8_one_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 back : BitVec 13)
    (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (halign : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (hvalid : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    cpsTripleWithin 15 base ((e3_target + 12) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
          (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
          (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB8 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB8 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0])) **
        (.x12 ↦ᵣ e0.zeroExtend 64) **
        (.x13 ↦ᵣ ((v13 + signExtend12 (1 : BitVec 12)) + 1)) **
        (.x14 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0
  rw [← rlp_be_byte_eq_fromBytesBE e0]
  exact rlp_phase1_e3_0xB8_one_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 back base
    e3_target htarget halign hvalid hd_phase3 hd_loop

/-- `0xB9` long string (`lenLen = 2`): `x11 = ofNat (fromBytesBE [e0, e1])`. -/
theorem rlp_phase1_e3_0xB9_two_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 back : BitVec 13)
    (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (halign1 : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (halign2 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 1) = dwordAddr)
    (hvalid1 : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hvalid2 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 1) = true)
    (hback : ((e3_target + 12) + 20) + signExtend13 back = (e3_target + 12))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    cpsTripleWithin 21 base ((e3_target + 12) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
          (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
          (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB9 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xB9 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1])) **
        (.x13 ↦ᵣ (ptr + 2)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e1.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1
  rw [← rlp_be_len_2_eq_fromBytesBE e0 e1,
      ← rlp_phase2_long_loop_two_byte_post_unfold]
  exact rlp_phase1_e3_0xB9_two_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 back base
    e3_target htarget halign1 halign2 hvalid1 hvalid2 hback hd_phase3 hd_loop

/-- `0xBA` long string (`lenLen = 3`). -/
theorem rlp_phase1_e3_0xBA_three_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 back : BitVec 13)
    (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (halign1 : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (halign2 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 1) = dwordAddr)
    (halign3 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 2) = dwordAddr)
    (hvalid1 : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hvalid2 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 1) = true)
    (hvalid3 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 2) = true)
    (hback : ((e3_target + 12) + 20) + signExtend13 back = (e3_target + 12))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    let e2 := extractByte wordVal (byteOffset (ptr + 2))
    cpsTripleWithin 27 base ((e3_target + 12) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
          (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
          (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBA : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xBA : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2])) **
        (.x13 ↦ᵣ (ptr + 3)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e2.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1 e2
  rw [← rlp_be_len_3_eq_fromBytesBE e0 e1 e2,
      ← rlp_phase2_long_loop_three_byte_post_unfold]
  exact rlp_phase1_e3_0xBA_three_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 back base
    e3_target htarget halign1 halign2 halign3 hvalid1 hvalid2 hvalid3 hback
    hd_phase3 hd_loop

/-- `0xBB` long string (`lenLen = 4`). -/
theorem rlp_phase1_e3_0xBB_four_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 back : BitVec 13)
    (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (halign1 : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (halign2 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 1) = dwordAddr)
    (halign3 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 2) = dwordAddr)
    (halign4 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 3) = dwordAddr)
    (hvalid1 : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hvalid2 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 1) = true)
    (hvalid3 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 2) = true)
    (hvalid4 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 3) = true)
    (hback : ((e3_target + 12) + 20) + signExtend13 back = (e3_target + 12))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    let e2 := extractByte wordVal (byteOffset (ptr + 2))
    let e3 := extractByte wordVal (byteOffset (ptr + 3))
    cpsTripleWithin 33 base ((e3_target + 12) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
          (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
          (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBB : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xBB : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2, e3])) **
        (.x13 ↦ᵣ (ptr + 4)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e3.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1 e2 e3
  rw [← rlp_be_len_4_eq_fromBytesBE e0 e1 e2 e3,
      ← rlp_phase2_long_loop_four_byte_post_unfold]
  exact rlp_phase1_e3_0xBB_four_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 back base
    e3_target htarget halign1 halign2 halign3 halign4
    hvalid1 hvalid2 hvalid3 hvalid4 hback hd_phase3 hd_loop

/-- `0xBC` long string (`lenLen = 5`). -/
theorem rlp_phase1_e3_0xBC_five_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 back : BitVec 13)
    (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (halign1 : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (halign2 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 1) = dwordAddr)
    (halign3 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 2) = dwordAddr)
    (halign4 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 3) = dwordAddr)
    (halign5 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 4) = dwordAddr)
    (hvalid1 : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hvalid2 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 1) = true)
    (hvalid3 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 2) = true)
    (hvalid4 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 3) = true)
    (hvalid5 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 4) = true)
    (hback : ((e3_target + 12) + 20) + signExtend13 back = (e3_target + 12))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    let e2 := extractByte wordVal (byteOffset (ptr + 2))
    let e3 := extractByte wordVal (byteOffset (ptr + 3))
    let e4 := extractByte wordVal (byteOffset (ptr + 4))
    cpsTripleWithin 39 base ((e3_target + 12) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
          (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
          (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBC : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xBC : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2, e3, e4])) **
        (.x13 ↦ᵣ (ptr + 5)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e4.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1 e2 e3 e4
  rw [← rlp_be_len_5_eq_fromBytesBE e0 e1 e2 e3 e4,
      ← rlp_phase2_long_loop_five_byte_post_unfold]
  exact rlp_phase1_e3_0xBC_five_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 back base
    e3_target htarget halign1 halign2 halign3 halign4 halign5
    hvalid1 hvalid2 hvalid3 hvalid4 hvalid5 hback hd_phase3 hd_loop

/-- `0xBD` long string (`lenLen = 6`). -/
theorem rlp_phase1_e3_0xBD_six_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 back : BitVec 13)
    (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (halign1 : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (halign2 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 1) = dwordAddr)
    (halign3 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 2) = dwordAddr)
    (halign4 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 3) = dwordAddr)
    (halign5 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 4) = dwordAddr)
    (halign6 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 5) = dwordAddr)
    (hvalid1 : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hvalid2 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 1) = true)
    (hvalid3 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 2) = true)
    (hvalid4 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 3) = true)
    (hvalid5 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 4) = true)
    (hvalid6 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 5) = true)
    (hback : ((e3_target + 12) + 20) + signExtend13 back = (e3_target + 12))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    let e2 := extractByte wordVal (byteOffset (ptr + 2))
    let e3 := extractByte wordVal (byteOffset (ptr + 3))
    let e4 := extractByte wordVal (byteOffset (ptr + 4))
    let e5 := extractByte wordVal (byteOffset (ptr + 5))
    cpsTripleWithin 45 base ((e3_target + 12) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
          (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
          (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBD : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xBD : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2, e3, e4, e5])) **
        (.x13 ↦ᵣ (ptr + 6)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e5.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1 e2 e3 e4 e5
  rw [← rlp_be_len_6_eq_fromBytesBE e0 e1 e2 e3 e4 e5,
      ← rlp_phase2_long_loop_six_byte_post_unfold]
  exact rlp_phase1_e3_0xBD_six_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 back base
    e3_target htarget halign1 halign2 halign3 halign4 halign5 halign6
    hvalid1 hvalid2 hvalid3 hvalid4 hvalid5 hvalid6 hback hd_phase3 hd_loop

/-- `0xBE` long string (`lenLen = 7`). -/
theorem rlp_phase1_e3_0xBE_seven_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 back : BitVec 13)
    (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (halign1 : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (halign2 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 1) = dwordAddr)
    (halign3 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 2) = dwordAddr)
    (halign4 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 3) = dwordAddr)
    (halign5 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 4) = dwordAddr)
    (halign6 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 5) = dwordAddr)
    (halign7 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 6) = dwordAddr)
    (hvalid1 : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hvalid2 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 1) = true)
    (hvalid3 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 2) = true)
    (hvalid4 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 3) = true)
    (hvalid5 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 4) = true)
    (hvalid6 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 5) = true)
    (hvalid7 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 6) = true)
    (hback : ((e3_target + 12) + 20) + signExtend13 back = (e3_target + 12))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    let e2 := extractByte wordVal (byteOffset (ptr + 2))
    let e3 := extractByte wordVal (byteOffset (ptr + 3))
    let e4 := extractByte wordVal (byteOffset (ptr + 4))
    let e5 := extractByte wordVal (byteOffset (ptr + 5))
    let e6 := extractByte wordVal (byteOffset (ptr + 6))
    cpsTripleWithin 51 base ((e3_target + 12) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
          (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
          (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBE : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xBE : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2, e3, e4, e5, e6])) **
        (.x13 ↦ᵣ (ptr + 7)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e6.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1 e2 e3 e4 e5 e6
  rw [← rlp_be_len_7_eq_fromBytesBE e0 e1 e2 e3 e4 e5 e6,
      ← rlp_phase2_long_loop_seven_byte_post_unfold]
  exact rlp_phase1_e3_0xBE_seven_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 back base
    e3_target htarget halign1 halign2 halign3 halign4 halign5 halign6 halign7
    hvalid1 hvalid2 hvalid3 hvalid4 hvalid5 hvalid6 hvalid7 hback hd_phase3 hd_loop

/-- `0xBF` long string (`lenLen = 8`, the maximum). -/
theorem rlp_phase1_e3_0xBF_eight_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 back : BitVec 13)
    (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (halign1 : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (halign2 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 1) = dwordAddr)
    (halign3 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 2) = dwordAddr)
    (halign4 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 3) = dwordAddr)
    (halign5 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 4) = dwordAddr)
    (halign6 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 5) = dwordAddr)
    (halign7 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 6) = dwordAddr)
    (halign8 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 7) = dwordAddr)
    (hvalid1 : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hvalid2 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 1) = true)
    (hvalid3 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 2) = true)
    (hvalid4 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 3) = true)
    (hvalid5 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 4) = true)
    (hvalid6 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 5) = true)
    (hvalid7 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 6) = true)
    (hvalid8 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 7) = true)
    (hback : ((e3_target + 12) + 20) + signExtend13 back = (e3_target + 12))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    let e2 := extractByte wordVal (byteOffset (ptr + 2))
    let e3 := extractByte wordVal (byteOffset (ptr + 3))
    let e4 := extractByte wordVal (byteOffset (ptr + 4))
    let e5 := extractByte wordVal (byteOffset (ptr + 5))
    let e6 := extractByte wordVal (byteOffset (ptr + 6))
    let e7 := extractByte wordVal (byteOffset (ptr + 7))
    cpsTripleWithin 57 base ((e3_target + 12) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
          (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
          (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBF : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xBF : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64
          (Nat.fromBytesBE [e0, e1, e2, e3, e4, e5, e6, e7])) **
        (.x13 ↦ᵣ (ptr + 8)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e7.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1 e2 e3 e4 e5 e6 e7
  rw [← rlp_be_len_8_eq_fromBytesBE e0 e1 e2 e3 e4 e5 e6 e7,
      ← rlp_phase2_long_loop_eight_byte_post_unfold]
  exact rlp_phase1_e3_0xBF_eight_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 back base
    e3_target htarget halign1 halign2 halign3 halign4 halign5 halign6 halign7
    halign8 hvalid1 hvalid2 hvalid3 hvalid4 hvalid5 hvalid6 hvalid7 hvalid8
    hback hd_phase3 hd_loop

end EvmAsm.Rv64.RLP
