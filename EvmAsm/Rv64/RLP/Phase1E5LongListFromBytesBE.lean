/-
  EvmAsm.Rv64.RLP.Phase1E5LongListFromBytesBE

  End-to-end spec-correctness restatements of the long list (e5) full paths:
  the decoder's output length register `x11` equals
  `BitVec.ofNat 64 (Nat.fromBytesBE [e0, …, e_{N-1}])`, the value the pure RLP
  spec decodes, where `ei = extractByte wordVal (byteOffset (ptr + i))`.

  Each theorem wraps the corresponding e5 full path and rewrites the raw
  big-endian accumulation in `x11` to the `Nat.fromBytesBE` form via
  `Phase2LongLengthBridge.lean`. Proof shape: rewrite the *goal* backwards
  (`← rlp_be_len_N`, `← …_post_unfold`) into the closure's `_post`, then close
  with the underlying full path.
-/

import EvmAsm.Rv64.RLP.Phase1E5LongListOne
import EvmAsm.Rv64.RLP.Phase1E5LongListTwo
import EvmAsm.Rv64.RLP.Phase1E5LongListThree
import EvmAsm.Rv64.RLP.Phase1E5LongListFour
import EvmAsm.Rv64.RLP.Phase1E5LongListFive
import EvmAsm.Rv64.RLP.Phase1E5LongListSix
import EvmAsm.Rv64.RLP.Phase1E5LongListSeven
import EvmAsm.Rv64.RLP.Phase1E5LongListEight
import EvmAsm.Rv64.RLP.Phase2LongLengthBridge

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- `0xF8` long list (`lenLen = 1`): `x11 = ofNat (fromBytesBE [e0])`. -/
theorem rlp_phase1_e5_0xF8_one_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 off4 back : BitVec 13)
    (base : Word)
    (halign1 : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (hvalid1 : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    cpsTripleWithin 17 base ((base + 44) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xF8 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xF8 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0])) **
        (.x13 ↦ᵣ (ptr + 1)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e0.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0
  rw [← rlp_be_len_1_eq_fromBytesBE e0,
      ← rlp_phase2_long_loop_one_byte_post_unfold]
  exact rlp_phase1_e5_0xF8_one_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 off4 back base
    halign1 hvalid1 hd_phase3 hd_loop

/-- `0xF9` long list (`lenLen = 2`). -/
theorem rlp_phase1_e5_0xF9_two_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 off4 back : BitVec 13)
    (base : Word)
    (halign1 : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (halign2 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 1) = dwordAddr)
    (hvalid1 : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hvalid2 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 1) = true)
    (hback : ((base + 44) + 20) + signExtend13 back = (base + 44))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    cpsTripleWithin 23 base ((base + 44) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xF9 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xF9 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1])) **
        (.x13 ↦ᵣ (ptr + 2)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e1.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1
  rw [← rlp_be_len_2_eq_fromBytesBE e0 e1,
      ← rlp_phase2_long_loop_two_byte_post_unfold]
  exact rlp_phase1_e5_0xF9_two_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 off4 back base
    halign1 halign2 hvalid1 hvalid2 hback hd_phase3 hd_loop

/-- `0xFA` long list (`lenLen = 3`). -/
theorem rlp_phase1_e5_0xFA_three_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 off4 back : BitVec 13)
    (base : Word)
    (halign1 : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (halign2 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 1) = dwordAddr)
    (halign3 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 2) = dwordAddr)
    (hvalid1 : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hvalid2 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 1) = true)
    (hvalid3 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 2) = true)
    (hback : ((base + 44) + 20) + signExtend13 back = (base + 44))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    let e2 := extractByte wordVal (byteOffset (ptr + 2))
    cpsTripleWithin 29 base ((base + 44) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xFA : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xFA : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2])) **
        (.x13 ↦ᵣ (ptr + 3)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e2.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1 e2
  rw [← rlp_be_len_3_eq_fromBytesBE e0 e1 e2,
      ← rlp_phase2_long_loop_three_byte_post_unfold]
  exact rlp_phase1_e5_0xFA_three_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 off4 back base
    halign1 halign2 halign3 hvalid1 hvalid2 hvalid3 hback hd_phase3 hd_loop

/-- `0xFB` long list (`lenLen = 4`). -/
theorem rlp_phase1_e5_0xFB_four_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 off4 back : BitVec 13)
    (base : Word)
    (halign1 : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (halign2 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 1) = dwordAddr)
    (halign3 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 2) = dwordAddr)
    (halign4 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 3) = dwordAddr)
    (hvalid1 : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hvalid2 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 1) = true)
    (hvalid3 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 2) = true)
    (hvalid4 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 3) = true)
    (hback : ((base + 44) + 20) + signExtend13 back = (base + 44))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    let e2 := extractByte wordVal (byteOffset (ptr + 2))
    let e3 := extractByte wordVal (byteOffset (ptr + 3))
    cpsTripleWithin 35 base ((base + 44) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xFB : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xFB : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2, e3])) **
        (.x13 ↦ᵣ (ptr + 4)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e3.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1 e2 e3
  rw [← rlp_be_len_4_eq_fromBytesBE e0 e1 e2 e3,
      ← rlp_phase2_long_loop_four_byte_post_unfold]
  exact rlp_phase1_e5_0xFB_four_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 off4 back base
    halign1 halign2 halign3 halign4 hvalid1 hvalid2 hvalid3 hvalid4 hback
    hd_phase3 hd_loop

/-- `0xFC` long list (`lenLen = 5`). -/
theorem rlp_phase1_e5_0xFC_five_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 off4 back : BitVec 13)
    (base : Word)
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
    (hback : ((base + 44) + 20) + signExtend13 back = (base + 44))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    let e2 := extractByte wordVal (byteOffset (ptr + 2))
    let e3 := extractByte wordVal (byteOffset (ptr + 3))
    let e4 := extractByte wordVal (byteOffset (ptr + 4))
    cpsTripleWithin 41 base ((base + 44) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xFC : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xFC : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2, e3, e4])) **
        (.x13 ↦ᵣ (ptr + 5)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e4.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1 e2 e3 e4
  rw [← rlp_be_len_5_eq_fromBytesBE e0 e1 e2 e3 e4,
      ← rlp_phase2_long_loop_five_byte_post_unfold]
  exact rlp_phase1_e5_0xFC_five_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 off4 back base
    halign1 halign2 halign3 halign4 halign5
    hvalid1 hvalid2 hvalid3 hvalid4 hvalid5 hback hd_phase3 hd_loop

/-- `0xFD` long list (`lenLen = 6`). -/
theorem rlp_phase1_e5_0xFD_six_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 off4 back : BitVec 13)
    (base : Word)
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
    (hback : ((base + 44) + 20) + signExtend13 back = (base + 44))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    let e2 := extractByte wordVal (byteOffset (ptr + 2))
    let e3 := extractByte wordVal (byteOffset (ptr + 3))
    let e4 := extractByte wordVal (byteOffset (ptr + 4))
    let e5 := extractByte wordVal (byteOffset (ptr + 5))
    cpsTripleWithin 47 base ((base + 44) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xFD : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xFD : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2, e3, e4, e5])) **
        (.x13 ↦ᵣ (ptr + 6)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e5.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1 e2 e3 e4 e5
  rw [← rlp_be_len_6_eq_fromBytesBE e0 e1 e2 e3 e4 e5,
      ← rlp_phase2_long_loop_six_byte_post_unfold]
  exact rlp_phase1_e5_0xFD_six_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 off4 back base
    halign1 halign2 halign3 halign4 halign5 halign6
    hvalid1 hvalid2 hvalid3 hvalid4 hvalid5 hvalid6 hback hd_phase3 hd_loop

/-- `0xFE` long list (`lenLen = 7`). -/
theorem rlp_phase1_e5_0xFE_seven_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 off4 back : BitVec 13)
    (base : Word)
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
    (hback : ((base + 44) + 20) + signExtend13 back = (base + 44))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    let e2 := extractByte wordVal (byteOffset (ptr + 2))
    let e3 := extractByte wordVal (byteOffset (ptr + 3))
    let e4 := extractByte wordVal (byteOffset (ptr + 4))
    let e5 := extractByte wordVal (byteOffset (ptr + 5))
    let e6 := extractByte wordVal (byteOffset (ptr + 6))
    cpsTripleWithin 53 base ((base + 44) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xFE : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xFE : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64
          (Nat.fromBytesBE [e0, e1, e2, e3, e4, e5, e6])) **
        (.x13 ↦ᵣ (ptr + 7)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e6.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1 e2 e3 e4 e5 e6
  rw [← rlp_be_len_7_eq_fromBytesBE e0 e1 e2 e3 e4 e5 e6,
      ← rlp_phase2_long_loop_seven_byte_post_unfold]
  exact rlp_phase1_e5_0xFE_seven_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 off4 back base
    halign1 halign2 halign3 halign4 halign5 halign6 halign7
    hvalid1 hvalid2 hvalid3 hvalid4 hvalid5 hvalid6 hvalid7 hback hd_phase3 hd_loop

/-- `0xFF` long list (`lenLen = 8`, the maximum). -/
theorem rlp_phase1_e5_0xFF_eight_byte_length_fromBytesBE_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 off4 back : BitVec 13)
    (base : Word)
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
    (hback : ((base + 44) + 20) + signExtend13 back = (base + 44))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let e0 := extractByte wordVal (byteOffset ptr)
    let e1 := extractByte wordVal (byteOffset (ptr + 1))
    let e2 := extractByte wordVal (byteOffset (ptr + 2))
    let e3 := extractByte wordVal (byteOffset (ptr + 3))
    let e4 := extractByte wordVal (byteOffset (ptr + 4))
    let e5 := extractByte wordVal (byteOffset (ptr + 5))
    let e6 := extractByte wordVal (byteOffset (ptr + 6))
    let e7 := extractByte wordVal (byteOffset (ptr + 7))
    cpsTripleWithin 59 base ((base + 44) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xFF : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xFF : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64
          (Nat.fromBytesBE [e0, e1, e2, e3, e4, e5, e6, e7])) **
        (.x13 ↦ᵣ (ptr + 8)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ e7.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (dwordAddr ↦ₘ wordVal)) := by
  intro ptr e0 e1 e2 e3 e4 e5 e6 e7
  rw [← rlp_be_len_8_eq_fromBytesBE e0 e1 e2 e3 e4 e5 e6 e7,
      ← rlp_phase2_long_loop_eight_byte_post_unfold]
  exact rlp_phase1_e5_0xFF_eight_byte_length_spec_within
    v10 v11Old v12Old v13 v14Old wordVal dwordAddr off1 off2 off3 off4 back base
    halign1 halign2 halign3 halign4 halign5 halign6 halign7 halign8
    hvalid1 hvalid2 hvalid3 hvalid4 hvalid5 hvalid6 hvalid7 hvalid8 hback
    hd_phase3 hd_loop

end EvmAsm.Rv64.RLP
