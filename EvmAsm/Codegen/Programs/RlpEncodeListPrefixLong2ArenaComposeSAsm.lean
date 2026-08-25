/-
  Shared-arena compatibility for the 2-byte long list-prefix arm.

  The first production use is at offset zero in the shared payload arena.  The
  machine proof is the existing 32-step Long2 proof; this theorem gives that
  proof the arena-shaped name and contract so the caller can consume it without
  introducing a second list-prefix implementation.
-/

import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong2Spec

namespace EvmAsm.Codegen
namespace RlpEncodeListPrefixLong2Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP

theorem rlp_encode_list_prefix_long2_arena_zero
    (base len arenaPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (arenaBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 256 ≤ len.toNat)
    (h_len_hi : len.toNat < 65536)
    (h_arena_align : arenaPtr.toNat % 8 = 0)
    (h_arena_len : 2 < arenaBytes.length)
    (h_arena_valid : ∀ k, k < arenaBytes.length →
      isValidByteAccess (arenaPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 32 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpEncodeListPrefix_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ arenaPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
       ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion arenaPtr arenaBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ arenaPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion arenaPtr
         (((arenaBytes.set 0 (0xF9 : BitVec 8)).set 1
             (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 2
           (BitVec.ofNat 8 len.toNat)) **
       (cellPtr ↦ₘ (3 : Word))) := by
  exact rlp_encode_list_prefix_long2_pinned_spec_within base len arenaPtr cellPtr
    raVal v5 v28 v29 v30 v31 arenaBytes cellOld h_len_lo h_len_hi
    h_arena_align h_arena_len h_arena_valid

end RlpEncodeListPrefixLong2Spec
end EvmAsm.Codegen
