/-
  EvmAsm.Codegen.Programs.RlpRecursiveDecodeDirect

  Linked-image view of the recursive RLP decoder.  `RecDecode.itemsProg` and
  `decProg` are the verified model programs, but their three/two-instruction
  `li x28; jalr` call pairs are not the linked image: RlpWalk emits a direct
  `jal` followed by `nop` at the same two-instruction footprint.  This module
  makes that distinction explicit and ties the direct image back to the
  existing string emitter before attempting the semantic correspondence.
-/

import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

set_option maxRecDepth 8000

def recursiveDecodeItemsDirectRelocs : RelocTable := rlpDecodeItemsDirectRelocs

def recursiveDecodeDecDirectRelocs : RelocTable := rlpDecodeDecDirectRelocs

def recursiveDecodeItemsDirect_prog : Program := rlpDecodeItemsDirect_prog

def recursiveDecodeDecDirect_prog : Program := rlpDecodeDecDirect_prog

#guard recursiveDecodeItemsDirect_prog.length = 93
#guard recursiveDecodeDecDirect_prog.length = 106
#guard recursiveDecodeItemsDirectRelocs.length = 3
#guard recursiveDecodeDecDirectRelocs.length = 3

theorem recursiveDecodeItemsDirect_readBe_slot_1 :
    CodeReq.ofProg GuestAddrs.rlp_recursive_decode_items
      recursiveDecodeItemsDirect_prog
      (GuestAddrs.rlp_recursive_decode_items + 96) =
      some (.JAL .x1 (jalOff GuestAddrs.rlp_recursive_decode_read_be
        (GuestAddrs.rlp_recursive_decode_items + 96))) := by
  decide

theorem recursiveDecodeItems_model_readBe_slot_1 :
    CodeReq.ofProg EvmAsm.Rv64.SAsm.RecDecode.itemsEntry
      EvmAsm.Rv64.SAsm.RecDecode.itemsProg
      (EvmAsm.Rv64.SAsm.RecDecode.itemsEntry + 96) =
      some (.LI .x28 6144) := by
  decide

theorem recursiveDecodeItemsDirect_readBe_slot_2 :
    CodeReq.ofProg GuestAddrs.rlp_recursive_decode_items
      recursiveDecodeItemsDirect_prog
      (GuestAddrs.rlp_recursive_decode_items + 204) =
      some (.JAL .x1 (jalOff GuestAddrs.rlp_recursive_decode_read_be
        (GuestAddrs.rlp_recursive_decode_items + 204))) := by
  decide

theorem recursiveDecodeItemsDirect_child_slot :
    CodeReq.ofProg GuestAddrs.rlp_recursive_decode_items
      recursiveDecodeItemsDirect_prog
      (GuestAddrs.rlp_recursive_decode_items + 308) =
      some (.JAL .x1 (jalOff GuestAddrs.rlp_recursive_decode
        (GuestAddrs.rlp_recursive_decode_items + 308))) := by
  decide

theorem recursiveDecodeDecDirect_readBe_slot_1 :
    CodeReq.ofProg GuestAddrs.rlp_recursive_decode
      recursiveDecodeDecDirect_prog
      (GuestAddrs.rlp_recursive_decode + 164) =
      some (.JAL .x1 (jalOff GuestAddrs.rlp_recursive_decode_read_be
        (GuestAddrs.rlp_recursive_decode + 164))) := by
  decide

theorem recursiveDecodeDecDirect_readBe_slot_2 :
    CodeReq.ofProg GuestAddrs.rlp_recursive_decode
      recursiveDecodeDecDirect_prog
      (GuestAddrs.rlp_recursive_decode + 316) =
      some (.JAL .x1 (jalOff GuestAddrs.rlp_recursive_decode_read_be
        (GuestAddrs.rlp_recursive_decode + 316))) := by
  decide

theorem recursiveDecodeDecDirect_items_slot :
    CodeReq.ofProg GuestAddrs.rlp_recursive_decode
      recursiveDecodeDecDirect_prog
      (GuestAddrs.rlp_recursive_decode + 392) =
      some (.JAL .x1 (jalOff GuestAddrs.rlp_recursive_decode_items
        (GuestAddrs.rlp_recursive_decode + 392))) := by
  decide

/-- The direct linked image's two recursive routines and the read-be leaf. -/
def recursiveDecodeDirectCode : CodeReq :=
  ((CodeReq.ofProg GuestAddrs.rlp_recursive_decode recursiveDecodeDecDirect_prog).union
    (CodeReq.ofProg GuestAddrs.rlp_recursive_decode_items
      recursiveDecodeItemsDirect_prog)).union
    (CodeReq.ofProg GuestAddrs.rlp_recursive_decode_read_be
      EvmAsm.Rv64.SAsm.RecDecode.rdbeProg)

/-- The direct-JAL items program renders to the symbolic body already emitted
    by `RlpWalk`; the reloc table hides only the concrete linked displacement. -/
theorem recursiveDecodeItemsDirect_body_eq :
    emitProgramR recursiveDecodeItemsDirect_prog recursiveDecodeItemsDirectRelocs =
      rlpDecodeItemsBody := by
  decide

/-- The direct-JAL decoder program renders to the symbolic body already emitted
    by `RlpWalk`; the reloc table hides only the concrete linked displacement. -/
theorem recursiveDecodeDecDirect_body_eq :
    emitProgramR recursiveDecodeDecDirect_prog recursiveDecodeDecDirectRelocs =
      rlpDecodeDecBody := by
  decide

#print axioms recursiveDecodeItemsDirect_body_eq
#print axioms recursiveDecodeDecDirect_body_eq

end EvmAsm.Codegen
