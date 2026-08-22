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

/- The direct image's call pair is a one-step transfer followed by a reserved
   NOP slot.  At the callee entry, it has the same PC, memory, and all
   non-link/non-target-register values as the model's `LI; JALR` pair.  The
   two intentionally visible differences are the model's target value in
   `x28` and its `pc + 8` link versus the direct JAL's unchanged `x28` and
   `pc + 4` link.  The RecDecode post leaves `x28` owned rather than pinned,
   and its body does not consume `x1` or `x28` after these calls; this is the
   local transport fact still needed by a full snapshot-call composition. -/
theorem recursiveDecode_direct_call_pair_transport
    (s : MachineState) (off : BitVec 21) (target : Word)
    (htarget : s.pc + signExtend21 off = target)
    (halign : target &&& ~~~(1 : Word) = target) :
    let model := execInstrBr (execInstrBr s (.LI .x28 target))
      (.JALR .x1 .x28 0)
    let direct := execInstrBr s (.JAL .x1 off)
    model.pc = direct.pc ∧ model.mem = direct.mem ∧
      (∀ r : Reg, r ≠ .x1 → r ≠ .x28 →
        model.getReg r = direct.getReg r) := by
  dsimp
  constructor
  · have htarget' :
        (target + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = target := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) by decide]
      simpa using halign
    simp [execInstrBr, MachineState.setPC, MachineState.getReg,
      MachineState.setReg, htarget]
    exact htarget'
  constructor
  · rfl
  · intro r h1 h28
    simp [execInstrBr, MachineState.setPC, MachineState.getReg,
      MachineState.setReg, htarget, h1, h28]

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
