/-
  EvmAsm.Codegen.Programs.RlpRecursiveDecodeDirect

  Linked-image view of the recursive RLP decoder.  The verified model programs
  and `RlpWalk` now both use the two-instruction direct-call shape (`jal; nop`),
  but the model uses the synthetic entries `0x1000/0x1400/0x1800` while the
  linked image uses `GuestAddrs`.  This module makes that address distinction
  explicit and ties the direct image back to the existing string emitter
  before attempting the semantic correspondence.
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
      some (.JAL .x1 (jalOff 0x1800 (0x1400 + 96))) := by
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

/- Standalone transport lemma for the former indirect spelling.  It records
   why replacing `li x28; jalr` by `jal; nop` preserves the callee-entry view
   after the caller's snapshot is restored; the current model programs already
   flatten to the direct shape, so this fact is not a substitute for the
   direct-call premises discharged in `RecDecode.Knot`. -/
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
