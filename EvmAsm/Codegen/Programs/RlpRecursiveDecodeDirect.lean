/-
  EvmAsm.Codegen.Programs.RlpRecursiveDecodeDirect

  Linked-image view of the recursive RLP decoder.  The verified model programs
  and `RlpWalk` both use the two-instruction direct-call shape (`jal; nop`),
  and since the address-pin move the model entries (`RecDecode.decEntry`
  etc.) are the linked `GuestAddrs` values themselves.  This module anchors
  that coincidence and ties the direct image back to the existing string
  emitter before the semantic correspondence.
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

/- Address anchors (build-checked): the verified core's entry pins are the
   linked guest addresses from `GuestAddrs`.  These `#guard`s are the drift
   surface for the pin move; the `rfl` theorems below carry the equalities
   into rewriting. -/
#guard EvmAsm.Rv64.SAsm.RecDecode.decEntry.toNat
  = GuestAddrs.rlp_recursive_decode
#guard EvmAsm.Rv64.SAsm.RecDecode.itemsEntry.toNat
  = GuestAddrs.rlp_recursive_decode_items
#guard EvmAsm.Rv64.SAsm.RecDecode.rdbeEntry.toNat
  = GuestAddrs.rlp_recursive_decode_read_be

theorem decEntry_eq_linked :
    EvmAsm.Rv64.SAsm.RecDecode.decEntry = GuestAddrs.rlp_recursive_decode := rfl

theorem itemsEntry_eq_linked :
    EvmAsm.Rv64.SAsm.RecDecode.itemsEntry
      = GuestAddrs.rlp_recursive_decode_items := rfl

theorem rdbeEntry_eq_linked :
    EvmAsm.Rv64.SAsm.RecDecode.rdbeEntry
      = GuestAddrs.rlp_recursive_decode_read_be := rfl

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
      some (.JAL .x1 (jalOff EvmAsm.Rv64.SAsm.RecDecode.rdbeEntry.toNat
        (EvmAsm.Rv64.SAsm.RecDecode.itemsEntry.toNat + 96))) := by
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

/-- The emitted direct-JAL decoder program IS the verified model program
    (`decProg`), now that the model's entry pins are the linked addresses:
    every `jalOff target site` immediate on both sides is computed from the
    same entry constants.  If this ever breaks, the emitted guest and the
    verified knot have diverged — that failure is the point of the tie. -/
theorem recursiveDecodeDecDirect_prog_eq_model :
    recursiveDecodeDecDirect_prog = EvmAsm.Rv64.SAsm.RecDecode.decProg := by
  decide

/-- The emitted direct-JAL items program IS the verified model program. -/
theorem recursiveDecodeItemsDirect_prog_eq_model :
    recursiveDecodeItemsDirect_prog = EvmAsm.Rv64.SAsm.RecDecode.itemsProg := by
  decide

/-- The code requirement the production adapter reasons about is exactly the
    knot's `decCr`: same three entries (by the anchors above), same three
    programs (by the two program equalities), same union shape. -/
theorem recursiveDecodeDirectCode_eq_decCr :
    recursiveDecodeDirectCode = EvmAsm.Rv64.SAsm.RecDecode.decCr := by
  simp only [recursiveDecodeDirectCode, EvmAsm.Rv64.SAsm.RecDecode.decCr,
    recursiveDecodeDecDirect_prog_eq_model,
    recursiveDecodeItemsDirect_prog_eq_model, decEntry_eq_linked,
    itemsEntry_eq_linked, rdbeEntry_eq_linked]

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
