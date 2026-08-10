/-
  Machine geometry + top triple skeleton for `mpt_node_kind` (#11799 dep).

  Frame: sp-32, saves ra/s0/s1 (x1,x8,x9). Body calls
  `rlp_list_count_items` then (on 2-item path) `rlp_list_nth_item`, then
  HP high-nibble classify. BSS scratches: mnk_item_count, mnk_path_offset,
  mnk_path_length.

  Domain for registry: NO input-domain gate for an honest full-guest post
  (arity-exact 17|2). Pure `mptNodeKindSpec` is looser and is NOT the machine
  post — use `mptNodeKindGuest` / Result composition. Under `MptNode.WF`,
  `mptNodeKindGuest_eq_kindTag` bridges to `kindTag`.
-/

import EvmAsm.Codegen.Programs.MptNodeKindSpec
import EvmAsm.Codegen.Programs.RlpListCountItemsCallSAsm
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FramePort

namespace EvmAsm.Codegen.MptNodeKindSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpListCountItemsSAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.mpt_node_kind
private abbrev CountB : Word := BitVec.ofNat 64 GuestAddrs.rlp_list_count_items
private abbrev NthB : Word := BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item
private abbrev MnkCount : Word := BitVec.ofNat 64 GuestAddrs.mnk_item_count
private abbrev MnkPathOff : Word := BitVec.ofNat 64 GuestAddrs.mnk_path_offset
private abbrev MnkPathLen : Word := BitVec.ofNat 64 GuestAddrs.mnk_path_length

#guard mptNodeKind_prog.length = 53
#guard GuestAddrs.mpt_node_kind = 0x80004790

/-- Frame: ra @0, s0 @8, s1 @16 (8 bytes unused of the 32-byte frame). -/
def kindFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16)]

structure KindSaved where
  ra : Word
  s0 : Word
  s1 : Word

def kindSavedVals (s : KindSaved) : Reg → Word
  | .x1 => s.ra
  | .x8 => s.s0
  | .x9 => s.s1
  | _ => 0

theorem kindFrame_length : kindFrame.length = 3 := by decide

theorem regsAt_kindFrame (s : KindSaved) :
    regsAt kindFrame (kindSavedVals s) =
      ((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1)) := by
  simp [kindFrame, regsAt, kindSavedVals, sepConj_emp_right']

def kindSavedFrame (newSp : Word) (s : KindSaved) : Assertion :=
  (newSp ↦ₘ s.ra) ** ((newSp + 8) ↦ₘ s.s0) ** ((newSp + 16) ↦ₘ s.s1)

theorem frameSlotsSaved_kindFrame (newSp : Word) (s : KindSaved) :
    frameSlotsSaved kindFrame newSp (kindSavedVals s) =
      kindSavedFrame newSp s := by
  simp [kindFrame, frameSlotsSaved, kindSavedFrame, kindSavedVals,
    sepConj_emp_right', signExtend12]

/-- Body after 4-insn prologue (ADDI+3 SD): indices 4..48 inclusive relative
    to program start = body length 45 before 5-insn epilogue (3 LD + ADDI + JALR).
    Prologue 4, body to fail/ret join 45, epilogue 5 → 54? Count:
    prog 53: idx 0-3 prolog (4), 4-47 body (44), 48-52 epi (5). -/
def kindBody : List Instr := mptNodeKind_prog.drop 4 |>.take 44

def kindPrologue : List Instr := mptNodeKind_prog.take 4
def kindEpilogue : List Instr := mptNodeKind_prog.drop 48

#guard kindPrologue.length = 4
#guard kindBody.length = 44
#guard kindEpilogue.length = 5
#guard kindPrologue ++ kindBody ++ kindEpilogue = mptNodeKind_prog

/-- Byte-tie: 32-byte frame (3 saved regs + spare slot) around body = emitted prog. -/
theorem kind_abiFrame_byte_tie :
    abiFrameProg (-32 : BitVec 12) (32 : BitVec 12) kindFrame kindBody =
      mptNodeKind_prog := by
  decide

end EvmAsm.Codegen.MptNodeKindSpec
