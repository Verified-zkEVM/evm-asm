/-
  Machine geometry + top triple skeleton for `mpt_node_kind` (#11799 dep).

  Frame: sp-32, saves ra/s0/s1 (x1,x8,x9). Body calls
  `rlp_list_count_items` then (on 2-item path) `rlp_list_nth_item`, then
  HP high-nibble classify. BSS scratches: mnk_item_count, mnk_path_offset,
  mnk_path_length.

  Domain for registry: NO input-domain gate for an honest full-guest post
  (arity-exact 17|2). Pure `mptNodeKindSpec` is looser and is NOT the machine
  post — use operational `MptNodeKindResult`. Under `MptNode.WF`,
  `MptNodeKindWire.mptNodeKindResult_eq_kindTag` recovers `kindTag` (success
  arms). The pure `mptNodeKindGuest` def remains for coverRef only.
-/

import EvmAsm.Codegen.Programs.MptNodeKindSpec
import EvmAsm.Codegen.Programs.RlpListCountItemsCallSAsm
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.TwoExitLoop

namespace EvmAsm.Codegen.MptNodeKindSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpListCountItemsSAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

abbrev kindB : Word := BitVec.ofNat 64 GuestAddrs.mpt_node_kind
abbrev CountB : Word := BitVec.ofNat 64 GuestAddrs.rlp_list_count_items
abbrev NthB : Word := BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item
abbrev MnkCount : Word := BitVec.ofNat 64 GuestAddrs.mnk_item_count
abbrev MnkPathOff : Word := BitVec.ofNat 64 GuestAddrs.mnk_path_offset
abbrev MnkPathLen : Word := BitVec.ofNat 64 GuestAddrs.mnk_path_length
private abbrev B : Word := kindB

#guard mptNodeKind_prog.length = 53
#guard GuestAddrs.mpt_node_kind = 0x80004a2c

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

/-! ## Linked code image: kind body ∪ count_items ∪ nth_item -/

private abbrev kindProg : List Instr := mptNodeKind_prog

def wrapperCode : CodeReq := CodeReq.ofProg B kindProg

/-- `wrapper ∪ (count ∪ nth)`. -/
def fullCode : CodeReq :=
  wrapperCode.union
    (RlpListCountItemsSAsm.code.union RlpListNthItemSAsm.code)

theorem program_length : kindProg.length = 53 := by decide

set_option maxRecDepth 8000 in
theorem wrapper_count_disjoint :
    wrapperCode.Disjoint RlpListCountItemsSAsm.code := by
  unfold wrapperCode RlpListCountItemsSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [RlpListCountItemsSAsm.total_length]; decide
  · rw [program_length, RlpListCountItemsSAsm.total_length]; decide

set_option maxRecDepth 8000 in
theorem wrapper_nth_disjoint :
    wrapperCode.Disjoint RlpListNthItemSAsm.code := by
  unfold wrapperCode RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [RlpListNthItemSAsm.total_length]; decide
  · rw [program_length, RlpListNthItemSAsm.total_length]; decide

set_option maxRecDepth 8000 in
theorem count_nth_disjoint :
    RlpListCountItemsSAsm.code.Disjoint RlpListNthItemSAsm.code := by
  unfold RlpListCountItemsSAsm.code RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListCountItemsSAsm.total_length]; decide
  · rw [RlpListNthItemSAsm.total_length]; decide
  · rw [RlpListCountItemsSAsm.total_length, RlpListNthItemSAsm.total_length]; decide

/-- Discharge one singleton membership into `fullCode` via the kind wrapper. -/
theorem kindMem (A : Word) (k : Nat) (ins : Instr)
    (hk : k < kindProg.length)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hins : kindProg[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i := by
  intro a i hs
  unfold fullCode
  exact CodeReq.union_mono_left a i
    (CodeReq.ofProg_mem_at B A kindProg k ins hA hk hins
      (by rw [program_length]; norm_num) a i hs)

theorem countCalleeMem : ∀ a i,
    RlpListCountItemsSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right wrapper_count_disjoint
    (fun a i h => CodeReq.union_mono_left a i h) a i hi

theorem nthCalleeMem : ∀ a i,
    RlpListNthItemSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right wrapper_nth_disjoint
    (fun a i h =>
      CodeReq.mono_union_right count_nth_disjoint (fun _ _ h => h) a i h)
    a i hi

/-- Body PC pins (instruction index → absolute). -/
def pc (n : Nat) : Word := kindB + BitVec.ofNat 64 (4 * n)

theorem pc_succ (n : Nat) : pc n + 4 = pc (n + 1) := by
  unfold pc; bv_omega

theorem pc_eq_B (n : Nat) : pc n = B + BitVec.ofNat 64 (4 * n) := rfl

/-- Fuel bound covering all arms: linear body + count(listLen) + nth(0). -/
def kindFuel (listLen : Nat) : Nat :=
  50 + (1 + (8 + (85 + (93 * (listLen + 1) + 3) + 7))) +
    (1 + ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9))

end EvmAsm.Codegen.MptNodeKindSpec
