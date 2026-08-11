/-
  Machine geometry for `mpt_walk` (#11799).

  Frame: sp-80, saves ra/s0-s8 (x1, x8, x9, x18-x24) — 10 slots.
  Body 291 insn between 11-insn prologue and 12-insn epilogue.
  First machine milestone: frame + setup + `mpt_node_kind` callWithin
  (callee already `.proven` via #11964). Root `witness_lookup_by_hash`
  is a SEPARATE residual (pure `witnessLookupSpec` only) — not bundled.

  Domain gate (`.conditional`): MptNode v1 hash-or-empty children;
  inlined sub-32 EXCLUDED BY GATE; see `MptWalkSpec` header.
-/

import EvmAsm.Codegen.Programs.MptWalkSpec
import EvmAsm.Codegen.Programs.MptNodeKindWrap
import EvmAsm.Codegen.Programs.RlpListCountItemsSAsm
import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Codegen.Programs.HpDecodeNibblesSAsm
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptNodeKindSpec
open EvmAsm.Codegen.RlpListCountItemsSAsm
open EvmAsm.Codegen.RlpListNthItemSAsm
open EvmAsm.Codegen.HpDecodeNibblesSAsm

abbrev walkB : Word := BitVec.ofNat 64 GuestAddrs.mpt_walk
abbrev kindB : Word := BitVec.ofNat 64 GuestAddrs.mpt_node_kind
abbrev MwLookupHash : Word := BitVec.ofNat 64 GuestAddrs.mw_lookup_hash
abbrev MwLookupOff : Word := BitVec.ofNat 64 GuestAddrs.mw_lookup_offset
abbrev MwLookupLen : Word := BitVec.ofNat 64 GuestAddrs.mw_lookup_length
abbrev MwChildOff : Word := BitVec.ofNat 64 GuestAddrs.mw_child_offset
abbrev MwChildLen : Word := BitVec.ofNat 64 GuestAddrs.mw_child_length
abbrev MwPathOff : Word := BitVec.ofNat 64 GuestAddrs.mw_path_offset
abbrev MwPathLen : Word := BitVec.ofNat 64 GuestAddrs.mw_path_length
abbrev MwNibbleBuf : Word := BitVec.ofNat 64 GuestAddrs.mw_nibble_buf
abbrev MwNibbleCount : Word := BitVec.ofNat 64 GuestAddrs.mw_nibble_count
abbrev MwIsLeaf : Word := BitVec.ofNat 64 GuestAddrs.mw_is_leaf
abbrev MwValueOff : Word := BitVec.ofNat 64 GuestAddrs.mw_value_offset
abbrev MwValueLen : Word := BitVec.ofNat 64 GuestAddrs.mw_value_length
abbrev NthB : Word := BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item
abbrev HpDecodeB : Word := BitVec.ofNat 64 GuestAddrs.hp_decode_nibbles

#guard mptWalk_prog.length = 314
#guard GuestAddrs.mpt_walk = 0x80005eb0

/-- Frame: ra@0, s0@8, s1@16, s2..s8 @24..72. -/
def walkFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32),
   (.x20, 40), (.x21, 48), (.x22, 56), (.x23, 64), (.x24, 72)]

structure WalkSaved where
  ra : Word
  s0 : Word
  s1 : Word
  s2 : Word
  s3 : Word
  s4 : Word
  s5 : Word
  s6 : Word
  s7 : Word
  s8 : Word

def walkSavedVals (s : WalkSaved) : Reg → Word
  | .x1 => s.ra
  | .x8 => s.s0
  | .x9 => s.s1
  | .x18 => s.s2
  | .x19 => s.s3
  | .x20 => s.s4
  | .x21 => s.s5
  | .x22 => s.s6
  | .x23 => s.s7
  | .x24 => s.s8
  | _ => 0

theorem walkFrame_length : walkFrame.length = 10 := by decide

theorem regsAt_walkFrame (s : WalkSaved) :
    regsAt walkFrame (walkSavedVals s) =
      ((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8)) := by
  simp [walkFrame, regsAt, walkSavedVals, sepConj_emp_right']

def walkSavedFrame (newSp : Word) (s : WalkSaved) : Assertion :=
  (newSp ↦ₘ s.ra) ** ((newSp + 8) ↦ₘ s.s0) ** ((newSp + 16) ↦ₘ s.s1) **
  ((newSp + 24) ↦ₘ s.s2) ** ((newSp + 32) ↦ₘ s.s3) **
  ((newSp + 40) ↦ₘ s.s4) ** ((newSp + 48) ↦ₘ s.s5) **
  ((newSp + 56) ↦ₘ s.s6) ** ((newSp + 64) ↦ₘ s.s7) **
  ((newSp + 72) ↦ₘ s.s8)

set_option maxRecDepth 8000 in
theorem frameSlotsSaved_walkFrame (newSp : Word) (s : WalkSaved) :
    frameSlotsSaved walkFrame newSp (walkSavedVals s) =
      walkSavedFrame newSp s := by
  simp [walkFrame, frameSlotsSaved, walkSavedFrame, walkSavedVals,
    sepConj_emp_right', signExtend12]

/-- Prologue ADDI+10 SD; body 291; epilogue 10 LD + ADDI + JALR. -/
def walkPrologue : List Instr := mptWalk_prog.take 11
def walkBody : List Instr := mptWalk_prog.drop 11 |>.take 291
def walkEpilogue : List Instr := mptWalk_prog.drop 302

#guard walkPrologue.length = 11
#guard walkBody.length = 291
#guard walkEpilogue.length = 12

set_option maxRecDepth 8000 in
theorem walk_parts_cover_prog :
    walkPrologue ++ walkBody ++ walkEpilogue = mptWalk_prog := by
  decide

/-! Byte-tie: 80-byte frame around body = emitted prog. -/
set_option maxRecDepth 8000 in
theorem walk_abiFrame_byte_tie :
    abiFrameProg (-80 : BitVec 12) (80 : BitVec 12) walkFrame walkBody =
      mptWalk_prog := by
  decide

/-! ## Linked code image: walk ∪ kind∪count∪nth ∪ hp_decode -/

private abbrev walkProg : List Instr := mptWalk_prog

def wrapperCode : CodeReq := CodeReq.ofProg walkB walkProg

/-- Kind-family image (kind∪count∪nth) before adding hp. -/
def kindFullCode : CodeReq := MptNodeKindSpec.fullCode

/-- `walk ∪ kindFull ∪ hdnCr`. -/
def fullCode : CodeReq :=
  (wrapperCode.union kindFullCode).union (hdnCr HpDecodeB)

set_option maxRecDepth 8000 in
theorem program_length : walkProg.length = 314 := by decide

set_option maxRecDepth 8000 in
theorem hp_program_length : hpDecodeNibbles_prog.length = 51 := by decide

set_option maxRecDepth 8000 in
theorem wrapper_kindWrap_disjoint :
    wrapperCode.Disjoint MptNodeKindSpec.wrapperCode := by
  unfold wrapperCode MptNodeKindSpec.wrapperCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [MptNodeKindSpec.program_length]; decide
  · rw [program_length, MptNodeKindSpec.program_length]; decide

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

theorem wrapper_kindFull_disjoint :
    wrapperCode.Disjoint kindFullCode := by
  unfold kindFullCode MptNodeKindSpec.fullCode
  exact CodeReq.Disjoint.union_right wrapper_kindWrap_disjoint
    (CodeReq.Disjoint.union_right wrapper_count_disjoint wrapper_nth_disjoint)

set_option maxRecDepth 8000 in
theorem wrapper_hp_disjoint :
    wrapperCode.Disjoint (hdnCr HpDecodeB) := by
  unfold wrapperCode hdnCr HpDecodeB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [hp_program_length]; decide
  · rw [program_length, hp_program_length]; decide

set_option maxRecDepth 8000 in
theorem kindWrap_hp_disjoint :
    MptNodeKindSpec.wrapperCode.Disjoint (hdnCr HpDecodeB) := by
  unfold MptNodeKindSpec.wrapperCode hdnCr HpDecodeB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [MptNodeKindSpec.program_length]; decide
  · rw [hp_program_length]; decide
  · rw [MptNodeKindSpec.program_length, hp_program_length]; decide

set_option maxRecDepth 8000 in
theorem count_hp_disjoint :
    RlpListCountItemsSAsm.code.Disjoint (hdnCr HpDecodeB) := by
  unfold RlpListCountItemsSAsm.code hdnCr HpDecodeB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListCountItemsSAsm.total_length]; decide
  · rw [hp_program_length]; decide
  · rw [RlpListCountItemsSAsm.total_length, hp_program_length]; decide

set_option maxRecDepth 8000 in
theorem nth_hp_disjoint :
    RlpListNthItemSAsm.code.Disjoint (hdnCr HpDecodeB) := by
  unfold RlpListNthItemSAsm.code hdnCr HpDecodeB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListNthItemSAsm.total_length]; decide
  · rw [hp_program_length]; decide
  · rw [RlpListNthItemSAsm.total_length, hp_program_length]; decide

theorem kindFull_hp_disjoint :
    kindFullCode.Disjoint (hdnCr HpDecodeB) := by
  unfold kindFullCode MptNodeKindSpec.fullCode
  exact CodeReq.Disjoint.union_left kindWrap_hp_disjoint
    (CodeReq.Disjoint.union_left count_hp_disjoint nth_hp_disjoint)

theorem walkKind_hp_disjoint :
    (wrapperCode.union kindFullCode).Disjoint (hdnCr HpDecodeB) :=
  CodeReq.Disjoint.union_left wrapper_hp_disjoint kindFull_hp_disjoint

/-- Discharge one walk singleton into `fullCode`. -/
theorem walkMem (A : Word) (k : Nat) (ins : Instr)
    (hk : k < walkProg.length)
    (hA : A = walkB + BitVec.ofNat 64 (4 * k))
    (hins : walkProg[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i := by
  intro a i hs
  unfold fullCode
  have hL := CodeReq.ofProg_mem_at walkB A walkProg k ins hA hk hins
    (by rw [program_length]; norm_num) a i hs
  exact CodeReq.union_mono_left a i
    (CodeReq.union_mono_left a i hL)

/-- Kind (with count∪nth) membership into walk fullCode. -/
theorem kindCalleeMem : ∀ a i,
    MptNodeKindSpec.fullCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode kindFullCode
  have hK := CodeReq.mono_union_right wrapper_kindFull_disjoint
    (fun _ _ h => h) a i hi
  exact CodeReq.union_mono_left a i hK

/-- Direct nth membership via kind fullCode. -/
theorem nthCalleeMem : ∀ a i,
    RlpListNthItemSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  apply kindCalleeMem
  exact MptNodeKindSpec.nthCalleeMem a i hi

/-- hp_decode_nibbles membership into walk fullCode. -/
theorem hpCalleeMem : ∀ a i,
    hdnCr HpDecodeB a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right walkKind_hp_disjoint
    (fun _ _ h => h) a i hi

/-- Body PC pins (instruction index → absolute). -/
def pc (n : Nat) : Word := walkB + BitVec.ofNat 64 (4 * n)

theorem pc_succ (n : Nat) : pc n + 4 = pc (n + 1) := by
  unfold pc; bv_omega

theorem pc_eq_walkB (n : Nat) : pc n = walkB + BitVec.ofNat 64 (4 * n) := rfl

/-- First `mpt_node_kind` call site (prog idx 47 = walk+188). -/
def kindCallPc : Word := pc 47

#guard GuestAddrs.mpt_walk + 188 = 0x80005eb0 + 188

theorem kindCallPc_eq : kindCallPc = walkB + 188 := by
  unfold kindCallPc pc walkB; decide

end EvmAsm.Codegen.MptWalkSpec
