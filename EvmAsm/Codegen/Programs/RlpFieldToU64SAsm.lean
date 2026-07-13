/-
  Strict K34 `rlp_field_to_u64` caller proof.

  The wrapper composes the verified strict list selector with the verified
  canonical scalar decoder. Its unified post keeps every runtime outcome in
  one genuine semantic relation.
-/

import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.Tactics.DropPure
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Codegen.RlpFieldToU64SAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP

/-! ## Genuine strict semantics -/

/-- Caller-visible K34 result. A malformed list, OOB index, or non-canonical
    scalar reports status one; an otherwise canonical payload wider than eight
    bytes reports status two; canonical scalars report their BE value. -/
inductive Result (bytes : List (BitVec 8)) (base : Word)
    (listLen index : Nat) : Word → Word → Prop
  | listFailure (hfail : EvmAsm.Codegen.RlpListNthItemSAsm.Failure
      bytes base listLen index) :
      Result bytes base listLen index 1 0
  | tooLong (offset len : Word)
      (hok : EvmAsm.Codegen.RlpListNthItemSAsm.Success
        bytes base listLen index offset len)
      (hlen : 8 < len.toNat) :
      Result bytes base listLen index 2 0
  | noncanonical (offset len : Word)
      (hok : EvmAsm.Codegen.RlpListNthItemSAsm.Success
        bytes base listLen index offset len)
      (hpos : 0 < len.toNat) (hfit : len.toNat ≤ 8)
      (hzero : getByteAt bytes offset.toNat = 0) :
      Result bytes base listLen index 1 0
  | empty (offset len : Word)
      (hok : EvmAsm.Codegen.RlpListNthItemSAsm.Success
        bytes base listLen index offset len)
      (hempty : len.toNat = 0) :
      Result bytes base listLen index 0 0
  | success (offset len : Word)
      (hok : EvmAsm.Codegen.RlpListNthItemSAsm.Success
        bytes base listLen index offset len)
      (hpos : 0 < len.toNat) (hfit : len.toNat ≤ 8)
      (hnz : getByteAt bytes offset.toNat ≠ 0) :
      Result bytes base listLen index 0
        (BitVec.ofNat 64
          (Nat.fromBytesBE ((bytes.drop offset.toNat).take len.toNat)))

theorem Result.status_cases {bytes : List (BitVec 8)} {base : Word}
    {listLen index : Nat} {status value : Word}
    (h : Result bytes base listLen index status value) :
    status = 0 ∨ status = 1 ∨ status = 2 := by
  cases h <;> simp

theorem Result.failure_value_zero {bytes : List (BitVec 8)} {base : Word}
    {listLen index : Nat} {status value : Word}
    (h : Result bytes base listLen index status value) (hne : status ≠ 0) :
    value = 0 := by
  cases h <;> simp_all

/-! ## Re-emitted code and linked closure -/

theorem wrapper_length : rlpFieldToU64Wrapper_prog.length = 37 := by decide
theorem program_length : rlpFieldToU64_prog.length = 37 := by
  simp [rlpFieldToU64_prog, wrapper_length]

theorem reemit_byte_tie :
    rlpFieldToU64_prog = rlpFieldToU64Wrapper_prog := by
  change (show List Instr from rlpFieldToU64Wrapper_prog) = _
  rfl

#guard rlpFieldToU64Wrapper_prog.length = 37
#guard rlpFieldToU64_prog.length = 37

abbrev B : Word := (GuestAddrs.rlp_field_to_u64 : Word)
abbrev K20B : Word := (GuestAddrs.rlp_list_nth_item : Word)
abbrev C64B : Word := (GuestAddrs.rlp_content_to_u64 : Word)
abbrev offsetCell : Word := (GuestAddrs.rfu_offset : Word)
abbrev lengthCell : Word := (GuestAddrs.rfu_length : Word)

def wrapperCode : CodeReq := CodeReq.ofProg B rlpFieldToU64_prog
def contentCode : CodeReq := rlp_content_to_u64_code C64B
def code : CodeReq := wrapperCode.union
  (EvmAsm.Codegen.RlpListNthItemSAsm.code.union contentCode)

/-! ## Three-register ABI frame -/

structure Saved where
  ra : Word
  s0 : Word
  s1 : Word

def frame : FrameDesc := [(.x1, 0), (.x8, 8), (.x9, 16)]

def savedVals (saved : Saved) : Reg → Word
  | .x1 => saved.ra
  | .x8 => saved.s0
  | .x9 => saved.s1
  | _ => 0

def savedFrame (newSp : Word) (saved : Saved) : Assertion :=
  (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) **
  ((newSp + 16) ↦ₘ saved.s1)

theorem regsAt_frame (saved : Saved) :
    regsAt frame (savedVals saved) =
      ((.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1)) := by
  simp [frame, regsAt, savedVals, sepConj_emp_right']

theorem frameSlotsSaved_frame (newSp : Word) (saved : Saved) :
    frameSlotsSaved frame newSp (savedVals saved) = savedFrame newSp saved := by
  simp [frame, frameSlotsSaved, savedFrame, savedVals, sepConj_emp_right',
    signExtend12]

theorem frameRegs_implies_owned (s0 s1 : Word) : ∀ h,
    (regOwn .x1 ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1)) h →
      regsOwnAt frame h := by
  intro h hp
  unfold regsOwnAt frame
  simp only [List.foldr_cons, List.foldr_nil, sepConj_emp_right']
  exact sepConj_mono (fun _ hx => hx)
    (sepConj_mono (regIs_implies_regOwn .x8)
      (regIs_implies_regOwn .x9)) h hp

#print axioms Result.status_cases
#print axioms frameRegs_implies_owned

end EvmAsm.Codegen.RlpFieldToU64SAsm
