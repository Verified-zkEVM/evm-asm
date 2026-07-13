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
def code : CodeReq := EvmAsm.Codegen.RlpListNthItemSAsm.code.union
  (wrapperCode.union contentCode)

/-! ## Strict list-callee call shape -/

def listSavedRegs (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved) : Assertion :=
  (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
  (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
  (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)

def listCallResult
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ status offset len v11 v12,
    (((.x2 ↦ᵣ sp0) ** listSavedRegs saved ** stackFree sp0 8 **
      ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
       (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len))) **
     ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes listBase listLen index
       oldOffset oldLen status offset len⌝) h

/-- Peel K20's restored `ra` out of its flat post, yielding the exact
    `(ra ** P) -> (ra ** Q)` contract expected by `callWithin_spec`. -/
theorem listCalleeCallContract
    (sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin
      ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
      K20B saved.ra code
      ((.x1 ↦ᵣ saved.ra) **
       ((.x2 ↦ᵣ sp0) ** listSavedRegs saved ** stackFree sp0 8 **
        EvmAsm.Codegen.RlpListNthItemSAsm.entryRest listBase listLenW indexW
          offsetPtr lenPtr oldOffset oldLen bytes))
      ((.x1 ↦ᵣ saved.ra) **
       listCallResult sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
         listLen index) := by
  have hflat := EvmAsm.Codegen.RlpListNthItemSAsm.rlpListNthItem_flat_spec_within
    sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen saved bytes
    listLen index hlistLenW hindexW hindex hsalign hslack hover hvalid hret
  have hcode := cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hflat
  refine cpsTripleWithin_weaken (fun h hp => by
    unfold listSavedRegs at hp
    rw [EvmAsm.Codegen.RlpListNthItemSAsm.regsAt_listNthFrame]
    xperm_hyp hp) (fun h hq => ?_) hcode
  unfold EvmAsm.Codegen.RlpListNthItemSAsm.flatReturnResult at hq
  obtain ⟨status, offset, len, v11, v12, hq⟩ := hq
  have hfixed : ((.x1 ↦ᵣ saved.ra) **
      (((.x2 ↦ᵣ sp0) ** listSavedRegs saved ** stackFree sp0 8 **
        ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
         (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len))) **
       ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes listBase listLen index
         oldOffset oldLen status offset len⌝)) h := by
    unfold listSavedRegs
    rw [EvmAsm.Codegen.RlpListNthItemSAsm.regsAt_listNthFrame] at hq
    xperm_hyp hq
  obtain ⟨hRa, hRest, hd, hu, hra, hrest⟩ := hfixed
  refine ⟨hRa, hRest, hd, hu, hra, ?_⟩
  unfold listCallResult
  exact ⟨status, offset, len, v11, v12, hrest⟩

#print axioms listCalleeCallContract

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
