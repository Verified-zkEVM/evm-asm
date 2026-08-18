/-
  Anti-vacuity witnesses for the #12457 shared-list call seam.

  The first theorem inhabits the rewritten premise at the empty child window.
  The second carries a genuine nested list, a nonzero cursor, and caller frame
  values.  Its only hypothesis is the positive validator family that the
  mutual induction supplies; the theorem deliberately does not manufacture
  that family as a standalone axiom.
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachine

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

def antiVacuityBytes : List (BitVec 8) := [0xc0]
def antiVacuityBase : Word := BitVec.ofNat 64 INPUT_MEM_START
def antiVacuityFloor : Nat := 0
def antiVacuityCursor : Nat := 0
def antiVacuityEnd : Nat := 1
def antiVacuityPayloadStart : Nat := 1
def antiVacuityPayloadEnd : Nat := 1
def antiVacuityParentFuel : Nat :=
  cycleFuel antiVacuityCursor antiVacuityEnd
def antiVacuitySp : Word := 0x1000
def antiVacuityRa : Word := 0x2000
def antiVacuityExit : Word := antiVacuityRa &&& ~~~(1 : Word)
def antiVacuityEndPtr : Word :=
  antiVacuityBase + BitVec.ofNat 64 antiVacuityEnd
def antiVacuityPfx : Word := 0xc0
def antiVacuityListBase : Word :=
  antiVacuityBase + BitVec.ofNat 64 antiVacuityCursor
def antiVacuityDepth : Word := 0
def antiVacuityP : Assertion := empAssertion
def antiVacuityWholeCode : CodeReq := validateCR

theorem shared_list_boundary_inhabited :
    Nonempty (SharedListArmInputs antiVacuityBytes antiVacuityBase
      antiVacuityFloor antiVacuityParentFuel antiVacuityCursor antiVacuityEnd
      antiVacuitySp antiVacuityRa antiVacuityExit antiVacuityEndPtr
      antiVacuityPfx antiVacuityListBase antiVacuityDepth antiVacuityWholeCode
      0 0 0 0 0 0 0 0 antiVacuityP) := by
  let hsel : SharedListSelection antiVacuityBytes antiVacuityParentFuel
      antiVacuityCursor antiVacuityEnd := {
    payloadStart := antiVacuityPayloadStart
    payloadEnd := antiVacuityPayloadEnd
    hparent := by rfl
    hcursor := by decide
    hpayload := by decide
    hpayloadEnd := by decide
    houter := by decide
    hvalidate := by
      exact validateFuel_empty_window_inhabited antiVacuityBytes rfl (by decide)
  }
  have hprefix : sharedPrefixByteAt antiVacuityBytes antiVacuityCursor
      antiVacuityPfx := by
    refine ⟨by decide, ?_⟩
    rfl
  have hchild0 : validateMachineIndexedFamily antiVacuityBytes
      antiVacuityBase antiVacuityFloor antiVacuitySp
      (RlpWalkNextStrictTie.S + 160)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word))
      antiVacuityWholeCode antiVacuityP 0 := by
    exact validate_machine_indexed_family_zero
  have hvalid : ∀ off, off < antiVacuityEnd →
      isValidByteAccess
        (antiVacuityBase + BitVec.ofNat 64 off) = true := by
    intro off hoff
    have hoff1 : off < 1 := by simpa [antiVacuityEnd] using hoff
    have hoff0 : off = 0 := by omega
    subst off
    decide
  refine ⟨{
    selector := hsel
    hprefix := hprefix
    hlistPrefix := by decide
    hdepth := by decide
    hlistBase := by rfl
    hendPtr := by rfl
    hbase_aligned := by decide
    hover := by decide
    hnowrap := by decide
    hvalid := hvalid
    hP := by exact pcFree_emp
    hvalidateSub := by intro a i h; exact h
    hchild := by
      dsimp [hsel, antiVacuityPayloadStart, antiVacuityPayloadEnd]
      exact hchild0
  }⟩

def discriminatingBytes : List (BitVec 8) := [0xc2, 0xc1, 0x00]
def discriminatingBase : Word := BitVec.ofNat 64 INPUT_MEM_START
def discriminatingFloor : Nat := 0
def discriminatingCursor : Nat := 1
def discriminatingEnd : Nat := 3
def discriminatingPayloadStart : Nat := 2
def discriminatingPayloadEnd : Nat := 3
def discriminatingParentFuel : Nat :=
  cycleFuel discriminatingCursor discriminatingEnd
def discriminatingSp : Word := 0x7000
def discriminatingRa : Word := 0x9000
def discriminatingExit : Word := discriminatingRa &&& ~~~(1 : Word)
def discriminatingEndPtr : Word :=
  discriminatingBase + BitVec.ofNat 64 discriminatingEnd
def discriminatingPfx : Word := 0xc1
def discriminatingListBase : Word :=
  discriminatingBase + BitVec.ofNat 64 discriminatingCursor
def discriminatingDepth : Word := 1
def discriminatingP : Assertion := empAssertion
def discriminatingWholeCode : CodeReq := validateCR

theorem shared_list_discriminating_inhabited
    (hchild : validateMachineIndexedFamily discriminatingBytes
      discriminatingBase discriminatingFloor discriminatingSp
      (RlpWalkNextStrictTie.S + 160)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word))
      discriminatingWholeCode discriminatingP
      (cycleFuel discriminatingPayloadStart discriminatingPayloadEnd)) :
    Nonempty (SharedListArmInputs discriminatingBytes discriminatingBase
      discriminatingFloor discriminatingParentFuel discriminatingCursor
      discriminatingEnd discriminatingSp discriminatingRa discriminatingExit
      discriminatingEndPtr discriminatingPfx discriminatingListBase
      discriminatingDepth discriminatingWholeCode 0 0 0 0 0 0 0 0
      discriminatingP) := by
  have hnested := nested_list_exact_fit_inhabited
  dsimp at hnested
  rcases hnested with ⟨_houterShared, _hinnerShared, _houterValidate,
    hinnerValidate, _hdone, _hdecode⟩
  let hsel : SharedListSelection discriminatingBytes
      discriminatingParentFuel discriminatingCursor discriminatingEnd := {
    payloadStart := discriminatingPayloadStart
    payloadEnd := discriminatingPayloadEnd
    hparent := by rfl
    hcursor := by decide
    hpayload := by decide
    hpayloadEnd := by decide
    houter := by decide
    hvalidate := by
      simpa [discriminatingBytes, discriminatingPayloadStart,
        discriminatingPayloadEnd] using hinnerValidate
  }
  have hprefix : sharedPrefixByteAt discriminatingBytes discriminatingCursor
      discriminatingPfx := by
    refine ⟨by decide, ?_⟩
    rfl
  have hvalid : ∀ off, off < discriminatingEnd →
      isValidByteAccess
        (discriminatingBase + BitVec.ofNat 64 off) = true := by
    intro off hoff
    have hoff3 : off < 3 := by simpa [discriminatingEnd] using hoff
    have hoff_cases : off = 0 ∨ off = 1 ∨ off = 2 := by omega
    rcases hoff_cases with rfl | rfl | rfl <;> decide
  refine ⟨{
    selector := hsel
    hprefix := hprefix
    hlistPrefix := by decide
    hdepth := by decide
    hlistBase := by rfl
    hendPtr := by rfl
    hbase_aligned := by decide
    hover := by decide
    hnowrap := by decide
    hvalid := hvalid
    hP := by exact pcFree_emp
    hvalidateSub := by intro a i h; exact h
    hchild := by
      dsimp [hsel, discriminatingPayloadStart, discriminatingPayloadEnd]
      exact hchild
  }⟩

end EvmAsm.Codegen.RlpWalkNextStrictFuel
