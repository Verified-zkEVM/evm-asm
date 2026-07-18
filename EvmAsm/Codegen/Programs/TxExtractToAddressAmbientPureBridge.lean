/-
  Pure bridges: slice-relative addresses ↔ ambient abs offsets.

  Residual: full `rlpItemDecode` transfer slice↔abs (needed to lift
  packaging hnext from loadPtr/txSlice to regionBase/bs). Cursor/end
  equalities below are the address half of that bridge.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitShort

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen.TxTypeDispatchSpec

theorem shortWalkCursor_loadPtr_eq
    (regionBase loadPtr : Word) (off listOff : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hspan : regionBase.toNat + (off + listOff) < 2 ^ 64) :
    shortWalkCursor loadPtr listOff =
      shortWalkCursor regionBase (ambientAbsOff off listOff) := by
  simp only [shortWalkCursor, ambientAbsOff]
  have h := loadPtr_add_rel_eq regionBase loadPtr off listOff hptr hspan
  rw [h]

theorem shortWalkEnd_loadPtr_eq
    (regionBase loadPtr listLen : Word) (off listOff : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hspan : regionBase.toNat + (off + listOff) < 2 ^ 64) :
    shortWalkEnd loadPtr listLen listOff =
      shortWalkEnd regionBase listLen (ambientAbsOff off listOff) := by
  simp only [shortWalkEnd, ambientAbsOff]
  have h := loadPtr_add_rel_eq regionBase loadPtr off listOff hptr hspan
  rw [h]

theorem txSlice_getElem?
    (bs : List (BitVec 8)) (off len k : Nat)
    (hbound : off + len ≤ bs.length) (hk : k < len) :
    (txSlice bs off len)[k]? = bs[off + k]? := by
  have hk' : k < (txSlice bs off len).length := by
    rw [txSlice_length bs off len hbound]; exact hk
  have habs : off + k < bs.length := by omega
  rw [List.getElem?_eq_getElem hk', List.getElem?_eq_getElem habs,
    txSlice_getElem bs off len k hk hbound]

#print axioms shortWalkCursor_loadPtr_eq
#print axioms shortWalkEnd_loadPtr_eq
#print axioms txSlice_getElem?

end EvmAsm.Codegen.TxExtractToAddressSpec
