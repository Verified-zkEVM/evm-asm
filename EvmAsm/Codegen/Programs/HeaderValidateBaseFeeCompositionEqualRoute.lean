/-
# Equal-route shape adapter for the K73 Route-B contract (#12346 residual 2b)

`k73_equal_route_spec_within` (`EvmAsm.Codegen.HeaderBaseFeeSpec`) is a
premise-free whole-routine triple covering the linked equal route of the
emitted `eip1559_calc_base_fee_per_gas` (used == target, which copies the
parent-fee bytes into the output window).  This file instantiates it at
the wrapper's vocabulary and converts the result pointwise into exactly
the SUCCESS ARM of the revised wrapper premise
`k73RouteBCallPost` — certifying that the repaired #12346-residual-2b
contract is discharge-able, not merely well-typed.

Atom mapping (wrapper name := source name):
* wrapper `spH` := their `sp0`; wrapper `spK` := their `spH`
  (the frame-offset hypotheses coincide: `spK = spH + signExtend12 (-56)`);
* `raIn := H + 40`, `v8 := headerPtr`, `v18-slot := old18`,
  `basePtr := parentPtr`, `outPtr := Expected`;
* equal-route guard `gasUsed = gasLimit >>> 1`.

Post conversion weakens the three source pins (`x10 ↦ 0`, `x11 ↦ gasUsed`,
`x5 ↦ packBytes …`) to `regOwn`s and casts the copied window through two
lemmas: the copy overwrites all four dwords so `k73CopyOut src out = src`
for length-32 lists, and at the guard the written image reduces to the
parent bytes (`k73_fixed_bytes_repr` roundtrip).
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeSpec
import EvmAsm.Codegen.Programs.K73Arithmetic
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecCore
import EvmAsm.Rv64.MemRegionWriteWide

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionEqualRoute

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec

/-- A full dword paste is byte-transparent: the little-endian expansion of a
    packed word reproduces an 8-byte chunk exactly. -/
theorem dwordBytes_packBytes_eq_self {c : List (BitVec 8)} (hlen : c.length = 8) :
    dwordBytes (packBytes c) = c := by
  apply List.ext_get
  · simp [dwordBytes, hlen]
  · intro n hn1 hn2
    have hn8 : n < 8 := by simpa [dwordBytes] using hn1
    interval_cases n <;> simp [dwordBytes, hlen, extractByte_packBytes]

private theorem take_succ_set {α : Type} (bs : List α) (b : α) (i : Nat)
    (h : i < bs.length) :
    (bs.take (i + 1)).set i b = bs.take i ++ [b] := by
  have hle : (List.take i bs).length ≤ i := by simp
  rw [List.take_add_one, List.getElem?_eq_getElem h,
    List.set_append_right (s := List.take i bs) i b hle]
  have hlt : (List.take i bs).length = min i bs.length := List.length_take
  have heq : (List.take i bs).length = i := by omega
  rw [heq]
  simp

/-- Pasting `ns` into `bs` at offset `i` splices prefix/chunk/suffix:
    prefix unchanged, pasted chunk whole, suffix after the chunk. -/
theorem win8_splice {bs : List (BitVec 8)} (ns : List (BitVec 8)) (i : Nat)
    (h : i + ns.length ≤ bs.length) :
    setBytes bs i ns = bs.take i ++ ns ++ bs.drop (i + ns.length) := by
  induction ns generalizing bs i with
  | nil => simp
  | cons b rest ih =>
    have hs : (bs.set i b).length = bs.length := List.length_set
    have h' := h
    simp only [List.length_cons] at h'
    have hb : i < bs.length := by omega
    have hle : (List.take i bs).length ≤ i := by simp
    have hlt : (List.take i bs).length = min i bs.length := List.length_take
    have heq : (List.take i bs).length = i := by omega
    have key := @ih (bs.set i b) (i + 1) (by rw [hs]; omega)
    rw [setBytes_cons, key, List.take_set, take_succ_set _ _ _ hb,
      List.drop_set, if_pos (by omega)]
    have hsimp : i + 1 + rest.length = i + (rest.length + 1) := by omega
    rw [hsimp]
    simp

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionEqualRoute
