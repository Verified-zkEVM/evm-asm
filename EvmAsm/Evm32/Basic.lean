/-
  EvmAsm.Evm32.Basic

  Types and conversions for 256-bit EVM words on 32-bit RISC-V.
  Each EvmWord is stored as 8 little-endian 32-bit limbs.
-/

import EvmAsm.Rv32.Basic
import Std.Tactic.BVDecide

namespace EvmAsm

/-- A 256-bit EVM word. -/
abbrev EvmWord := BitVec 256

namespace EvmWord

/-- Extract the i-th 32-bit limb (little-endian, i=0 is LSB). -/
def getLimb (v : EvmWord) (i : Fin 8) : Word :=
  v.extractLsb' (i.val * 32) 32

/-- Reconstruct a 256-bit value from 8 limbs. -/
def fromLimbs (limbs : Fin 8 → Word) : EvmWord :=
  (limbs 0).zeroExtend 256 |||
  ((limbs 1).zeroExtend 256 <<< 32) |||
  ((limbs 2).zeroExtend 256 <<< 64) |||
  ((limbs 3).zeroExtend 256 <<< 96) |||
  ((limbs 4).zeroExtend 256 <<< 128) |||
  ((limbs 5).zeroExtend 256 <<< 160) |||
  ((limbs 6).zeroExtend 256 <<< 192) |||
  ((limbs 7).zeroExtend 256 <<< 224)

/-- Bitwise AND distributes over limbs. -/
theorem getLimb_and (x y : EvmWord) (i : Fin 8) :
    (x &&& y).getLimb i = x.getLimb i &&& y.getLimb i := by
  simp only [getLimb, BitVec.extractLsb'_and]

/-- Bitwise OR distributes over limbs. -/
theorem getLimb_or (x y : EvmWord) (i : Fin 8) :
    (x ||| y).getLimb i = x.getLimb i ||| y.getLimb i := by
  simp only [getLimb, BitVec.extractLsb'_or]

/-- Bitwise XOR distributes over limbs. -/
theorem getLimb_xor (x y : EvmWord) (i : Fin 8) :
    (x ^^^ y).getLimb i = x.getLimb i ^^^ y.getLimb i := by
  simp only [getLimb, BitVec.extractLsb'_xor]

/-- Bitwise NOT distributes over limbs. -/
theorem getLimb_not (x : EvmWord) (i : Fin 8) :
    (~~~x).getLimb i = ~~~(x.getLimb i) := by
  simp only [getLimb]
  have hi := i.isLt
  ext j
  simp only [BitVec.getElem_extractLsb', BitVec.getElem_not, BitVec.getLsbD_not]
  have hbound : i.val * 32 + j < 256 := by omega
  simp [hbound]

/-- Round-trip: fromLimbs ∘ getLimb = id. -/
theorem fromLimbs_getLimb (v : EvmWord) :
    EvmWord.fromLimbs (v.getLimb) = v := by
  simp only [fromLimbs, getLimb,
    show (0 : Fin 8).val = 0 from rfl, show (1 : Fin 8).val = 1 from rfl,
    show (2 : Fin 8).val = 2 from rfl, show (3 : Fin 8).val = 3 from rfl,
    show (4 : Fin 8).val = 4 from rfl, show (5 : Fin 8).val = 5 from rfl,
    show (6 : Fin 8).val = 6 from rfl, show (7 : Fin 8).val = 7 from rfl]
  bv_decide

private theorem getLimb_fromLimbs_0 (limbs : Fin 8 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 0 = limbs 0 := by
  simp only [fromLimbs, getLimb, show (0 : Fin 8).val = 0 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1; generalize limbs 2 = l2
  generalize limbs 3 = l3; generalize limbs 4 = l4; generalize limbs 5 = l5
  generalize limbs 6 = l6; generalize limbs 7 = l7
  bv_decide
private theorem getLimb_fromLimbs_1 (limbs : Fin 8 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 1 = limbs 1 := by
  simp only [fromLimbs, getLimb, show (1 : Fin 8).val = 1 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1; generalize limbs 2 = l2
  generalize limbs 3 = l3; generalize limbs 4 = l4; generalize limbs 5 = l5
  generalize limbs 6 = l6; generalize limbs 7 = l7
  bv_decide
private theorem getLimb_fromLimbs_2 (limbs : Fin 8 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 2 = limbs 2 := by
  simp only [fromLimbs, getLimb, show (2 : Fin 8).val = 2 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1; generalize limbs 2 = l2
  generalize limbs 3 = l3; generalize limbs 4 = l4; generalize limbs 5 = l5
  generalize limbs 6 = l6; generalize limbs 7 = l7
  bv_decide
private theorem getLimb_fromLimbs_3 (limbs : Fin 8 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 3 = limbs 3 := by
  simp only [fromLimbs, getLimb, show (3 : Fin 8).val = 3 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1; generalize limbs 2 = l2
  generalize limbs 3 = l3; generalize limbs 4 = l4; generalize limbs 5 = l5
  generalize limbs 6 = l6; generalize limbs 7 = l7
  bv_decide
private theorem getLimb_fromLimbs_4 (limbs : Fin 8 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 4 = limbs 4 := by
  simp only [fromLimbs, getLimb, show (4 : Fin 8).val = 4 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1; generalize limbs 2 = l2
  generalize limbs 3 = l3; generalize limbs 4 = l4; generalize limbs 5 = l5
  generalize limbs 6 = l6; generalize limbs 7 = l7
  bv_decide
private theorem getLimb_fromLimbs_5 (limbs : Fin 8 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 5 = limbs 5 := by
  simp only [fromLimbs, getLimb, show (5 : Fin 8).val = 5 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1; generalize limbs 2 = l2
  generalize limbs 3 = l3; generalize limbs 4 = l4; generalize limbs 5 = l5
  generalize limbs 6 = l6; generalize limbs 7 = l7
  bv_decide
private theorem getLimb_fromLimbs_6 (limbs : Fin 8 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 6 = limbs 6 := by
  simp only [fromLimbs, getLimb, show (6 : Fin 8).val = 6 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1; generalize limbs 2 = l2
  generalize limbs 3 = l3; generalize limbs 4 = l4; generalize limbs 5 = l5
  generalize limbs 6 = l6; generalize limbs 7 = l7
  bv_decide
private theorem getLimb_fromLimbs_7 (limbs : Fin 8 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 7 = limbs 7 := by
  simp only [fromLimbs, getLimb, show (7 : Fin 8).val = 7 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1; generalize limbs 2 = l2
  generalize limbs 3 = l3; generalize limbs 4 = l4; generalize limbs 5 = l5
  generalize limbs 6 = l6; generalize limbs 7 = l7
  bv_decide

/-- Round-trip: getLimb ∘ fromLimbs = id. -/
theorem getLimb_fromLimbs (limbs : Fin 8 → Word) (i : Fin 8) :
    (EvmWord.fromLimbs limbs).getLimb i = limbs i := by
  rcases i with ⟨i, hi⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact getLimb_fromLimbs_0 limbs
  · exact getLimb_fromLimbs_1 limbs
  · exact getLimb_fromLimbs_2 limbs
  · exact getLimb_fromLimbs_3 limbs
  · exact getLimb_fromLimbs_4 limbs
  · exact getLimb_fromLimbs_5 limbs
  · exact getLimb_fromLimbs_6 limbs
  · exact getLimb_fromLimbs_7 limbs

/-- The list of 8 limbs for an EvmWord. -/
def toLimbs (v : EvmWord) : List Word :=
  List.ofFn fun i : Fin 8 => v.getLimb i

theorem toLimbs_length (v : EvmWord) : v.toLimbs.length = 8 := by
  simp [toLimbs]

end EvmWord

end EvmAsm
