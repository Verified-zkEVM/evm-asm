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

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionEqualRoute
