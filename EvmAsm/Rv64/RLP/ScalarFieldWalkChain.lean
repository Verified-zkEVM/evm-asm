/-
  EvmAsm.Rv64.RLP.ScalarFieldWalkChain

  EL.3 / Phase 5 — reusable scalar-field-unit CodeReq + chaining beyond two fields.

  The two-field walk (`unified_two_scalar_field_walk`) discharged the unit-A ⊥ unit-B
  disjointness with an explicit 36-leaf term. Chaining a *third* unit that way would
  need 72+ leaves, and an N-field walk is hopeless. This file factors the decode-and-
  store unit's 46-slot CodeReq into a named `scalarFieldUnitCR` and proves, ONCE, a
  range-based disjointness lemma `scalarFieldUnitCR_disjoint` (à la `descend_cr_disjoint`):
  two units whose 184-byte code ranges don't overlap have disjoint CodeReqs. Composing
  any number of units is then a handful of `union_left`/`union_right` + one lemma
  application per pair.

  `unified_three_scalar_field_walk` demonstrates it: compose `unified_two_scalar_field_walk`
  (fields A, B) with one more `regOwn` unit (field C), each storing to its own output
  slot. This is the concrete inductive step toward the fixed-schema N-field decoders.

  Unit layout (46 instruction slots `base + 4*k`, k = 0..45):
      k=0       LBU x5, x13, 0
      k=1..36   unified_decoder_prog       (base+4 .. base+144)
      k=37      ADDI x14, x11, 0           (base+148)
      k=38      ADDI x11, x0, 0            (base+152)
      k=39..44  rlp_phase2_long_loop_body  (base+156 .. base+176)
      k=45      SD rOut, x11, offset       (base+180)
-/

import EvmAsm.Rv64.RLP.UnifiedTwoScalarFieldWalk

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

end EvmAsm.Rv64.RLP
