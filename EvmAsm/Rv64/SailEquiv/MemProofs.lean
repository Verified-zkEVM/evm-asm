/-
  EvmAsm.Rv64.SailEquiv.MemProofs

  Per-instruction equivalence for the memory instructions
  LD, SD, LW, LWU, SW, LB, LH, LBU, LHU, SB, SH — all DISCHARGED unconditionally:

  * `ld_sail_equiv` (doubleword load, Tier A) lives in `VmemReduction.lean`;
  * the six sub-doubleword loads (Tier C) live in `VmemReductionLoads.lean`;
  * the four stores `sd/sw/sh/sb_sail_equiv` (Tier B) live in
    `VmemReductionStores.lean`.

  Each takes a real `StateRel` + `BareModeInv` + per-access bundle (alignment,
  PMA region, MMIO disjointness — and, for loads only, byte presence) instead of
  the vacuous `h_exec` hypothesis the original deferred versions carried. This
  file is kept as the historical anchor of that layout; no conditional memory
  lemmas remain.
-/

import EvmAsm.Rv64.SailEquiv.ALUProofs

namespace EvmAsm.Rv64.SailEquiv

end EvmAsm.Rv64.SailEquiv
