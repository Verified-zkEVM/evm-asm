/-
  EvmAsm.Codegen.RegionMapLinkPins

  GENERATED — do not edit by hand.
  `python3 scripts/gen-region-map-link-pins.py` regenerates this from the
  linked stateless_guest ELF (issue #11230).

  Link-layout-dependent pins only (class A): section sizes and two
  BSS bases, which move when the guest image moves. Class B stable
  bases stay hand-typed in RegionMap.lean; `.state_gas_diag`'s base is
  neither — RegionMap DERIVES it from `bssSizeBytes` (GH #11186).

  Regenerated from: gen-out/regionmap/stateless_guest.elf
  Guard contract (check-region-map.sh): pins are this file (regen-time
  ELF reading); expectation is readelf/nm of the ELF built at *check*
  time. Two independent readings of two artefacts. Catches: image moved
  and nobody regenerated.
-/

namespace EvmAsm.Codegen.RegionMapLinkPins

abbrev textSizeBytes : Nat := 0x53c38
abbrev dataSizeBytes : Nat := 0x5310
abbrev bssSizeBytes : Nat := 0x1aedaee0

abbrev stateGasDiagSizeBytes : Nat := 0x61a78

abbrev callFrameArenaBase : Nat := 0xabe4dc00
abbrev evmMemoryPoolBase : Nat := 0xb2266c00

end EvmAsm.Codegen.RegionMapLinkPins
