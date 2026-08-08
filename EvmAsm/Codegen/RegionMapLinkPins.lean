/-
  EvmAsm.Codegen.RegionMapLinkPins

  GENERATED — do not edit by hand.
  `python3 scripts/gen-region-map-link-pins.py` regenerates this from the
  linked stateless_guest ELF (issue #11230).

  Link-layout-dependent pins only (class A): section sizes, three BSS
  bases, and `.state_gas_diag`'s base — all move when the guest image
  moves. Class B stable bases stay hand-typed in RegionMap.lean.

  Regenerated from: gen-out/regionmap/stateless_guest.elf
  Guard contract (check-region-map.sh): pins are this file (regen-time
  ELF reading); expectation is readelf/nm of the ELF built at *check*
  time. Two independent readings of two artefacts. Catches: image moved
  and nobody regenerated.
-/

namespace EvmAsm.Codegen.RegionMapLinkPins

abbrev textSizeBytes : Nat := 0x544b4
abbrev dataSizeBytes : Nat := 0x5370
abbrev bssSizeBytes : Nat := 0x18d63c00

abbrev stateGasDiagBase : Nat := 0xbbe73c00
abbrev stateGasDiagSizeBytes : Nat := 0x37cd0

abbrev callFrameArenaBase : Nat := 0xabe98880
abbrev evmMemoryPoolBase : Nat := 0xb22b1880
abbrev syslogBase : Nat := 0xaa370100

end EvmAsm.Codegen.RegionMapLinkPins
