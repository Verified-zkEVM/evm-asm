/-
  EvmAsm.Evm64.MulMod.AddPartialTable

  Stable, product-layout ordered names for the concrete MULMOD add-partial
  specs.  These aliases let the product composition proof cite each call by
  ordinal without unfolding `evm_mulmod_product_add_partial`.
-/

import EvmAsm.Evm64.MulMod.AddPartialSpecs

namespace EvmAsm.Evm64

-- ============================================================================
-- Product-layout add-partial call table
-- ============================================================================

/-- Layout call 00: offsets `(0, 32, 96, 104)`, carry tail `[3952, 3960, 3968, 3976, 3984, 3992]`,
    entry `base`, exit `base + 60 + 96`, bound `15 + 24`. -/
abbrev evm_mulmod_product_add_partial_layout_call00_spec_within :=
  evm_mulmod_product_add_partial_0_32_96_104_112_120_128_136_144_152_spec_within

/-- Layout call 01: offsets `(8, 32, 104, 112)`, carry tail `[3960, 3968, 3976, 3984, 3992]`,
    entry `base`, exit `base + 60 + 80`, bound `15 + 20`. -/
abbrev evm_mulmod_product_add_partial_layout_call01_spec_within :=
  evm_mulmod_product_add_partial_8_32_104_112_120_128_136_144_152_spec_within

/-- Layout call 02: offsets `(0, 40, 104, 112)`, carry tail `[3960, 3968, 3976, 3984, 3992]`,
    entry `base`, exit `base + 60 + 80`, bound `15 + 20`. -/
abbrev evm_mulmod_product_add_partial_layout_call02_spec_within :=
  evm_mulmod_product_add_partial_0_40_104_112_120_128_136_144_152_spec_within

/-- Layout call 03: offsets `(16, 32, 112, 120)`, carry tail `[3968, 3976, 3984, 3992]`,
    entry `base`, exit `base + 60 + 64`, bound `15 + 16`. -/
abbrev evm_mulmod_product_add_partial_layout_call03_spec_within :=
  evm_mulmod_product_add_partial_16_32_112_120_128_136_144_152_spec_within

/-- Layout call 04: offsets `(8, 40, 112, 120)`, carry tail `[3968, 3976, 3984, 3992]`,
    entry `base`, exit `base + 60 + 64`, bound `15 + 16`. -/
abbrev evm_mulmod_product_add_partial_layout_call04_spec_within :=
  evm_mulmod_product_add_partial_8_40_112_120_128_136_144_152_spec_within

/-- Layout call 05: offsets `(0, 48, 112, 120)`, carry tail `[3968, 3976, 3984, 3992]`,
    entry `base`, exit `base + 60 + 64`, bound `15 + 16`. -/
abbrev evm_mulmod_product_add_partial_layout_call05_spec_within :=
  evm_mulmod_product_add_partial_0_48_112_120_128_136_144_152_spec_within

/-- Layout call 06: offsets `(24, 32, 120, 128)`, carry tail `[3976, 3984, 3992]`,
    entry `base`, exit `base + 60 + 48`, bound `15 + 12`. -/
abbrev evm_mulmod_product_add_partial_layout_call06_spec_within :=
  evm_mulmod_product_add_partial_24_32_120_128_136_144_152_spec_within

/-- Layout call 07: offsets `(16, 40, 120, 128)`, carry tail `[3976, 3984, 3992]`,
    entry `base`, exit `base + 60 + 48`, bound `15 + 12`. -/
abbrev evm_mulmod_product_add_partial_layout_call07_spec_within :=
  evm_mulmod_product_add_partial_16_40_120_128_136_144_152_spec_within

/-- Layout call 08: offsets `(8, 48, 120, 128)`, carry tail `[3976, 3984, 3992]`,
    entry `base`, exit `base + 60 + 48`, bound `15 + 12`. -/
abbrev evm_mulmod_product_add_partial_layout_call08_spec_within :=
  evm_mulmod_product_add_partial_8_48_120_128_136_144_152_spec_within

/-- Layout call 09: offsets `(0, 56, 120, 128)`, carry tail `[3976, 3984, 3992]`,
    entry `base`, exit `base + 60 + 48`, bound `15 + 12`. -/
abbrev evm_mulmod_product_add_partial_layout_call09_spec_within :=
  evm_mulmod_product_add_partial_0_56_120_128_136_144_152_spec_within

/-- Layout call 10: offsets `(24, 40, 128, 136)`, carry tail `[3984, 3992]`,
    entry `base`, exit `base + 60 + 32`, bound `15 + 8`. -/
abbrev evm_mulmod_product_add_partial_layout_call10_spec_within :=
  evm_mulmod_product_add_partial_24_40_128_136_144_152_spec_within

/-- Layout call 11: offsets `(16, 48, 128, 136)`, carry tail `[3984, 3992]`,
    entry `base`, exit `base + 60 + 32`, bound `15 + 8`. -/
abbrev evm_mulmod_product_add_partial_layout_call11_spec_within :=
  evm_mulmod_product_add_partial_16_48_128_136_144_152_spec_within

/-- Layout call 12: offsets `(8, 56, 128, 136)`, carry tail `[3984, 3992]`,
    entry `base`, exit `base + 60 + 32`, bound `15 + 8`. -/
abbrev evm_mulmod_product_add_partial_layout_call12_spec_within :=
  evm_mulmod_product_add_partial_8_56_128_136_144_152_spec_within

/-- Layout call 13: offsets `(24, 48, 136, 144)`, carry tail `[3992]`,
    entry `base`, exit `base + 60 + 16`, bound `15 + 4`. -/
abbrev evm_mulmod_product_add_partial_layout_call13_spec_within :=
  evm_mulmod_product_add_partial_24_48_136_144_152_spec_within

/-- Layout call 14: offsets `(16, 56, 136, 144)`, carry tail `[3992]`,
    entry `base`, exit `base + 60 + 16`, bound `15 + 4`. -/
abbrev evm_mulmod_product_add_partial_layout_call14_spec_within :=
  evm_mulmod_product_add_partial_16_56_136_144_152_spec_within

/-- Layout call 15: offsets `(24, 56, 144, 152)`, carry tail `[]`,
    entry `base`, exit `base + 60`, bound `15`. -/
abbrev evm_mulmod_product_add_partial_layout_call15_spec_within :=
  evm_mulmod_product_add_partial_144_152_nil_spec_within

end EvmAsm.Evm64
