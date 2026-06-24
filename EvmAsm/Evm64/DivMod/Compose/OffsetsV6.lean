/-
  EvmAsm.Evm64.DivMod.Compose.OffsetsV6

  Named byte offsets and code bundles for the n=1 fast-path programs
  `evm_div_v6` / `evm_mod_v6` (issue #9303), mirroring `Compose.Offsets` for
  the base v5 layout. The `drift_check_*` examples below fail to compile if a
  block length changes without the matching offset being bumped.

  Layout of `evm_div_v6` (bytes from program base; instruction count in parens):
    [dispatchN1Off  =   0] divK_dispatchN1 796 788     (8)
    [v6ClzOff       =  32] divK_clz                    (24)
    [v6SetupOff     = 128] divK_fastSetup 88           (7)
    [v6NormAOff     = 156] divK_normA 40               (21)
    [v6CopyAUOff    = 240] divK_copyAU                 (9)
    [v6Digit3Off    = 276] divK_fastDigit .. 188       (10)
    [v6Digit2Off    = 316] divK_fastDigit .. 148       (10)
    [v6Digit1Off    = 356] divK_fastDigit .. 108       (10)
    [v6Digit0Off    = 396] divK_fastDigit .. 68        (10)
    [v6EpilogueOff  = 436] divK_div_epilogue 1412      (10)
    [v6Div128Off    = 476] divK_div128_v5              (85)  ← fast path's own copy
    [v6V5Off        = 816] evm_div_v5                  (353)
    [v6ExitOff      =1884] embedded v5 NOP (= v6V5Off + nopOff)

  `evm_mod_v6` inserts `divK_fastDenorm` (7) at [modV6DenormOff = 436], pushing
  the MOD epilogue / div128 copy / v5 down by 7 instructions (28 bytes).
-/

import EvmAsm.Evm64.DivMod.FastN1Program
import EvmAsm.Evm64.DivMod.Compose.V5Code2

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- evm_div_v6 block offsets
-- ============================================================================

abbrev dispatchN1Off : Word :=    0
abbrev v6ClzOff      : Word :=   32
abbrev v6SetupOff    : Word :=  128
abbrev v6NormAOff    : Word :=  156
abbrev v6CopyAUOff   : Word :=  240
abbrev v6Digit3Off   : Word :=  276
abbrev v6Digit2Off   : Word :=  316
abbrev v6Digit1Off   : Word :=  356
abbrev v6Digit0Off   : Word :=  396
abbrev v6EpilogueOff : Word :=  436
abbrev v6Div128Off   : Word :=  476
abbrev v6V5Off       : Word :=  816
/-- v6 exit PC = embedded v5's NOP block (v6V5Off + nopOff = 816 + 1068). -/
abbrev v6ExitOff     : Word := 1884

-- evm_mod_v6: identical through the digits, then a denorm block is inserted.
abbrev modV6DenormOff   : Word :=  436
abbrev modV6EpilogueOff : Word :=  464
abbrev modV6Div128Off   : Word :=  504
abbrev modV6V5Off       : Word :=  844
abbrev modV6ExitOff     : Word := 1912

-- ============================================================================
-- Code bundles
-- ============================================================================

/-- Full `evm_div_v6` code as block-decomposed `CodeReq`. The last element is
    the reused v5 bundle at the shifted base, so `divCode_v5 (base + v6V5Off)`
    is a sub-bundle (for framing `evm_div_stack_spec_unconditional`). -/
abbrev divCodeV6 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                   (divK_dispatchN1 796 788),
    CodeReq.ofProg (base + v6ClzOff)       divK_clz,
    CodeReq.ofProg (base + v6SetupOff)     (divK_fastSetup 88),
    CodeReq.ofProg (base + v6NormAOff)     (divK_normA 40),
    CodeReq.ofProg (base + v6CopyAUOff)    divK_copyAU,
    CodeReq.ofProg (base + v6Digit3Off)    (divK_fastDigit 4024 4032 4064 188),
    CodeReq.ofProg (base + v6Digit2Off)    (divK_fastDigit 4032 4040 4072 148),
    CodeReq.ofProg (base + v6Digit1Off)    (divK_fastDigit 4040 4048 4080 108),
    CodeReq.ofProg (base + v6Digit0Off)    (divK_fastDigit 4048 4056 4088 68),
    CodeReq.ofProg (base + v6EpilogueOff)  (divK_div_epilogue 1412),
    CodeReq.ofProg (base + v6Div128Off)    divK_div128_v5,
    divCode_v5 (base + v6V5Off)
  ]

/-- Full `evm_mod_v6` code as block-decomposed `CodeReq`. -/
abbrev modCodeV6 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                     (divK_dispatchN1 824 816),
    CodeReq.ofProg (base + v6ClzOff)         divK_clz,
    CodeReq.ofProg (base + v6SetupOff)       (divK_fastSetup 88),
    CodeReq.ofProg (base + v6NormAOff)       (divK_normA 40),
    CodeReq.ofProg (base + v6CopyAUOff)      divK_copyAU,
    CodeReq.ofProg (base + v6Digit3Off)      (divK_fastDigit 4024 4032 4064 216),
    CodeReq.ofProg (base + v6Digit2Off)      (divK_fastDigit 4032 4040 4072 176),
    CodeReq.ofProg (base + v6Digit1Off)      (divK_fastDigit 4040 4048 4080 136),
    CodeReq.ofProg (base + v6Digit0Off)      (divK_fastDigit 4048 4056 4088 96),
    CodeReq.ofProg (base + modV6DenormOff)   divK_fastDenorm,
    CodeReq.ofProg (base + modV6EpilogueOff) (divK_mod_epilogue 1412),
    CodeReq.ofProg (base + modV6Div128Off)   divK_div128_v5,
    modCode_v5 (base + modV6V5Off)
  ]

-- ============================================================================
-- Drift checks — each block's start = previous start + 4 * previous length.
-- ============================================================================

example : v6ClzOff      = dispatchN1Off + 4 * (divK_dispatchN1 796 788).length := by decide
example : v6SetupOff    = v6ClzOff      + 4 * divK_clz.length := by decide
example : v6NormAOff    = v6SetupOff    + 4 * (divK_fastSetup 88).length := by decide
example : v6CopyAUOff   = v6NormAOff    + 4 * (divK_normA 40).length := by decide
example : v6Digit3Off   = v6CopyAUOff   + 4 * divK_copyAU.length := by decide
example : v6Digit2Off   = v6Digit3Off   + 4 * (divK_fastDigit 4024 4032 4064 188).length := by decide
example : v6Digit1Off   = v6Digit2Off   + 4 * (divK_fastDigit 4032 4040 4072 148).length := by decide
example : v6Digit0Off   = v6Digit1Off   + 4 * (divK_fastDigit 4040 4048 4080 108).length := by decide
example : v6EpilogueOff = v6Digit0Off   + 4 * (divK_fastDigit 4048 4056 4088 68).length := by decide
example : v6Div128Off   = v6EpilogueOff + 4 * (divK_div_epilogue 1412).length := by decide
example : v6V5Off       = v6Div128Off   + 4 * divK_div128_v5.length := by
  have : divK_div128_v5.length = 85 := by unfold divK_div128_v5; rfl
  rw [this]; decide
-- exit = v5 entry + v5's internal NOP offset (1068)
example : v6ExitOff = v6V5Off + 1068 := by decide

-- MOD layout (denorm inserted after the digits)
example : modV6DenormOff   = v6Digit0Off      + 4 * (divK_fastDigit 4048 4056 4088 96).length := by decide
example : modV6EpilogueOff = modV6DenormOff   + 4 * divK_fastDenorm.length := by decide
example : modV6Div128Off   = modV6EpilogueOff + 4 * (divK_mod_epilogue 1412).length := by decide
example : modV6V5Off       = modV6Div128Off   + 4 * divK_div128_v5.length := by
  have : divK_div128_v5.length = 85 := by unfold divK_div128_v5; rfl
  rw [this]; decide
example : modV6ExitOff = modV6V5Off + 1068 := by decide

end EvmAsm.Evm64
