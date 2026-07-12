/-
  EvmAsm.Evm64.MulMod.Program

  MULMOD opcode (`MULMOD(a, b, N)` = (a * b) mod N under EVM
  rules, with `N = 0` returning `0`) as a 64-bit RISC-V program.

  This file currently carries the product-layout foundation for the
  eventual total `evm_mulmod`: a straight-line 4x4 schoolbook product
  block that leaves both halves of the 512-bit product addressable.
  Later slices add the reduction-by-N pipeline, top-level assembly,
  stack spec, and dispatcher wiring.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.Program

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Product layout
-- ============================================================================

/-- Low half of the full `a * b` product lives at `sp - 160 .. sp - 136`
    (the scratchpad sits *below* the live stack so MULMOD never clobbers
    unrelated stack items; the offsets are encoded as `signExtend12`
    negatives, e.g. `3936 ≡ -160 (mod 2^12)`). The stack input itself stays
    untouched:

      * `sp + 0  .. sp + 24`: `a`
      * `sp + 32 .. sp + 56`: `b`
      * `sp + 64 .. sp + 88`: `N`
      * `sp - 160 .. sp - 136`: product low half `pL`
      * `sp - 128 .. sp - 104`: product high half `pH`
      * `sp - 32  .. sp - 8`:   remainder accumulator

    All scratch slots are 8-byte aligned and lie in the free region below
    the stack pointer (negative 12-bit LD/SD offsets from `x12`), mirroring
    DIV's `sp + signExtend12 3936..` layout. -/
def mulmodProductLowBase : BitVec 12 := 3936

/-- High half of the full `a * b` product. See `mulmodProductLowBase`. -/
def mulmodProductHighBase : BitVec 12 := 3968

/-- All eight product-limb offsets, low half first then high half. -/
def mulmodProductOffsets : List (BitVec 12) :=
  [3936, 3944, 3952, 3960, 3968, 3976, 3984, 3992]

/-- Zero the product window before accumulating partial products. -/
def evm_mulmod_product_zero : Program :=
  SD .x12 .x0 3936 ;;
  SD .x12 .x0 3944 ;;
  SD .x12 .x0 3952 ;;
  SD .x12 .x0 3960 ;;
  SD .x12 .x0 3968 ;;
  SD .x12 .x0 3976 ;;
  SD .x12 .x0 3984 ;;
  SD .x12 .x0 3992

/-- Propagate the carry in `x10` through product result limbs.

    Each step adds the carry to one limb, stores the updated limb, and
    leaves the next carry in `x10`. Running this with `x10 = 0` is harmless,
    which keeps the per-partial-product shape straight-line. -/
def evm_mulmod_product_propagate_carry : List (BitVec 12) → Program
  | [] => []
  | off :: rest =>
      LD .x9 .x12 off ;;
      ADD .x9 .x9 .x10 ;;
      SLTU .x10 .x9 .x10 ;;
      SD .x12 .x9 off ;;
      evm_mulmod_product_propagate_carry rest

/-- Add one 64x64 partial product into the 512-bit result window.

    `aOff` and `bOff` select input limbs. `loOff` is product limb `i+j`;
    `hiOff` is product limb `i+j+1`; `carryOffsets` are the remaining
    higher limbs. The sequence computes `lo = MUL(a_i,b_j)` and
    `hi = MULHU(a_i,b_j)`, adds `lo` into `loOff`, adds `hi` plus the
    low-limb carry into `hiOff`, and then propagates any carry through
    `carryOffsets`. -/
def evm_mulmod_product_add_partial
    (aOff bOff loOff hiOff : BitVec 12) (carryOffsets : List (BitVec 12)) : Program :=
  LD .x5 .x12 aOff ;;
  LD .x6 .x12 bOff ;;
  single (.MUL .x7 .x5 .x6) ;;
  single (.MULHU .x8 .x5 .x6) ;;
  LD .x9 .x12 loOff ;;
  ADD .x9 .x9 .x7 ;;
  SLTU .x10 .x9 .x7 ;;
  SD .x12 .x9 loOff ;;
  LD .x9 .x12 hiOff ;;
  ADD .x11 .x9 .x8 ;;
  SLTU .x13 .x11 .x8 ;;
  ADD .x11 .x11 .x10 ;;
  SLTU .x14 .x11 .x10 ;;
  OR' .x10 .x13 .x14 ;;
  SD .x12 .x11 hiOff ;;
  evm_mulmod_product_propagate_carry carryOffsets

/-- Full 4x4 schoolbook product layout for MULMOD.

    Entry stack: `[a, b, N, ...]` at `x12 + 0`, `x12 + 32`, `x12 + 64`.
    Exit: `x12` and the input cells are unchanged; the 512-bit product is
    available as eight little-endian limbs at `mulmodProductOffsets`.
    The first four limbs are `pL`; the last four limbs are `pH`. -/
def evm_mulmod_product_layout : Program :=
  evm_mulmod_product_zero ;;
  evm_mulmod_product_add_partial 0 32 3936 3944 [3952, 3960, 3968, 3976, 3984, 3992] ;;
  evm_mulmod_product_add_partial 8 32 3944 3952 [3960, 3968, 3976, 3984, 3992] ;;
  evm_mulmod_product_add_partial 0 40 3944 3952 [3960, 3968, 3976, 3984, 3992] ;;
  evm_mulmod_product_add_partial 16 32 3952 3960 [3968, 3976, 3984, 3992] ;;
  evm_mulmod_product_add_partial 8 40 3952 3960 [3968, 3976, 3984, 3992] ;;
  evm_mulmod_product_add_partial 0 48 3952 3960 [3968, 3976, 3984, 3992] ;;
  evm_mulmod_product_add_partial 24 32 3960 3968 [3976, 3984, 3992] ;;
  evm_mulmod_product_add_partial 16 40 3960 3968 [3976, 3984, 3992] ;;
  evm_mulmod_product_add_partial 8 48 3960 3968 [3976, 3984, 3992] ;;
  evm_mulmod_product_add_partial 0 56 3960 3968 [3976, 3984, 3992] ;;
  evm_mulmod_product_add_partial 24 40 3968 3976 [3984, 3992] ;;
  evm_mulmod_product_add_partial 16 48 3968 3976 [3984, 3992] ;;
  evm_mulmod_product_add_partial 8 56 3968 3976 [3984, 3992] ;;
  evm_mulmod_product_add_partial 24 48 3976 3984 [3992] ;;
  evm_mulmod_product_add_partial 16 56 3976 3984 [3992] ;;
  evm_mulmod_product_add_partial 24 56 3984 3992 []

theorem evm_mulmod_product_zero_length :
    evm_mulmod_product_zero.length = 8 := by rfl

theorem evm_mulmod_product_zero_byte_length :
    4 * evm_mulmod_product_zero.length = 32 := by
  rw [evm_mulmod_product_zero_length]

theorem evm_mulmod_product_layout_length :
    evm_mulmod_product_layout.length = 440 := by set_option maxRecDepth 1000 in rfl

theorem evm_mulmod_product_layout_byte_length :
    4 * evm_mulmod_product_layout.length = 1760 := by
  rw [evm_mulmod_product_layout_length]

-- ============================================================================
-- Reduction helper blocks
-- ============================================================================

/-- Scratch dividend base for 256-bit `evm_mod_callable` calls used by the
    MULMOD reduction pipeline. The original stack and product layout stay at:

      * `sp + 0  .. sp + 24`: input `a`
      * `sp + 32 .. sp + 56`: input `b`
      * `sp + 64 .. sp + 88`: modulus `N`
      * `sp + 96 .. sp + 120`: product low half `pL`
      * `sp + 128.. sp + 152`: product high half `pH`

    The reduction work window starts after `pH`:

      * `sp + 160.. sp + 184`: callable MOD dividend
      * `sp + 192.. sp + 216`: callable MOD divisor, then MOD remainder

    `evm_mod_callable` is entered with `x12 = sp + 160`; it returns with
    `x12 = sp + 192` and the remainder in `sp + 192..216`. The caller then
    restores `x12` back to the original `sp`. -/
def mulmodReductionWorkDividendBase : BitVec 12 := 160

/-- Scratch divisor / result base for MULMOD reduction helper calls. -/
def mulmodReductionWorkModulusBase : BitVec 12 := 192

/-- Phase 2 -- short-circuit test for `N = 0`.

    On entry, `x12 = sp` and `N` is still the third input stack cell at
    `sp + 64..88`. OR-fold the four limbs into `x6`; if all are zero, branch
    to the zero-result path. The branch byte distance is a parameter so the
    later top-level `evm_mulmod` assembly can pin the concrete layout.

    8 instructions. -/
def evm_mulmod_reduce_n_zero_test (zeroPathOff : BitVec 13) : Program :=
  LD .x6 .x12 64 ;;
  LD .x5 .x12 72 ;;
  OR' .x6 .x6 .x5 ;;
  LD .x5 .x12 80 ;;
  OR' .x6 .x6 .x5 ;;
  LD .x5 .x12 88 ;;
  OR' .x6 .x6 .x5 ;;
  single (.BEQ .x6 .x0 zeroPathOff)

theorem evm_mulmod_reduce_n_zero_test_length (zeroPathOff : BitVec 13) :
    (evm_mulmod_reduce_n_zero_test zeroPathOff).length = 8 := by
  revert zeroPathOff
  decide

theorem evm_mulmod_reduce_n_zero_test_byte_length (zeroPathOff : BitVec 13) :
    4 * (evm_mulmod_reduce_n_zero_test zeroPathOff).length = 32 := by
  rw [evm_mulmod_reduce_n_zero_test_length]

/-- Prepare the shared 256-bit MOD work window.

    Copies a four-limb dividend from `src + 0..24` and the original modulus
    `N` from `sp + 64..88` into the callable work slots:

      * `sp + 160..184`: dividend
      * `sp + 192..216`: divisor `N`

    The block does not change `x12`; it only prepares memory. The later
    call block temporarily moves `x12` to `sp + 160` for `evm_mod_callable`.

    16 instructions. -/
def evm_mulmod_reduce_prepare_mod_args (src : BitVec 12) : Program :=
  LD .x5 .x12 src ;;
  SD .x12 .x5 160 ;;
  LD .x5 .x12 (src + 8) ;;
  SD .x12 .x5 168 ;;
  LD .x5 .x12 (src + 16) ;;
  SD .x12 .x5 176 ;;
  LD .x5 .x12 (src + 24) ;;
  SD .x12 .x5 184 ;;
  LD .x5 .x12 64 ;;
  SD .x12 .x5 192 ;;
  LD .x5 .x12 72 ;;
  SD .x12 .x5 200 ;;
  LD .x5 .x12 80 ;;
  SD .x12 .x5 208 ;;
  LD .x5 .x12 88 ;;
  SD .x12 .x5 216

theorem evm_mulmod_reduce_prepare_mod_args_length (src : BitVec 12) :
    (evm_mulmod_reduce_prepare_mod_args src).length = 16 := by
  revert src
  decide

theorem evm_mulmod_reduce_prepare_mod_args_byte_length (src : BitVec 12) :
    4 * (evm_mulmod_reduce_prepare_mod_args src).length = 64 := by
  rw [evm_mulmod_reduce_prepare_mod_args_length]

/-- Call `evm_mod_callable` on the prepared work window.

    Precondition: `evm_mulmod_reduce_prepare_mod_args` has copied a dividend
    into `sp + 160..184` and `N` into `sp + 192..216`. This block shifts
    `x12` to `sp + 160`, performs a near call to the callable MOD routine, and
    restores `x12` to the original `sp`. Since callable MOD returns with
    `x12 = sp + 192`, the restore is `ADDI x12, x12, -192`, encoded as the
    12-bit immediate `3904`.

    The MOD remainder is left in `sp + 192..216`.

    3 instructions. -/
def evm_mulmod_reduce_call_mod (modOff : BitVec 21) : Program :=
  ADDI .x12 .x12 160 ;;
  JAL .x1 modOff ;;
  ADDI .x12 .x12 3904

theorem evm_mulmod_reduce_call_mod_length (modOff : BitVec 21) :
    (evm_mulmod_reduce_call_mod modOff).length = 3 := by
  show (((ADDI .x12 .x12 160 ;; JAL .x1 modOff) ;;
          ADDI .x12 .x12 3904) : Program).length = 3
  simp only [seq, Program.length_append]
  rfl

theorem evm_mulmod_reduce_call_mod_byte_length (modOff : BitVec 21) :
    4 * (evm_mulmod_reduce_call_mod modOff).length = 12 := by
  rw [evm_mulmod_reduce_call_mod_length]

/-- Reduce the high half of the product, `pH mod N`.

    Entry contract from `evm_mulmod_product_layout`: `pH` is at
    `sp + 128..152`, `N` is at `sp + 64..88`, and `x12 = sp`. Exit:
    `x12 = sp`; `sp + 192..216` contains `pH mod N` as returned by
    `evm_mod_callable`.

    19 instructions. -/
def evm_mulmod_reduce_high_half (modOff : BitVec 21) : Program :=
  evm_mulmod_reduce_prepare_mod_args mulmodProductHighBase ;;
  evm_mulmod_reduce_call_mod modOff

theorem evm_mulmod_reduce_high_half_length (modOff : BitVec 21) :
    (evm_mulmod_reduce_high_half modOff).length = 19 := by
  unfold evm_mulmod_reduce_high_half
  simp only [seq, Program.length_append,
    evm_mulmod_reduce_prepare_mod_args_length, evm_mulmod_reduce_call_mod_length]

theorem evm_mulmod_reduce_high_half_byte_length (modOff : BitVec 21) :
    4 * (evm_mulmod_reduce_high_half modOff).length = 76 := by
  rw [evm_mulmod_reduce_high_half_length]

/-- Reduce the low half of the product, `pL mod N`.

    Entry contract from `evm_mulmod_product_layout`: `pL` is at
    `sp + 96..120`, `N` is at `sp + 64..88`, and `x12 = sp`. Exit:
    `x12 = sp`; `sp + 192..216` contains `pL mod N` as returned by
    `evm_mod_callable`.

    19 instructions. -/
def evm_mulmod_reduce_low_half (modOff : BitVec 21) : Program :=
  evm_mulmod_reduce_prepare_mod_args mulmodProductLowBase ;;
  evm_mulmod_reduce_call_mod modOff

theorem evm_mulmod_reduce_low_half_length (modOff : BitVec 21) :
    (evm_mulmod_reduce_low_half modOff).length = 19 := by
  unfold evm_mulmod_reduce_low_half
  simp only [seq, Program.length_append,
    evm_mulmod_reduce_prepare_mod_args_length, evm_mulmod_reduce_call_mod_length]

theorem evm_mulmod_reduce_low_half_byte_length (modOff : BitVec 21) :
    4 * (evm_mulmod_reduce_low_half modOff).length = 76 := by
  rw [evm_mulmod_reduce_low_half_length]

/-- Zero-result path for `N = 0`.

    MULMOD pops `[a, b, N]` and pushes one result, so the final result slot is
    the original `sp + 64..88` after the epilogue advances `x12` by 64. This
    block writes the four zero limbs there and leaves pointer movement to
    `evm_mulmod_epilogue`.

    4 instructions. -/
def evm_mulmod_reduce_zero_path : Program :=
  SD .x12 .x0 64 ;;
  SD .x12 .x0 72 ;;
  SD .x12 .x0 80 ;;
  SD .x12 .x0 88

theorem evm_mulmod_reduce_zero_path_length :
    evm_mulmod_reduce_zero_path.length = 4 := by rfl

theorem evm_mulmod_reduce_zero_path_byte_length :
    4 * evm_mulmod_reduce_zero_path.length = 16 := by
  rw [evm_mulmod_reduce_zero_path_length]

/-- MULMOD epilogue: advance the EVM stack pointer after the result has been
    placed at the original `sp + 64..88`. -/
def evm_mulmod_epilogue : Program :=
  ADDI .x12 .x12 64

theorem evm_mulmod_epilogue_length :
    evm_mulmod_epilogue.length = 1 := by rfl

theorem evm_mulmod_epilogue_byte_length :
    4 * evm_mulmod_epilogue.length = 4 := by
  rw [evm_mulmod_epilogue_length]


-- ============================================================================
-- Total top-level MULMOD assembly
-- ============================================================================

/-- Remainder accumulator base for the bit-serial 512-bit reduction.
    Lives at `sp - 32 .. sp - 8` (`4064 ≡ -32 (mod 2^12)`), below the stack. -/
def mulmodRemainderBase : BitVec 12 := 4064

/-- OR-fold the modulus limbs and branch to the nonzero path.

    The nonzero target sits immediately after the zero-result path, epilogue,
    and one skip-JAL, so the `BNE` byte offset is fixed at 28. -/
def evm_mulmod_nonzero_or_zero_prefix : Program :=
  LD .x6 .x12 64 ;;
  LD .x5 .x12 72 ;;
  OR' .x6 .x6 .x5 ;;
  LD .x5 .x12 80 ;;
  OR' .x6 .x6 .x5 ;;
  LD .x5 .x12 88 ;;
  OR' .x6 .x6 .x5 ;;
  BNE .x6 .x0 (28 : BitVec 13)

/-- Branch over the nonzero product/reduction path after the `N = 0` result.
    The target is the end of `evm_mulmod`. -/
def evm_mulmod_zero_path_skip_nonzero : Program :=
  JAL .x0 (2108 : BitVec 21)

/-- Initialize the 256-bit remainder accumulator and loop cursors.

    `x16` points at the current product limb, starting from the highest limb at
    `sp - 104` (`3992 ≡ -104`); `x18` counts the eight product limbs. -/
def evm_mulmod_reduce512_init : Program :=
  SD .x12 .x0 4064 ;;
  SD .x12 .x0 4072 ;;
  SD .x12 .x0 4080 ;;
  SD .x12 .x0 4088 ;;
  ADDI .x16 .x12 3992 ;;
  ADDI .x18 .x0 8

/-- One bit step of the 512-bit long reduction.

    On entry `x17` holds the current product limb. The block consumes its most
    significant bit, shifts `x17` left by one for the next iteration, updates
    `rem = 2 * rem + bit`, and conditionally subtracts `N` if the updated
    remainder is at least `N`. -/
def evm_mulmod_reduce512_inner_step : Program :=
  SRLI .x19 .x17 63 ;;
  SLLI .x17 .x17 1 ;;
  LD .x5 .x12 4064 ;;
  SRLI .x20 .x5 63 ;;
  SLLI .x6 .x5 1 ;;
  OR' .x6 .x6 .x19 ;;
  SD .x12 .x6 4064 ;;
  LD .x5 .x12 4072 ;;
  SRLI .x19 .x5 63 ;;
  SLLI .x6 .x5 1 ;;
  OR' .x6 .x6 .x20 ;;
  SD .x12 .x6 4072 ;;
  LD .x5 .x12 4080 ;;
  SRLI .x20 .x5 63 ;;
  SLLI .x6 .x5 1 ;;
  OR' .x6 .x6 .x19 ;;
  SD .x12 .x6 4080 ;;
  LD .x5 .x12 4088 ;;
  SLLI .x6 .x5 1 ;;
  OR' .x6 .x6 .x20 ;;
  SD .x12 .x6 4088 ;;
  SRLI .x8 .x5 63 ;;
  BNE .x8 .x0 (64 : BitVec 13) ;;
  LD .x6 .x12 4088 ;;
  LD .x7 .x12 88 ;;
  BLTU .x7 .x6 (52 : BitVec 13) ;;
  BLTU .x6 .x7 (152 : BitVec 13) ;;
  LD .x6 .x12 4080 ;;
  LD .x7 .x12 80 ;;
  BLTU .x7 .x6 (36 : BitVec 13) ;;
  BLTU .x6 .x7 (136 : BitVec 13) ;;
  LD .x6 .x12 4072 ;;
  LD .x7 .x12 72 ;;
  BLTU .x7 .x6 (20 : BitVec 13) ;;
  BLTU .x6 .x7 (120 : BitVec 13) ;;
  LD .x6 .x12 4064 ;;
  LD .x7 .x12 64 ;;
  BLTU .x6 .x7 (108 : BitVec 13) ;;
  LD .x6 .x12 4064 ;;
  LD .x7 .x12 64 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x11 .x6 .x7 ;;
  SD .x12 .x5 4064 ;;
  LD .x6 .x12 4072 ;;
  LD .x7 .x12 72 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x10 .x6 .x7 ;;
  SLTU .x13 .x5 .x11 ;;
  SUB .x5 .x5 .x11 ;;
  OR' .x11 .x10 .x13 ;;
  SD .x12 .x5 4072 ;;
  LD .x6 .x12 4080 ;;
  LD .x7 .x12 80 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x10 .x6 .x7 ;;
  SLTU .x13 .x5 .x11 ;;
  SUB .x5 .x5 .x11 ;;
  OR' .x11 .x10 .x13 ;;
  SD .x12 .x5 4080 ;;
  LD .x6 .x12 4088 ;;
  LD .x7 .x12 88 ;;
  SUB .x5 .x6 .x7 ;;
  SUB .x5 .x5 .x11 ;;
  SD .x12 .x5 4088 ;;
  ADDI .x15 .x15 4095 ;;
  BNE .x15 .x0 (-260 : BitVec 13)

/-- Outer eight-limb reducer loop. -/
def evm_mulmod_reduce512_loop : Program :=
  LD .x17 .x16 0 ;;
  ADDI .x15 .x0 64 ;;
  evm_mulmod_reduce512_inner_step ;;
  ADDI .x16 .x16 4088 ;;
  ADDI .x18 .x18 4095 ;;
  BNE .x18 .x0 (-280 : BitVec 13)

/-- Copy the finalized remainder into the EVM result slot `sp + 64..88`. -/
def evm_mulmod_reduce512_write_result : Program :=
  LD .x5 .x12 4064 ;;
  SD .x12 .x5 64 ;;
  LD .x5 .x12 4072 ;;
  SD .x12 .x5 72 ;;
  LD .x5 .x12 4080 ;;
  SD .x12 .x5 80 ;;
  LD .x5 .x12 4088 ;;
  SD .x12 .x5 88

/-- Total 512-bit-by-256-bit MULMOD reduction path. -/
def evm_mulmod_reduce512 : Program :=
  evm_mulmod_reduce512_init ;;
  evm_mulmod_reduce512_loop ;;
  evm_mulmod_reduce512_write_result ;;
  evm_mulmod_epilogue

/-- Total runtime MULMOD program.

    The nonzero path computes the full 512-bit product with
    `evm_mulmod_product_layout` and reduces it with a bit-serial long-reduction
    loop. This is intentionally runtime-first: it favors complete behavior for
    EEST over proof-oriented performance. -/
def evm_mulmod : Program :=
  evm_mulmod_nonzero_or_zero_prefix ;;
  evm_mulmod_reduce_zero_path ;;
  evm_mulmod_epilogue ;;
  evm_mulmod_zero_path_skip_nonzero ;;
  evm_mulmod_product_layout ;;
  evm_mulmod_reduce512

theorem evm_mulmod_nonzero_or_zero_prefix_length :
    evm_mulmod_nonzero_or_zero_prefix.length = 8 := by rfl

theorem evm_mulmod_zero_path_skip_nonzero_length :
    evm_mulmod_zero_path_skip_nonzero.length = 1 := by rfl

theorem evm_mulmod_reduce512_init_length :
    evm_mulmod_reduce512_init.length = 6 := by rfl

theorem evm_mulmod_reduce512_inner_step_length :
    evm_mulmod_reduce512_inner_step.length = 66 := by set_option maxRecDepth 1000 in rfl

theorem evm_mulmod_reduce512_loop_length :
    evm_mulmod_reduce512_loop.length = 71 := by set_option maxRecDepth 1000 in rfl

theorem evm_mulmod_reduce512_write_result_length :
    evm_mulmod_reduce512_write_result.length = 8 := by rfl

theorem evm_mulmod_reduce512_length :
    evm_mulmod_reduce512.length = 86 := by
  unfold evm_mulmod_reduce512
  simp only [seq, Program.length_append, evm_mulmod_reduce512_init_length,
    evm_mulmod_reduce512_loop_length, evm_mulmod_reduce512_write_result_length,
    evm_mulmod_epilogue_length]

theorem evm_mulmod_length : evm_mulmod.length = 540 := by
  unfold evm_mulmod
  simp only [seq, Program.length_append, evm_mulmod_nonzero_or_zero_prefix_length,
    evm_mulmod_reduce_zero_path_length, evm_mulmod_epilogue_length,
    evm_mulmod_zero_path_skip_nonzero_length, evm_mulmod_product_layout_length,
    evm_mulmod_reduce512_length]

theorem evm_mulmod_byte_length : 4 * evm_mulmod.length = 2160 := by
  rw [evm_mulmod_length]

theorem evm_mulmod_nonzero_path_start_byte :
    4 * (evm_mulmod_nonzero_or_zero_prefix.length +
      evm_mulmod_reduce_zero_path.length + evm_mulmod_epilogue.length +
      evm_mulmod_zero_path_skip_nonzero.length) = 56 := by
  rw [evm_mulmod_nonzero_or_zero_prefix_length, evm_mulmod_reduce_zero_path_length,
    evm_mulmod_epilogue_length, evm_mulmod_zero_path_skip_nonzero_length]

theorem evm_mulmod_bne_nonzero_target_byte : 28 + (28 : Nat) = 56 := by rfl

theorem evm_mulmod_zero_skip_target_byte : 52 + (2108 : Nat) = 2160 := by rfl

theorem evm_mulmod_reduce512_start_byte : 56 + 4 * evm_mulmod_product_layout.length = 1816 := by
  rw [evm_mulmod_product_layout_length]

theorem evm_mulmod_reduce512_end_byte : 1816 + 4 * evm_mulmod_reduce512.length = 2160 := by
  rw [evm_mulmod_reduce512_length]

-- ============================================================================
-- Concrete execution checks for the layout slice
-- ============================================================================


/-- Bounded execution until a target PC is reached. -/
def runUntilPc (targetPc : Word) : Nat → MachineState → Option MachineState
  | 0, s => if s.pc == targetPc then some s else none
  | fuel + 1, s =>
      if s.pc == targetPc then
        some s
      else
        (step s).bind (runUntilPc targetPc fuel ·)

/-- Create a test state for the total MULMOD program with `a`, `b`, and `N`
    in EVM stack order. -/
def mkMulModTestState (sp : Word)
    (a0 a1 a2 a3 : Word)
    (b0 b1 b2 b3 : Word)
    (n0 n1 n2 n3 : Word) : MachineState where
  regs := fun r =>
    match r with
    | .x12 => sp
    | _    => 0
  mem := fun a =>
    if a == sp then a0
    else if a == sp + 8 then a1
    else if a == sp + 16 then a2
    else if a == sp + 24 then a3
    else if a == sp + 32 then b0
    else if a == sp + 40 then b1
    else if a == sp + 48 then b2
    else if a == sp + 56 then b3
    else if a == sp + 64 then n0
    else if a == sp + 72 then n1
    else if a == sp + 80 then n2
    else if a == sp + 88 then n3
    else 0
  code := loadProgram 0 evm_mulmod
  pc := 0

/-- Run `evm_mulmod` and extract `(x12, result limbs)`. -/
def runMulMod (sp : Word)
    (a0 a1 a2 a3 : Word)
    (b0 b1 b2 b3 : Word)
    (n0 n1 n2 n3 : Word)
    (fuel : Nat) : Option (Word × List Word) :=
  let s := mkMulModTestState sp a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3
  match runUntilPc (4 * evm_mulmod.length) fuel s with
  | some s' =>
      some (s'.getReg .x12,
        [s'.getMem (sp + 64), s'.getMem (sp + 72), s'.getMem (sp + 80), s'.getMem (sp + 88)])
  | none => none

/-- Zero modulus returns zero without entering the product/reduction path. -/
example : runMulMod 1024
    2 0 0 0
    3 0 0 0
    0 0 0 0
    64 = some (1088, [0, 0, 0, 0]) := by set_option maxRecDepth 5000 in rfl

-- Nonzero end-to-end MULMOD cases execute the 512-iteration reducer loop and
-- are intentionally covered by ziskemu runtime tests in the dispatcher slice
-- rather than as module-level `native_decide` examples.

/-- Create a test state for the product-layout block with `a`, `b`, and `N`
    in the eventual MULMOD stack order. -/
def mkMulModProductLayoutTestState (sp : Word)
    (a0 a1 a2 a3 : Word)
    (b0 b1 b2 b3 : Word)
    (n0 n1 n2 n3 : Word) : MachineState where
  regs := fun r =>
    match r with
    | .x12 => sp
    | _    => 0
  mem := fun a =>
    if a == sp then a0
    else if a == sp + 8 then a1
    else if a == sp + 16 then a2
    else if a == sp + 24 then a3
    else if a == sp + 32 then b0
    else if a == sp + 40 then b1
    else if a == sp + 48 then b2
    else if a == sp + 56 then b3
    else if a == sp + 64 then n0
    else if a == sp + 72 then n1
    else if a == sp + 80 then n2
    else if a == sp + 88 then n3
    else 0
  code := loadProgram 0 evm_mulmod_product_layout
  pc := 0

/-- Run the product-layout block and extract `(x12, N limbs, pL limbs, pH limbs)`. -/
def runMulModProductLayout (sp : Word)
    (a0 a1 a2 a3 : Word)
    (b0 b1 b2 b3 : Word)
    (n0 n1 n2 n3 : Word)
    (steps : Nat) : Option (Word × List Word × List Word × List Word) :=
  let s := mkMulModProductLayoutTestState sp a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3
  match stepN steps s with
  | some s' =>
      some (s'.getReg .x12,
        [s'.getMem (sp + 64), s'.getMem (sp + 72), s'.getMem (sp + 80), s'.getMem (sp + 88)],
        [s'.getMem (sp + signExtend12 3936), s'.getMem (sp + signExtend12 3944),
         s'.getMem (sp + signExtend12 3952), s'.getMem (sp + signExtend12 3960)],
        [s'.getMem (sp + signExtend12 3968), s'.getMem (sp + signExtend12 3976),
         s'.getMem (sp + signExtend12 3984), s'.getMem (sp + signExtend12 3992)])
  | none => none

/-- Zero product leaves both halves zero and preserves `N`. -/
example : runMulModProductLayout 1024
    0 0 0 0
    0 0 0 0
    7 0 0 0
    440 = some (1024, [7, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]) := by set_option maxRecDepth 5000 in rfl

/-- Small product: 2 * 3 = 6, high half zero. -/
example : runMulModProductLayout 1024
    2 0 0 0
    3 0 0 0
    5 0 0 0
    440 = some (1024, [5, 0, 0, 0], [6, 0, 0, 0], [0, 0, 0, 0]) := by set_option maxRecDepth 5000 in rfl

/-- High-half-producing product: 2^192 * 2^64 = 2^256. -/
example : runMulModProductLayout 1024
    0 0 0 1
    0 1 0 0
    11 0 0 0
    440 = some (1024, [11, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]) := by set_option maxRecDepth 5000 in rfl

/-- Carry-heavy product: `(2^256 - 1)^2 = 1 + (2^256 - 2) * 2^256`. -/
example : runMulModProductLayout 1024
    0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
    0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
    13 0 0 0
    440 = some (1024, [13, 0, 0, 0],
      [1, 0, 0, 0],
      [0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF]) := by set_option maxRecDepth 5000 in rfl

end EvmAsm.Evm64
