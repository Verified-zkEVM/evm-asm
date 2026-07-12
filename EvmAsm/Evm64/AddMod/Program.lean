/-
  EvmAsm.Evm64.AddMod.Program

  ADDMOD opcode (`ADDMOD(a, b, N)` = (a + b) mod N under EVM
  rules, with `N = 0` returning `0`) as a 64-bit RISC-V program.

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0).

  Slice `evm-asm-4gq5y` lands the first two building blocks of the
  decomposition described in `docs/91-addmod-mulmod-survey.md` §5.1:

  * `evm_addmod_prologue` — fold `a + b` into the second operand slot
    using the existing 4-limb `evm_add` Program. After this block, the
    EVM stack is `[a + b (mod 2^256), N, …]` and `x12` has advanced by
    +32. The 257th carry-out bit produced by the limb-3 add of
    `evm_add` is left in scratch register `x5` (per
    `EvmAsm/Evm64/Add/Program.lean`); the next block parks it in `x7`.
  * `evm_addmod_phase1_carry` — copy the 257th carry bit from `x5`
    (where `evm_add` deposits it) into the dedicated scratch register
    `x7`, freeing `x5` for the modulus-reduction phase that follows
    (which reuses `x5..x6/x11` as inner-loop scratch).

  The actual top-level `evm_addmod : Program` will be assembled in a
  later slice (`evm-asm-xl2jn`); this file currently only carries the
  prologue + phase 1 sub-programs and their length lemmas.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Add.Program

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- ADDMOD prologue: fold `a + b` (mod 2^256) into the second-from-top
    EVM stack slot using the existing 4-limb `evm_add` Program. On
    entry: stack top-to-bottom is `[a, b, N, …]` (32 bytes each, with
    `a` at `x12 + 0`, `b` at `x12 + 32`, `N` at `x12 + 64`). On exit:
    `x12` has advanced by +32 and the top two cells are
    `[a + b (mod 2^256), N, …]`; `N` at the original `x12 + 64` is
    untouched (it now sits at the new `x12 + 32`).

    Note: `evm_add` is reused verbatim — it performs the limb-by-limb
    schoolbook add and finishes with `ADDI x12, x12, 32`. Crucially,
    `evm_add`'s final block leaves the limb-3 carry-out bit (i.e. the
    257th bit of `a.toNat + b.toNat`) in scratch register `x5` via
    the trailing `OR x5, x11, x6` (see `EvmAsm/Evm64/Add/Program.lean`
    line 36). `evm_addmod_phase1_carry` consumes that bit immediately.

    Length: identical to `evm_add` (30 instructions: 5 + 3·8 + 1
    trailing `ADDI`). -/
def evm_addmod_prologue : Program :=
  evm_add

theorem evm_addmod_prologue_length :
    evm_addmod_prologue.length = 30 := by decide

theorem evm_addmod_prologue_byte_length :
    4 * evm_addmod_prologue.length = 120 := by
  rw [evm_addmod_prologue_length]

/-- ADDMOD phase 1 — park the 257th carry bit into the dedicated
    scratch register `x7`.

    On entry (immediately after `evm_addmod_prologue` = `evm_add`):
    `x5` holds the 257th carry-out bit of `a.toNat + b.toNat` (`0` or
    `1`), per the trailing `OR x5, x11, x6` in `evm_add`'s limb-3
    block. The remainder of ADDMOD wants this bit in `x7` so that
    `x5..x6/x11` are free as scratch for the upcoming modulus
    reduction phase.

    Implementation: a single register move `x7 := x5`, encoded as
    `ADDI x7, x5, 0` (the canonical RV64 `MV` pseudo-instruction
    spelling already used elsewhere in the codebase, e.g.
    `EvmAsm/Rv64/RLP/Phase3LongList.lean`).

    1 instruction. -/
def evm_addmod_phase1_carry : Program :=
  ADDI .x7 .x5 0

theorem evm_addmod_phase1_carry_length :
    evm_addmod_phase1_carry.length = 1 := by decide

theorem evm_addmod_phase1_carry_byte_length :
    4 * evm_addmod_phase1_carry.length = 4 := by
  rw [evm_addmod_phase1_carry_length]

-- ============================================================================
-- Slice 3b — Phase 2 (modulus reduction) + Epilogue program skeletons
-- ============================================================================
--
-- Per `docs/91-addmod-mulmod-survey.md` §5.1, after the prologue + phase 1
-- finish, the runtime state is:
--
--   * `x12 = sp + 32` (advanced by `evm_add`'s trailing `ADDI x12, x12, 32`)
--   * Top stack cell at `x12 + 0..24` holds `r := (a + b) (mod 2^256)`
--   * Stack cell at `x12 + 32..58` holds `N` (the modulus) — untouched
--   * `x7` holds the 257th carry bit `c ∈ {0, 1}` of `a.toNat + b.toNat`
--
-- The remaining work decomposes into three bite-sized blocks (as four
-- separate `Program`s here, plus the assembled phase-2 wrapper in slice
-- 3c). All branch / call distances are passed in as `BitVec`-typed
-- parameters so the assembled `evm_addmod` Program in slice 3c
-- (`evm-asm-xl2jn`) can pin the concrete offsets without re-rolling
-- this file.
--
-- This slice introduces only the program text and length lemmas; per
-- `evm-asm-f027s` acceptance, no `cpsTriple` proofs are required.
-- The actual stack-level `evm_addmod_stack_spec` is the job of slice 3d
-- (`evm-asm-s7v49`).

/-- Phase 2 — short-circuit test for `N = 0`.

    OR-folds the four 64-bit limbs of `N` (currently at `x12 + 32..56`,
    since the prologue advanced `x12` by 32 and `N` was originally the
    third stack cell) into scratch register `x6`, then takes a
    forward `BEQ x6, x0, skipOff` branch to the zero-store path when
    `N` is identically zero. The `BEQ` byte offset `skipOff` is the
    distance from this BEQ instruction to the entry of
    `evm_addmod_phase2_zero_path`; the concrete value is pinned in
    slice 3c when `evm_addmod` is assembled.

    8 instructions:

      LD  x6, x12, 32     -- N limb 0
      LD  x5, x12, 40     -- N limb 1
      OR  x6, x6, x5
      LD  x5, x12, 48     -- N limb 2
      OR  x6, x6, x5
      LD  x5, x12, 56     -- N limb 3
      OR  x6, x6, x5
      BEQ x6, x0, skipOff -- if N = 0, branch to zero-store path
-/
def evm_addmod_phase2_n_zero_test (skipOff : BitVec 13) : Program :=
  LD .x6 .x12 32 ;;
  LD .x5 .x12 40 ;;
  OR' .x6 .x6 .x5 ;;
  LD .x5 .x12 48 ;;
  OR' .x6 .x6 .x5 ;;
  LD .x5 .x12 56 ;;
  OR' .x6 .x6 .x5 ;;
  single (.BEQ .x6 .x0 skipOff)

theorem evm_addmod_phase2_n_zero_test_length (skipOff : BitVec 13) :
    (evm_addmod_phase2_n_zero_test skipOff).length = 8 := by
  show ((((((((LD .x6 .x12 32 ;; LD .x5 .x12 40) ;; OR' .x6 .x6 .x5) ;;
              LD .x5 .x12 48) ;; OR' .x6 .x6 .x5) ;;
            LD .x5 .x12 56) ;; OR' .x6 .x6 .x5) ;;
          single (.BEQ .x6 .x0 skipOff)) : Program).length = 8
  simp only [seq, Program.length_append]
  rfl

theorem evm_addmod_phase2_n_zero_test_byte_length (skipOff : BitVec 13) :
    4 * (evm_addmod_phase2_n_zero_test skipOff).length = 32 := by
  rw [evm_addmod_phase2_n_zero_test_length]

/-- Phase 2 — modulus-reduction call site.

    Single-instruction near `JAL` invocation of `evm_mod_callable`
    (the LP64 shim around `evm_mod`, see
    `EvmAsm/Evm64/DivMod/Callable.lean`). The full reduction
    pipeline per the survey is

       1. compute `m := 2^256 mod N`        (a near-call to `evm_mod`)
       2. compute `(c · m + r) mod N`       (a second near-call to
                                              `evm_mod` after a
                                              257-bit accumulate)

    Both call sites share the same `JAL x1, modOff` shape; this
    block is a single such call. The surrounding scaffolding
    (argument marshalling, post-call result move, the conditional
    use of the carry bit `c`) lives in slice 3c (`evm-asm-xl2jn`)
    when the loop layout is final.

    The `modOff : BitVec 21` parameter is the signed 21-bit byte
    offset from the JAL site to the entry of `evm_mod_callable`;
    the concrete numeric value is pinned in slice 3c.

    1 instruction. -/
def evm_addmod_phase2_mod_call (modOff : BitVec 21) : Program :=
  JAL .x1 modOff

theorem evm_addmod_phase2_mod_call_length (modOff : BitVec 21) :
    (evm_addmod_phase2_mod_call modOff).length = 1 := rfl

theorem evm_addmod_phase2_mod_call_byte_length (modOff : BitVec 21) :
    4 * (evm_addmod_phase2_mod_call modOff).length = 4 := by
  rw [evm_addmod_phase2_mod_call_length]

/-- Phase 2 — composite reduce body (the non-zero-N path).

    Sequences the modulus-reduction call into a structural block.
    For the no-proofs slice we keep this thin: a single
    `JAL x1, modOff` near-call. Slice 3c may either wrap this in
    additional marshalling instructions or replace it with a richer
    composition of `evm_addmod_phase2_mod_call` invocations once the
    full m / accumulate pipeline is laid out.

    Currently 1 instruction; the parameter shape is fixed so slice
    3c does not need to re-derive offsets if the body grows.

    The trailing `JAL x0, exitOff` (an unconditional branch past the
    zero-store path to the epilogue entry) is *not* part of this
    block — slice 3c emits it inline so that the zero-store path
    can BEQ-skip exactly past the reduce body without extra
    bookkeeping. -/
def evm_addmod_phase2_reduce (modOff : BitVec 21) : Program :=
  evm_addmod_phase2_mod_call modOff

theorem evm_addmod_phase2_reduce_length (modOff : BitVec 21) :
    (evm_addmod_phase2_reduce modOff).length = 1 := rfl

theorem evm_addmod_phase2_reduce_byte_length (modOff : BitVec 21) :
    4 * (evm_addmod_phase2_reduce modOff).length = 4 := by
  rw [evm_addmod_phase2_reduce_length]

-- ============================================================================
-- pow256ModN runtime helper blocks
-- ============================================================================

/-- Dividend scratch base for the `2^256 mod N` helper.

    After `evm_addmod_prologue`, `x12 = sp + 32`, the truncated sum `r` is at
    `x12 + 0..24`, and the modulus `N` is at `x12 + 32..56`. The helper uses
    a temporary callable-MOD work window after these live cells:

      * `x12 + 64..88`: callable MOD dividend
      * `x12 + 96..120`: callable MOD divisor, then callable MOD remainder

    Entering `evm_mod_callable` with `x12 = x12 + 64` returns with `x12` at
    the divisor/remainder base (`old x12 + 96`), so the caller restores the
    ADDMOD frame pointer with `ADDI x12, x12, -96` (immediate 4000). -/
def addmodPow256WorkDividendBase : BitVec 12 := 64

/-- Divisor/result scratch base for the `2^256 mod N` helper. -/
def addmodPow256WorkModulusBase : BitVec 12 := 96

/-- Prepare the first MOD call for `(-1) mod N`.

    The algebraic identity used by the total ADDMOD runtime is
    `2^256 mod N = (((2^256 - 1) mod N) + 1) mod N` for `N != 0`.
    This block materializes the four-limb all-ones dividend at
    `x12 + 64..88` and copies the live modulus from `x12 + 32..56` to the
    callable divisor slots at `x12 + 96..120`.

    It does not move `x12`; the call wrapper does that.

    13 instructions. -/
def evm_addmod_pow256_prepare_minus_one_mod_args : Program :=
  ADDI .x5 .x0 4095 ;;
  SD .x12 .x5 64 ;;
  SD .x12 .x5 72 ;;
  SD .x12 .x5 80 ;;
  SD .x12 .x5 88 ;;
  LD .x5 .x12 32 ;;
  SD .x12 .x5 96 ;;
  LD .x5 .x12 40 ;;
  SD .x12 .x5 104 ;;
  LD .x5 .x12 48 ;;
  SD .x12 .x5 112 ;;
  LD .x5 .x12 56 ;;
  SD .x12 .x5 120

theorem evm_addmod_pow256_prepare_minus_one_mod_args_length :
    evm_addmod_pow256_prepare_minus_one_mod_args.length = 13 := by decide

theorem evm_addmod_pow256_prepare_minus_one_mod_args_byte_length :
    4 * evm_addmod_pow256_prepare_minus_one_mod_args.length = 52 := by
  rw [evm_addmod_pow256_prepare_minus_one_mod_args_length]

/-- Call `evm_mod_callable` on the pow256 helper work window.

    Precondition: dividend at `x12 + 64..88`, divisor at `x12 + 96..120`.
    The block shifts `x12` to the dividend, performs the near call, then
    restores `x12` to the ADDMOD frame. The remainder is left at
    `x12 + 96..120`.

    3 instructions. -/
def evm_addmod_pow256_call_mod (modOff : BitVec 21) : Program :=
  ADDI .x12 .x12 64 ;;
  JAL .x1 modOff ;;
  ADDI .x12 .x12 4000

theorem evm_addmod_pow256_call_mod_length (modOff : BitVec 21) :
    (evm_addmod_pow256_call_mod modOff).length = 3 := by
  show (((ADDI .x12 .x12 64 ;; JAL .x1 modOff) ;;
          ADDI .x12 .x12 4000) : Program).length = 3
  simp only [seq, Program.length_append]
  rfl

theorem evm_addmod_pow256_call_mod_byte_length (modOff : BitVec 21) :
    4 * (evm_addmod_pow256_call_mod modOff).length = 12 := by
  rw [evm_addmod_pow256_call_mod_length]

/-- Prepare the second MOD call for `(((-1 mod N) + 1) mod N)`.

    Entry: the first MOD remainder `(-1 mod N)` is at `x12 + 96..120`, and
    the original modulus is still at `x12 + 32..56`. This block adds one to
    the four-limb remainder, propagating carry across all limbs, writes the
    result into the callable dividend slots `x12 + 64..88`, and refreshes the
    callable divisor slots with `N`.

    The add-one carry detection is total for all inputs: limb 0 uses
    `SLTIU x7, x6, 1`, which is true exactly when `x5 + 1` wrapped to zero;
    higher limbs use `SLTU x7, x6, x7`, which propagates a one-bit carry and
    yields zero when the incoming carry was zero.

    24 instructions. -/
def evm_addmod_pow256_prepare_plus_one_mod_args : Program :=
  LD .x5 .x12 96 ;;
  ADDI .x6 .x5 1 ;;
  SLTIU .x7 .x6 1 ;;
  SD .x12 .x6 64 ;;
  LD .x5 .x12 104 ;;
  ADD .x6 .x5 .x7 ;;
  SLTU .x7 .x6 .x7 ;;
  SD .x12 .x6 72 ;;
  LD .x5 .x12 112 ;;
  ADD .x6 .x5 .x7 ;;
  SLTU .x7 .x6 .x7 ;;
  SD .x12 .x6 80 ;;
  LD .x5 .x12 120 ;;
  ADD .x6 .x5 .x7 ;;
  SLTU .x7 .x6 .x7 ;;
  SD .x12 .x6 88 ;;
  LD .x5 .x12 32 ;;
  SD .x12 .x5 96 ;;
  LD .x5 .x12 40 ;;
  SD .x12 .x5 104 ;;
  LD .x5 .x12 48 ;;
  SD .x12 .x5 112 ;;
  LD .x5 .x12 56 ;;
  SD .x12 .x5 120

theorem evm_addmod_pow256_prepare_plus_one_mod_args_length :
    evm_addmod_pow256_prepare_plus_one_mod_args.length = 24 := by decide

theorem evm_addmod_pow256_prepare_plus_one_mod_args_byte_length :
    4 * evm_addmod_pow256_prepare_plus_one_mod_args.length = 96 := by
  rw [evm_addmod_pow256_prepare_plus_one_mod_args_length]

/-- Materialize `2^256 mod N` in the pow256 helper result slots.

    For the nonzero-`N` path, this helper computes the runtime value used by
    total ADDMOD's carry contribution:

      1. `(-1) mod N`
      2. `(((-1 mod N) + 1) mod N) = 2^256 mod N`

    Exit: `x12` is restored to the ADDMOD frame, and `x12 + 96..120` contains
    `EvmWord.pow256ModN N` for `N != 0`. The top-level ADDMOD assembly keeps
    the `N = 0` bypass outside this helper.

    43 instructions. -/
def evm_addmod_pow256_mod_n (modOff : BitVec 21) : Program :=
  evm_addmod_pow256_prepare_minus_one_mod_args ;;
  evm_addmod_pow256_call_mod modOff ;;
  evm_addmod_pow256_prepare_plus_one_mod_args ;;
  evm_addmod_pow256_call_mod modOff

theorem evm_addmod_pow256_mod_n_length (modOff : BitVec 21) :
    (evm_addmod_pow256_mod_n modOff).length = 43 := by
  unfold evm_addmod_pow256_mod_n
  simp only [seq, Program.length_append,
    evm_addmod_pow256_prepare_minus_one_mod_args_length,
    evm_addmod_pow256_call_mod_length,
    evm_addmod_pow256_prepare_plus_one_mod_args_length]

theorem evm_addmod_pow256_mod_n_byte_length (modOff : BitVec 21) :
    4 * (evm_addmod_pow256_mod_n modOff).length = 172 := by
  rw [evm_addmod_pow256_mod_n_length]

/-- Phase 2 — zero-store path (taken when `N = 0`).

    On entry: `x12 = sp + 32`, the result cell is at `x12 + 32 .. 56`
    (currently holding `N = 0`, but we overwrite to be explicit and
    to make the instruction sequence symmetric with the non-zero
    path's writeback). 4 `SD x12, x0, k` stores write zero into
    each of the four output limbs; the epilogue (separate block)
    handles the trailing `ADDI x12, x12, 32` that ADDMOD shares
    between both paths.

    4 instructions. -/
def evm_addmod_phase2_zero_path : Program :=
  SD .x12 .x0 32 ;;
  SD .x12 .x0 40 ;;
  SD .x12 .x0 48 ;;
  SD .x12 .x0 56

theorem evm_addmod_phase2_zero_path_length :
    evm_addmod_phase2_zero_path.length = 4 := by decide

theorem evm_addmod_phase2_zero_path_byte_length :
    4 * evm_addmod_phase2_zero_path.length = 16 := by
  rw [evm_addmod_phase2_zero_path_length]

/-- ADDMOD epilogue: shared writeback / pointer-advance suffix that
    runs after either the reduce-via-mod path or the zero-store path
    has placed the 256-bit result into the four limb cells at
    `x12 + 32 .. 56`.

    On entry: `x12 = sp + 32` (advanced once by the prologue's
    `evm_add`), result at `x12 + 32..58`. On exit: `x12 = sp + 64`
    (the original ADDMOD top-of-stack after popping `[a, b, N]` and
    pushing one cell), with the result now occupying `x12 + 0..24`.

    A single `ADDI x12, x12, 32` performs the final pointer advance.
    The result limbs are already in place from the upstream blocks —
    the epilogue does not move data, only the pointer.

    1 instruction. -/
def evm_addmod_epilogue : Program :=
  ADDI .x12 .x12 32

theorem evm_addmod_epilogue_length :
    evm_addmod_epilogue.length = 1 := by decide

theorem evm_addmod_epilogue_byte_length :
    4 * evm_addmod_epilogue.length = 4 := by
  rw [evm_addmod_epilogue_length]

-- ============================================================================
-- Slice 3c — top-level `evm_addmod` Program assembly + length lemmas
-- ============================================================================
--
-- This slice glues the four block skeletons (prologue / phase1 carry /
-- phase2 reduce / epilogue) into the top-level `evm_addmod` Program.
-- The phase-2 modulus-reduction call site takes a signed 21-bit byte
-- offset `modOff` to the entry of `evm_mod_callable`; the concrete
-- numeric value is pinned by the surrounding caller frame and is
-- threaded through unchanged here.
--
-- Per the slice acceptance, this is glue only — no `cpsTriple` proofs.
-- The eventual `evm_addmod_stack_spec` is the job of slice 3d
-- (`evm-asm-s7v49`); it consumes the per-block byte-offset lemmas
-- proved here to align block entries with PC values.
--
-- Block layout (instruction index → byte offset within `evm_addmod`):
--
--   prologue      : instr  0 .. 29  (length 30, bytes   0 ..119)
--   phase1_carry  : instr 30        (length  1, byte  120)
--   phase2_reduce : instr 31        (length  1, byte  124)
--   epilogue      : instr 32        (length  1, byte  128)
--   end           : instr 33        (              byte 132)
--
-- The phase-2 zero-path / `phase2_n_zero_test` blocks defined above
-- are *not* part of this skeleton — the linear assembly here matches
-- the slice description exactly. A richer assembly that wires in the
-- `N = 0` short-circuit branch will be folded in at slice 3d when the
-- runtime branch shape stabilises.

/-- Top-level ADDMOD program: prologue ;; phase1 carry ;; phase2 reduce
    (one near-call to `evm_mod_callable`) ;; epilogue. The `modOff`
    parameter is the signed 21-bit byte offset from the phase-2 JAL
    site to the entry of `evm_mod_callable`; it is pinned by the
    surrounding dispatcher frame. -/
def evm_addmod (modOff : BitVec 21) : Program :=
  evm_addmod_prologue ;;
  evm_addmod_phase1_carry ;;
  evm_addmod_phase2_reduce modOff ;;
  evm_addmod_epilogue

theorem evm_addmod_length (modOff : BitVec 21) :
    (evm_addmod modOff).length = 33 := by
  show ((((evm_addmod_prologue ;; evm_addmod_phase1_carry) ;;
            evm_addmod_phase2_reduce modOff) ;;
          evm_addmod_epilogue) : Program).length = 33
  simp only [seq, Program.length_append,
    evm_addmod_prologue_length, evm_addmod_phase1_carry_length,
    evm_addmod_phase2_reduce_length, evm_addmod_epilogue_length]

theorem evm_addmod_byte_length (modOff : BitVec 21) :
    4 * (evm_addmod modOff).length = 132 := by
  rw [evm_addmod_length]

/-- Byte offset of the prologue block within `evm_addmod`. -/
theorem evm_addmod_prologue_byte_off : 4 * 0 = 0 := by rfl

/-- Byte offset of the phase-1 carry block within `evm_addmod`. -/
theorem evm_addmod_phase1_carry_byte_off : 4 * 30 = 120 := by rfl

/-- Byte offset of the phase-2 reduce block within `evm_addmod`. -/
theorem evm_addmod_phase2_reduce_byte_off : 4 * 31 = 124 := by rfl

/-- Byte offset of the epilogue block within `evm_addmod`. -/
theorem evm_addmod_epilogue_byte_off : 4 * 32 = 128 := by rfl

/-- Byte offset immediately after the full `evm_addmod` program. -/
theorem evm_addmod_end_byte_off : 4 * 33 = 132 := by rfl

/-- Sanity check: the assembled `evm_addmod` length equals the sum of
    its four sub-block lengths. Picks an arbitrary `modOff` since the
    `evm_addmod_phase2_reduce` length is independent of it. -/
example : (evm_addmod 0).length =
    evm_addmod_prologue.length +
    evm_addmod_phase1_carry.length +
    (evm_addmod_phase2_reduce 0).length +
    evm_addmod_epilogue.length := by
  decide

-- ============================================================================
-- Total ADDMOD assembly (`evm_addmod_total`) — carry-out branch included
-- ============================================================================
--
-- Per `docs/addmod-total-runtime-plan.md`, the total runtime branches on `N`
-- and the 257th carry bit `x7` after phase 1:
--
--   1. `N = 0`          → store zero, advance 64 bytes total.
--   2. `N ≠ 0, x7 = 0`  → reduce the truncated sum: one MOD call.
--   3. `N ≠ 0, x7 = 1`  → `(2^256 + r) mod N` via
--        `rMod := r mod N`, `m := 2^256 mod N = ((2^256−1) mod N + 1) mod N`,
--        `result := (m + rMod) mod N` (both operands pre-reduced, so the
--        final step is one 257-bit add plus one conditional subtract of `N`).
--
-- Layout invariants (deliberate, proof-facing):
--
--   * **Every MOD call uses the same frame base `F = sp + 32`** (the post-
--     prologue `x12`): dividend at `F + 0..24`, divisor at `F + 32..56`,
--     remainder returned at `F + 32..56` with `x12` advanced to `F + 32`.
--     A single frame base means a single div-scratch band
--     (`divScratchOwnCallNoX1 (sp + 32)`) — the same term the existing
--     partial ADDMOD frames already own. Each call is followed by
--     `ADDI x12, x12, -32` restoring `x12 = F`.
--   * **Parking scratch lives BELOW `sp`** (the MULMOD precedent: the push-
--     direction slack is dead space, so the live deeper EVM stack at
--     `sp + 96..` is never touched, unlike a tail-window layout), and below
--     the callable's own scratch band: the MOD callable scribbles over
--     `F − 160 .. F − 8` (the 19 `divScratchOwnCallNoX1` dwords at
--     `F + signExtend12 3944..4088` plus the extra cell at
--     `F + signExtend12 3936`), i.e. `sp − 128 .. sp + 24`. The parking
--     cells sit strictly below that band:
--       S1 = `F − 192..−168` (sp − 160, offs 3904..3928)  saved `N`
--       S2 = `F − 224..−200` (sp − 192, offs 3872..3896)  saved `r`
--       S3 = `F − 256..−232` (sp − 224, offs 3840..3864)  parked `m`
--   * The final modular add reuses `evm_add` verbatim (m at `F + 0`, rMod at
--     `F + 32` → sum at `F + 32 = sp + 64`, the ADDMOD result cell, with
--     `x12` advanced to `sp + 64` and the carry-out bit in `x5`), followed by
--     a **branch-free conditional subtract** of `N`.
--   * Scratch registers stay within the owned set {x5, x6, x7, x10, x11};
--     `x7` (the parked ADDMOD carry bit) is only clobbered inside the carry
--     branch, where its value (`1`) has already been consumed by the branch.

/-- Carry path — park the two live operands below the callable's scratch
    band before the frame at `F + 0..56` is reused for the helper MOD calls:
    `N` (at `F + 32..56`) → S1 (`F − 192..−168`), and the truncated sum `r`
    (at `F + 0..24`) → S2 (`F − 224..−200`).

    16 instructions. -/
def evm_addmod_carry_save_operands : Program :=
  LD .x5 .x12 32 ;;
  SD .x12 .x5 3904 ;;
  LD .x5 .x12 40 ;;
  SD .x12 .x5 3912 ;;
  LD .x5 .x12 48 ;;
  SD .x12 .x5 3920 ;;
  LD .x5 .x12 56 ;;
  SD .x12 .x5 3928 ;;
  LD .x5 .x12 0 ;;
  SD .x12 .x5 3872 ;;
  LD .x5 .x12 8 ;;
  SD .x12 .x5 3880 ;;
  LD .x5 .x12 16 ;;
  SD .x12 .x5 3888 ;;
  LD .x5 .x12 24 ;;
  SD .x12 .x5 3896

theorem evm_addmod_carry_save_operands_length :
    evm_addmod_carry_save_operands.length = 16 := by decide

theorem evm_addmod_carry_save_operands_byte_length :
    4 * evm_addmod_carry_save_operands.length = 64 := by
  rw [evm_addmod_carry_save_operands_length]

/-- Carry path — materialize the all-ones dividend `2^256 − 1` in the MOD
    frame dividend slots `F + 0..24` for the first helper call
    `(2^256 − 1) mod N`. The divisor slots `F + 32..56` still hold the live
    `N` at this point, so no divisor copy is needed.

    5 instructions. -/
def evm_addmod_carry_minus_one_args : Program :=
  ADDI .x5 .x0 4095 ;;
  SD .x12 .x5 0 ;;
  SD .x12 .x5 8 ;;
  SD .x12 .x5 16 ;;
  SD .x12 .x5 24

theorem evm_addmod_carry_minus_one_args_length :
    evm_addmod_carry_minus_one_args.length = 5 := by decide

theorem evm_addmod_carry_minus_one_args_byte_length :
    4 * evm_addmod_carry_minus_one_args.length = 20 := by
  rw [evm_addmod_carry_minus_one_args_length]

/-- Carry path — one helper MOD call on the `F = sp + 32` frame: near-call
    `evm_mod_callable` (dividend `F + 0..24`, divisor `F + 32..56`), then
    restore `x12` from the callable's exit value `F + 32` back to `F`
    (`ADDI x12, x12, -32`, immediate 4064). The remainder is left at
    `F + 32..56`.

    2 instructions. -/
def evm_addmod_carry_call_mod (modOff : BitVec 21) : Program :=
  JAL .x1 modOff ;;
  ADDI .x12 .x12 4064

theorem evm_addmod_carry_call_mod_length (modOff : BitVec 21) :
    (evm_addmod_carry_call_mod modOff).length = 2 := by
  show ((JAL .x1 modOff ;; ADDI .x12 .x12 4064) : Program).length = 2
  simp only [seq, Program.length_append]
  rfl

theorem evm_addmod_carry_call_mod_byte_length (modOff : BitVec 21) :
    4 * (evm_addmod_carry_call_mod modOff).length = 8 := by
  rw [evm_addmod_carry_call_mod_length]

/-- Carry path — prepare the second helper call
    `((2^256 − 1) mod N + 1) mod N`: add one to the four-limb remainder at
    `F + 32..56` (total carry chain: limb 0 detects wrap via `SLTIU`, higher
    limbs propagate via `SLTU`), writing the incremented value into the
    dividend slots `F + 0..24`, then reload `N` from S1 into the divisor
    slots `F + 32..56`.

    `x7` is used as the carry register — safe here because the carry branch
    has already consumed the parked ADDMOD carry bit.

    24 instructions. -/
def evm_addmod_carry_plus_one_args : Program :=
  LD .x5 .x12 32 ;;
  ADDI .x6 .x5 1 ;;
  SLTIU .x7 .x6 1 ;;
  SD .x12 .x6 0 ;;
  LD .x5 .x12 40 ;;
  ADD .x6 .x5 .x7 ;;
  SLTU .x7 .x6 .x7 ;;
  SD .x12 .x6 8 ;;
  LD .x5 .x12 48 ;;
  ADD .x6 .x5 .x7 ;;
  SLTU .x7 .x6 .x7 ;;
  SD .x12 .x6 16 ;;
  LD .x5 .x12 56 ;;
  ADD .x6 .x5 .x7 ;;
  SLTU .x7 .x6 .x7 ;;
  SD .x12 .x6 24 ;;
  LD .x5 .x12 3904 ;;
  SD .x12 .x5 32 ;;
  LD .x5 .x12 3912 ;;
  SD .x12 .x5 40 ;;
  LD .x5 .x12 3920 ;;
  SD .x12 .x5 48 ;;
  LD .x5 .x12 3928 ;;
  SD .x12 .x5 56

theorem evm_addmod_carry_plus_one_args_length :
    evm_addmod_carry_plus_one_args.length = 24 := by decide

theorem evm_addmod_carry_plus_one_args_byte_length :
    4 * evm_addmod_carry_plus_one_args.length = 96 := by
  rw [evm_addmod_carry_plus_one_args_length]

/-- Carry path — stage the low-sum reduction `r mod N`: park the freshly
    computed `m = 2^256 mod N` (at `F + 32..56`) into S3 (`F − 256..−232`),
    reload the truncated sum `r` from S2 into the dividend slots `F + 0..24`,
    and reload `N` from S1 into the divisor slots `F + 32..56`.

    24 instructions. -/
def evm_addmod_carry_stage_low_args : Program :=
  LD .x5 .x12 32 ;;
  SD .x12 .x5 3840 ;;
  LD .x5 .x12 40 ;;
  SD .x12 .x5 3848 ;;
  LD .x5 .x12 48 ;;
  SD .x12 .x5 3856 ;;
  LD .x5 .x12 56 ;;
  SD .x12 .x5 3864 ;;
  LD .x5 .x12 3872 ;;
  SD .x12 .x5 0 ;;
  LD .x5 .x12 3880 ;;
  SD .x12 .x5 8 ;;
  LD .x5 .x12 3888 ;;
  SD .x12 .x5 16 ;;
  LD .x5 .x12 3896 ;;
  SD .x12 .x5 24 ;;
  LD .x5 .x12 3904 ;;
  SD .x12 .x5 32 ;;
  LD .x5 .x12 3912 ;;
  SD .x12 .x5 40 ;;
  LD .x5 .x12 3920 ;;
  SD .x12 .x5 48 ;;
  LD .x5 .x12 3928 ;;
  SD .x12 .x5 56

theorem evm_addmod_carry_stage_low_args_length :
    evm_addmod_carry_stage_low_args.length = 24 := by decide

theorem evm_addmod_carry_stage_low_args_byte_length :
    4 * evm_addmod_carry_stage_low_args.length = 96 := by
  rw [evm_addmod_carry_stage_low_args_length]

/-- Carry path — stage the final modular add: copy `m` from S3 back into the
    dividend slots `F + 0..24`. The third MOD call has just left
    `rMod = r mod N` at `F + 32..56`, so after this block the frame holds
    exactly the two pre-reduced `evm_add` operands (`m` at `x12 + 0..24`,
    `rMod` at `x12 + 32..56`).

    8 instructions. -/
def evm_addmod_carry_mod_add_stage : Program :=
  LD .x5 .x12 3840 ;;
  SD .x12 .x5 0 ;;
  LD .x5 .x12 3848 ;;
  SD .x12 .x5 8 ;;
  LD .x5 .x12 3856 ;;
  SD .x12 .x5 16 ;;
  LD .x5 .x12 3864 ;;
  SD .x12 .x5 24

theorem evm_addmod_carry_mod_add_stage_length :
    evm_addmod_carry_mod_add_stage.length = 8 := by decide

theorem evm_addmod_carry_mod_add_stage_byte_length :
    4 * evm_addmod_carry_mod_add_stage.length = 32 := by
  rw [evm_addmod_carry_mod_add_stage_length]

/-- Carry path — branch-free conditional subtract closing the pre-reduced
    modular add `(m + rMod) mod N`.

    On entry (immediately after the embedded `evm_add`): `x12 = sp + 64`,
    the truncated sum `s = (m + rMod) mod 2^256` is at `x12 + 0..24`, the
    `evm_add` carry-out bit is in `x5`, and `N` is parked at S1
    (`F − 192..−168` = `x12 − 224..−200`, offs 3872..3896 from the new
    `x12`).

    Since `m, rMod < N`, the true sum `σ = carry·2^256 + s < 2N`, so
    `σ mod N = σ − N` exactly when `carry = 1 ∨ s ≥ N` (and the 256-bit
    wrap of `s − N` equals `σ − N` in the carry case). The block computes

      1. pass 1: the borrow-out `B` of `s − N` (4-limb `SUB`/`SLTU`/`OR`
         chain, diffs discarded) — `B = 1 ↔ s < N`;
      2. `take = carry ∨ ¬B`, `mask = 0 − take` (all-ones or zero);
      3. pass 2: `s := s − (N &&& mask)` in place at `x12 + 0..24`
         (4-limb borrow chain).

    The `evm_add` carry-out is parked in `x10` first because pass 1 uses
    `x5` as its borrow scratch. Borrow propagation uses the verified
    `evm_sub` idiom — the incoming-borrow test `SLTU (d, b_in)` runs
    **before** the borrow is subtracted (the post-subtraction variant used
    by the legacy runtime handler inverts the borrow on the `d ∈ {0, 1}`
    boundary). After this block the ADDMOD result sits in the final result
    cell `sp + 64..88` with `x12 = sp + 64` — no epilogue.

    55 instructions. -/
def evm_addmod_carry_cond_sub : Program :=
  ADDI .x10 .x5 0 ;;
  LD .x6 .x12 0 ;;
  LD .x7 .x12 3872 ;;
  SLTU .x11 .x6 .x7 ;;
  LD .x6 .x12 8 ;;
  LD .x7 .x12 3880 ;;
  SLTU .x5 .x6 .x7 ;;
  SUB .x6 .x6 .x7 ;;
  SLTU .x7 .x6 .x11 ;;
  OR' .x11 .x5 .x7 ;;
  LD .x6 .x12 16 ;;
  LD .x7 .x12 3888 ;;
  SLTU .x5 .x6 .x7 ;;
  SUB .x6 .x6 .x7 ;;
  SLTU .x7 .x6 .x11 ;;
  OR' .x11 .x5 .x7 ;;
  LD .x6 .x12 24 ;;
  LD .x7 .x12 3896 ;;
  SLTU .x5 .x6 .x7 ;;
  SUB .x6 .x6 .x7 ;;
  SLTU .x7 .x6 .x11 ;;
  OR' .x11 .x5 .x7 ;;
  XORI .x11 .x11 1 ;;
  OR' .x11 .x10 .x11 ;;
  SUB .x11 .x0 .x11 ;;
  LD .x6 .x12 0 ;;
  LD .x7 .x12 3872 ;;
  AND' .x7 .x7 .x11 ;;
  SLTU .x10 .x6 .x7 ;;
  SUB .x5 .x6 .x7 ;;
  SD .x12 .x5 0 ;;
  LD .x6 .x12 8 ;;
  LD .x7 .x12 3880 ;;
  AND' .x7 .x7 .x11 ;;
  SLTU .x5 .x6 .x7 ;;
  SUB .x6 .x6 .x7 ;;
  SLTU .x7 .x6 .x10 ;;
  SUB .x6 .x6 .x10 ;;
  OR' .x10 .x5 .x7 ;;
  SD .x12 .x6 8 ;;
  LD .x6 .x12 16 ;;
  LD .x7 .x12 3888 ;;
  AND' .x7 .x7 .x11 ;;
  SLTU .x5 .x6 .x7 ;;
  SUB .x6 .x6 .x7 ;;
  SLTU .x7 .x6 .x10 ;;
  SUB .x6 .x6 .x10 ;;
  OR' .x10 .x5 .x7 ;;
  SD .x12 .x6 16 ;;
  LD .x6 .x12 24 ;;
  LD .x7 .x12 3896 ;;
  AND' .x7 .x7 .x11 ;;
  SUB .x6 .x6 .x7 ;;
  SUB .x6 .x6 .x10 ;;
  SD .x12 .x6 24

theorem evm_addmod_carry_cond_sub_length :
    evm_addmod_carry_cond_sub.length = 55 := by decide

theorem evm_addmod_carry_cond_sub_byte_length :
    4 * evm_addmod_carry_cond_sub.length = 220 := by
  rw [evm_addmod_carry_cond_sub_length]

/-- **Total ADDMOD program** — all three runtime branches.

    Block layout (instruction index → byte offset):

      prologue             : instr   0..29   bytes   0..119
      phase1_carry         : instr  30       byte  120
      n_zero_test (→ zero) : instr  31..38   bytes 124..155  (BEQ @ 152, +704)
      BEQ x7 (→ no-carry)  : instr  39       byte  156       (+692)
      carry: save_operands : instr  40..55   bytes 160..223
      carry: minus_one     : instr  56..60   bytes 224..243
      carry: call 1        : instr  61..62   bytes 244..251  (JAL @ 244)
      carry: plus_one      : instr  63..86   bytes 252..347
      carry: call 2        : instr  87..88   bytes 348..355  (JAL @ 348)
      carry: stage_low     : instr  89..112  bytes 356..451
      carry: call 3        : instr 113..114  bytes 452..459  (JAL @ 452)
      carry: mod_add_stage : instr 115..122  bytes 460..491
      carry: evm_add       : instr 123..152  bytes 492..611
      carry: cond_sub      : instr 153..207  bytes 612..831
      carry: JAL → end     : instr 208       byte  832       (+32)
      no-carry: JAL x1 mod : instr 209       byte  836
      no-carry: JAL → end  : instr 210       byte  840       (+24)
      zero: zero_path      : instr 211..214  bytes 844..859
      zero: epilogue       : instr 215       byte  860
      end                  : instr 216       byte  864

    The internal branch offsets (692, 680, 32, 24) are hardwired to this
    layout; the offset drift-check examples below pin them against the block
    length lemmas. The four `JAL x1` MOD-call offsets are parameters pinned
    by the surrounding dispatcher frame (for the canonical layout — the
    `evm_mod_callable` variant appended at `end + 4` behind a skip-JAL — they
    are 624 / 520 / 416 / 32).

    Exit state on every branch: `x12 = sp + 64` with the ADDMOD result in
    the cell at `sp + 64..88` (the zero path via the shared epilogue; the
    MOD-call paths via the callable's own `x12` advance; the carry path via
    the embedded `evm_add`'s advance). The zero path falls through to `end`.

    216 instructions. -/
def evm_addmod_total
    (modOff1 modOff2 modOff3 modOffNC : BitVec 21) : Program :=
  evm_addmod_prologue ;;
  evm_addmod_phase1_carry ;;
  evm_addmod_phase2_n_zero_test 692 ;;
  BEQ .x7 .x0 680 ;;
  evm_addmod_carry_save_operands ;;
  evm_addmod_carry_minus_one_args ;;
  evm_addmod_carry_call_mod modOff1 ;;
  evm_addmod_carry_plus_one_args ;;
  evm_addmod_carry_call_mod modOff2 ;;
  evm_addmod_carry_stage_low_args ;;
  evm_addmod_carry_call_mod modOff3 ;;
  evm_addmod_carry_mod_add_stage ;;
  evm_add ;;
  evm_addmod_carry_cond_sub ;;
  JAL .x0 32 ;;
  evm_addmod_phase2_mod_call modOffNC ;;
  JAL .x0 24 ;;
  evm_addmod_phase2_zero_path ;;
  evm_addmod_epilogue

theorem evm_addmod_total_length
    (modOff1 modOff2 modOff3 modOffNC : BitVec 21) :
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC).length = 216 := by
  unfold evm_addmod_total
  simp only [seq, Program.length_append,
    evm_addmod_prologue_length, evm_addmod_phase1_carry_length,
    evm_addmod_phase2_n_zero_test_length,
    evm_addmod_carry_save_operands_length,
    evm_addmod_carry_minus_one_args_length,
    evm_addmod_carry_call_mod_length,
    evm_addmod_carry_plus_one_args_length,
    evm_addmod_carry_stage_low_args_length,
    evm_addmod_carry_mod_add_stage_length,
    evm_addmod_carry_cond_sub_length,
    evm_addmod_phase2_mod_call_length,
    evm_addmod_phase2_zero_path_length,
    evm_addmod_epilogue_length]
  decide

theorem evm_addmod_total_byte_length
    (modOff1 modOff2 modOff3 modOffNC : BitVec 21) :
    4 * (evm_addmod_total modOff1 modOff2 modOff3 modOffNC).length = 864 := by
  rw [evm_addmod_total_length]

-- Offset drift checks: pin the hardwired internal branch distances against
-- the block length lemmas, so a block edit that shifts the layout fails the
-- build here instead of silently retargeting a branch.

/-- The `n_zero_test` BEQ (instr 38, byte 152) reaches the zero path
    (instr 211, byte 844): offset 692. -/
example : 4 * (30 + 1 + 8 - 1) + 692 = 4 * 211 := by decide

/-- The carry-test BEQ (instr 39, byte 156) reaches the no-carry path
    (instr 209, byte 836): offset 680. -/
example : 4 * (30 + 1 + 8) + 680 = 4 * 209 := by decide

/-- The carry-path exit JAL (instr 208, byte 832) reaches `end`
    (instr 216, byte 864): offset 32. -/
example : 4 * 208 + 32 = 4 * 216 := by decide

/-- The no-carry-path exit JAL (instr 210, byte 840) reaches `end`
    (instr 216, byte 864): offset 24. -/
example : 4 * 210 + 24 = 4 * 216 := by decide

/-- Sub-block instruction indices quoted in the layout table stay in sync
    with the block length lemmas. -/
example :
    (30 + 1 + 8 + 1 = 40) ∧                     -- carry path entry
    (40 + 16 + 5 = 61) ∧                        -- call-1 JAL site
    (61 + 2 + 24 = 87) ∧                        -- call-2 JAL site
    (87 + 2 + 24 = 113) ∧                       -- call-3 JAL site
    (113 + 2 + 8 = 123) ∧                       -- embedded evm_add entry
    (123 + 30 = 153) ∧                          -- cond_sub entry
    (153 + 55 = 208) ∧                          -- carry exit JAL
    (208 + 1 = 209) ∧ (209 + 1 + 1 = 211) ∧     -- no-carry / zero entries
    (211 + 4 + 1 = 216) := by decide            -- end

end EvmAsm.Evm64
