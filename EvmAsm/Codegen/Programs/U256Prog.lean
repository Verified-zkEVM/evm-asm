/-
  EvmAsm.Codegen.Programs.U256Prog

  LEAF of the U256 module split (GH #10753): the eleven `u256_*_prog`
  Programs parameterised over `GuestLayout` (`*_prog_of (L : GuestLayout)`)
  plus their emission views (`*Function`, `_eq_prog`, `#guard`s), the
  emission views applied at `.zero` (sound: emission is layout-independent
  and CHECKED, not assumed — see `EvmAsm/Codegen/GuestLayout.lean`).

  Deliberately does NOT import `GuestAddrs`; the concrete layout enters only
  through the bridge `EvmAsm.Codegen.Programs.U256`.
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestLayout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## u256_add_be -- PR-K51 modular addition on BE u256 buffers

    Compute `(a + b) mod 2^256` over two 32-byte big-endian
    `u256` buffers, storing the result in `out` and returning a
    0/1 overflow flag (`1` ⇔ unsigned overflow ⇔ `a + b >= 2^256`).

    BE storage convention: byte 0 = MSB, byte 31 = LSB. Mirrors
    the layout produced by `rlp_field_to_u256_be` and consumed by
    `u256_lt` (PR-K50).

    Building block for `tx_cost = max_fee_per_gas * gas_limit +
    value` in tx validation, and for any subsequent u256
    arithmetic helpers (`u256_sub_be`, `u256_mul_u64`).

    Calling convention:
      a0 (input)  : u256 a ptr (32 bytes, BE)
      a1 (input)  : u256 b ptr (32 bytes, BE)
      a2 (input)  : u256 out ptr (32 bytes, BE; may alias a or b)
      ra (input)  : return
      a0 (output) : 1 on overflow, 0 otherwise.

    Aliasing is safe: `out` may alias `a` or `b`. The
    byte-by-byte loop reads `a[i]` and `b[i]` before writing
    `out[i]` at each step. Pure register arithmetic, no scratch
    memory, leaf-callable. -/
def u256AddBe_prog_of (_L : GuestLayout) : Program :=
  [ .LI .x5 (31 : Word),
    .LI .x6 (0 : Word),
    .ADD .x7 .x10 .x5,
    .ADD .x28 .x11 .x5,
    .ADD .x29 .x12 .x5,
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .ADD .x30 .x30 .x31,
    .ADD .x30 .x30 .x6,
    .SRLI .x6 .x30 (8 : BitVec 6),
    .ANDI .x30 .x30 (255 : BitVec 12),
    .SB .x29 .x30 (0 : BitVec 12),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-48 : BitVec 21),
    .MV .x10 .x6,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def u256AddBeFunction : String :=
  "u256_add_be:\n" ++ emitProgram (u256AddBe_prog_of .zero)

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `u256AddBe_prog_of .zero` rendered under its label (layout-parameterised
    per GH #10753; emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). -/
theorem u256AddBeFunction_eq_prog :
    u256AddBeFunction = "u256_add_be:\n" ++ emitProgram (u256AddBe_prog_of .zero) := rfl

#guard u256AddBeFunction.startsWith "u256_add_be:\n"
#guard (u256AddBe_prog_of .zero).length = 17


/-! ## u256_lt_be -- PR-K160

    The missing companion to PR-K53 `u256_eq` and PR-K52
    `u256_sub_be`. Earlier helpers in the u256 family reference
    "PR-K50 `u256_lt`" in their doc-comments, but the function
    was never actually shipped; this PR finally pins the
    primitive into the registry.

    Compare two 32-byte big-endian u256 buffers and return the
    verdict `a < b` as a u64 (1 if strictly less, 0 otherwise).

    Pure byte-walk from MSB to LSB: on the first differing byte,
    return early based on the byte ordering; on full match,
    return 0. Constant-cycle on a per-buffer basis (no early
    exit) keeps the helper friendly to gas-cost modelling --
    but a typical caller wants the early-exit (cheaper); since
    this is a register-level helper we go with early exit.

    Use cases:
      * sender balance check (`account.balance >= cost`):
        `u256_lt_be(account_balance, cost, &is_less);
         assert is_less == 0`.
      * EVM LT/GT opcode dispatch (after sign-handling).
      * U256 min / max where K59 / K60's "pick smaller of two"
        callers explicitly call this primitive.

    Companion to:
      - PR-K53 `u256_eq`         -- equality
      - PR-K52 `u256_sub_be`     -- modular subtraction
      - PR-K59 `u256_min`        -- already does its own compare;
                                   could be refactored to use this

    Calling convention:
      a0 (input)  : a ptr (32 bytes, BE)
      a1 (input)  : b ptr (32 bytes, BE)
      a2 (input)  : u64 out ptr (1 if a < b, 0 otherwise)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def u256LtBe_prog_of (_L : GuestLayout) : Program :=
  [ .LI .x5 (32 : Word),
    .MV .x6 .x10,
    .MV .x7 .x11,
    .BEQ .x5 .x0 (52 : BitVec 13),
    .LBU .x28 .x6 (0 : BitVec 12),
    .LBU .x29 .x7 (0 : BitVec 12),
    .BLTU .x28 .x29 (24 : BitVec 13),
    .BLTU .x29 .x28 (36 : BitVec 13),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x30 (1 : Word),
    .SD .x12 .x30 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x12 .x0 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def u256LtBeFunction : String :=
  "u256_lt_be:\n" ++ emitProgram (u256LtBe_prog_of .zero)

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `u256LtBe_prog_of .zero` rendered under its label (layout-parameterised
    per GH #10753; emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). -/
theorem u256LtBeFunction_eq_prog :
    u256LtBeFunction = "u256_lt_be:\n" ++ emitProgram (u256LtBe_prog_of .zero) := rfl

#guard u256LtBeFunction.startsWith "u256_lt_be:\n"
#guard (u256LtBe_prog_of .zero).length = 19


/-! ## u256_sub_be -- PR-K52 modular subtraction on BE u256 buffers

    Compute `(a - b) mod 2^256` over two 32-byte big-endian
    `u256` buffers, storing the result in `out` and returning a
    0/1 borrow flag (`1` ⇔ unsigned underflow ⇔ `a < b`).

    Natural pair to PR-K51 `u256_add_be`. Direct use case:

      new_balance = u256_sub_be(account.balance, tx_cost)
      if borrow: reject tx (insufficient funds)

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : u256 a ptr (32 bytes, BE)
      a1 (input)  : u256 b ptr (32 bytes, BE)
      a2 (input)  : u256 out ptr (32 bytes, BE; may alias a or b)
      ra (input)  : return
      a0 (output) : 1 on underflow (a < b), 0 otherwise.

    Aliasing is safe: `out` may alias `a` or `b`. Pure register
    arithmetic, no scratch memory, leaf-callable. -/
def u256SubBe_prog_of (_L : GuestLayout) : Program :=
  [ .LI .x5 (31 : Word),
    .LI .x6 (0 : Word),
    .ADD .x7 .x10 .x5,
    .ADD .x28 .x11 .x5,
    .ADD .x29 .x12 .x5,
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .SUB .x30 .x30 .x31,
    .SUB .x30 .x30 .x6,
    .SLT .x6 .x30 .x0,
    .ANDI .x30 .x30 (255 : BitVec 12),
    .SB .x29 .x30 (0 : BitVec 12),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-48 : BitVec 21),
    .MV .x10 .x6,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def u256SubBeFunction : String :=
  "u256_sub_be:\n" ++ emitProgram (u256SubBe_prog_of .zero)

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `u256SubBe_prog_of .zero` rendered under its label (layout-parameterised
    per GH #10753; emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). -/
theorem u256SubBeFunction_eq_prog :
    u256SubBeFunction = "u256_sub_be:\n" ++ emitProgram (u256SubBe_prog_of .zero) := rfl

#guard u256SubBeFunction.startsWith "u256_sub_be:\n"
#guard (u256SubBe_prog_of .zero).length = 17


/-! ## u256_from_u64_be -- PR-K56 zero-extend u64 → BE u256 buffer

    Materialize a `u64` value as a 32-byte big-endian `u256`
    buffer by zero-extending. Lets callers feed small operands
    (`gas_limit`, `nonce`, `data_length`, etc.) into the u256
    arithmetic and comparison toolkit (`u256_add_be`,
    `u256_sub_be`, `u256_lt`, `u256_eq`, `u256_mul_u64_be`).

    BE storage convention: byte 0 = MSB, byte 31 = LSB. Output:
      bytes 0..24  = 0x00
      bytes 24..32 = u64 value in big-endian order

    Calling convention:
      a0 (input)  : u64 value (in register)
      a1 (input)  : u256 out ptr (32 bytes; will be fully written)
      ra (input)  : return

    Pure register arithmetic except for the 4 zero-stores + 8
    byte-stores; no scratch memory; leaf-callable. Uses RV64 `sb`
    semantics (stores low 8 bits of rs2), so no `andi 0xff`
    masking is needed before each byte write. -/
def u256FromU64Be_prog_of (_L : GuestLayout) : Program :=
  [ .SD .x11 .x0 (0 : BitVec 12),
    .SD .x11 .x0 (8 : BitVec 12),
    .SD .x11 .x0 (16 : BitVec 12),
    .SRLI .x5 .x10 (56 : BitVec 6),
    .SB .x11 .x5 (24 : BitVec 12),
    .SRLI .x5 .x10 (48 : BitVec 6),
    .SB .x11 .x5 (25 : BitVec 12),
    .SRLI .x5 .x10 (40 : BitVec 6),
    .SB .x11 .x5 (26 : BitVec 12),
    .SRLI .x5 .x10 (32 : BitVec 6),
    .SB .x11 .x5 (27 : BitVec 12),
    .SRLI .x5 .x10 (24 : BitVec 6),
    .SB .x11 .x5 (28 : BitVec 12),
    .SRLI .x5 .x10 (16 : BitVec 6),
    .SB .x11 .x5 (29 : BitVec 12),
    .SRLI .x5 .x10 (8 : BitVec 6),
    .SB .x11 .x5 (30 : BitVec 12),
    .SB .x11 .x10 (31 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def u256FromU64BeFunction : String :=
  "u256_from_u64_be:\n" ++ emitProgram (u256FromU64Be_prog_of .zero)

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `u256FromU64Be_prog_of .zero` rendered under its label (layout-parameterised
    per GH #10753; emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). -/
theorem u256FromU64BeFunction_eq_prog :
    u256FromU64BeFunction = "u256_from_u64_be:\n" ++ emitProgram (u256FromU64Be_prog_of .zero) := rfl

#guard u256FromU64BeFunction.startsWith "u256_from_u64_be:\n"
#guard (u256FromU64Be_prog_of .zero).length = 19


/-! ## u256_is_zero -- PR-K58 all-zero predicate on BE u256 buffers

    Test whether a 32-byte big-endian `u256` buffer encodes the
    value `0`. Returns `1` if all 32 bytes are zero, else `0`.

    Saves callers from keeping a 32-byte zero buffer around just
    to call `u256_eq` against it. Common pattern in tx
    validation:

      // Reject zero-value txs to a contract creation address
      if not u256_is_zero(tx.value) and tx.is_creation: ...

      // Skip the priority-fee credit if no surplus
      if u256_is_zero(priority_fee_after_cap): goto next

    BE storage convention: byte 0 = MSB, byte 31 = LSB. (For
    is-zero the endian doesn't matter — all-zero bytes mean
    value 0 either way — but kept consistent with the K50/K53
    convention.)

    Calling convention:
      a0 (input)  : u256 ptr (32 bytes)
      ra (input)  : return
      a0 (output) : 1 if all-zero, 0 otherwise.

    Pure register arithmetic: 4 ld + 3 or + 1 seqz. No
    short-circuit (we always read all 32 bytes), keeping
    timing data-independent for any future side-channel
    considerations. Leaf-callable. -/
def u256IsZero_prog_of (_L : GuestLayout) : Program :=
  [ .LD .x5 .x10 (0 : BitVec 12),
    .LD .x6 .x10 (8 : BitVec 12),
    .LD .x7 .x10 (16 : BitVec 12),
    .LD .x28 .x10 (24 : BitVec 12),
    .OR .x5 .x5 .x6,
    .OR .x5 .x5 .x7,
    .OR .x5 .x5 .x28,
    .SLTIU .x10 .x5 (1 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def u256IsZeroFunction : String :=
  "u256_is_zero:\n" ++ emitProgram (u256IsZero_prog_of .zero)

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `u256IsZero_prog_of .zero` rendered under its label (layout-parameterised
    per GH #10753; emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). -/
theorem u256IsZeroFunction_eq_prog :
    u256IsZeroFunction = "u256_is_zero:\n" ++ emitProgram (u256IsZero_prog_of .zero) := rfl

#guard u256IsZeroFunction.startsWith "u256_is_zero:\n"
#guard (u256IsZero_prog_of .zero).length = 9


/-! ## u256_min -- PR-K59 minimum of two BE u256 buffers

    Compare two 32-byte big-endian `u256` buffers and copy the
    smaller (or `a` on equality) into `out`. Standalone — does
    not call `u256_lt` (PR-K50); the byte-walk-and-pick logic
    is inlined to avoid the cross-PR dependency.

    Direct use case — EIP-1559 effective priority fee:

      surplus = u256_sub_be(tx.max_fee_per_gas, base_fee_per_gas)
      priority = u256_min(tx.max_priority_fee_per_gas, surplus)

    Per the Python `transaction_priority_fee_per_gas`:

      def priority_fee(tx, base_fee):
          if tx.type == 0:  # legacy
              return tx.gas_price - base_fee
          else:
              return min(tx.max_priority_fee_per_gas,
                         tx.max_fee_per_gas - base_fee)

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : u256 a ptr (32 bytes, BE)
      a1 (input)  : u256 b ptr (32 bytes, BE)
      a2 (input)  : u256 out ptr (may alias a or b)
      ra (input)  : return
      a0 (output) : 0 (the selected pointer is internally chosen).

    The byte-walk pass short-circuits on the first differing
    byte. Then a 4 × (ld + sd) chunk copy emits 32 bytes. Pure
    register arithmetic, no scratch memory, leaf-callable.

    Note on aliasing: if `out` aliases either input, the byte
    walk is read-only over both inputs, and the 4 × (ld + sd)
    copy reads each chunk from one of them and writes to `out`
    in the same step — fine since `ld` happens before `sd`. -/
def u256Min_prog_of (_L : GuestLayout) : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x31 (32 : Word),
    .BEQ .x5 .x31 (36 : BitVec 13),
    .ADD .x6 .x10 .x5,
    .ADD .x7 .x11 .x5,
    .LBU .x28 .x6 (0 : BitVec 12),
    .LBU .x29 .x7 (0 : BitVec 12),
    .BLTU .x28 .x29 (16 : BitVec 13),
    .BLTU .x29 .x28 (20 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .MV .x5 .x10,
    .JAL .x0 (8 : BitVec 21),
    .MV .x5 .x11,
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x12 .x6 (0 : BitVec 12),
    .LD .x6 .x5 (8 : BitVec 12),
    .SD .x12 .x6 (8 : BitVec 12),
    .LD .x6 .x5 (16 : BitVec 12),
    .SD .x12 .x6 (16 : BitVec 12),
    .LD .x6 .x5 (24 : BitVec 12),
    .SD .x12 .x6 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def u256MinFunction : String :=
  "u256_min:\n" ++ emitProgram (u256Min_prog_of .zero)

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `u256Min_prog_of .zero` rendered under its label (layout-parameterised
    per GH #10753; emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). -/
theorem u256MinFunction_eq_prog :
    u256MinFunction = "u256_min:\n" ++ emitProgram (u256Min_prog_of .zero) := rfl

#guard u256MinFunction.startsWith "u256_min:\n"
#guard (u256Min_prog_of .zero).length = 24


/-! ## u256_max -- PR-K60 maximum of two BE u256 buffers

    Direct companion to PR-K59 `u256_min`. Compares two 32-byte
    big-endian `u256` buffers and copies the larger (or `a` on
    equality) into `out`. Same byte-walk + inline pick logic as
    `u256_min` with inverted selection; no separate `u256_lt`
    dependency.

    Direct use case — EIP-1559 base-fee delta floor:

      base_fee_delta = u256_max(target_fee_delta_div_8,
                                u256_from_u64(1))

    (Per Python `calculate_base_fee_per_gas`'s `max(..., 1)`
    when parent.gas_used > parent_gas_target.)

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : u256 a ptr (32 bytes, BE)
      a1 (input)  : u256 b ptr (32 bytes, BE)
      a2 (input)  : u256 out ptr (may alias a or b)
      ra (input)  : return
      a0 (output) : 0.

    Short-circuits on the first differing byte. Pure register
    arithmetic + 4 × (ld + sd) chunk copy. Leaf-callable.
    Aliasing safe. -/
def u256Max_prog_of (_L : GuestLayout) : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x31 (32 : Word),
    .BEQ .x5 .x31 (36 : BitVec 13),
    .ADD .x6 .x10 .x5,
    .ADD .x7 .x11 .x5,
    .LBU .x28 .x6 (0 : BitVec 12),
    .LBU .x29 .x7 (0 : BitVec 12),
    .BLTU .x29 .x28 (16 : BitVec 13),
    .BLTU .x28 .x29 (20 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .MV .x5 .x10,
    .JAL .x0 (8 : BitVec 21),
    .MV .x5 .x11,
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x12 .x6 (0 : BitVec 12),
    .LD .x6 .x5 (8 : BitVec 12),
    .SD .x12 .x6 (8 : BitVec 12),
    .LD .x6 .x5 (16 : BitVec 12),
    .SD .x12 .x6 (16 : BitVec 12),
    .LD .x6 .x5 (24 : BitVec 12),
    .SD .x12 .x6 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def u256MaxFunction : String :=
  "u256_max:\n" ++ emitProgram (u256Max_prog_of .zero)

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `u256Max_prog_of .zero` rendered under its label (layout-parameterised
    per GH #10753; emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). -/
theorem u256MaxFunction_eq_prog :
    u256MaxFunction = "u256_max:\n" ++ emitProgram (u256Max_prog_of .zero) := rfl

#guard u256MaxFunction.startsWith "u256_max:\n"
#guard (u256Max_prog_of .zero).length = 24


/-! ## u256_div_u64_be -- PR-K61 u256 / u64 byte-by-byte long division

    Compute `(quotient, remainder)` where
    `src = quotient * b + remainder` with `0 <= remainder < b`.
    Stores the 32-byte BE quotient at `out` and returns the
    u64 remainder.

    Direct use case — EIP-1559 base-fee formula:

      parent_gas_target  = parent.gas_limit / 2   (b = 2)
      target_fee_delta   = parent_fee_gas_delta / parent_gas_target  (b ≤ 2^30)
      base_fee_per_gas_delta = target_fee_delta / BASE_FEE_MAX_CHANGE_DENOMINATOR  (b = 8)

    All three divisors fit far inside the safe range.

    ## Precondition: divisor ≤ 2^56

    The byte-by-byte algorithm maintains `carry < b` across
    iterations. Each step computes `num = (carry << 8) | a[i]`.
    For `num` to fit in `u64` we need `carry << 8 < 2^64`, i.e.
    `carry < 2^56`. Since `carry < b`, this is satisfied iff
    `b ≤ 2^56`. The function does NOT check this precondition;
    passing `b > 2^56` produces garbage but no crash.

    The precondition still admits a 56-bit divisor (≈ `7.2e16`),
    which covers every Ethereum-state-related divisor:

      - Gas limits / targets:  < 2^30
      - EIP-1559 denominator:  = 8
      - Withdrawal counts:     < 2^32
      - Per-block tx counts:   < 2^20

    For larger divisors, a future PR can ship a bit-by-bit
    long-division helper supporting `b ≤ 2^63`.

    Also: caller must pass `b > 0`. Passing `b == 0` invokes
    RV64's `divu`-by-zero behavior (quotient = all-1s, remainder
    = dividend) — not a crash, but the output is meaningless.

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : u256 src ptr (32 bytes, BE)
      a1 (input)  : u64 b (0 < b ≤ 2^56)
      a2 (input)  : u256 out ptr (32 bytes, BE; may alias src)
      ra (input)  : return
      a0 (output) : u64 remainder.

    Aliasing safe: each iteration reads `src[i]` then writes
    `out[i]`; subsequent iterations advance to `src[i+1]`. -/
def u256DivU64Be_prog_of (_L : GuestLayout) : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x6 (0 : Word),
    .LI .x7 (32 : Word),
    .BEQ .x6 .x7 (44 : BitVec 13),
    .ADD .x28 .x10 .x6,
    .LBU .x29 .x28 (0 : BitVec 12),
    .SLLI .x30 .x5 (8 : BitVec 6),
    .OR .x30 .x30 .x29,
    .DIVU .x31 .x30 .x11,
    .REMU .x5 .x30 .x11,
    .ADD .x28 .x12 .x6,
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-44 : BitVec 21),
    .MV .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def u256DivU64BeFunction : String :=
  "u256_div_u64_be:\n" ++ emitProgram (u256DivU64Be_prog_of .zero)

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `u256DivU64Be_prog_of .zero` rendered under its label (layout-parameterised
    per GH #10753; emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). -/
theorem u256DivU64BeFunction_eq_prog :
    u256DivU64BeFunction = "u256_div_u64_be:\n" ++ emitProgram (u256DivU64Be_prog_of .zero) := rfl

#guard u256DivU64BeFunction.startsWith "u256_div_u64_be:\n"
#guard (u256DivU64Be_prog_of .zero).length = 16


/-! ## u256_eq -- PR-K53 equality companion to PR-K50 u256_lt

    Equality predicate on two 32-byte big-endian `u256` buffers.
    Returns `1` if `a == b`, else `0`. Pair to PR-K50 `u256_lt`
    so callers can express `a >= b` as `!u256_lt(a, b)` plus
    optionally `u256_eq` for equality discrimination, or `a > b`
    as `u256_lt(b, a)`, etc.

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : u256 a ptr (32 bytes, BE)
      a1 (input)  : u256 b ptr (32 bytes, BE)
      ra (input)  : return
      a0 (output) : 1 if a == b, 0 otherwise.

    Pure register arithmetic, no scratch memory, leaf-callable.
    Walks at most 32 bytes; short-circuits on the first
    differing byte. -/
def u256Eq_prog_of (_L : GuestLayout) : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x31 (32 : Word),
    .BEQ .x5 .x31 (32 : BitVec 13),
    .ADD .x6 .x10 .x5,
    .ADD .x7 .x11 .x5,
    .LBU .x28 .x6 (0 : BitVec 12),
    .LBU .x29 .x7 (0 : BitVec 12),
    .BNE .x28 .x29 (20 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def u256EqFunction : String :=
  "u256_eq:\n" ++ emitProgram (u256Eq_prog_of .zero)

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `u256Eq_prog_of .zero` rendered under its label (layout-parameterised
    per GH #10753; emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). -/
theorem u256EqFunction_eq_prog :
    u256EqFunction = "u256_eq:\n" ++ emitProgram (u256Eq_prog_of .zero) := rfl

#guard u256EqFunction.startsWith "u256_eq:\n"
#guard (u256Eq_prog_of .zero).length = 14


/-! ## u256_mul_u64_be -- PR-K54 u256 × u64 schoolbook multiply

    Compute `(a * b) mod 2^256` where `a` is a 32-byte big-endian
    `u256` buffer and `b` is a u64 scalar. Stores the low 256 bits
    of the product in `out` (BE) and returns a 0/1 overflow flag.

    Direct use case: `tx_cost = max_fee_per_gas * gas_limit` in
    tx validation (then `+ value` via PR-K51 `u256_add_be`).

    Algorithm: byte-by-byte schoolbook over the u256 operand,
    avoiding any BE↔u64 conversion of `a`. For each byte
    `a[31-p]` (p in 0..31, LSB first):

      1. partial = a[31-p] * b  (u72; mul + mulhu)
      2. add `partial` to an LSB-first 40-byte accumulator at
         byte offset `p`, with carry propagation
      3. After all 32 bytes, accumulator[0..32] = low 256 bits
         (LSB first), accumulator[32..40] holds the high 64 bits

    Final output:
      out[i]   = accumulator[31 - i]  for i in 0..32  (BE)
      overflow = (accumulator[32..40] != 0)

    The accumulator lives in `.data` (`u256m_acc`, 40 bytes), so
    this function is NOT reentrant.

    Calling convention:
      a0 (input)  : u256 a ptr (32 bytes, BE)
      a1 (input)  : u64 b (scalar, in register)
      a2 (input)  : u256 out ptr (32 bytes, BE; out may alias a;
                    must NOT alias `u256m_acc`)
      ra (input)  : return
      a0 (output) : 1 on overflow (a * b >= 2^256), 0 otherwise.

    Uses 40 bytes of `.data` scratch (`u256m_acc`). -/
def u256MulU64Be_prog_of (L : GuestLayout) : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x19 (laHi L.u256m_acc (L.u256_mul_u64_be + 40)),
    .ADDI .x19 .x19 (laLo L.u256m_acc (L.u256_mul_u64_be + 40)),
    .MV .x5 .x19,
    .LI .x6 (5 : Word),
    .BEQ .x6 .x0 (20 : BitVec 13),
    .SD .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .LI .x20 (0 : Word),
    .LI .x5 (32 : Word),
    .BEQ .x20 .x5 (156 : BitVec 13),
    .LI .x5 (31 : Word),
    .SUB .x5 .x5 .x20,
    .ADD .x5 .x8 .x5,
    .LBU .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (128 : BitVec 13),
    .MUL .x6 .x5 .x9,
    .MULHU .x7 .x5 .x9,
    .ADD .x28 .x19 .x20,
    .LI .x29 (8 : Word),
    .LI .x30 (0 : Word),
    .LBU .x31 .x28 (0 : BitVec 12),
    .ANDI .x13 .x6 (255 : BitVec 12),
    .ADD .x31 .x31 .x13,
    .ADD .x31 .x31 .x30,
    .ANDI .x13 .x31 (255 : BitVec 12),
    .SB .x28 .x13 (0 : BitVec 12),
    .SRLI .x30 .x31 (8 : BitVec 6),
    .SRLI .x6 .x6 (8 : BitVec 6),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .BNE .x29 .x0 (-40 : BitVec 13),
    .LBU .x31 .x28 (0 : BitVec 12),
    .ADD .x31 .x31 .x7,
    .ADD .x31 .x31 .x30,
    .ANDI .x13 .x31 (255 : BitVec 12),
    .SB .x28 .x13 (0 : BitVec 12),
    .SRLI .x30 .x31 (8 : BitVec 6),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .BEQ .x30 .x0 (32 : BitVec 13),
    .LBU .x31 .x28 (0 : BitVec 12),
    .ADD .x31 .x31 .x30,
    .ANDI .x13 .x31 (255 : BitVec 12),
    .SB .x28 .x13 (0 : BitVec 12),
    .SRLI .x30 .x31 (8 : BitVec 6),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-156 : BitVec 21),
    .MV .x5 .x19,
    .ADDI .x6 .x18 (32 : BitVec 12),
    .LI .x7 (32 : Word),
    .BEQ .x7 .x0 (28 : BitVec 13),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x6 (8 : Word),
    .LI .x10 (0 : Word),
    .BEQ .x6 .x0 (32 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .BEQ .x28 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (16 : BitVec 21),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `u256MulU64Be_prog_of`: the `la`/cross-`jal` instruction
    indices kept SYMBOLIC in the emitted image text (`emitProgramR`), while
    the Program above carries the layout-parameterised immediates
    (`laHi`/`laLo`/`jalOff L.…`) for verification. -/
def u256MulU64Be_relocs : RelocTable :=
  [ (10, .la .x19 "u256m_acc") ]

def u256MulU64BeFunction : String :=
  "u256_mul_u64_be:\n" ++ emitProgramR (u256MulU64Be_prog_of .zero) u256MulU64Be_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `u256MulU64Be_prog_of .zero` rendered under its label with the
    `la`/`jal` relocs kept symbolic (layout-parameterised per GH #10753;
    emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp
    over the bridge's `u256MulU64Be_prog` (`_of guestLayout`). -/
theorem u256MulU64BeFunction_eq_prog :
    u256MulU64BeFunction = "u256_mul_u64_be:\n" ++ emitProgramR (u256MulU64Be_prog_of .zero) u256MulU64Be_relocs := rfl

#guard u256MulU64BeFunction.startsWith "u256_mul_u64_be:\n"
#guard (u256MulU64Be_prog_of .zero).length = 88


/-! ## u256_to_u64_be -- PR-K57 truncate BE u256 → u64 with overflow flag

    Truncate a 32-byte big-endian `u256` buffer down to its
    low 64 bits, storing them at `*out`. Returns a 0/1 overflow
    flag: `1` if any of the high 192 bits are nonzero, `0`
    otherwise.

    Natural inverse of PR-K56 `u256_from_u64_be`. Together they
    let callers move values between the u256 BE byte-buffer
    representation and the u64 register-resident form.

    Direct use cases:
      - `gas_left = u256_to_u64_be(account.balance / gas_price)`
      - Tx validation: check `intrinsic_gas <= tx.gas_limit`
        after computing intrinsic gas as a u64
      - Compact a small u256 result for further u64-domain work

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : u256 src ptr (32 bytes, BE)
      a1 (input)  : u64 out ptr
      ra (input)  : return
      a0 (output) : 1 on overflow (high 192 bits nonzero), 0 otherwise.

    Pure register arithmetic, no scratch memory, leaf-callable.
    Always writes the low-64-bit value to `*out`, even on
    overflow (so callers don't need to branch on the flag to
    read a defined value). -/
def u256ToU64Be_prog_of (_L : GuestLayout) : Program :=
  [ .LD .x5 .x10 (0 : BitVec 12),
    .LD .x6 .x10 (8 : BitVec 12),
    .LD .x7 .x10 (16 : BitVec 12),
    .OR .x5 .x5 .x6,
    .OR .x5 .x5 .x7,
    .LBU .x6 .x10 (24 : BitVec 12),
    .SLLI .x6 .x6 (56 : BitVec 6),
    .LBU .x7 .x10 (25 : BitVec 12),
    .SLLI .x7 .x7 (48 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x10 (26 : BitVec 12),
    .SLLI .x7 .x7 (40 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x10 (27 : BitVec 12),
    .SLLI .x7 .x7 (32 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x10 (28 : BitVec 12),
    .SLLI .x7 .x7 (24 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x10 (29 : BitVec 12),
    .SLLI .x7 .x7 (16 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x10 (30 : BitVec 12),
    .SLLI .x7 .x7 (8 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x10 (31 : BitVec 12),
    .OR .x6 .x6 .x7,
    .SD .x11 .x6 (0 : BitVec 12),
    .SLTU .x10 .x0 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def u256ToU64BeFunction : String :=
  "u256_to_u64_be:\n" ++ emitProgram (u256ToU64Be_prog_of .zero)

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `u256ToU64Be_prog_of .zero` rendered under its label (layout-parameterised
    per GH #10753; emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). -/
theorem u256ToU64BeFunction_eq_prog :
    u256ToU64BeFunction = "u256_to_u64_be:\n" ++ emitProgram (u256ToU64Be_prog_of .zero) := rfl

#guard u256ToU64BeFunction.startsWith "u256_to_u64_be:\n"
#guard (u256ToU64Be_prog_of .zero).length = 30

end EvmAsm.Codegen
