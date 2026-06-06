/-
  EvmAsm.Codegen.Programs.U256

  U256-BE arithmetic / comparison helpers lifted out
  of `EvmAsm.Codegen.Programs.Tx` per the file-size hard cap.

  Atomic primitives:
    K51 u256_add_be
    K52 u256_sub_be
    K53 u256_eq
    K54 u256_mul_u64_be
    K56 u256_from_u64_be
    K57 u256_to_u64_be
    K58 u256_is_zero
    K59 u256_min
    K60 u256_max
    K61 u256_div_u64_be
    K160 u256_lt_be

  Lives standalone so Tx / Header / Block / Mpt consumers can
  import the u256 arithmetic family without pulling the full Tx module.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

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
def u256AddBeFunction : String :=
  "u256_add_be:\n" ++
  "  li t0, 31                  # byte index (LSB first)\n" ++
  "  li t1, 0                   # carry\n" ++
  ".Lu256a_loop:\n" ++
  "  add t2, a0, t0\n" ++
  "  add t3, a1, t0\n" ++
  "  add t4, a2, t0\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  add t5, t5, t6\n" ++
  "  add t5, t5, t1             # + carry-in\n" ++
  "  srli t1, t5, 8             # carry-out\n" ++
  "  andi t5, t5, 0xff          # masked sum byte\n" ++
  "  sb t5, 0(t4)\n" ++
  "  beqz t0, .Lu256a_done\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lu256a_loop\n" ++
  ".Lu256a_done:\n" ++
  "  mv a0, t1                  # final carry = overflow flag\n" ++
  "  ret"

/-- `zisk_u256_add_be`: probe BuildUnit. Reads (32B a, 32B b) from
    host input, writes (overflow_flag, 32B result) to OUTPUT (40
    bytes total). -/
def ziskU256AddBePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # a ptr\n" ++
  "  addi a1, a3, 40             # b ptr\n" ++
  "  li a2, 0xa0010008           # out ptr at OUTPUT + 8\n" ++
  "  # Pre-zero the 32 output bytes (defensive).\n" ++
  "  mv t0, a2; li t1, 4\n" ++
  ".Lu256a_zinit:\n" ++
  "  beqz t1, .Lu256a_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lu256a_zinit\n" ++
  ".Lu256a_zdone:\n" ++
  "  jal ra, u256_add_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # overflow flag\n" ++
  "  j .Lu256a_pdone\n" ++
  u256AddBeFunction ++ "\n" ++
  ".Lu256a_pdone:"

def ziskU256AddBeDataSection : String :=
  ".section .data\n" ++
  "u256a_pad:\n" ++
  "  .zero 8"

def ziskU256AddBeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256AddBePrologue
  dataAsm     := ziskU256AddBeDataSection
}

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
def u256LtBeFunction : String :=
  "u256_lt_be:\n" ++
  "  li t0, 32                  # byte counter (MSB-first)\n" ++
  "  mv t1, a0                  # a cursor\n" ++
  "  mv t2, a1                  # b cursor\n" ++
  ".Lulb_loop:\n" ++
  "  beqz t0, .Lulb_equal\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bltu t3, t4, .Lulb_less\n" ++
  "  bltu t4, t3, .Lulb_greater\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lulb_loop\n" ++
  ".Lulb_less:\n" ++
  "  li t5, 1\n" ++
  "  sd t5, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lulb_greater:\n" ++
  ".Lulb_equal:\n" ++
  "  sd zero, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_u256_lt_be`: probe BuildUnit.
    Input layout (after host shift):
      bytes  0.. 8 : padding
      bytes  8..40 : a (32 B BE)
      bytes 40..72 : b (32 B BE)
    Output layout:
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : is_less (1 if a < b, else 0) -/
def ziskU256LtBePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 16             # a ptr\n" ++
  "  addi a1, a3, 48             # b ptr (a + 32)\n" ++
  "  li a2, 0xa0010008           # is_less out\n" ++
  "  jal ra, u256_lt_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lulb_pdone\n" ++
  u256LtBeFunction ++ "\n" ++
  ".Lulb_pdone:"

def ziskU256LtBeDataSection : String :=
  ".section .data\n" ++
  "ulb_pad:\n" ++
  "  .zero 8"

def ziskU256LtBeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256LtBePrologue
  dataAsm     := ziskU256LtBeDataSection
}

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
def u256SubBeFunction : String :=
  "u256_sub_be:\n" ++
  "  li t0, 31                  # byte index (LSB first)\n" ++
  "  li t1, 0                   # borrow\n" ++
  ".Lu256s_loop:\n" ++
  "  add t2, a0, t0\n" ++
  "  add t3, a1, t0\n" ++
  "  add t4, a2, t0\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  sub t5, t5, t6\n" ++
  "  sub t5, t5, t1             # - borrow-in\n" ++
  "  sltz t1, t5                # borrow-out = (t5 < 0)\n" ++
  "  andi t5, t5, 0xff          # masked diff byte\n" ++
  "  sb t5, 0(t4)\n" ++
  "  beqz t0, .Lu256s_done\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lu256s_loop\n" ++
  ".Lu256s_done:\n" ++
  "  mv a0, t1                  # final borrow = underflow flag\n" ++
  "  ret"

/-- `zisk_u256_sub_be`: probe BuildUnit. Reads (32B a, 32B b)
    from host input, writes (borrow_flag, 32B result) to OUTPUT
    (40 bytes total). -/
def ziskU256SubBePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # a ptr\n" ++
  "  addi a1, a3, 40             # b ptr\n" ++
  "  li a2, 0xa0010008           # out ptr at OUTPUT + 8\n" ++
  "  mv t0, a2; li t1, 4\n" ++
  ".Lu256s_zinit:\n" ++
  "  beqz t1, .Lu256s_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lu256s_zinit\n" ++
  ".Lu256s_zdone:\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # borrow flag\n" ++
  "  j .Lu256s_pdone\n" ++
  u256SubBeFunction ++ "\n" ++
  ".Lu256s_pdone:"

def ziskU256SubBeDataSection : String :=
  ".section .data\n" ++
  "u256s_pad:\n" ++
  "  .zero 8"

def ziskU256SubBeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256SubBePrologue
  dataAsm     := ziskU256SubBeDataSection
}

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
def u256FromU64BeFunction : String :=
  "u256_from_u64_be:\n" ++
  "  # Zero the high 24 bytes.\n" ++
  "  sd zero,  0(a1)\n" ++
  "  sd zero,  8(a1)\n" ++
  "  sd zero, 16(a1)\n" ++
  "  # Write the u64 in BE order at bytes 24..32.\n" ++
  "  srli t0, a0, 56; sb t0, 24(a1)\n" ++
  "  srli t0, a0, 48; sb t0, 25(a1)\n" ++
  "  srli t0, a0, 40; sb t0, 26(a1)\n" ++
  "  srli t0, a0, 32; sb t0, 27(a1)\n" ++
  "  srli t0, a0, 24; sb t0, 28(a1)\n" ++
  "  srli t0, a0, 16; sb t0, 29(a1)\n" ++
  "  srli t0, a0,  8; sb t0, 30(a1)\n" ++
  "                  sb a0, 31(a1)\n" ++
  "  ret"

/-- `zisk_u256_from_u64_be`: probe BuildUnit. Reads (u64 value)
    from host input, writes the 32-byte BE u256 to OUTPUT. -/
def ziskU256FromU64BePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a2, 0x40000000\n" ++
  "  ld a0, 8(a2)                # value\n" ++
  "  li a1, 0xa0010000           # out ptr at OUTPUT\n" ++
  "  jal ra, u256_from_u64_be\n" ++
  "  j .Lu256f_pdone\n" ++
  u256FromU64BeFunction ++ "\n" ++
  ".Lu256f_pdone:"

def ziskU256FromU64BeDataSection : String :=
  ".section .data\n" ++
  "u256f_pad:\n" ++
  "  .zero 8"

def ziskU256FromU64BeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256FromU64BePrologue
  dataAsm     := ziskU256FromU64BeDataSection
}

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
def u256IsZeroFunction : String :=
  "u256_is_zero:\n" ++
  "  ld t0,  0(a0)\n" ++
  "  ld t1,  8(a0)\n" ++
  "  ld t2, 16(a0)\n" ++
  "  ld t3, 24(a0)\n" ++
  "  or t0, t0, t1\n" ++
  "  or t0, t0, t2\n" ++
  "  or t0, t0, t3\n" ++
  "  seqz a0, t0\n" ++
  "  ret"

/-- `zisk_u256_is_zero`: probe BuildUnit. Reads 32B u256 from host
    input, writes the u64 result. -/
def ziskU256IsZeroPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a1, 0x40000000\n" ++
  "  addi a0, a1, 8              # u256 ptr\n" ++
  "  jal ra, u256_is_zero\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # result\n" ++
  "  j .Lu256z_pdone\n" ++
  u256IsZeroFunction ++ "\n" ++
  ".Lu256z_pdone:"

def ziskU256IsZeroDataSection : String :=
  ".section .data\n" ++
  "u256z_pad:\n" ++
  "  .zero 8"

def ziskU256IsZeroProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256IsZeroPrologue
  dataAsm     := ziskU256IsZeroDataSection
}

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
def u256MinFunction : String :=
  "u256_min:\n" ++
  "  li t0, 0                   # byte index\n" ++
  "  li t6, 32\n" ++
  ".Lumin_lt_loop:\n" ++
  "  beq t0, t6, .Lumin_pick_a  # all bytes equal → return a\n" ++
  "  add t1, a0, t0\n" ++
  "  add t2, a1, t0\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bltu t3, t4, .Lumin_pick_a # a < b → return a\n" ++
  "  bgtu t3, t4, .Lumin_pick_b # a > b → return b\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lumin_lt_loop\n" ++
  ".Lumin_pick_a:\n" ++
  "  mv t0, a0\n" ++
  "  j .Lumin_copy\n" ++
  ".Lumin_pick_b:\n" ++
  "  mv t0, a1\n" ++
  ".Lumin_copy:\n" ++
  "  ld t1,  0(t0); sd t1,  0(a2)\n" ++
  "  ld t1,  8(t0); sd t1,  8(a2)\n" ++
  "  ld t1, 16(t0); sd t1, 16(a2)\n" ++
  "  ld t1, 24(t0); sd t1, 24(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_u256_min`: probe BuildUnit. Reads (32B a, 32B b) from
    host input, writes the 32B min into OUTPUT. -/
def ziskU256MinPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # a ptr\n" ++
  "  addi a1, a3, 40             # b ptr\n" ++
  "  li a2, 0xa0010000           # out ptr at OUTPUT\n" ++
  "  jal ra, u256_min\n" ++
  "  j .Lumin_pdone\n" ++
  u256MinFunction ++ "\n" ++
  ".Lumin_pdone:"

def ziskU256MinDataSection : String :=
  ".section .data\n" ++
  "umin_pad:\n" ++
  "  .zero 8"

def ziskU256MinProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256MinPrologue
  dataAsm     := ziskU256MinDataSection
}

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
def u256MaxFunction : String :=
  "u256_max:\n" ++
  "  li t0, 0                   # byte index\n" ++
  "  li t6, 32\n" ++
  ".Lumax_loop:\n" ++
  "  beq t0, t6, .Lumax_pick_a  # all bytes equal → return a\n" ++
  "  add t1, a0, t0\n" ++
  "  add t2, a1, t0\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bgtu t3, t4, .Lumax_pick_a # a > b → return a\n" ++
  "  bltu t3, t4, .Lumax_pick_b # a < b → return b\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lumax_loop\n" ++
  ".Lumax_pick_a:\n" ++
  "  mv t0, a0\n" ++
  "  j .Lumax_copy\n" ++
  ".Lumax_pick_b:\n" ++
  "  mv t0, a1\n" ++
  ".Lumax_copy:\n" ++
  "  ld t1,  0(t0); sd t1,  0(a2)\n" ++
  "  ld t1,  8(t0); sd t1,  8(a2)\n" ++
  "  ld t1, 16(t0); sd t1, 16(a2)\n" ++
  "  ld t1, 24(t0); sd t1, 24(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_u256_max`: probe BuildUnit. Reads (32B a, 32B b) from
    host input, writes the 32B max into OUTPUT. -/
def ziskU256MaxPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # a ptr\n" ++
  "  addi a1, a3, 40             # b ptr\n" ++
  "  li a2, 0xa0010000           # out ptr at OUTPUT\n" ++
  "  jal ra, u256_max\n" ++
  "  j .Lumax_pdone\n" ++
  u256MaxFunction ++ "\n" ++
  ".Lumax_pdone:"

def ziskU256MaxDataSection : String :=
  ".section .data\n" ++
  "umax_pad:\n" ++
  "  .zero 8"

def ziskU256MaxProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256MaxPrologue
  dataAsm     := ziskU256MaxDataSection
}

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
def u256DivU64BeFunction : String :=
  "u256_div_u64_be:\n" ++
  "  li t0, 0                   # carry (< b)\n" ++
  "  li t1, 0                   # byte index (MSB → LSB)\n" ++
  ".Lu256d_loop:\n" ++
  "  li t2, 32\n" ++
  "  beq t1, t2, .Lu256d_done\n" ++
  "  add t3, a0, t1\n" ++
  "  lbu t4, 0(t3)              # src[i]\n" ++
  "  slli t5, t0, 8\n" ++
  "  or t5, t5, t4              # num = (carry << 8) | src[i]\n" ++
  "  divu t6, t5, a1            # q_byte = num / b  (< 256)\n" ++
  "  remu t0, t5, a1            # new carry = num mod b\n" ++
  "  add t3, a2, t1\n" ++
  "  sb t6, 0(t3)               # out[i] = q_byte (low 8 bits)\n" ++
  "  addi t1, t1, 1\n" ++
  "  j .Lu256d_loop\n" ++
  ".Lu256d_done:\n" ++
  "  mv a0, t0                  # remainder\n" ++
  "  ret"

/-- `zisk_u256_div_u64_be`: probe BuildUnit. Reads (32B BE src,
    8B LE b) from host input, writes (u64 remainder, 32B BE
    quotient) to OUTPUT (40 bytes total). -/
def ziskU256DivU64BePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # src ptr (32B BE)\n" ++
  "  ld a1, 40(a3)               # b (u64 LE)\n" ++
  "  li a2, 0xa0010008           # out ptr at OUTPUT + 8\n" ++
  "  # Pre-zero 32 output bytes (defensive).\n" ++
  "  mv t0, a2; li t1, 4\n" ++
  ".Lu256d_zout:\n" ++
  "  beqz t1, .Lu256d_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lu256d_zout\n" ++
  ".Lu256d_zout_done:\n" ++
  "  jal ra, u256_div_u64_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # remainder\n" ++
  "  j .Lu256d_pdone\n" ++
  u256DivU64BeFunction ++ "\n" ++
  ".Lu256d_pdone:"

def ziskU256DivU64BeDataSection : String :=
  ".section .data\n" ++
  "u256d_pad:\n" ++
  "  .zero 8"

def ziskU256DivU64BeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256DivU64BePrologue
  dataAsm     := ziskU256DivU64BeDataSection
}

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
def u256EqFunction : String :=
  "u256_eq:\n" ++
  "  li t0, 0                   # byte index\n" ++
  "  li t6, 32\n" ++
  ".Lu256eq_loop:\n" ++
  "  beq t0, t6, .Lu256eq_yes   # 32 bytes equal → a == b\n" ++
  "  add t1, a0, t0\n" ++
  "  add t2, a1, t0\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bne t3, t4, .Lu256eq_no\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lu256eq_loop\n" ++
  ".Lu256eq_yes:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lu256eq_no:\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_u256_eq`: probe BuildUnit. Reads (32B a, 32B b) from
    host input, writes the u64 result. -/
def ziskU256EqPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a2, 0x40000000\n" ++
  "  addi a0, a2, 8              # a ptr\n" ++
  "  addi a1, a2, 40             # b ptr (a + 32)\n" ++
  "  jal ra, u256_eq\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # result\n" ++
  "  j .Lu256eq_pdone\n" ++
  u256EqFunction ++ "\n" ++
  ".Lu256eq_pdone:"

def ziskU256EqDataSection : String :=
  ".section .data\n" ++
  "u256eq_pad:\n" ++
  "  .zero 8"

def ziskU256EqProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256EqPrologue
  dataAsm     := ziskU256EqDataSection
}


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
def u256MulU64BeFunction : String :=
  "u256_mul_u64_be:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # a ptr\n" ++
  "  mv s1, a1                  # b\n" ++
  "  mv s2, a2                  # out ptr\n" ++
  "  # Zero 40-byte accumulator.\n" ++
  "  la s3, u256m_acc\n" ++
  "  mv t0, s3\n" ++
  "  li t1, 5\n" ++
  ".Lmul_zinit:\n" ++
  "  beqz t1, .Lmul_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lmul_zinit\n" ++
  ".Lmul_zdone:\n" ++
  "  # Outer loop: p in 0..32 (byte position from LSB).\n" ++
  "  li s4, 0\n" ++
  ".Lmul_outer:\n" ++
  "  li t0, 32\n" ++
  "  beq s4, t0, .Lmul_post\n" ++
  "  # byte_a = a[31 - p]\n" ++
  "  li t0, 31\n" ++
  "  sub t0, t0, s4\n" ++
  "  add t0, s0, t0\n" ++
  "  lbu t0, 0(t0)\n" ++
  "  beqz t0, .Lmul_step        # skip zero bytes (optimization)\n" ++
  "  # partial = byte_a * b: low 64 in t1, high ≤ 0xff in t2.\n" ++
  "  mul   t1, t0, s1\n" ++
  "  mulhu t2, t0, s1\n" ++
  "  # Add to acc[p..p+9] with carry.\n" ++
  "  add t3, s3, s4             # &acc[p]\n" ++
  "  li t4, 8                   # 8 low bytes\n" ++
  "  li t5, 0                   # carry\n" ++
  ".Lmul_addlo:\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  andi a3, t1, 0xff\n" ++
  "  add  t6, t6, a3\n" ++
  "  add  t6, t6, t5\n" ++
  "  andi a3, t6, 0xff\n" ++
  "  sb   a3, 0(t3)\n" ++
  "  srli t5, t6, 8\n" ++
  "  srli t1, t1, 8\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lmul_addlo\n" ++
  "  # Add p_hi (t2; ≤ 1 byte) + carry at acc[p+8].\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  add t6, t6, t2\n" ++
  "  add t6, t6, t5\n" ++
  "  andi a3, t6, 0xff\n" ++
  "  sb   a3, 0(t3)\n" ++
  "  srli t5, t6, 8\n" ++
  "  addi t3, t3, 1\n" ++
  "  # Propagate remaining carry through higher bytes.\n" ++
  ".Lmul_carry:\n" ++
  "  beqz t5, .Lmul_step\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  add t6, t6, t5\n" ++
  "  andi a3, t6, 0xff\n" ++
  "  sb   a3, 0(t3)\n" ++
  "  srli t5, t6, 8\n" ++
  "  addi t3, t3, 1\n" ++
  "  j .Lmul_carry\n" ++
  ".Lmul_step:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lmul_outer\n" ++
  ".Lmul_post:\n" ++
  "  # Copy acc[0..32] (LSB first) into out (BE, MSB first).\n" ++
  "  mv t0, s3                  # acc cursor (LSB)\n" ++
  "  addi t1, s2, 32            # out end (exclusive)\n" ++
  "  li t2, 32\n" ++
  ".Lmul_copy:\n" ++
  "  beqz t2, .Lmul_overflow_check\n" ++
  "  addi t1, t1, -1\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lmul_copy\n" ++
  ".Lmul_overflow_check:\n" ++
  "  # t0 now points to acc[32]; any nonzero in acc[32..40] → overflow.\n" ++
  "  li t1, 8\n" ++
  "  li a0, 0\n" ++
  ".Lmul_of_loop:\n" ++
  "  beqz t1, .Lmul_done\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  beqz t3, .Lmul_of_next\n" ++
  "  li a0, 1\n" ++
  "  j .Lmul_done\n" ++
  ".Lmul_of_next:\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lmul_of_loop\n" ++
  ".Lmul_done:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_u256_mul_u64_be`: probe BuildUnit. Reads (32B a BE,
    8B b LE) from host input, writes (overflow_flag, 32B result
    BE) to OUTPUT (40 bytes total). -/
def ziskU256MulU64BePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # a ptr (32B BE)\n" ++
  "  ld a1, 40(a3)               # b (u64 LE)\n" ++
  "  li a2, 0xa0010008           # out ptr at OUTPUT + 8\n" ++
  "  # Pre-zero the 32 output bytes (defensive).\n" ++
  "  mv t0, a2; li t1, 4\n" ++
  ".Lmul_zout:\n" ++
  "  beqz t1, .Lmul_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lmul_zout\n" ++
  ".Lmul_zout_done:\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # overflow flag\n" ++
  "  j .Lmul_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  ".Lmul_pdone:"

def ziskU256MulU64BeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40"

def ziskU256MulU64BeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256MulU64BePrologue
  dataAsm     := ziskU256MulU64BeDataSection
}

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
def u256ToU64BeFunction : String :=
  "u256_to_u64_be:\n" ++
  "  # Check high 24 bytes (positions 0..24) are all zero.\n" ++
  "  ld t0,  0(a0)\n" ++
  "  ld t1,  8(a0)\n" ++
  "  ld t2, 16(a0)\n" ++
  "  or t0, t0, t1\n" ++
  "  or t0, t0, t2\n" ++
  "  # Assemble low u64 from BE bytes at positions 24..32.\n" ++
  "  lbu t1, 24(a0); slli t1, t1, 56\n" ++
  "  lbu t2, 25(a0); slli t2, t2, 48; or t1, t1, t2\n" ++
  "  lbu t2, 26(a0); slli t2, t2, 40; or t1, t1, t2\n" ++
  "  lbu t2, 27(a0); slli t2, t2, 32; or t1, t1, t2\n" ++
  "  lbu t2, 28(a0); slli t2, t2, 24; or t1, t1, t2\n" ++
  "  lbu t2, 29(a0); slli t2, t2, 16; or t1, t1, t2\n" ++
  "  lbu t2, 30(a0); slli t2, t2,  8; or t1, t1, t2\n" ++
  "  lbu t2, 31(a0);                  or t1, t1, t2\n" ++
  "  sd t1, 0(a1)\n" ++
  "  snez a0, t0                      # overflow = (high bits != 0)\n" ++
  "  ret"

/-- `zisk_u256_to_u64_be`: probe BuildUnit. Reads 32B BE u256
    from host input, writes (overflow_flag, u64 result LE) to
    OUTPUT (16 bytes total). -/
def ziskU256ToU64BePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a2, 0x40000000\n" ++
  "  addi a0, a2, 8              # src ptr\n" ++
  "  li a1, 0xa0010008           # u64 out\n" ++
  "  jal ra, u256_to_u64_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # overflow flag\n" ++
  "  j .Lu256t_pdone\n" ++
  u256ToU64BeFunction ++ "\n" ++
  ".Lu256t_pdone:"

def ziskU256ToU64BeDataSection : String :=
  ".section .data\n" ++
  "u256t_pad:\n" ++
  "  .zero 8"

def ziskU256ToU64BeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256ToU64BePrologue
  dataAsm     := ziskU256ToU64BeDataSection
}



end EvmAsm.Codegen
