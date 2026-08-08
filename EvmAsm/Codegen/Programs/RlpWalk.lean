/-
  EvmAsm.Codegen.Programs.RlpWalk

  Cursor-advancing RLP walker primitives -- a single-pass
  alternative to the index-based `rlp_list_nth_item` (PR-K20) used
  by the container decoders in `Tx.lean` / `TxDecode{1559,2930,
  4844,7702}.lean`.

  Motivation: every call to `rlp_list_nth_item` / `rlp_field_to_*`
  re-walks the list from byte 0, so decoding all N fields of one
  container costs 0+1+...+(N-1) = O(N^2) item visits. The pair
  here walks the list exactly once: `rlp_walk_init` positions the
  cursor at the first item, then each `rlp_walk_next` advances
  past exactly one item and reports its content bounds, so the
  decoder consumes fields 0..N-1 in N visits.

  Key invariant.  For every RLP item form, the content (payload)
  start pointer is recoverable from the two values `walk_next`
  returns -- the *advanced* cursor and the *content length*:

      content_ptr = advanced_cursor - content_length

  Verified per form (C = item-start cursor):
    * single byte  (<0x80)   : adv = C+1, len = 1     -> ptr = C
    * short string (0x80..b7): adv = C+1+len          -> ptr = C+1
    * long string  (b8..bf)  : adv = C+1+lol+len      -> ptr = C+1+lol
    * short list   (c0..f7)  : len = full span, ptr = C
    * long list    (f8..ff)  : len = full span, ptr = C

  This mirrors PR-K20's content semantics exactly: byte-string
  items are prefix-stripped, sub-list items are returned in full
  (so callers can recurse / store whole-encoded spans).

  No proofs yet -- these are codegen `String` defs only.  The
  verified cursor-advancing walker in `EvmAsm.Rv64.RLP` (e.g.
  `ValidatingFieldWalk.lean`) is the future verification target.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.RLP.ContentToU256Be
import EvmAsm.Rv64.RLP.Field0ToU64

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## rlp_walk_init -- position cursor at the first list item

    Skip the outer RLP list prefix (0xc0..0xff) so the cursor
    points at the first encoded child item.

    Calling convention:
      a0 (input)  : list bytes ptr (start of outer list prefix)
      a1 (input)  : total list byte length (full encoded item)
      ra (input)  : return
      a0 (output) : cursor (first child item, abs ptr)
      a1 (output) : end (list_ptr + list_len, exclusive)
      a2 (output) : status (0 ok; nonzero = malformed, distinct per reason):
                      1 not-a-list (prefix < 0xc0)
                      2 empty (list_len == 0)
                      3 short-list length mismatch (1 + (prefix-0xc0) != list_len)
                      4 long-list header truncated (1 + lol > list_len)
                      5 long-list length-field leading zero (len[0] == 0)
                      6 long-list non-minimal (decoded < 56)
                      7 long-list length mismatch (1 + lol + decoded != list_len)

    EXACT (execution-specs-equivalent): the list's self-declared length must
    equal `list_len` -- `1 + lol + decoded` (long) or `1 + (prefix-0xc0)` (short).
    Frameless leaf -- clobbers t0..t6, returns in a0/a1/a2.

    Emitted from the verified body `EvmAsm.Rv64.RLP.rlp_walk_init_prog` (proven
    correct by `rlp_walk_init_spec_within`); the rendered assembly is
    instruction-identical to the prior hand-written version (EEST 200/200 on spike). -/
def rlpWalkInitFunction : String :=
  "rlp_walk_init:\n" ++ emitProgram EvmAsm.Rv64.RLP.rlp_walk_init_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly the
    verified `rlp_walk_init_prog` rendered under its label, so any future
    hand-edit of `rlpWalkInitFunction` that diverges from the verified body
    fails to typecheck here. -/
theorem rlpWalkInitFunction_eq_verified_prog :
    rlpWalkInitFunction =
      "rlp_walk_init:\n" ++ emitProgram EvmAsm.Rv64.RLP.rlp_walk_init_prog :=
  rfl

#guard rlpWalkInitFunction.startsWith "rlp_walk_init:\n"
#guard EvmAsm.Rv64.RLP.rlp_walk_init_prog.length = 53

/-! ## rlp_walk_next -- advance cursor past one item, report content (STRICT)

    Decode the single item at the cursor, advance the cursor past it, and return
    the item's content length.  STRICT (execution-specs-equivalent): rejects an
    item whose header or content runs past `end` (bound), a non-canonical long
    form (leading-zero length field, non-minimal decoded length), and a
    non-canonical single-byte short string -- each with a distinct status.

    Calling convention:
      a0 (input)  : cursor (current item, abs ptr)
      a1 (input)  : end (exclusive, abs ptr)
      ra (input)  : return
      a0 (output) : advanced cursor (next item); = cursor on every fail path
      a1 (output) : status:
                      0 ok
                      2 end-of-list (cursor >= end)
                      3 bound (item or length field runs past end)
                      4 long-form non-minimal (decoded < 56)
                      5 long-form length-field leading zero (len[0] == 0)
                      6 single-byte short-string non-canonical (len==1, content < 0x80)
                      7 recursively invalid list payload (malformed child or fuel exhaustion)
      a2 (output) : content length (0 on every fail path)
                      (byte-string items: prefix-stripped payload;
                       sub-list items: full encoded span)

    The content pointer is derived by the caller as `advanced_cursor - content_length`.
    Frameless leaf -- clobbers t0..t6, returns in a0/a1/a2. -/
/-! ### Recursive list validation

The verified leaf above classifies one item and checks its own header/span, but
the execution-specs decoder also decodes every item in a list payload.  Keep
that single-item body as the mechanical core and put the recursive part in a
small ABI wrapper.  The wrapper deliberately has no accepting fallback: a
child failure (including fuel exhaustion) is returned as status `7`.

`s0` is the shared, input-derived fuel counter.  The top entry seeds it from
twice the remaining input length; every successfully decoded item consumes two
units, matching `EL.RLP.decode`'s `2 * bs.length` budget.  Nested calls use the
same counter rather than resetting it.  `s1` tracks simultaneously open list
levels and is capped at 1024: this is at or above the CPython recursion boundary
where the pinned reference raises `RecursionError` (outside its caught
`DecodingError` behavior), and below the guest-stack ceiling.  The ordinary
entry saves/restores `s0` and `s1`, while the nested entry is used only by the
validator.

The frames are ordinary RV64 call-stack frames and are restored on all paths;
the fuel bounds item work and termination, while the 1024-level cap bounds
active-list stack use separately.  Each active level uses 96 bytes (the 64-byte
shared frame plus the 32-byte validator frame), so 1024 levels consume 96 KiB
within the fixed 192 KiB guest stack `[0xa0020000,0xa0050000)`; if either the
fuel or depth bound is exhausted, the result is an explicit status-`7` reject.
If frame sizes change, this capacity check must be redone.  A list's payload is
accepted only when repeated calls reach its end exactly; malformed, truncated,
non-canonical, nested-malformed, trailing and fuel-exhausted payloads all
return status `7`.
-/
def rlpWalkNextCoreFunction : String :=
  "rlp_walk_next_core:\n" ++ emitProgram EvmAsm.Rv64.RLP.rlp_walk_next_prog

def rlpWalkNextFunction : String :=
  "rlp_walk_next:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sub t0, a1, a0\n" ++
  "  slli s0, t0, 1\n" ++
  "  li s1, 0\n" ++
  "  jal ra, rlp_walk_next_shared\n" ++
  "  ld s0, 8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n" ++
  "rlp_walk_next_nested:\n" ++
  "  j rlp_walk_next_shared\n" ++
  "rlp_walk_next_shared:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd a0, 8(sp)\n" ++
  "  sd a1, 16(sp)\n" ++
  "  jal ra, rlp_walk_next_core\n" ++
  "  sd a0, 24(sp)\n" ++
  "  sd a1, 32(sp)\n" ++
  "  sd a2, 40(sp)\n" ++
  "  bnez a1, .Lrw_shared_done\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lrw_shared_fuel\n" ++
  "  addi s0, s0, -2\n" ++
  "  ld t0, 8(sp)\n" ++
  "  lbu t1, 0(t0)\n" ++
  "  li t2, 0xc0\n" ++
  "  bltu t1, t2, .Lrw_shared_done\n" ++
  "  li t2, 1024\n" ++
  "  bgeu s1, t2, .Lrw_shared_fuel\n" ++
  "  addi s1, s1, 1\n" ++
  "  ld a1, 24(sp)\n" ++
  "  li t2, 0xf8\n" ++
  "  bltu t1, t2, .Lrw_shared_short_list\n" ++
  "  li t2, 0xf7\n" ++
  "  sub t3, t1, t2\n" ++
  "  mv a3, t3\n" ++
  "  addi t4, t0, 1\n" ++
  "  li t5, 0\n" ++
  ".Lrw_shared_long_len:\n" ++
  "  beqz t3, .Lrw_shared_long_done\n" ++
  "  slli t5, t5, 8\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  or t5, t5, t6\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lrw_shared_long_len\n" ++
  ".Lrw_shared_long_done:\n" ++
  "  add a2, t0, a3\n" ++
  "  addi a2, a2, 1\n" ++
  "  j .Lrw_shared_validate\n" ++
  ".Lrw_shared_short_list:\n" ++
  "  addi a2, t0, 1\n" ++
  ".Lrw_shared_validate:\n" ++
  "  mv a0, a2\n" ++
  "  jal ra, rlp_validate_payload\n" ++
  "  addi s1, s1, -1\n" ++
  "  beqz a0, .Lrw_shared_done\n" ++
  ".Lrw_shared_fuel:\n" ++
  "  ld a0, 8(sp)\n" ++
  "  li a1, 7\n" ++
  "  li a2, 0\n" ++
  "  j .Lrw_shared_restore_fail\n" ++
  ".Lrw_shared_done:\n" ++
  "  ld a0, 24(sp)\n" ++
  "  ld a1, 32(sp)\n" ++
  "  ld a2, 40(sp)\n" ++
  ".Lrw_shared_restore_fail:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n" ++
  "rlp_validate_payload:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd a0, 8(sp)\n" ++
  "  sd a1, 16(sp)\n" ++
  ".Lrw_validate_loop:\n" ++
  "  ld a0, 8(sp)\n" ++
  "  ld t0, 16(sp)\n" ++
  "  mv a1, t0\n" ++
  "  beq a0, t0, .Lrw_validate_ok\n" ++
  "  bltu t0, a0, .Lrw_validate_fail\n" ++
  "  jal ra, rlp_walk_next_nested\n" ++
  "  bnez a1, .Lrw_validate_fail\n" ++
  "  ld t0, 16(sp)\n" ++
  "  bltu t0, a0, .Lrw_validate_fail\n" ++
  "  sd a0, 8(sp)\n" ++
  "  j .Lrw_validate_loop\n" ++
  ".Lrw_validate_ok:\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n" ++
  ".Lrw_validate_fail:\n" ++
  "  li a0, 7\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n" ++
  rlpWalkNextCoreFunction

/-- Kernel-checked drift guard for the mechanical single-item core.  The
    recursive wrapper above is intentionally codegen-specific; this theorem
    keeps the verified leaf it delegates to tied to its emitted program. -/
theorem rlpWalkNextCoreFunction_eq_verified_prog :
    rlpWalkNextCoreFunction =
      "rlp_walk_next_core:\n" ++ emitProgram EvmAsm.Rv64.RLP.rlp_walk_next_prog :=
  rfl

#guard rlpWalkNextFunction.startsWith "rlp_walk_next:\n"
#guard EvmAsm.Rv64.RLP.rlp_walk_next_prog.length = 103

/-! ## rlp_content_to_u64 -- big-endian content bytes -> u64

    Decode a big-endian byte string (the prefix-stripped payload
    of an RLP byte-string item, as reported by `rlp_walk_next`) as
    a u64.  This is the BE-decode half of PR-K34
    `rlp_field_to_u64`, taking an explicit (ptr, len) instead of
    re-walking the list.

    Emitted from the verified **canonical-strict** body
    `EvmAsm.Rv64.RLP.rlp_content_to_u64_prog` (proven correct by the four-way
    dispatch theorem `rlp_content_to_u64_spec_within`, see
    `EvmAsm/Rv64/RLP/ContentToU64.lean`). Behavior difference from the prior
    hand-written body that matters for callers: this version enforces RLP
    scalar canonicality (execution-specs `_deserialize_to_uint`) and rejects a
    nonzero-length content whose high byte is `0` with a dedicated status `3`
    (`non-canonical`), where the old body silently accepted it.

    Calling convention:
      a0 (input)  : content bytes ptr
      a1 (input)  : content byte length
      ra (input)  : return
      a0 (output) : u64 value (LE register form)
      a1 (output) : status (0 ok / 2 too long (> 8 bytes) / 3 non-canonical
                      (0 < len <= 8 and content[0] == 0))

    Frameless leaf. -/
def rlpContentToU64Function : String :=
  "rlp_content_to_u64:\n" ++ emitProgram EvmAsm.Rv64.RLP.rlp_content_to_u64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly the
    verified `rlp_content_to_u64_prog` rendered under its label, so any
    future hand-edit of `rlpContentToU64Function` that diverges from the
    verified body fails to typecheck here. -/
theorem rlpContentToU64Function_eq_verified_prog :
    rlpContentToU64Function =
      "rlp_content_to_u64:\n" ++ emitProgram EvmAsm.Rv64.RLP.rlp_content_to_u64_prog :=
  rfl

#guard rlpContentToU64Function.startsWith "rlp_content_to_u64:\n"
#guard EvmAsm.Rv64.RLP.rlp_content_to_u64_prog.length = 22

/-! ## rlp_content_to_u256_be -- right-align content bytes -> u256 BE

    Right-align a big-endian byte string (the prefix-stripped
    payload of an RLP byte-string item) into a 32-byte BE u256
    buffer.  This is the copy half of PR-K35
    `rlp_field_to_u256_be`, taking an explicit (ptr, len, out)
    instead of re-walking the list.

    Emitted from the verified **canonical-strict** body
    `EvmAsm.Rv64.RLP.rlp_content_to_u256_be_prog` (proven correct by the
    four-way dispatch theorem `rlp_content_to_u256_be_spec_within`, see
    `EvmAsm/Rv64/RLP/ContentToU256Be.lean`). Behavior difference from the
    prior hand-written body that matters for callers: this version enforces
    RLP scalar canonicality (execution-specs `_deserialize_to_uint`) and
    rejects a nonzero-length content whose high byte is `0` with a dedicated
    status `3` (non-canonical), where the old body silently right-aligned it.

    Calling convention:
      a0 (input)  : content bytes ptr
      a1 (input)  : content byte length
      a2 (input)  : 32-byte u256 BE output ptr (right-aligned)
      ra (input)  : return
      a0 (output) : status
                      0 ok (canonical: len = 0, or len <= 32 and content[0] != 0)
                      2 too long (len > 32)
                      3 non-canonical (0 < len <= 32 and content[0] == 0)

    The output is always zeroed first, so fail / too-long / non-canonical
    paths leave a zero u256. Frameless leaf. -/
def rlpContentToU256BeFunction : String :=
  "rlp_content_to_u256_be:\n" ++
    emitProgram EvmAsm.Rv64.RLP.rlp_content_to_u256_be_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly the
    verified `rlp_content_to_u256_be_prog` rendered under its label, so any
    future hand-edit of `rlpContentToU256BeFunction` that diverges from the
    verified body fails to typecheck here. -/
theorem rlpContentToU256BeFunction_eq_verified_prog :
    rlpContentToU256BeFunction =
      "rlp_content_to_u256_be:\n" ++
        emitProgram EvmAsm.Rv64.RLP.rlp_content_to_u256_be_prog :=
  rfl

#guard rlpContentToU256BeFunction.startsWith "rlp_content_to_u256_be:\n"
#guard EvmAsm.Rv64.RLP.rlp_content_to_u256_be_prog.length = 26

/-! ## rlp_field0_to_u64 -- fixed-offset first-field u64 wrapper

    Experimental verified-layout alternative to the index-based
    rlp_field_to_u64 helper for callers that only need field 0. The emitted
    image is the wrapper plus the verified walk/content callees, padded with
    NOPs so the wrapper's fixed PC-relative JAL offsets land at the proven
    callee entry points.

    The wrapper body is partially verified today: the shared parse-failure tail
    is proved by rlp_field0_to_u64_parse_fail_spec_within, and the successful
    content_to_u64 call composition is proved by
    rlp_field0_to_u64_content_call_success_spec_within. The remaining work is
    to compose walk_init and walk_next into the unified top theorem. -/
def rlpField0ToU64Function : String :=
  "rlp_field0_to_u64:\n" ++
    emitProgram EvmAsm.Rv64.RLP.rlp_field0_to_u64_full_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly the
    deployable fixed-offset image from EvmAsm.Rv64.RLP.Field0ToU64. -/
theorem rlpField0ToU64Function_eq_verified_prog :
    rlpField0ToU64Function =
      "rlp_field0_to_u64:\n" ++
        emitProgram EvmAsm.Rv64.RLP.rlp_field0_to_u64_full_prog :=
  rfl

#guard rlpField0ToU64Function.startsWith "rlp_field0_to_u64:\n"
#guard EvmAsm.Rv64.RLP.rlp_field0_to_u64_prog.length = 15
#guard EvmAsm.Rv64.RLP.rlp_walk_init_prog.length = 53
#guard EvmAsm.Rv64.RLP.rlp_walk_next_prog.length = 103
#guard EvmAsm.Rv64.RLP.rlp_content_to_u64_prog.length = 22

/-! The four cursor-walk primitives concatenated as a single helper block.

    Standalone debug probes that embed the tx/header decoders (which now use
    the single-pass cursor walker) must link these bodies too. Mirrors the
    index-based RLP primitives each such probe already bundles; centralised
    here so new probes don't hand-copy four lines (the documented closure-drift
    pattern, see `BlockVerdictV2.lean` ziskStatelessVerdictV2ProbeUnit). -/
def rlpWalkHelpersClosure : String :=
  rlpWalkInitFunction ++ "\n" ++
  rlpWalkNextFunction ++ "\n" ++
  rlpContentToU64Function ++ "\n" ++
  rlpContentToU256BeFunction

/-- Kernel-checked drift guard: the closure is exactly the concatenation of
    the four guarded helper definitions, so future edits cannot quietly
    bypass one of them (each helper is itself tied to its verified Rv64
    program by `rlpWalkInitFunction_eq_verified_prog`,
    `rlpWalkNextCoreFunction_eq_verified_prog`,
    `rlpContentToU64Function_eq_verified_prog`, and
    `rlpContentToU256BeFunction_eq_verified_prog`). -/
theorem rlpWalkHelpersClosure_eq_helpers :
    rlpWalkHelpersClosure =
      rlpWalkInitFunction ++ "\n" ++
      rlpWalkNextFunction ++ "\n" ++
      rlpContentToU64Function ++ "\n" ++
      rlpContentToU256BeFunction :=
  rfl

end EvmAsm.Codegen
