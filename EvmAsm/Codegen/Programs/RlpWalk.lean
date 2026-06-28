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
    Frameless leaf -- clobbers t0..t6, returns in a0/a1/a2. -/
def rlpWalkInitFunction : String :=
  "rlp_walk_init:\n" ++
  "  beqz a1, .Lwi_empty        # list_len == 0 -> empty (status 2)\n" ++
  "  add a1, a0, a1             # end = list_ptr + list_len\n" ++
  "  lbu t0, 0(a0)              # prefix\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lwi_notlist  # prefix < 0xc0 -> not a list (status 1)\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lwi_short    # 0xc0 <= prefix < 0xf8 -> short list\n" ++
  "  # Long list: lol = prefix - 0xf7\n" ++
  "  li t1, 0xf7\n" ++
  "  sub t2, t0, t1             # lol (1..8)\n" ++
  "  addi t3, t2, 1             # header size = 1 + lol\n" ++
  "  add t4, a0, t3             # cursor = list_ptr + 1 + lol\n" ++
  "  bltu a1, t4, .Lwi_ltrunc   # end < cursor -> length field truncated (status 4)\n" ++
  "  addi t1, a0, 1             # length-field ptr = list_ptr + 1\n" ++
  "  lbu t5, 0(t1)              # first length byte\n" ++
  "  beqz t5, .Lwi_llz          # leading zero -> status 5\n" ++
  "  # read length field (lol bytes, big-endian) -> t6 = decoded\n" ++
  "  li t6, 0\n" ++
  "  mv t5, t2                  # count = lol\n" ++
  ".Lwi_lloop:\n" ++
  "  beqz t5, .Lwi_ldone\n" ++
  "  slli t6, t6, 8\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  or t6, t6, t3\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lwi_lloop\n" ++
  ".Lwi_ldone:\n" ++
  "  li t1, 56\n" ++
  "  bltu t6, t1, .Lwi_lmin     # decoded < 56 -> non-minimal (status 6)\n" ++
  "  add t1, t4, t6             # content_end = cursor + decoded\n" ++
  "  bne t1, a1, .Lwi_lmism     # content_end != end -> length mismatch (status 7)\n" ++
  "  mv a0, t4                  # cursor = list_ptr + 1 + lol\n" ++
  "  li a2, 0\n" ++
  "  ret\n" ++
  ".Lwi_short:\n" ++
  "  li t1, 0xc0\n" ++
  "  sub t2, t0, t1             # content_len = prefix - 0xc0\n" ++
  "  addi t3, t2, 1             # 1 + content_len\n" ++
  "  add t4, a0, t3             # content_end = list_ptr + 1 + content_len\n" ++
  "  bne t4, a1, .Lwi_smism     # content_end != end -> short mismatch (status 3)\n" ++
  "  addi a0, a0, 1             # cursor = list_ptr + 1\n" ++
  "  li a2, 0\n" ++
  "  ret\n" ++
  ".Lwi_empty:\n" ++
  "  li a2, 2\n" ++
  "  ret\n" ++
  ".Lwi_notlist:\n" ++
  "  li a2, 1\n" ++
  "  ret\n" ++
  ".Lwi_smism:\n" ++
  "  li a2, 3\n" ++
  "  ret\n" ++
  ".Lwi_ltrunc:\n" ++
  "  li a2, 4\n" ++
  "  ret\n" ++
  ".Lwi_llz:\n" ++
  "  li a2, 5\n" ++
  "  ret\n" ++
  ".Lwi_lmin:\n" ++
  "  li a2, 6\n" ++
  "  ret\n" ++
  ".Lwi_lmism:\n" ++
  "  li a2, 7\n" ++
  "  ret"

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
      a2 (output) : content length (0 on every fail path)
                      (byte-string items: prefix-stripped payload;
                       sub-list items: full encoded span)

    The content pointer is derived by the caller as `advanced_cursor - content_length`.
    Frameless leaf -- clobbers t0..t6, returns in a0/a1/a2. -/
def rlpWalkNextFunction : String :=
  "rlp_walk_next:\n" ++
  "  bgeu a0, a1, .Lwn_end      # cursor >= end -> end-of-list (status 2)\n" ++
  "  lbu t0, 0(a0)              # prefix byte\n" ++
  "  li t1, 0x80\n" ++
  "  bltu t0, t1, .Lwn_single\n" ++
  "  li t1, 0xb8\n" ++
  "  bltu t0, t1, .Lwn_short_string\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lwn_long_string\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lwn_short_list\n" ++
  "  # Long list (full encoded span): lol = t0 - 0xf7\n" ++
  "  li t1, 0xf7\n" ++
  "  sub t2, t0, t1             # lol\n" ++
  "  addi t1, t2, 1             # 1 + lol (header size)\n" ++
  "  add t4, a0, t1             # header_end = cursor + 1 + lol\n" ++
  "  bltu a1, t4, .Lwn_bound    # header runs past end -> bound (status 3)\n" ++
  "  addi t5, a0, 1             # length-field ptr\n" ++
  "  lbu t6, 0(t5)              # first length byte\n" ++
  "  beqz t6, .Lwn_lz           # leading zero -> status 5\n" ++
  "  li t3, 0                   # decoded accumulator\n" ++
  "  mv t1, t2                  # count = lol\n" ++
  ".Lwn_ll_be:\n" ++
  "  beqz t1, .Lwn_ll_done\n" ++
  "  slli t3, t3, 8\n" ++
  "  lbu t6, 0(t5)\n" ++
  "  or t3, t3, t6\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lwn_ll_be\n" ++
  ".Lwn_ll_done:\n" ++
  "  li t1, 56\n" ++
  "  bltu t3, t1, .Lwn_nonmin   # decoded < 56 -> non-minimal (status 4)\n" ++
  "  add t6, t2, t3             # lol + decoded\n" ++
  "  addi t6, t6, 1             # full span = 1 + lol + decoded\n" ++
  "  add t1, a0, t6             # advanced (temp)\n" ++
  "  bltu a1, t1, .Lwn_bound    # content runs past end -> bound (status 3)\n" ++
  "  mv a0, t1                  # advanced cursor\n" ++
  "  mv a2, t6                  # content length = full span\n" ++
  "  li a1, 0\n" ++
  "  ret\n" ++
  ".Lwn_long_string:\n" ++
  "  li t1, 0xb7\n" ++
  "  sub t2, t0, t1             # lol\n" ++
  "  addi t1, t2, 1             # 1 + lol\n" ++
  "  add t4, a0, t1             # header_end = cursor + 1 + lol\n" ++
  "  bltu a1, t4, .Lwn_bound    # header runs past end -> bound (status 3)\n" ++
  "  addi t5, a0, 1             # length-field ptr\n" ++
  "  lbu t6, 0(t5)              # first length byte\n" ++
  "  beqz t6, .Lwn_lz           # leading zero -> status 5\n" ++
  "  li t3, 0                   # decoded accumulator\n" ++
  "  mv t1, t2                  # count = lol\n" ++
  ".Lwn_ls_be:\n" ++
  "  beqz t1, .Lwn_ls_done\n" ++
  "  slli t3, t3, 8\n" ++
  "  lbu t6, 0(t5)\n" ++
  "  or t3, t3, t6\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lwn_ls_be\n" ++
  ".Lwn_ls_done:\n" ++
  "  li t1, 56\n" ++
  "  bltu t3, t1, .Lwn_nonmin   # decoded < 56 -> non-minimal (status 4)\n" ++
  "  add t1, t4, t3             # advanced = header_end + decoded (temp)\n" ++
  "  bltu a1, t1, .Lwn_bound    # content runs past end -> bound (status 3)\n" ++
  "  mv a0, t1                  # advanced cursor\n" ++
  "  mv a2, t3                  # content length = decoded (stripped)\n" ++
  "  li a1, 0\n" ++
  "  ret\n" ++
  ".Lwn_short_string:\n" ++
  "  li t1, 0x80\n" ++
  "  sub a2, t0, t1             # content length = t0 - 0x80\n" ++
  "  addi t2, a0, 1             # content start = cursor + 1\n" ++
  "  add t3, t2, a2             # advanced = cursor + 1 + len (temp)\n" ++
  "  bltu a1, t3, .Lwn_bound    # content runs past end -> bound (status 3)\n" ++
  "  li t1, 1\n" ++
  "  bne a2, t1, .Lwn_ss_ok     # len != 1 -> canonical\n" ++
  "  lbu t1, 0(t2)              # content[0]\n" ++
  "  li t4, 0x80\n" ++
  "  bltu t1, t4, .Lwn_noncanon # len==1 and content[0] < 0x80 -> non-canonical (status 6)\n" ++
  ".Lwn_ss_ok:\n" ++
  "  mv a0, t3                  # advanced cursor\n" ++
  "  li a1, 0\n" ++
  "  ret\n" ++
  ".Lwn_single:\n" ++
  "  addi a0, a0, 1             # advanced cursor (cursor < end ensures in-bounds)\n" ++
  "  li a2, 1                   # content length = 1\n" ++
  "  li a1, 0\n" ++
  "  ret\n" ++
  ".Lwn_short_list:\n" ++
  "  li t1, 0xc0\n" ++
  "  sub t6, t0, t1             # t0 - 0xc0\n" ++
  "  addi t6, t6, 1             # full span = 1 + (t0 - 0xc0)\n" ++
  "  add t1, a0, t6             # advanced (temp)\n" ++
  "  bltu a1, t1, .Lwn_bound    # content runs past end -> bound (status 3)\n" ++
  "  mv a0, t1                  # advanced cursor\n" ++
  "  mv a2, t6                  # content length = full span\n" ++
  "  li a1, 0\n" ++
  "  ret\n" ++
  ".Lwn_end:\n" ++
  "  li a1, 2                   # end-of-list\n" ++
  "  li a2, 0\n" ++
  "  ret\n" ++
  ".Lwn_bound:\n" ++
  "  li a1, 3\n" ++
  "  li a2, 0\n" ++
  "  ret\n" ++
  ".Lwn_nonmin:\n" ++
  "  li a1, 4\n" ++
  "  li a2, 0\n" ++
  "  ret\n" ++
  ".Lwn_lz:\n" ++
  "  li a1, 5\n" ++
  "  li a2, 0\n" ++
  "  ret\n" ++
  ".Lwn_noncanon:\n" ++
  "  li a1, 6\n" ++
  "  li a2, 0\n" ++
  "  ret"

/-! ## rlp_content_to_u64 -- big-endian content bytes -> u64

    Decode a big-endian byte string (the prefix-stripped payload
    of an RLP byte-string item, as reported by `rlp_walk_next`) as
    a u64.  This is the BE-decode half of PR-K34
    `rlp_field_to_u64`, taking an explicit (ptr, len) instead of
    re-walking the list.

    Calling convention:
      a0 (input)  : content bytes ptr
      a1 (input)  : content byte length
      ra (input)  : return
      a0 (output) : u64 value (LE register form)
      a1 (output) : status (0 ok / 2 too long (> 8 bytes))

    Frameless leaf. -/
def rlpContentToU64Function : String :=
  "rlp_content_to_u64:\n" ++
  "  li t0, 8\n" ++
  "  bgtu a1, t0, .Lrcu_too_long\n" ++
  "  mv t1, a0                  # ptr\n" ++
  "  mv t2, a1                  # remaining\n" ++
  "  li a0, 0                   # accumulator\n" ++
  ".Lrcu_loop:\n" ++
  "  beqz t2, .Lrcu_done\n" ++
  "  slli a0, a0, 8\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  or a0, a0, t3\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lrcu_loop\n" ++
  ".Lrcu_done:\n" ++
  "  li a1, 0\n" ++
  "  ret\n" ++
  ".Lrcu_too_long:\n" ++
  "  li a0, 0\n" ++
  "  li a1, 2\n" ++
  "  ret"

/-! ## rlp_content_to_u256_be -- right-align content bytes -> u256 BE

    Right-align a big-endian byte string (the prefix-stripped
    payload of an RLP byte-string item) into a 32-byte BE u256
    buffer.  This is the copy half of PR-K35
    `rlp_field_to_u256_be`, taking an explicit (ptr, len, out)
    instead of re-walking the list.

    Calling convention:
      a0 (input)  : content bytes ptr
      a1 (input)  : content byte length
      a2 (input)  : 32-byte u256 BE output ptr (right-aligned)
      ra (input)  : return
      a0 (output) : status (0 ok / 2 too long (> 32 bytes))

    The output is always zeroed first, so fail / too-long paths
    leave a zero u256.  Frameless leaf. -/
def rlpContentToU256BeFunction : String :=
  "rlp_content_to_u256_be:\n" ++
  "  sd zero,  0(a2); sd zero,  8(a2); sd zero, 16(a2); sd zero, 24(a2)\n" ++
  "  li t0, 32\n" ++
  "  bgtu a1, t0, .Lrc256_too_long\n" ++
  "  sub t0, t0, a1             # 32 - len\n" ++
  "  add t1, a2, t0             # dst start (right-aligned)\n" ++
  "  mv t2, a0                  # src ptr\n" ++
  "  mv t3, a1                  # remaining\n" ++
  ".Lrc256_copy:\n" ++
  "  beqz t3, .Lrc256_done\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  sb  t4, 0(t1)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lrc256_copy\n" ++
  ".Lrc256_done:\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lrc256_too_long:\n" ++
  "  li a0, 2\n" ++
  "  ret"

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

end EvmAsm.Codegen
