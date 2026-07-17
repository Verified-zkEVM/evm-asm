/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsSpec

  Verified-triple groundwork for `bal_account_nonstorage_finals` (bead
  evm-asm-4ch8f.43.5) — the BAL AccountChanges NON-storage finals parser, the
  value-bearing companion of the `.43.1` `bal_storage_reads_in_exec_log` port
  (PR #10161, whose slice architecture this file mirrors).

  EIP-7928 AccountChanges = RLP `[address, storage_changes, storage_reads,
  balance_changes, nonce_changes, code_changes]`; each of the three value
  fields (items 3/4/5) is a list of `[block_access_index, value]` tuples and
  the account's FINAL value for the field is the `value` of the LAST tuple.
  The routine materialises, into the 80-byte out block:

    +0  has_balance   +8  post_balance (32 B big-endian, right-aligned)
    +40 has_nonce     +48 post_nonce (u64)
    +56 has_code      +64 code_off (relative to a0)   +72 code_len

  Architecture (within-level, additive — no `Ast`/`Vc`/`StmtSound` changes):

  * the routine is EXACTLY an `AbiFrame.abiFrameProg` instance (kernel-checked
    below): `addi sp,sp,-80` + 6 saves (ra,s0,s1,s2,s3,s4), a 177-instruction
    body, the shared 6-load epilogue + `ret` — so `abiFrame_spec` discharges
    the frame and the whole obligation is the BODY triple; the body's four
    stack spill slots (`48/56/64/72(sp)`) are caller-supplied `memOwn` dwords
    below the entry `sp` (they are NOT part of the frame descriptor);
  * the body's callees are `rlp_walk_init` / `rlp_walk_next` /
    `rlp_content_to_u64` / `rlp_content_to_u256_be` only — all four already
    verified within-level — composed at each `jal` site via `WP.cpsCallWithin`
    (the 24 call-site adapters in §4);
  * loop shapes (fed to bead .70.4): the three find-last-tuple loops
    (slots 55–65 / 102–112 / 148–158) are the SAME 11-instruction head-test
    whileBreak shape at three stations — head `beq t0,t1` exits to the
    station's tuple-parse block, body = `rlp_walk_next` call + span capture +
    `j` back — with every parse-fail branch a straight branch into the shared
    reject stub (slot 183, `li a0,1`, falling through to the epilogue), and
    the success stub (slots 181–182) is `liJumpTailProg [(a0,0)] (+8)` jumping
    over it — the jump-join tail shape (PR #10115).

  Program geometry (instruction slots, byte offset = 4·slot):

     0      addi sp, sp, -80
     1–6    sd ra/s0/s1/s2/s3/s4, 0/8/16/24/32/40(sp)
     7–9    mv s0,a0 ; mv s1,a1 ; mv s2,a2
    10–19   sd x0 → 0/40/56/64/72/8/16/24/32/48(s2)   (zero the out block)
    20–21   mv a0,s0 ; mv a1,s1
    22      jal rlp_walk_init            (AccountChanges outer list)
    23      bnez a2 → 183
    24–25   sd a0→48(sp) ; sd a1→56(sp)  (outer cursor / end spills)
    26–28   ld ; ld ; jal rlp_walk_next  (item 0 = address; 29 bnez a1 → 183)
    30–34   sd ; ld ; ld ; jal ; bnez    (item 1 = storage_changes)
    35–39   …                            (item 2 = storage_reads)
    40–44   …                            (item 3 = balance_changes)
    45      sd a0→48(sp)
    46–47   sub s3,a0,a2 ; mv s4,a2      (balance_changes span start / span)
    48–50   mv ; mv ; jal rlp_walk_init  (into balance_changes; 51 bnez → 183)
    52      beq a0,a1 → 88               (empty list: skip, has_balance stays 0)
    53–54   sd a0→64(sp) ; sd a1→72(sp)  (tuple cursor / end spills)
    55–57   ld t0,64(sp) ; ld t1,72(sp) ; beq t0,t1 → 66   (FIND-LAST HEAD 1)
    58–61   mv ; mv ; jal rlp_walk_next ; bnez a1 → 183
    62–64   sd a0→64(sp) ; sub s3,a0,a2 ; mv s4,a2         (span capture)
    65      j 55                                            (back edge)
    66–68   mv ; mv ; jal rlp_walk_init  (into the LAST tuple; 69 bnez → 183)
    70–75   sd;sd;ld;ld ; jal rlp_walk_next ; bnez   (tuple item 0 = index)
    76–80   sd;ld;ld ; jal rlp_walk_next ; bnez      (tuple item 1 = value)
    81–83   sub a0,a0,a2 ; mv a1,a2 ; addi a2,s2,8   (value content → out+8)
    84–85   jal rlp_content_to_u256_be ; bnez a0 → 183
    86–87   li t0,1 ; sd t0→0(s2)                    (has_balance := 1)
    88–91   ld;ld ; jal rlp_walk_next ; bnez         (item 4 = nonce_changes)
    92–98   sd ; sub/mv ; mv/mv ; jal rlp_walk_init ; bnez
    99      beq a0,a1 → 135              (empty list: skip, has_nonce stays 0)
   100–112  spills + FIND-LAST loop 2 (head 102–104, back edge 112)
   113–116  mv;mv ; jal rlp_walk_init ; bnez         (into the LAST tuple)
   117–127  tuple items 0/1 via rlp_walk_next (fails → 183)
   128–131  sub;mv ; jal rlp_content_to_u64 ; bnez a1 → 183
   132–134  sd a0→48(s2) ; li t0,1 ; sd t0→40(s2)    (post_nonce / has_nonce)
   135–138  ld;ld ; jal rlp_walk_next ; bnez         (item 5 = code_changes)
   139–144  sub/mv ; mv/mv ; jal rlp_walk_init ; bnez
   145      beq a0,a1 → 181              (empty list: SUCCESS, has_code stays 0)
   146–158  spills + FIND-LAST loop 3 (head 148–150, back edge 158)
   159–162  mv;mv ; jal rlp_walk_init ; bnez
   163–174  tuple items 0/1 via rlp_walk_next (fails → 183)
   175–176  sub x29,a0,a2 ; sub x29,x29,s0           (code_off relative to a0)
   177–180  sd x29→64(s2) ; sd a2→72(s2) ; li t0,1 ; sd t0→56(s2)
   181–182  li a0,0 ; j +8               (success stub = liJumpTailProg)
   183      li a0,1                      (reject stub; falls through)
   184–189  ld ra/s0/s1/s2/s3/s4 ; 190 addi sp,sp,80
   191      ret
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.RetFromLoop
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.AccumLoop
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.RLP.ContentToU256Be
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-! ## §1  Geometry: the routine IS an `abiFrameProg` instance -/

/-- The emitted program at `List Instr` (the `Program` alias is a plain `def`,
    opaque to `GetElem`). -/
def bansfProg : List Instr := balAccountNonstorageFinals_prog

/-- The ABI frame descriptor: `ra` at 0, then s0/s1/s2/s3/s4. -/
def bansfFrame : FrameDesc :=
  [((.x1 : Reg), (0 : BitVec 12)), (.x8, 8), (.x9, 16), (.x18, 24),
   (.x19, 32), (.x20, 40)]

/-- The 177-instruction body between the prologue and the shared epilogue. -/
def bansfBody : List Instr := (bansfProg.drop 7).take 177

/-- **The frame decomposition** — the whole routine is byte-for-byte an
    `abiFrameProg` instance, so `abiFrame_spec` owns the frame reasoning.
    The body's `48/56/64/72(sp)` spill slots are NOT frame slots: they are
    caller-supplied `memOwn` dwords threaded through the body pre/post. -/
theorem bansf_prog_eq_abiFrame :
    bansfProg = abiFrameProg (-80 : BitVec 12) (80 : BitVec 12) bansfFrame bansfBody := by
  decide +kernel

#guard bansfProg.length = 192
#guard bansfBody.length = 177

-- Station / loop / stub geometry pins (relative slots; byte offsets in the
-- branch immediates are 4× these).
-- Every parse-fail branch lands on the shared reject stub (slot 183).
#guard bansfProg[23]? = some (.BNE .x12 .x0 (640 : BitVec 13))
#guard 4 * 23 + 640 = 4 * 183
#guard bansfProg[29]? = some (.BNE .x11 .x0 (616 : BitVec 13))
#guard 4 * 29 + 616 = 4 * 183
#guard bansfProg[34]? = some (.BNE .x11 .x0 (596 : BitVec 13))
#guard 4 * 34 + 596 = 4 * 183
#guard bansfProg[39]? = some (.BNE .x11 .x0 (576 : BitVec 13))
#guard 4 * 39 + 576 = 4 * 183
#guard bansfProg[44]? = some (.BNE .x11 .x0 (556 : BitVec 13))
#guard 4 * 44 + 556 = 4 * 183
#guard bansfProg[51]? = some (.BNE .x12 .x0 (528 : BitVec 13))
#guard 4 * 51 + 528 = 4 * 183
#guard bansfProg[61]? = some (.BNE .x11 .x0 (488 : BitVec 13))
#guard 4 * 61 + 488 = 4 * 183
#guard bansfProg[69]? = some (.BNE .x12 .x0 (456 : BitVec 13))
#guard 4 * 69 + 456 = 4 * 183
#guard bansfProg[75]? = some (.BNE .x11 .x0 (432 : BitVec 13))
#guard 4 * 75 + 432 = 4 * 183
#guard bansfProg[80]? = some (.BNE .x11 .x0 (412 : BitVec 13))
#guard 4 * 80 + 412 = 4 * 183
#guard bansfProg[85]? = some (.BNE .x10 .x0 (392 : BitVec 13))
#guard 4 * 85 + 392 = 4 * 183
#guard bansfProg[91]? = some (.BNE .x11 .x0 (368 : BitVec 13))
#guard 4 * 91 + 368 = 4 * 183
#guard bansfProg[98]? = some (.BNE .x12 .x0 (340 : BitVec 13))
#guard 4 * 98 + 340 = 4 * 183
#guard bansfProg[108]? = some (.BNE .x11 .x0 (300 : BitVec 13))
#guard 4 * 108 + 300 = 4 * 183
#guard bansfProg[116]? = some (.BNE .x12 .x0 (268 : BitVec 13))
#guard 4 * 116 + 268 = 4 * 183
#guard bansfProg[122]? = some (.BNE .x11 .x0 (244 : BitVec 13))
#guard 4 * 122 + 244 = 4 * 183
#guard bansfProg[127]? = some (.BNE .x11 .x0 (224 : BitVec 13))
#guard 4 * 127 + 224 = 4 * 183
#guard bansfProg[131]? = some (.BNE .x11 .x0 (208 : BitVec 13))
#guard 4 * 131 + 208 = 4 * 183
#guard bansfProg[138]? = some (.BNE .x11 .x0 (180 : BitVec 13))
#guard 4 * 138 + 180 = 4 * 183
#guard bansfProg[144]? = some (.BNE .x12 .x0 (156 : BitVec 13))
#guard 4 * 144 + 156 = 4 * 183
#guard bansfProg[154]? = some (.BNE .x11 .x0 (116 : BitVec 13))
#guard 4 * 154 + 116 = 4 * 183
#guard bansfProg[162]? = some (.BNE .x12 .x0 (84 : BitVec 13))
#guard 4 * 162 + 84 = 4 * 183
#guard bansfProg[168]? = some (.BNE .x11 .x0 (60 : BitVec 13))
#guard 4 * 168 + 60 = 4 * 183
#guard bansfProg[174]? = some (.BNE .x11 .x0 (36 : BitVec 13))
#guard 4 * 174 + 36 = 4 * 183
-- Empty-field skips: balance → nonce station (88), nonce → code station (135),
-- code → SUCCESS stub (181).
#guard bansfProg[52]? = some (.BEQ .x10 .x11 (144 : BitVec 13))
#guard 4 * 52 + 144 = 4 * 88
#guard bansfProg[99]? = some (.BEQ .x10 .x11 (144 : BitVec 13))
#guard 4 * 99 + 144 = 4 * 135
#guard bansfProg[145]? = some (.BEQ .x10 .x11 (144 : BitVec 13))
#guard 4 * 145 + 144 = 4 * 181
-- The three find-last-tuple loops: head test + exit + back edge (the SAME
-- 11-instruction shape at three stations).
#guard bansfProg[57]? = some (.BEQ .x5 .x6 (36 : BitVec 13))
#guard 4 * 57 + 36 = 4 * 66
#guard bansfProg[65]? = some (.JAL .x0 (-40 : BitVec 21))
#guard 4 * 65 - 40 = 4 * 55
#guard bansfProg[104]? = some (.BEQ .x5 .x6 (36 : BitVec 13))
#guard 4 * 104 + 36 = 4 * 113
#guard bansfProg[112]? = some (.JAL .x0 (-40 : BitVec 21))
#guard 4 * 112 - 40 = 4 * 102
#guard bansfProg[150]? = some (.BEQ .x5 .x6 (36 : BitVec 13))
#guard 4 * 150 + 36 = 4 * 159
#guard bansfProg[158]? = some (.JAL .x0 (-40 : BitVec 21))
#guard 4 * 158 - 40 = 4 * 148
-- The three loop bodies are literally IDENTICAL instruction windows modulo
-- the `jal` immediate (same station shape; feeds the parameterized loop fold).
#guard (bansfProg.drop 55).take 5 = (bansfProg.drop 102).take 5
#guard (bansfProg.drop 102).take 5 = (bansfProg.drop 148).take 5
-- The success stub IS the jump-join tail combinator's byte shape, jumping
-- over the reject stub into the shared epilogue.
#guard (bansfProg.drop 181).take 3
  = liJumpTailProg [((.x10 : Reg), (0 : Word))] (8 : BitVec 21) ++ [.LI .x10 (1 : Word)]
#guard 4 * 182 + 8 = 4 * 184
-- Exactly ONE ret; the shared epilogue starts at slot 184.
#guard (bansfProg.filter
  (fun i => i = Instr.JALR .x0 .x1 (0 : BitVec 12))).length = 1
#guard bansfProg[184]? = some (.LD .x1 .x2 (0 : BitVec 12))
#guard bansfProg[191]? = some (.JALR .x0 .x1 (0 : BitVec 12))

/-! ## §2  The genuine functional spec

    Stated against the SAME abstractions the verified callees export —
    `rlpItemDecode` (WalkNext.lean) for per-item parses, `EL.RLP.Nat.fromBytesBE`
    (ContentToU64) for the nonce scalar, and the right-aligned big-endian
    32-byte image (ContentToU256Be's `copyN` post) for the balance. -/

/-- RLP list-header size for a LIST item whose prefix byte is `b`
    (`0xc0 ≤ b`): one prefix byte for the short form, `1 + (b - 0xf7)`
    header bytes for the long form.  The content window of a list item
    spanning `[off, off + span)` is `[off + listHeaderSize b, off + span)` —
    exactly the cursor/end pair `rlp_walk_init` yields on its success arms. -/
def listHeaderSize (b : BitVec 8) : Nat :=
  if b.toNat < 0xf8 then 1 else 1 + (b.toNat - 0xf7)

/-- Walking items from byte offset `off` (cursor `base + off`) up to
    `endPtr`, the LAST item's decode is `(next, len)` — i.e. the span the
    routine's find-last loop leaves in `s3 = next - len` / `s4 = len`.
    Terminates because `rlpItemDecode` forces the cursor to advance. -/
inductive LastItemAt (bytes : List (BitVec 8)) (base endPtr : Word) :
    Nat → Word → Word → Prop
  | last (off : Nat) (next len : Word)
      (hitem : rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len)
      (hend : next = endPtr) :
      LastItemAt bytes base endPtr off next len
  | step (off : Nat) (next len next' len' : Word)
      (hitem : rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len)
      (hne : next ≠ endPtr)
      (hrest : LastItemAt bytes base endPtr (next - base).toNat next' len') :
      LastItemAt bytes base endPtr off next' len'

/-- The `[block_access_index, value]` tuple parse the routine performs on the
    last tuple's span `[tOff, tOff + tSpan)`: descend past the tuple's list
    header, decode item 0 (the index, skipped) then item 1 (the value); the
    value's CONTENT window is `[(vNext - vLen - base).toNat, … + vLen)` —
    exactly the `sub a0,a0,a2 ; mv a1,a2` window handed to the content
    parsers. -/
def TupleValueWindow (bytes : List (BitVec 8)) (base : Word)
    (tOff tSpan : Nat) (vNext vLen : Word) : Prop :=
  ∃ b : BitVec 8, bytes[tOff]? = some b ∧
    ∃ iNext iLen : Word,
      rlpItemDecode bytes (tOff + listHeaderSize b)
        (base + BitVec.ofNat 64 (tOff + listHeaderSize b))
        (base + BitVec.ofNat 64 (tOff + tSpan)) iNext iLen ∧
      rlpItemDecode bytes (iNext - base).toNat iNext
        (base + BitVec.ofNat 64 (tOff + tSpan)) vNext vLen

/-- Per-field finals semantics (EIP-7928 "last tuple wins"), for the field
    list item spanning `[fOff, fOff + fSpan)` inside the AccountChanges
    bytes: either the field's tuple list is EMPTY (`none` — the routine
    leaves `has_* = 0`), or the value content window of the LAST tuple is
    `(vNext, vLen)` (`some` — the routine parses/records it). -/
inductive FieldFinal (bytes : List (BitVec 8)) (base : Word)
    (fOff fSpan : Nat) : Option (Word × Word) → Prop
  | empty (b : BitVec 8)
      (hb : bytes[fOff]? = some b)
      (hempty : fOff + listHeaderSize b = fOff + fSpan) :
      FieldFinal bytes base fOff fSpan none
  | last (b : BitVec 8) (tNext tSpan vNext vLen : Word)
      (hb : bytes[fOff]? = some b)
      (hne : fOff + listHeaderSize b ≠ fOff + fSpan)
      (hlast : LastItemAt bytes base (base + BitVec.ofNat 64 (fOff + fSpan))
        (fOff + listHeaderSize b) tNext tSpan)
      (hval : TupleValueWindow bytes base (tNext - tSpan - base).toNat
        tSpan.toNat vNext vLen) :
      FieldFinal bytes base fOff fSpan (some (vNext, vLen))

/-- The abstract result the routine materialises in the out block. -/
structure FinalsOut where
  hasBalance : Bool
  /-- 32-byte right-aligned big-endian post-balance image (all-zero when
      `hasBalance = false`). -/
  balanceBE  : List (BitVec 8)
  hasNonce   : Bool
  /-- `EL.RLP.Nat.fromBytesBE` of the nonce value content (0 when absent). -/
  nonce      : Word
  hasCode    : Bool
  /-- Byte offset of the final code content RELATIVE to the AccountChanges
      base pointer (0 when absent). -/
  codeOff    : Word
  /-- Byte length of the final code content (0 when absent). -/
  codeLen    : Word

/-- The all-absent result (what the pre-zeroed out block encodes). -/
def FinalsOut.absent : FinalsOut :=
  { hasBalance := false, balanceBE := List.replicate 32 0, hasNonce := false,
    nonce := 0, hasCode := false, codeOff := 0, codeLen := 0 }

/-- One value field resolves to its `FinalsOut` components: an empty field
    list leaves `(false, defaults)`; a last-tuple value window `(vNext, vLen)`
    yields `true` plus the field-specific image of the content bytes
    `[(vNext - vLen - base).toNat, (vNext - base).toNat)`. -/
def fieldResolves (bytes : List (BitVec 8)) (base : Word) (fOff fSpan : Nat)
    (has : Bool) (imageOf : Word → Word → Prop) : Prop :=
  (has = false ∧ FieldFinal bytes base fOff fSpan none) ∨
  (has = true ∧ ∃ vNext vLen,
    FieldFinal bytes base fOff fSpan (some (vNext, vLen)) ∧ imageOf vNext vLen)

/-- **The success derivation** (the genuine post of the end-to-end triple,
    against EIP-7928 semantics): the AccountChanges WINDOW `[base, base+aLen)`
    (the routine's `(a0, a1)` arguments; `bytes` is the owned region, which
    may extend past the window — the walkers need header-read slack) decodes
    as an RLP list whose items 0..5 chain by `rlpItemDecode`; items 3/4/5
    (balance/nonce/code changes) each resolve per `fieldResolves` with the
    field-specific value image —

    * balance: the 32-byte right-aligned big-endian image of the value
      content (`rlp_content_to_u256_be`'s `copyN` success post);
    * nonce: `EL.RLP.Nat.fromBytesBE` of the value content
      (`rlp_content_to_u64`'s success post);
    * code: the recorded `(code_off, code_len)` window equals the value
      content window, `code_off` stated relative to the AccountChanges base. -/
def FinalsDerivation (bytes : List (BitVec 8)) (base : Word) (aLen : Nat)
    (out : FinalsOut) : Prop :=
  ∃ b0 : BitVec 8, bytes[0]? = some b0 ∧
  ∃ n0 l0 n1 l1 n2 l2 n3 l3 n4 l4 n5 l5 : Word,
    -- the six outer items, chained from the outer list's content start
    rlpItemDecode bytes (listHeaderSize b0)
      (base + BitVec.ofNat 64 (listHeaderSize b0))
      (base + BitVec.ofNat 64 aLen) n0 l0 ∧
    rlpItemDecode bytes (n0 - base).toNat n0
      (base + BitVec.ofNat 64 aLen) n1 l1 ∧
    rlpItemDecode bytes (n1 - base).toNat n1
      (base + BitVec.ofNat 64 aLen) n2 l2 ∧
    rlpItemDecode bytes (n2 - base).toNat n2
      (base + BitVec.ofNat 64 aLen) n3 l3 ∧
    rlpItemDecode bytes (n3 - base).toNat n3
      (base + BitVec.ofNat 64 aLen) n4 l4 ∧
    rlpItemDecode bytes (n4 - base).toNat n4
      (base + BitVec.ofNat 64 aLen) n5 l5 ∧
    -- item 3 = balance_changes: 32-byte right-aligned BE image
    fieldResolves bytes base (n3 - l3 - base).toNat l3.toNat out.hasBalance
      (fun vNext vLen =>
        out.balanceBE = copyN (List.replicate 32 (0 : BitVec 8)) bytes
          (32 - vLen.toNat) (vNext - vLen - base).toNat vLen.toNat ∧
        vLen.toNat ≤ 32) ∧
    (out.hasBalance = false → out.balanceBE = List.replicate 32 0) ∧
    -- item 4 = nonce_changes: fromBytesBE scalar
    fieldResolves bytes base (n4 - l4 - base).toNat l4.toNat out.hasNonce
      (fun vNext vLen =>
        out.nonce = BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
          ((bytes.drop (vNext - vLen - base).toNat).take vLen.toNat)) ∧
        vLen.toNat ≤ 8) ∧
    (out.hasNonce = false → out.nonce = 0) ∧
    -- item 5 = code_changes: recorded content window, offset relative to base
    fieldResolves bytes base (n5 - l5 - base).toNat l5.toNat out.hasCode
      (fun vNext vLen =>
        out.codeOff = vNext - vLen - base ∧ out.codeLen = vLen) ∧
    (out.hasCode = false → out.codeOff = 0 ∧ out.codeLen = 0)

/-! ### §2.1  Anti-vacuity witness

    The derivation is inhabited: the minimal AccountChanges
    `[0xc6, 0x80, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0]` (empty address, five empty
    field lists) derives the all-absent result.  Stated at the concrete base
    `0` so every `rlpItemDecode` obligation is a closed decidable
    proposition. -/

/-- `[0xc6, 0x80, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0]`: the minimal AccountChanges
    with empty address and five empty field lists. -/
def witnessBytes : List (BitVec 8) := [0xc6, 0x80, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0]

/-- The derivation accepts the minimal witness with the all-absent result —
    the pre is satisfiable and the post is not vacuous. -/
theorem finalsDerivation_witness :
    FinalsDerivation witnessBytes 0 7 FinalsOut.absent := by
  refine ⟨0xc6, rfl, 2, 0, 3, 1, 4, 1, 5, 1, 6, 1, 7, 1,
    ⟨0x80, rfl, by decide⟩, ⟨0xc0, rfl, by decide⟩, ⟨0xc0, rfl, by decide⟩,
    ⟨0xc0, rfl, by decide⟩, ⟨0xc0, rfl, by decide⟩, ⟨0xc0, rfl, by decide⟩,
    ?_, fun _ => rfl, ?_, fun _ => rfl, ?_, fun _ => ⟨rfl, rfl⟩⟩
  · exact Or.inl ⟨rfl, by
      show FieldFinal witnessBytes 0 ((5 - 1 - 0 : Word)).toNat ((1 : Word)).toNat none
      have h1 : ((5 - 1 - 0 : Word)).toNat = 4 := by decide
      have h2 : ((1 : Word)).toNat = 1 := by decide
      rw [h1, h2]
      exact FieldFinal.empty 0xc0 rfl (by decide)⟩
  · exact Or.inl ⟨rfl, by
      show FieldFinal witnessBytes 0 ((6 - 1 - 0 : Word)).toNat ((1 : Word)).toNat none
      have h1 : ((6 - 1 - 0 : Word)).toNat = 5 := by decide
      have h2 : ((1 : Word)).toNat = 1 := by decide
      rw [h1, h2]
      exact FieldFinal.empty 0xc0 rfl (by decide)⟩
  · exact Or.inl ⟨rfl, by
      show FieldFinal witnessBytes 0 ((7 - 1 - 0 : Word)).toNat ((1 : Word)).toNat none
      have h1 : ((7 - 1 - 0 : Word)).toNat = 6 := by decide
      have h2 : ((1 : Word)).toNat = 1 := by decide
      rw [h1, h2]
      exact FieldFinal.empty 0xc0 rfl (by decide)⟩


/-! ## §3  The verdict stubs

    Both stubs end at the shared epilogue entry (slot 184, `base + 736`) —
    the BODY exit in the `abiFrame_spec` architecture, so these are plain
    two/one instruction triples, not `ret`-reaching tails. -/

/-- The success stub (slots 181–182): `li a0, 0 ; j +8` jumps over the
    reject stub into the shared epilogue with the verdict pinned. -/
theorem bansf_successTail_spec (base vOld : Word)
    (hbound : 4 * bansfProg.length < 2 ^ 64) :
    cpsTripleWithin 2 (base + 724) (base + 736)
      (CodeReq.ofProg base bansfProg)
      ((.x10 : Reg) ↦ᵣ vOld) ((.x10 : Reg) ↦ᵣ (0 : Word)) := by
  have hli := liftCode (cr' := CodeReq.ofProg base bansfProg)
    (li_spec_gen_within .x10 vOld (0 : Word) (base + 724) (by decide))
    (CodeReq.ofProg_mem_at base (base + 724) bansfProg 181 (.LI .x10 (0 : Word))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 724 + 4 = base + 728 from by bv_omega] at hli
  have hjal := liftCode (cr' := CodeReq.ofProg base bansfProg)
    (jal_x0_spec_gen_within (8 : BitVec 21) (base + 728))
    (CodeReq.ofProg_mem_at base (base + 728) bansfProg 182 (.JAL .x0 (8 : BitVec 21))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 728 + signExtend21 (8 : BitVec 21) = base + 736 from by
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
    bv_omega] at hjal
  have hjalF := cpsTripleWithin_frameL ((.x10 : Reg) ↦ᵣ (0 : Word))
    pcFree_regIs hjal
  rw [sepConj_emp_right'] at hjalF
  exact cpsTripleWithin_seq_same_cr hli hjalF

/-- The reject stub (slot 183): `li a0, 1`, falling through into the shared
    epilogue with the verdict pinned. -/
theorem bansf_rejectTail_spec (base vOld : Word)
    (hbound : 4 * bansfProg.length < 2 ^ 64) :
    cpsTripleWithin 1 (base + 732) (base + 736)
      (CodeReq.ofProg base bansfProg)
      ((.x10 : Reg) ↦ᵣ vOld) ((.x10 : Reg) ↦ᵣ (1 : Word)) := by
  have hli := liftCode (cr' := CodeReq.ofProg base bansfProg)
    (li_spec_gen_within .x10 vOld (1 : Word) (base + 732) (by decide))
    (CodeReq.ofProg_mem_at base (base + 732) bansfProg 183 (.LI .x10 (1 : Word))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 732 + 4 = base + 736 from by bv_omega] at hli
  exact hli


/-! ## §4  Concrete linkage: code requirement, call-site adapters

    Everything below is at the CONCRETE linked base
    (`GuestAddrs.bal_account_nonstorage_finals`) — the four verified callees
    live at fixed entries, so the `jal` offsets, code-range disjointness, and
    subsumption embeddings are all kernel-decided. -/

/-- Concrete routine/callee entries. -/
abbrev B : Word := (GuestAddrs.bal_account_nonstorage_finals : Word)
abbrev WI : Word := (GuestAddrs.rlp_walk_init : Word)
abbrev WN : Word := (GuestAddrs.rlp_walk_next : Word)
abbrev C6 : Word := (GuestAddrs.rlp_content_to_u64 : Word)
abbrev CB : Word := (GuestAddrs.rlp_content_to_u256_be : Word)

/-- The routine's full code requirement: its own bytes plus the four verified
    callees at their linked entries. -/
def bansfCR : CodeReq :=
  (CodeReq.ofProg B bansfProg).union
    ((rlp_walk_init_code WI).union
      ((rlp_walk_next_code WN).union
        ((rlp_content_to_u64_code C6).union (rlp_content_to_u256_be_code CB))))

-- The routine's bytes never shadow the callees, and the callees occupy
-- pairwise separated ranges.
theorem bansf_prog_disj_walkInit :
    (CodeReq.ofProg B bansfProg).Disjoint (rlp_walk_init_code WI) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bansf_prog_disj_walkNext :
    (CodeReq.ofProg B bansfProg).Disjoint (rlp_walk_next_code WN) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bansf_prog_disj_ctu64 :
    (CodeReq.ofProg B bansfProg).Disjoint (rlp_content_to_u64_code C6) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bansf_prog_disj_ctu256 :
    (CodeReq.ofProg B bansfProg).Disjoint (rlp_content_to_u256_be_code CB) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bansf_walkInit_disj_walkNext :
    (rlp_walk_init_code WI).Disjoint (rlp_walk_next_code WN) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bansf_walkInit_disj_ctu64 :
    (rlp_walk_init_code WI).Disjoint (rlp_content_to_u64_code C6) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bansf_walkInit_disj_ctu256 :
    (rlp_walk_init_code WI).Disjoint (rlp_content_to_u256_be_code CB) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bansf_walkNext_disj_ctu64 :
    (rlp_walk_next_code WN).Disjoint (rlp_content_to_u64_code C6) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bansf_walkNext_disj_ctu256 :
    (rlp_walk_next_code WN).Disjoint (rlp_content_to_u256_be_code CB) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bansf_ctu64_disj_ctu256 :
    (rlp_content_to_u64_code C6).Disjoint (rlp_content_to_u256_be_code CB) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Call-site adapter for the `jal rlp_walk_init` at slot 22 (`B + 88`). -/
theorem bansf_callSite22_walk_init {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 88 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 88 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 88) (B + 88 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 88) (calleeEntry := WI) (vOld := vRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 88))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 88) bansfProg 22 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkInit
      (fun a i h => CodeReq.union_mono_left a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 28 (`B + 112`). -/
theorem bansf_callSite28_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 112 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 112 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 112) (B + 112 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 112) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 112))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 112) bansfProg 28 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 33 (`B + 132`). -/
theorem bansf_callSite33_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 132 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 132 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 132) (B + 132 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 132) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 132))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 132) bansfProg 33 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 38 (`B + 152`). -/
theorem bansf_callSite38_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 152 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 152 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 152) (B + 152 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 152) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 152))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 152) bansfProg 38 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 43 (`B + 172`). -/
theorem bansf_callSite43_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 172 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 172 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 172) (B + 172 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 172) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 172))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 172) bansfProg 43 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_init` at slot 50 (`B + 200`). -/
theorem bansf_callSite50_walk_init {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 200 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 200 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 200) (B + 200 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 200) (calleeEntry := WI) (vOld := vRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 200))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 200) bansfProg 50 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkInit
      (fun a i h => CodeReq.union_mono_left a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 60 (`B + 240`). -/
theorem bansf_callSite60_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 240 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 240 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 240) (B + 240 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 240) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 240))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 240) bansfProg 60 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_init` at slot 68 (`B + 272`). -/
theorem bansf_callSite68_walk_init {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 272 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 272 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 272) (B + 272 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 272) (calleeEntry := WI) (vOld := vRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 272))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 272) bansfProg 68 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkInit
      (fun a i h => CodeReq.union_mono_left a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 74 (`B + 296`). -/
theorem bansf_callSite74_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 296 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 296 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 296) (B + 296 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 296) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 296))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 296) bansfProg 74 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 79 (`B + 316`). -/
theorem bansf_callSite79_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 316 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 316 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 316) (B + 316 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 316) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 316))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 316) bansfProg 79 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_content_to_u256_be` at slot 84 (`B + 336`). -/
theorem bansf_callSite84_content_to_u256_be {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n CB ((B + 336 + 4) &&& ~~~(1 : Word))
      (rlp_content_to_u256_be_code CB) ((.x1 ↦ᵣ (B + 336 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 336) (B + 336 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 336) (calleeEntry := CB) (vOld := vRa)
    (calleeCode := rlp_content_to_u256_be_code CB) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.bal_account_nonstorage_finals + 336))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 336) bansfProg 84 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_ctu256
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_ctu256
        (fun a i h => CodeReq.mono_union_right bansf_walkNext_disj_ctu256
          (fun a i h => CodeReq.mono_union_right bansf_ctu64_disj_ctu256
            (fun _ _ hh => hh) a i h) a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 90 (`B + 360`). -/
theorem bansf_callSite90_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 360 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 360 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 360) (B + 360 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 360) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 360))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 360) bansfProg 90 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_init` at slot 97 (`B + 388`). -/
theorem bansf_callSite97_walk_init {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 388 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 388 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 388) (B + 388 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 388) (calleeEntry := WI) (vOld := vRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 388))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 388) bansfProg 97 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkInit
      (fun a i h => CodeReq.union_mono_left a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 107 (`B + 428`). -/
theorem bansf_callSite107_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 428 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 428 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 428) (B + 428 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 428) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 428))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 428) bansfProg 107 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_init` at slot 115 (`B + 460`). -/
theorem bansf_callSite115_walk_init {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 460 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 460 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 460) (B + 460 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 460) (calleeEntry := WI) (vOld := vRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 460))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 460) bansfProg 115 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkInit
      (fun a i h => CodeReq.union_mono_left a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 121 (`B + 484`). -/
theorem bansf_callSite121_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 484 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 484 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 484) (B + 484 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 484) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 484))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 484) bansfProg 121 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 126 (`B + 504`). -/
theorem bansf_callSite126_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 504 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 504 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 504) (B + 504 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 504) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 504))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 504) bansfProg 126 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_content_to_u64` at slot 130 (`B + 520`). -/
theorem bansf_callSite130_content_to_u64 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n C6 ((B + 520 + 4) &&& ~~~(1 : Word))
      (rlp_content_to_u64_code C6) ((.x1 ↦ᵣ (B + 520 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 520) (B + 520 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 520) (calleeEntry := C6) (vOld := vRa)
    (calleeCode := rlp_content_to_u64_code C6) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.bal_account_nonstorage_finals + 520))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 520) bansfProg 130 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_ctu64
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_ctu64
        (fun a i h => CodeReq.mono_union_right bansf_walkNext_disj_ctu64
          (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 137 (`B + 548`). -/
theorem bansf_callSite137_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 548 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 548 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 548) (B + 548 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 548) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 548))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 548) bansfProg 137 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_init` at slot 143 (`B + 572`). -/
theorem bansf_callSite143_walk_init {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 572 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 572 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 572) (B + 572 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 572) (calleeEntry := WI) (vOld := vRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 572))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 572) bansfProg 143 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkInit
      (fun a i h => CodeReq.union_mono_left a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 153 (`B + 612`). -/
theorem bansf_callSite153_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 612 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 612 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 612) (B + 612 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 612) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 612))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 612) bansfProg 153 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_init` at slot 161 (`B + 644`). -/
theorem bansf_callSite161_walk_init {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 644 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 644 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 644) (B + 644 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 644) (calleeEntry := WI) (vOld := vRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 644))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 644) bansfProg 161 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkInit
      (fun a i h => CodeReq.union_mono_left a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 167 (`B + 668`). -/
theorem bansf_callSite167_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 668 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 668 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 668) (B + 668 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 668) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 668))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 668) bansfProg 167 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 173 (`B + 692`). -/
theorem bansf_callSite173_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 692 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 692 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 692) (B + 692 + 4) bansfCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 692) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 692))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 692) bansfProg 173 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bansf_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bansf_walkInit_disj_walkNext
        (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h


end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
