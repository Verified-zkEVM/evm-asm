/-
  EvmAsm.Codegen.Programs.HeaderValidatePostMergeLoopSpec

  Statement-only skeleton for the K67 re-emit on #12461 (loop reshape +
  byte-wise field compares).  This file fixes the LOOP-HEADER INVARIANT and
  the degenerate full-premise inhabitant BEFORE any emitted code changes, per
  the standing directives:

  * the invariant is stated AT the loop header, so the `i = 0` instance is
    exactly the `rlp_walk_init` success exit (no separate "entry" algebra);
  * entry vs loop-back states are NAMED ONCE here (`k67LoopEntry`,
    `k67LoopBack`) and later lemmas must not conflate them: loop-back differs
    in `x20` (index) and in `x12` (previous field's content length), and
    `x5` is clobbered until the next header reload;
  * the cycle OWNS the registers it writes (`x18`, `x19`, `x20`, and the
    `x8`/`x9` ommers capture) and FRAMES everything else;
  * `k67LoopInv_satisfiable` inhabits the FULL premise set at once -- the
    codex2 `outerHeaderInv_satisfiable` standard -- so no clause of the
    contract is vacuous by construction.

  NO emitted code, `GuestAddrs`, or registry entry is touched here; all
  addresses stay abstract.  The eventual re-emit PR (based on post-#12477
  main) folds this skeleton in and proves the cycle contract against it.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderPostMergeCorrespondence
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## Frame

The re-emitted routine keeps the existing 40-byte layout (spills of `ra`,
`x8`, `x9`, `x18`, `x19` at 0/8/16/24/32) and widens the frame to 48 bytes
to spill `x20` at slot 40.  `x20` is the LOOP INDEX holder: it must survive
`jal` into the walker, and every other callee-saved register is already
committed (`x18`/`x19` cursor/end, `x8`/`x9` ommers capture), so the index
lives on the stack.  A `.data` index cell was rejected: it would be invented
guest state with no spec counterpart.

The adapter contract in `ValidateHeaderPostMergeCorrespondence` keeps its
`x20 ↦ s4` pass-through exactly, because the epilogue RESTORES `x20` from
slot 40; only `frameSlotsOwn postMergeFrame` widens from 40 to 48 bytes
(`k67Frame` below), a mechanical edit to that (currently unconsumed) file
that the re-emit PR will flag as a contract tweak. -/

/-- K67 frame after the re-emit: 48 bytes, `x20` spilled at slot 40. -/
def k67Frame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]

def k67SavedFrame : FrameDesc :=
  [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]

/-! ## Loop-header invariant

The reshaped walk loop visits header fields 0-14 (15 iterations of
`rlp_walk_next` after one `rlp_walk_init`).  Walker ABI: `x10` cursor,
`x11` end pointer, `x12` content length; `rlp_walk_init` reports status in
`x12` and on success leaves the cursor in `x10` and the end pointer in
`x11`.

Parameters:

* `sp0` the caller's stack pointer; `spC = sp0 - 48` the allocated frame;
* `base`/`bytes` the caller-owned header RLP byte region;
* `endPtr` the walk end pointer (`base + endOff`);
* `off i` the cursor offset at the head of iteration `i` (before the
  `mv x10, x18` reload), so `x18 = base + off i`;
* `L i` the content length of field `i` reported by the field-`i` walk
  (`L 0` comes from the walk that visits field 0, etc.);
* `omEnd`/`omLen` the ommers capture taken after the field-1 walk
  (`omEnd = base + off 2`, the content end of field 1);
* `i` the loop index (0 on entry from the init exit, incremented by the
  cycle).

State the invariant as data (an `Assertion`) plus the pure window facts as
an explicit Prop conjunct, so both halves of the contract are visible to,
and checkable by, the eventual cycle lemma. -/

/-- Pure window facts pinned alongside the invariant: the cursor lives in
the header window, the end pointer is the region end, the ommers capture
sits inside the window, and content lengths are bounded by it. -/
def k67LoopWindow (bytes : List (BitVec 8)) (endOff omEnd omLen : Nat) : Prop :=
  endOff = bytes.length ∧ omEnd ≤ endOff ∧ omLen ≤ omEnd

/-- The loop-header invariant.  Owned: the frame, the durable cursor and
end registers, the index, the previous content length, the ommers capture
registers, and the two byte regions (header and the 32-byte
`empty_ommers_hash` constant).  Framed through: `x1` (dead last return
    site), `x5`/`x6`/`x7`/`x10`/`x11`/`x13`/`x14`/`x21`/`x28`-`x31` (scratch,
clobbered by the walkers; `x10`/`x11` are reloaded from `x18`/`x19` at the
head, `x5` only at the next index test -- the codex2 lesson), and `x0`. -/
def k67LoopInv (sp0 base endPtr omConst : Word) (bytes : List (BitVec 8))
    (omEnd omLen : Nat) (off : Nat → Nat) (L : Nat → Nat) (i : Nat) : Assertion :=
  (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
  (.x18 ↦ᵣ base + BitVec.ofNat 64 (off i)) **
  (.x19 ↦ᵣ endPtr) **
  (.x20 ↦ᵣ BitVec.ofNat 64 i) **
  (.x12 ↦ᵣ BitVec.ofNat 64 (L (i - 1))) **
  (if i ≤ 1 then (.x8 ↦ᵣ base) ** (.x9 ↦ᵣ BitVec.ofNat 64 bytes.length)
   else (.x8 ↦ᵣ base + BitVec.ofNat 64 omEnd) ** (.x9 ↦ᵣ BitVec.ofNat 64 omLen)) **
  regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x13 ** regOwn .x14 ** regOwn .x21 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) **
  frameSlotsOwn k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) **
  bytesRegion base bytes **
  bytesRegion omConst (List.replicate 32 (0 : BitVec 8))

/-! ## Entry vs loop-back, named once

`k67LoopEntry` is the `i = 0` instance reached from the `rlp_walk_init`
success exit: `x12` still carries the init SUCCESS status 0 (hence
`L (0 - 1) = L 0 = 0` via the truncation convention below), and `x8`/`x9`
still hold their ENTRY copies (header pointer and length).

`k67LoopBack` is the `i ≥ 1` instance at the same program point after one
cycle: `x12` now carries the PREVIOUS field's content length, and (for
`i ≥ 2`) `x8`/`x9` hold the ommers capture instead.  Lemmas about the
cycle must use these names and must not re-derive either state. -/

/-- `L` pinned for the entry instance: the init success status is 0. -/
def k67EntryL (i : Nat) : Nat := if i = 0 then 0 else i

/-- Entry instance: `i = 0`, init-exit state. -/
def k67LoopEntry (sp0 base endPtr omConst : Word)
    (bytes : List (BitVec 8)) (off : Nat → Nat) : Assertion :=
  k67LoopInv sp0 base endPtr omConst bytes bytes.length bytes.length off k67EntryL 0

/-- Loop-back instance at index `i ≥ 1`: previous-field `x12`, ommers
capture in `x8`/`x9` once past the field-1 walk. -/
def k67LoopBack (sp0 base endPtr omConst : Word) (bytes : List (BitVec 8))
    (omEnd omLen : Nat) (off : Nat → Nat) (L : Nat → Nat) (i : Nat) : Assertion :=
  k67LoopInv sp0 base endPtr omConst bytes omEnd omLen off L i

/-! ## Degenerate full-premise inhabitant

The codex2 standard: exhibit ONE concrete witness satisfying EVERY clause
of the premise set at once (frame + regions + registers + window facts),
with no new domain assumption and no `sorry`, so the contract is not
vacuous by construction.  The witness uses zeroed memory, fixed concrete
addresses, and `i = 0`. -/

theorem k67LoopInv_satisfiable :
    ∃ (sp0 base omConst endPtr : Word) (bytes : List (BitVec 8))
      (off : Nat → Nat),
      base.toNat % 8 = 0 ∧
      omConst.toNat % 8 = 0 ∧
      k67LoopWindow bytes bytes.length bytes.length bytes.length ∧
      (k67LoopInv sp0 base endPtr omConst bytes bytes.length bytes.length
          off k67EntryL 0).pcFree ∧
      sp0.toNat + 48 < 2 ^ 64 ∧
      base.toNat + bytes.length < 2 ^ 64 ∧
      omConst.toNat + 32 < 2 ^ 64 ∧
      (sp0 + signExtend12 (-48 : BitVec 12)).toNat + 48 ≤ sp0.toNat ∧
      (base.toNat + bytes.length ≤ omConst.toNat ∨
        omConst.toNat + 32 ≤ base.toNat) := by
  refine ⟨0x10000, 0x20000, 0x30000, 0x20000 + BitVec.ofNat 64 4,
    List.replicate 4 0, fun _ => 2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · unfold k67LoopWindow; omega
  · unfold k67LoopInv k67EntryL
    simp only [Nat.zero_le, if_true]
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsOwn _ _
      | exact bytesRegion_pcFree _ _
      | exact pcFree_emp
  · decide
  · decide
  · decide
  · unfold signExtend12; decide
  · decide

/-! ## Re-emission draft (statement work; pins the exact static delta)

The reshaped `headerValidatePostMerge` the eventual re-emit PR will carry.
Instruction-for-instruction draft with exact counts, so emission is a
mechanical transcription and the `.text` delta is pinned BEFORE measuring.
Base: the emitted routine retired 127 instructions / 508 bytes.

### Draft program (166 instructions, indices into the new program)

    -- prologue (7)
    [0]  ADDI x2, x2, -48
    [1]  SD   x1,  0(x2)         -- ra
    [2]  SD   x8,  8(x2)
    [3]  SD   x9, 16(x2)
    [4]  SD   x18,24(x2)
    [5]  SD   x19,32(x2)
    [6]  SD   x20,40(x2)         -- NEW: spilled loop index
    -- preheader (5)
    [7]  MV   x8, x10            -- keep entry header ptr
    [8]  MV   x9, x11            -- keep entry header len
    [9]  LI   x20, 0             -- NEW: i := 0
    [10] JAL  x1, rlp_walk_init
    [11] BNE  x12, x0, status4   -- init status (x12) != 0 -> parse fail
    -- post-init cursor (2)
    [12] MV   x18, x10           -- durable cursor
    [13] MV   x19, x11           -- invariant end pointer
    -- walk loop body (15 static instructions, head at [14])
    [14] MV   x10, x18           -- <LOOP HEAD> restore cursor
    [15] MV   x11, x19           -- restore end
    [16] JAL  x1, rlp_walk_next
    [17] BNE  x11, x0, status4   -- walk status (x11) != 0 -> parse fail
    [18] LI   x5, 1
    [19] BNE  x20, x5, +3        -- i != 1 -> skip capture (target [22])
    [20] MV   x8, x10            -- capture field-1 content end
    [21] MV   x9, x12            -- capture field-1 content len
    [22] LI   x5, 7
    [23] BNE  x20, x5, +2        -- i != 7 -> skip difficulty (target [25])
    [24] BNE  x12, x0, status1   -- difficulty content_len != 0 -> status 1
    [25] MV   x18, x10           -- commit cursor
    [26] ADDI x20, x20, 1        -- i := i + 1
    [27] LI   x5, 15
    [28] BNE  x20, x5, -56       -- i != 15 -> loop head [14]
    -- nonce tail (19): field 14 content must be 8 zero bytes
    [29] LI   x5, 8
    [30] BNE  x12, x5, status2
    [31] SUB  x6, x10, x12       -- nonce content base
    [32..47] 8x (LBU x7, k(x6); BNE x7, x0, status2)   -- k = 0..7
    -- ommers tail (101): field-1 content == empty_ommers_hash (32 bytes)
    [48] LI   x5, 32
    [49] BNE  x9, x5, status3
    [50] SUB  x6, x8, x9         -- ommers content base (header side)
    [51] AUIPC x5, ...           -- la empty_ommers_hash (constant side,
    [52] ADDI  x5, x5, ...       --   aligned .data, 32 bytes)
    [53..148] 32x (LBU x7, k(x6); LBU x28, k(x5); BNE x7, x28, status3)
    -- status tails (9, unchanged shapes; exact JAL offsets pinned at
    -- emission against the regenerated layout)
    [149..157] LI x10, s ; JAL chains for s = 0,1,2,3 ; LI x10, 4
    -- epilogue (8)
    [158..163] LD x1/x8/x9/x18/x19/x20 at 0/8/16/24/32/40(x2)
    [164] ADDI x2, x2, 48
    [165] JALR x0, x1, 0

(`LBU` destinations are always x7/x28, bases x6/x5 — destination != base,
per the generic-LBU rd=rs1 unsatisfiability warning.)

### Section count table

| section        | original | reshaped | delta |
|----------------|----------|----------|-------|
| prologue       | 6        | 7        | +1 (SD x20) |
| preheader      | 6        | 5        | -1 (identity MVs out, LI x20 in) |
| walk region    | 75       | 15       | **-60** (one static body, not 15) |
| nonce tail     | 5        | 19       | +14 (8x LBU replaces 1 LD) |
| ommers tail    | 17       | 101      | +84 (32x LBU-pairs replaces 4x LD-pairs) |
| status tails   | 9        | 9        | 0 |
| epilogue       | 8        | 8        | +1 (LD x20; ADDI ±48) |
| **total**      | **127**  | **166**  | **+39 instructions = +156 bytes** |

K67 grows 508 -> 664 bytes; every later link address shifts +156. The
relocation table shrinks 17 -> 3 (one init JAL, one next JAL, one la): one
callee-return site per callee instead of fifteen, which is what the cycle
contract consumes.

### Cycle-contract state table (vs `k67LoopInv`)

- ENTRY (i = 0, `k67LoopEntry`): reached from the init-success exit; x12 = 0
  (init success status), x8/x9 = entry header copies, x20 = 0, x18/x19 =
  post-init cursor/end. This is the i = 0 instance of the invariant.
- LOOP-BACK (i >= 1, `k67LoopBack`): after [25]-[28]; x12 = content length
  of field i-1, x8/x9 = ommers capture once i >= 2, x20 = i. x5 is clobbered
  (LI-loaded per use); x10/x11 are dead at the head (restored from x18/x19).
- EXIT (i = 15): falls through [28] with x10/x12 = last walk outputs,
  feeding the unchanged nonce/ommers tails.

Registers the cycle OWNS: x10, x11, x12 (restored/written each iteration),
x18 (cursor commit), x20 (index), x5, x6 (transient), and — on the i = 1
and i = 7 guarded edges only — x8/x9 capture and the status-1 branch.
Registers FRAMED through the walk JALs (absent from the walk specs' pre,
hence preserved): x8, x9, x18, x19, x20, x21, and the frame slots plus the
two byte regions (`bytesRegion base bytes`, `bytesRegion omConst ...`). -/
end EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec
