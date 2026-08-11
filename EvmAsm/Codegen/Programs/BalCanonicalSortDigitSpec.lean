/-
  EvmAsm.Codegen.Programs.BalCanonicalSortDigitSpec

  **`bal_canonical_sort`'s canonical nibble extractor, against a semantically
  decoded key** (GH #10817).

  ## The vacuity this defeats

  `BalCanonicalSort.lean:41-44` records why the routine shipped with no
  verification: *"sortedness plus permutation-preservation is insufficient — both
  properties hold for a sort on the wrong key: sorted-by-the-limb-swapped-key is
  still sorted, and still a permutation."* Any later sortedness theorem is
  therefore only as strong as its key, and a key read off **the sorter's own
  segment descriptor** would be no strength at all: a descriptor with two limbs
  swapped describes the swapped order, so both properties would still hold.

  So the key here is defined from the **field semantics** — `balCanonicalKey`
  concatenates each field's canonical big-endian bytes, reversing exactly the
  fields the row stores as little-endian u64 limbs — and the descriptor walk is
  then proven to **agree** with it. That agreement is what makes a later
  sortedness theorem non-vacuous, and it is the whole deliverable here.

  ⚠️ **A hand-written Lean model of the extraction would be worthless on its
  own**: it would say a model agrees with the spec, not that the *program* does.
  `RlpWalkNextStrict` was FALSE for exactly that reason — a pure relation as its
  hypothesis, the routine nowhere in the statement. So every `balDig*` theorem is
  stated over `CodeReq.ofProg base balCanonicalSort_prog` at a pc range.

  ## The slice, and why it is stated over the whole routine

  `balCanonicalDigit_prog` (`BalCanonicalSort.lean:149`, 28 instructions) is
  **flat indices 67..94** of the 147-instruction `balCanonicalSort_prog`, which is
  *defined* as `head ++ digit ++ tail` with a 67-instruction head
  (`balSortHeadLen`, `balDigit_at_67`). The digit runs
  `base + 268 → base + 380`, entered and left by **fallthrough** — no `jal`/`jalr`
  at either end. The established idiom for such a slice is
  `RlpEncodeListPrefixLoopSpec.lpLolLoop`: a `cpsTripleWithin` over the **whole**
  program's `CodeReq.ofProg` at a pc range, with no return. This module copies it.

  ## Instruction-by-instruction (verified against the `Instr` list)

  Indices are 0-based within the 28; `Bidx` is the byte offset from `base`.

  | idx | Bidx | instr | meaning |
  |---|---|---|---|
  | 0 | 268 | `SRLI x7, x22, 1` | `b := depth / 2`, the canonical BYTE index |
  | 1 | 272 | `LI x16, 0` | segment index `i := 0` |
  | 2 | 276 | `SLLI x17, x16, 4` | loop head: bit position `16 i` |
  | 3-4 | 280 | `SRL x30, x26, x17`; `ANDI x30, 255` | `off_i` = descriptor byte `2i` |
  | 5-7 | 288 | `ADDI x17, 8`; `SRL x28, x26, x17`; `ANDI x28, 127` | `w_i` = byte `2i+1` masked |
  | 8 | 300 | `BLTU x7, x28, +16` | `b < w_i` exits to idx12 (`300+16 = 316`) |
  | 9-11 | 304 | `SUB x7, x7, x28`; `ADDI x16, 1`; `JAL -36` | step; `312-36 = 276` |
  | 12-15 | 316 | recompute the width byte, `ANDI x17, 128` | test bit 7, the BE flag |
  | 16 | 332 | `BNE x17, x0, +20` | flag set (BE) goes to idx21 (`332+20 = 352`) |
  | 17-19 | 336 | `ADD x30, x30, x28`; `ADDI x30, -1`; `SUB x30, x30, x7` | LE: `k + w - 1 - b` |
  | 20 | 348 | `JAL x0, +8` | `348+8 = 356`, skipping idx21 |
  | 21 | 352 | `ADD x30, x30, x7` | BE: `k + b` |
  | 22-23 | 356 | `ADD x30, x5, x30`; `LBU x28, 0(x30)` | load `row[rowOffset]` |
  | 24-25 | 364 | `ANDI x17, x22, 1`; `BNE x17, x0, +8` | odd depth goes to idx27 (`368+8 = 376`) |
  | 26 | 372 | `SRLI x28, x28, 4` | even depth: the byte's HIGH nibble |
  | 27 | 376 | `ANDI x28, x28, 15` | mask to `0..15` |

  Register mapping (`BalCanonicalSort.lean:139-148`): in `x5` = row pointer,
  `x22` = nibble depth, `x26` = packed descriptor; out `x28` = the nibble;
  `x7 x16 x17 x30` clobbered. The docstring's `t2 t3 t5 a6 a7` is
  `x7 x28 x30 x16 x17`, so it lists `x28` as a clobber as well as the result.

  ## Step counts, and why the headline needs only one

  `cpsTripleWithin n` is an **at most `n` steps** obligation, so one bound covering
  every path is sound and the headline needs no case analysis in its statement.
  Exiting at segment `i`, the paths cost `24 + 10 i` (LE segment, even depth),
  `23 + 10 i` (LE, odd), `21 + 10 i` (BE, even) and `20 + 10 i` (BE, odd), from
  `2` (prologue) `+ 10 i` (skipped segments) `+ 7` (the exiting head) `+ 9`/`6`
  (LE/BE offset arm) `+ 2`/`1` (even/odd nibble). BE is **6 fewer per path**: that
  arm skips the three-instruction reversal and the `jal` over it.

  ## Two preconditions the program does NOT check

  1. **The byte index must lie inside the real segments.** The loop tests only
     `b < w_i` and never consults the segment count `a4`, so a `b` past the last
     real segment reads garbage width bytes off the descriptor register's high end
     and walks on. `balDigitAgree_2seg` therefore carries
     `depth.toNat < 2 * (w0 + w1)`. The runtime `s11 = 2 * keysum` cap
     (`balSortMaxDepth`, `BalCanonicalSort.lean:134`) is the operational form of
     the same bound, but it is a **fail-closed backstop, not the termination
     argument** — do not read one as the other.
  2. **Every width must be nonzero**, or `b` never decreases and the walk does not
     terminate. The unrolled form does not need it: exit at segment `i` is
     *witnessed* by `¬ b_j < w_j` for `j < i` plus `b_i < w_i`. It becomes a real
     obligation only at a symbolic trip count, which this module does not attempt;
     `balDigWidthsPos` states it so a later loop proof can cite it.

  ## Scope

  Only the extractor. **No `.Lbalsort_pop` work of any kind** — it pops a frame and
  may push successors in one iteration, so its trip count is not a bound in any
  loop variable and it has no measure yet. No sortedness and no permutation
  theorem: both *consume* this agreement. `seps_permute` is not used and must not
  be — it re-lists one atom multiset, whereas a row sort holds addresses fixed and
  changes contents, so before and after are different assertions at the same
  addresses.

  No `set_option maxRecDepth` is needed and no elaboration budget is widened.
-/
import EvmAsm.Codegen.Programs.BalCanonicalSort
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen

namespace BalCanonicalSortDigitSpec

open EvmAsm.Rv64

/-! ## Where the slice lives — pinned, not asserted in prose. Every address in
    this module is `base + 268 + 4 * idx`. -/

theorem balSortHeadLen : balCanonicalSortHead_prog.length = 67 := by decide
theorem balDigitLen : balCanonicalDigit_prog.length = 28 := by decide
theorem balSortTailLen : balCanonicalSortTail_prog.length = 52 := by decide
theorem balSortProgLen : balCanonicalSort_prog.length = 147 := by
  rw [show balCanonicalSort_prog
      = balCanonicalSortHead_prog ++ (balCanonicalDigit_prog ++ balCanonicalSortTail_prog)
      from rfl, Program.length_append, Program.length_append,
    balSortHeadLen, balDigitLen, balSortTailLen]

/-- The digit sits at index 67 of the flat program: the `drop` lands on it.
    Structural rather than a text match, and it is what makes an address
    `base + 268 + 4 * idx` an address *of the digit's* instruction. -/
theorem balDigit_at_67 :
    (balCanonicalSort_prog.drop 67).take 28 = balCanonicalDigit_prog := by
  have hdrop : List.drop 67 balCanonicalSort_prog
      = balCanonicalDigit_prog ++ balCanonicalSortTail_prog :=
    List.drop_left' (l₁ := balCanonicalSortHead_prog)
      (l₂ := balCanonicalDigit_prog ++ balCanonicalSortTail_prog) balSortHeadLen
  have htake : List.take 28 (balCanonicalDigit_prog ++ balCanonicalSortTail_prog)
      = balCanonicalDigit_prog := List.take_left' balDigitLen
  rw [hdrop, htake]

/-! ## The canonical key, defined from the field semantics

    ⭐ **Not from the descriptor.** `balCanonicalKey` renders each field
    big-endian and concatenates, most significant first — the spec's key
    (`block_access_lists.py:564,578` sorts on address and slot, canonical
    big-endian values), with no reference to the routine's walk. The two are then
    proven equal; defining the key BY the walk would make every downstream
    ordering theorem vacuous in the header's precise sense. -/

/-- One key field's semantic account: `off`/`len` locate its bytes in the row;
    `alreadyBE` says whether the row holds them canonically big-endian (as the
    builder's rows do) or as little-endian u64 limbs (an EVM stack word,
    `EvmLogHandlers.lean:74`). -/
structure BalKeyField where
  /-- Byte offset of the field inside the row. -/
  off : Nat
  /-- Significant width in bytes. -/
  len : Nat
  /-- `true` when the row already stores the field big-endian. -/
  alreadyBE : Bool
deriving Repr, DecidableEq

/-- The field's canonical bytes, most significant first: forward when the row
    already holds it big-endian, reversed when it holds little-endian limbs.
    Reversing an already-BE field would order rows by a byte-reversed field: a
    total order, a permutation, and not canonical. -/
def BalKeyField.beBytes (f : BalKeyField) (row : List (BitVec 8)) : List (BitVec 8) :=
  if f.alreadyBE then (row.drop f.off).take f.len
  else ((row.drop f.off).take f.len).reverse

/-- **The row's canonical key**: the fields' canonical big-endian bytes
    concatenated, most significant field first — address-major, slot-minor for a
    storage row, matching `block_access_lists.py:564,578`. -/
def balCanonicalKey (fs : List BalKeyField) (row : List (BitVec 8)) : List (BitVec 8) :=
  (fs.map (fun f => f.beBytes row)).flatten

/-- **Nibble `d` of a canonical key**: byte `d / 2`, the HIGH half at even `d` and
    the low half at odd `d`, so the more significant nibble is compared first.

    ⭐ Each depth is pinned to its own byte *and* its own half; a statement
    symmetric in the halves would not detect two cursors being swapped. -/
def balCanonicalNibble (key : List (BitVec 8)) (d : Nat) : Nat :=
  if d % 2 = 0 then (key.getD (d / 2) 0).toNat / 16
  else (key.getD (d / 2) 0).toNat % 16

/-- The same choice applied to an already-selected byte, so the machine lemmas can
    name the *half* without naming the key. -/
def balByteNibble (v : BitVec 8) (d : Nat) : Nat :=
  if d % 2 = 0 then v.toNat / 16 else v.toNat % 16

theorem balCanonicalNibble_eq_byte (key : List (BitVec 8)) (d : Nat) :
    balCanonicalNibble key d = balByteNibble (key.getD (d / 2) 0) d := by
  unfold balCanonicalNibble balByteNibble
  split <;> rfl

/-- The row byte the *routine* reads for byte index `b` of field `f`: forward from
    the offset for a BE field, backward from the field's last byte for an LE one.
    This is `BalCanonicalSort.lean:104-105`'s rule, written once. -/
def balRowOffset (f : BalKeyField) (b : Nat) : Nat :=
  if f.alreadyBE then f.off + b else f.off + f.len - 1 - b

/-- Every field is nonempty and fits inside the row. The routine assumes both: a
    zero width stalls the walk, and an overrunning field reads the next row. -/
def balFieldsWf (fs : List BalKeyField) (rowLen : Nat) : Prop :=
  ∀ f ∈ fs, 0 < f.len ∧ f.off + f.len ≤ rowLen

/-- ⚠️ **Nonzero widths, for a later loop-shaped proof to cite.** The unrolled
    theorems do not need it; a symbolic trip count does (`b` must decrease). -/
theorem balDigWidthsPos {fs : List BalKeyField} {rowLen : Nat}
    (h : balFieldsWf fs rowLen) : ∀ f ∈ fs, 0 < f.len := fun f hf => (h f hf).1

/-! ### The key's bytes, one field at a time

    Two lemmas, and between them they are exactly the walk: peel a field while the
    index is past it, then index inside it. Proved on the model side alone — the
    machine meets them in `balDigitAgree_*`. -/

/-! Three `List.getD` shims; core states these for `getElem?`. -/

private theorem getD_eq_getElem {α : Type _} (l : List α) (i : Nat) (a : α)
    (h : i < l.length) : l.getD i a = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

private theorem getD_append_left {α : Type _} (l₁ l₂ : List α) (i : Nat) (a : α)
    (h : i < l₁.length) : (l₁ ++ l₂).getD i a = l₁.getD i a := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

private theorem getD_append_right {α : Type _} (l₁ l₂ : List α) (i : Nat) (a : α)
    (h : l₁.length ≤ i) : (l₁ ++ l₂).getD i a = l₂.getD (i - l₁.length) a := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right h]

/-- A field's canonical bytes are as wide as the field, provided it fits. -/
theorem beBytes_length {f : BalKeyField} {row : List (BitVec 8)}
    (hf : f.off + f.len ≤ row.length) : (f.beBytes row).length = f.len := by
  have hlen : ((row.drop f.off).take f.len).length = f.len := by
    simp only [List.length_take, List.length_drop]; omega
  unfold BalKeyField.beBytes
  cases hbe : f.alreadyBE with
  | true => simpa [hbe] using hlen
  | false => simpa [hbe] using hlen

/-- **Inside the field**: byte `b` of a field's canonical bytes is the row byte the
    routine's endianness rule names — the reversal, as an equation. -/
theorem beBytes_getD {f : BalKeyField} {row : List (BitVec 8)}
    (hf : f.off + f.len ≤ row.length) {b : Nat} (hb : b < f.len) :
    (f.beBytes row).getD b 0 = row.getD (balRowOffset f b) 0 := by
  have hlen : ((row.drop f.off).take f.len).length = f.len := by
    simp only [List.length_take, List.length_drop]; omega
  have hinner : ∀ j, j < f.len →
      ((row.drop f.off).take f.len).getD j 0 = row.getD (f.off + j) 0 := by
    intro j hj
    rw [getD_eq_getElem _ _ _ (by omega), getD_eq_getElem _ _ _ (by omega),
      List.getElem_take, List.getElem_drop]
  unfold BalKeyField.beBytes balRowOffset
  cases hbe : f.alreadyBE with
  | true => simpa [hbe] using hinner b hb
  | false =>
    have hrev : (((row.drop f.off).take f.len).reverse).getD b 0
        = ((row.drop f.off).take f.len).getD (f.len - 1 - b) 0 := by
      rw [getD_eq_getElem _ _ _ (by rw [List.length_reverse, hlen]; omega),
        getD_eq_getElem _ _ _ (by omega), List.getElem_reverse]
      congr 1
      omega
    have hstep := hinner (f.len - 1 - b) (by omega)
    have hshift : f.off + (f.len - 1 - b) = f.off + f.len - 1 - b := by omega
    simp only [Bool.false_eq_true, if_false]
    rw [hrev, hstep, hshift]

/-- **Index inside the leading field**: below the first field's width, the key's
    byte is that field's, at the routine's row offset. -/
theorem balCanonicalKey_getD_head (f : BalKeyField) (fs : List BalKeyField)
    (row : List (BitVec 8)) (hf : f.off + f.len ≤ row.length) {b : Nat}
    (hb : b < f.len) :
    (balCanonicalKey (f :: fs) row).getD b 0 = row.getD (balRowOffset f b) 0 := by
  have hlen := beBytes_length (f := f) (row := row) hf
  have hkey : balCanonicalKey (f :: fs) row
      = f.beBytes row ++ balCanonicalKey fs row := by
    simp [balCanonicalKey]
  rw [hkey, getD_append_left _ _ _ _ (by omega), beBytes_getD hf hb]

/-- **Peel the leading field**: at or past its width, the key's byte is the rest's
    byte at the index shifted down — the walk's `sub t2, t2, t3`
    (`BalCanonicalSort.lean:159`), on the model side. -/
theorem balCanonicalKey_getD_tail (f : BalKeyField) (fs : List BalKeyField)
    (row : List (BitVec 8)) (hf : f.off + f.len ≤ row.length) {b : Nat}
    (hb : f.len ≤ b) :
    (balCanonicalKey (f :: fs) row).getD b 0
      = (balCanonicalKey fs row).getD (b - f.len) 0 := by
  have hlen := beBytes_length (f := f) (row := row) hf
  have hkey : balCanonicalKey (f :: fs) row
      = f.beBytes row ++ balCanonicalKey fs row := by
    simp [balCanonicalKey]
  rw [hkey, getD_append_right _ _ _ _ (by omega), hlen]

/-! ## Code membership, once

    Every block cites the digit's own 28-instruction `ofProg` and lifts through
    `balDigCode`, which keeps the `decide`s small: the 147-element flat list's
    `length` does not reduce at the default recursion depth, so nothing asks it
    to, and no elaboration budget is widened. -/

/-- The digit's own code requirement is contained in the whole routine's, at
    `base + 268`. This is the one place the 67-instruction offset is used. -/
theorem balDigCode (base : Word) :
    ∀ a i, CodeReq.ofProg (base + 268) balCanonicalDigit_prog a = some i →
           CodeReq.ofProg base balCanonicalSort_prog a = some i :=
  CodeReq.ofProg_mono_sub base (base + 268) balCanonicalSort_prog balCanonicalDigit_prog 67
    (by bv_omega)
    (by rw [balDigitLen]; exact balDigit_at_67)
    (by rw [balDigitLen, balSortProgLen]; omega)
    (by rw [balSortProgLen]; omega)

/-- Triple-first `cpsTripleWithin_extend_code`, so the containment side-goal
    elaborates with the single-instruction `CodeReq` pinned. `SAsm.liftCode`'s
    role, restated locally rather than importing the `AbiFrame` tower. -/
private theorem liftCR {n : Nat} {entry exit_ : Word} {cr cr' : CodeReq}
    {P Q : Assertion} (h : cpsTripleWithin n entry exit_ cr P Q)
    (hmono : ∀ a i, cr a = some i → cr' a = some i) :
    cpsTripleWithin n entry exit_ cr' P Q := cpsTripleWithin_extend_code hmono h

/-- `pcFree` for frames that include the row's bytes: the stock tactic's atom list
    omits `bytesRegion`, so it is added here rather than left as a stray goal. -/
local macro "pcfr" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _)

/-- Frame a `pcFree` assertion on and permute both ends into canonical atom order.
    Used where `runBlock`'s framing cannot carry an untouched `bytesRegion`. -/
private theorem framePerm {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q F P' Q' : Assertion} (hF : F.pcFree)
    (hpre : ∀ h, P' h → (P ** F) h) (hpost : ∀ h, (Q ** F) h → Q' h)
    (h : cpsTripleWithin n entry exit_ cr P Q) :
    cpsTripleWithin n entry exit_ cr P' Q' :=
  cpsTripleWithin_weaken hpre hpost (cpsTripleWithin_frameR F hF h)

/-- Code-membership for digit instruction `k` (0-based within the 28), lifted into
    the whole routine's `CodeReq`. Mirrors `RlpEncodeListPrefixLoopSpec`'s `cmem`. -/
local macro "cmem" k:term:max : tactic =>
  `(tactic| exact CodeReq.singleton_mono
      (balDigCode _ _ _ (CodeReq.ofProg_lookup_addr _ balCanonicalDigit_prog $k _
        (by decide) (by decide) (by bv_omega))))

/-! ## Immediate and word arithmetic — one-line `decide`/`omega` facts about a
    concrete immediate or a `BitVec.ofNat` round trip. -/

private theorem se12_255 : signExtend12 (255 : BitVec 12) = (255 : Word) := by decide
private theorem se12_127 : signExtend12 (127 : BitVec 12) = (127 : Word) := by decide
private theorem se12_128 : signExtend12 (128 : BitVec 12) = (128 : Word) := by decide
private theorem se12_15 : signExtend12 (15 : BitVec 12) = (15 : Word) := by decide
private theorem se12_8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se12_neg1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide

/-- `idx2/idx12 SLLI x17, x16, 4` is the bit position `16 i` for a segment index in
    range. `i < 4` because three segments is the descriptor's capacity. -/
private theorem bal_shl4 (i : Nat) (hi : i < 4) :
    (BitVec.ofNat 64 i) <<< (4 : BitVec 6).toNat = BitVec.ofNat 64 (16 * i) := by
  interval_cases i <;> decide

/-- `idx5/idx13 ADDI x17, x17, 8` steps from the offset byte to the width byte. -/
private theorem bal_bitpos (i : Nat) (hi : i < 4) :
    BitVec.ofNat 64 (16 * i) + (8 : Word) = BitVec.ofNat 64 (16 * i + 8) := by
  interval_cases i <;> decide

/-- `SRL`'s low-6-bit shift amount is exact at the offset byte: `16 i ≤ 48 < 64`. -/
private theorem bal_shamt0 (i : Nat) (hi : i < 4) :
    (BitVec.ofNat 64 (16 * i)).toNat % 64 = 16 * i := by
  interval_cases i <;> decide

/-- …and at the width byte: `16 i + 8 ≤ 56 < 64`. -/
private theorem bal_shamt8 (i : Nat) (hi : i < 4) :
    (BitVec.ofNat 64 (16 * i + 8)).toNat % 64 = 16 * i + 8 := by
  interval_cases i <;> decide

/-- `idx10 ADDI x16, x16, 1` advances the segment index. -/
private theorem bal_inc (i : Nat) (hi : i < 4) :
    BitVec.ofNat 64 i + (1 : Word) = BitVec.ofNat 64 (i + 1) := by
  interval_cases i <;> decide

private theorem bal_sub (b w : Nat) (hb : b < 2 ^ 64) (hw : w ≤ b) :
    BitVec.ofNat 64 b - BitVec.ofNat 64 w = BitVec.ofNat 64 (b - w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem bal_add (x y : Nat) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem bal_dec (n : Nat) (hn : 0 < n) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n + (-1 : Word) = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (-1 : Word).toNat = 2 ^ 64 - 1 from by decide]
  omega

/-- `idx8 BLTU x7, x28` is the byte index against the segment width, unsigned. -/
private theorem bal_ult (b w : Nat) (hb : b < 2 ^ 64) (hw : w < 2 ^ 64) :
    (BitVec.ult (BitVec.ofNat 64 b) (BitVec.ofNat 64 w) = true) ↔ b < w := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

/-- `idx0 SRLI x7, x22, 1`: the nibble depth halves to the canonical BYTE index. -/
private theorem bal_shr1 (d : Word) :
    d >>> (1 : BitVec 6).toNat = BitVec.ofNat 64 (d.toNat / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  have := d.isLt
  simp only [show (1 : BitVec 6).toNat = 1 from by decide, Nat.shiftRight_eq_div_pow]
  omega

/-- `idx24 ANDI x17, x22, 1` is the depth's parity. -/
private theorem bal_and1 (d : Word) : (d &&& (1 : Word)).toNat = d.toNat % 2 := by
  rw [BitVec.toNat_and, show (1 : Word).toNat = 2 ^ 1 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem bal_even (d : Word) (h : d.toNat % 2 = 0) : d &&& (1 : Word) = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [bal_and1, h]; rfl

private theorem bal_odd (d : Word) (h : d.toNat % 2 = 1) : d &&& (1 : Word) ≠ 0 := by
  intro hz
  have := congrArg BitVec.toNat hz
  rw [bal_and1, h] at this
  exact absurd this (by decide)

/-- `idx26/idx27` at an EVEN depth: the byte's HIGH nibble. -/
private theorem bal_nib_hi (v : BitVec 8) :
    ((v.zeroExtend 64) >>> (4 : BitVec 6).toNat) &&& (15 : Word)
      = BitVec.ofNat 64 (v.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    show (15 : Word).toNat = 2 ^ 4 - 1 from by decide, BitVec.toNat_ofNat,
    show (4 : BitVec 6).toNat = 4 from by decide, Nat.shiftRight_eq_div_pow,
    Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)]
  omega

/-- `idx27` at an ODD depth: the byte's low nibble. -/
private theorem bal_nib_lo (v : BitVec 8) :
    (v.zeroExtend 64) &&& (15 : Word) = BitVec.ofNat 64 (v.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  rw [BitVec.toNat_and, BitVec.toNat_setWidth,
    show (15 : Word).toNat = 2 ^ 4 - 1 from by decide, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `idx14 SRL x17, x26, x17` writes its own shift-amount register. Core has the
    `rd = rs1` and 3-distinct shapes for `SRL` but not `rd = rs2`, so it is derived
    here from the same generic. -/
private theorem srl_rd_eq_rs2_within (rd rs1 : Reg) (v1 v2 : Word) (addr : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SRL rd rs1 rd))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 >>> (v2.toNat % 64)))) :=
  generic_2reg_spec_within (.SRL rd rs1 rd) rs1 rd v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrs1 hrd; simp [execInstrBr, hrs1, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))

/-! ## The blocks, at the routine's own addresses

    Each carries the extractor's register footprint in one fixed order — `x5`,
    `x22`, `x26`, `x0`, `x7`, `x16`, `x17`, `x28`, `x30` — so composing two is a
    permutation, not a re-framing, and the `CodeReq` is the **whole routine's** in
    every one. The row's bytes are framed on only where they are read
    (`balDigLoad`, the tails): `runBlock`'s frame computation does not carry a
    `bytesRegion` no spec in the block touches. -/

/-- **idx0-idx1** (`base+268 → base+276`): halve the nibble depth into the
    canonical byte index `b`, and start the segment walk at 0. -/
private theorem balDigPrologue (base rowPtr depth desc : Word)
    (v7 v16 v17 v28 v30 : Word) :
    cpsTripleWithin 2 (base + 268) (base + 276)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ v17) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ v30))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (depth.toNat / 2)) **
       ((.x16 : Reg) ↦ᵣ (0 : Word)) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ v30)) := by
  set CR := CodeReq.ofProg base balCanonicalSort_prog with hCR
  have h0 := liftCR (cr' := CR)
    (srli_spec_gen_within .x7 .x22 v7 depth (1 : BitVec 6) (base + 268) (by nofun))
    (by rw [hCR]; cmem 0)
  rw [show (base + 268 : Word) + 4 = base + 272 from by bv_omega, bal_shr1 depth] at h0
  have h1 := liftCR (cr' := CR)
    (li_spec_gen_within .x16 v16 (0 : Word) (base + 272) (by nofun))
    (by rw [hCR]; cmem 1)
  rw [show (base + 272 : Word) + 4 = base + 276 from by bv_omega] at h1
  runBlock h0 h1

/-- **idx2-idx7** (`base+276 → base+300`), the walk's loop head: decode segment
    `i`'s offset byte into `x30` and its width byte, endianness bit masked off, into
    `x28`.

    The two descriptor facts are **hypotheses**, not a decode performed here: a
    caller supplies them from its own literal by `decide`, and that is where the
    packed descriptor is checked against the semantic field list — the step that
    keeps the agreement from being circular. -/
private theorem balDigHead (base rowPtr depth desc : Word)
    (i k w : Nat) (hi : i < 4) (v7 v17 v28 v30 : Word)
    (hoff : (desc >>> (16 * i)) &&& (255 : Word) = BitVec.ofNat 64 k)
    (hwid : (desc >>> (16 * i + 8)) &&& (127 : Word) = BitVec.ofNat 64 w) :
    cpsTripleWithin 6 (base + 276) (base + 300)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ v30))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
       ((.x17 : Reg) ↦ᵣ BitVec.ofNat 64 (16 * i + 8)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k)) := by
  set CR := CodeReq.ofProg base balCanonicalSort_prog with hCR
  have h2 := liftCR (cr' := CR)
    (slli_spec_gen_within .x17 .x16 v17 (BitVec.ofNat 64 i) (4 : BitVec 6)
      (base + 276) (by nofun))
    (by rw [hCR]; cmem 2)
  rw [show (base + 276 : Word) + 4 = base + 280 from by bv_omega, bal_shl4 i hi] at h2
  have h3 := liftCR (cr' := CR)
    (srl_spec_gen_within .x30 .x26 .x17 v30 desc (BitVec.ofNat 64 (16 * i))
      (base + 280) (by nofun))
    (by rw [hCR]; cmem 3)
  rw [show (base + 280 : Word) + 4 = base + 284 from by bv_omega, bal_shamt0 i hi] at h3
  have h4 := liftCR (cr' := CR)
    (andi_spec_gen_same_within .x30 (desc >>> (16 * i)) (255 : BitVec 12)
      (base + 284) (by nofun))
    (by rw [hCR]; cmem 4)
  rw [show (base + 284 : Word) + 4 = base + 288 from by bv_omega, se12_255, hoff] at h4
  have h5 := liftCR (cr' := CR)
    (addi_spec_gen_same_within .x17 (BitVec.ofNat 64 (16 * i)) (8 : BitVec 12)
      (base + 288) (by nofun))
    (by rw [hCR]; cmem 5)
  rw [show (base + 288 : Word) + 4 = base + 292 from by bv_omega, se12_8,
    bal_bitpos i hi] at h5
  have h6 := liftCR (cr' := CR)
    (srl_spec_gen_within .x28 .x26 .x17 v28 desc (BitVec.ofNat 64 (16 * i + 8))
      (base + 292) (by nofun))
    (by rw [hCR]; cmem 6)
  rw [show (base + 292 : Word) + 4 = base + 296 from by bv_omega, bal_shamt8 i hi] at h6
  have h7 := liftCR (cr' := CR)
    (andi_spec_gen_same_within .x28 (desc >>> (16 * i + 8)) (127 : BitVec 12)
      (base + 296) (by nofun))
    (by rw [hCR]; cmem 7)
  rw [show (base + 296 : Word) + 4 = base + 300 from by bv_omega, se12_127, hwid] at h7
  runBlock h2 h3 h4 h5 h6 h7

/-- **idx8 taken** (`base+300 → base+316`): the byte index is inside segment `i`,
    so the walk stops (`300 + 16 = 316` is idx12). -/
private theorem balDigExit (base rowPtr depth desc : Word)
    (b w : Nat) (hb : b < 2 ^ 64) (hw : w < 2 ^ 64) (hlt : b < w)
    (v16 v17 v30 : Word) :
    cpsTripleWithin 1 (base + 300) (base + 316)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) ** ((.x30 : Reg) ↦ᵣ v30))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) ** ((.x30 : Reg) ↦ᵣ v30)) := by
  set CR := CodeReq.ofProg base balCanonicalSort_prog with hCR
  have hbr := bltu_spec_gen_within .x7 .x28 (16 : BitVec 13)
    (BitVec.ofNat 64 b) (BitVec.ofNat 64 w) (base + 300)
  rw [show (base + 300 : Word) + signExtend13 (16 : BitVec 13) = base + 316 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
    show (base + 300 : Word) + 4 = base + 304 from by bv_omega] at hbr
  have hbrf := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ v17) **
     ((.x30 : Reg) ↦ᵣ v30)) (by pcFree) hbr
  have hbre := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 8) (h := hbrf)
  have htaken := cpsBranchWithin_takenPath hbre (fun _ hQf => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
    exact ((sepConj_pure_right _).1 h_pure).2 ((bal_ult b w hb hw).2 hlt))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) htaken
  have hq1 := sepConj_mono_left
    (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
  xperm_hyp hq1

/-- **idx8 not taken, then idx9-idx11** (`base+300 → base+276`): the byte index is
    past segment `i` — subtract its width, advance `i`, take the back edge. -/
private theorem balDigCont (base rowPtr depth desc : Word)
    (i b w k : Nat) (hi : i < 4) (hb : b < 2 ^ 64) (hw : w < 2 ^ 64)
    (hnlt : ¬ b < w) (v17 : Word) :
    cpsTripleWithin 4 (base + 300) (base + 276)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (b - w)) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k)) := by
  set CR := CodeReq.ofProg base balCanonicalSort_prog with hCR
  have hbr := bltu_spec_gen_within .x7 .x28 (16 : BitVec 13)
    (BitVec.ofNat 64 b) (BitVec.ofNat 64 w) (base + 300)
  rw [show (base + 300 : Word) + signExtend13 (16 : BitVec 13) = base + 316 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
    show (base + 300 : Word) + 4 = base + 304 from by bv_omega] at hbr
  have hbrf := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
     ((.x17 : Reg) ↦ᵣ v17) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k)) (by pcFree) hbr
  have hbre := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 8) (h := hbrf)
  have hnt := cpsBranchWithin_ntakenPath hbre (fun _ hQt => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
    exact absurd ((bal_ult b w hb hw).1 ((sepConj_pure_right _).1 h_pure).2) hnlt)
  have hA : cpsTripleWithin 1 (base + 300) (base + 304) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k)) := by
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hnt
    have hq1 := sepConj_mono_left
      (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
    xperm_hyp hq1
  have h9 := liftCR (cr' := CR)
    (sub_spec_gen_rd_eq_rs1_within .x7 .x28 (BitVec.ofNat 64 b) (BitVec.ofNat 64 w)
      (base + 304) (by nofun))
    (by rw [hCR]; cmem 9)
  rw [show (base + 304 : Word) + 4 = base + 308 from by bv_omega,
    bal_sub b w hb (by omega)] at h9
  have h10 := liftCR (cr' := CR)
    (addi_spec_gen_same_within .x16 (BitVec.ofNat 64 i) (1 : BitVec 12)
      (base + 308) (by nofun))
    (by rw [hCR]; cmem 10)
  rw [show (base + 308 : Word) + 4 = base + 312 from by bv_omega, se12_1,
    bal_inc i hi] at h10
  have hB : cpsTripleWithin 2 (base + 304) (base + 312) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (b - w)) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k)) := by
    runBlock h9 h10
  have hjal := jal_x0_spec_gen_within (-36 : BitVec 21) (base + 312)
  rw [show (base + 312 : Word) + signExtend21 (-36 : BitVec 21) = base + 276 from by
        rw [show signExtend21 (-36 : BitVec 21) = -(36 : Word) from by decide]
        bv_omega] at hjal
  have hjale := liftCR (cr' := CR) hjal (by rw [hCR]; cmem 11)
  have hC := cpsTripleWithin_weaken
    (fun h hp => by simpa only [sepConj_emp_left'] using hp)
    (fun h hp => by simpa only [sepConj_emp_left'] using hp)
    (cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (b - w)) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k))
      (by pcFree) hjale)
  have hAB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hA hB
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hAB hC

/-- **idx12-idx15** (`base+316 → base+332`): recompute segment `i`'s width byte,
    isolate bit 7 — the "row already holds this field big-endian" flag. -/
private theorem balDigFlag (base rowPtr depth desc : Word)
    (i : Nat) (hi : i < 4) (v7 v17 v28 v30 : Word) :
    cpsTripleWithin 4 (base + 316) (base + 332)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ v30))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
       ((.x17 : Reg) ↦ᵣ ((desc >>> (16 * i + 8)) &&& (128 : Word))) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ v30)) := by
  set CR := CodeReq.ofProg base balCanonicalSort_prog with hCR
  have h12 := liftCR (cr' := CR)
    (slli_spec_gen_within .x17 .x16 v17 (BitVec.ofNat 64 i) (4 : BitVec 6)
      (base + 316) (by nofun))
    (by rw [hCR]; cmem 12)
  rw [show (base + 316 : Word) + 4 = base + 320 from by bv_omega, bal_shl4 i hi] at h12
  have h13 := liftCR (cr' := CR)
    (addi_spec_gen_same_within .x17 (BitVec.ofNat 64 (16 * i)) (8 : BitVec 12)
      (base + 320) (by nofun))
    (by rw [hCR]; cmem 13)
  rw [show (base + 320 : Word) + 4 = base + 324 from by bv_omega, se12_8,
    bal_bitpos i hi] at h13
  have h14 := liftCR (cr' := CR)
    (srl_rd_eq_rs2_within .x17 .x26 desc (BitVec.ofNat 64 (16 * i + 8))
      (base + 324) (by nofun))
    (by rw [hCR]; cmem 14)
  rw [show (base + 324 : Word) + 4 = base + 328 from by bv_omega, bal_shamt8 i hi] at h14
  have h15 := liftCR (cr' := CR)
    (andi_spec_gen_same_within .x17 (desc >>> (16 * i + 8)) (128 : BitVec 12)
      (base + 328) (by nofun))
    (by rw [hCR]; cmem 15)
  rw [show (base + 328 : Word) + 4 = base + 332 from by bv_omega, se12_128] at h15
  runBlock h12 h13 h14 h15

/-- ⭐ **idx16 not taken, then idx17-idx20** (`base+332 → base+356`), the
    LITTLE-ENDIAN arm: the row offset is `k + w - 1 - b`, the segment indexed
    BACKWARD — the reversal `BalCanonicalSort.lean:754-759` guards on the
    instruction list, here as what the offset *means*. The flag register arriving
    as literal `0` is what makes this the LE arm. -/
private theorem balDigArmLE (base rowPtr depth desc : Word)
    (b w k : Nat) (hw : 0 < w) (hlt : b < w) (hkw : k + w < 2 ^ 64) (v16 : Word) :
    cpsTripleWithin 5 (base + 332) (base + 356)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (k + w - 1 - b))) := by
  set CR := CodeReq.ofProg base balCanonicalSort_prog with hCR
  have hbr := bne_spec_gen_within .x17 .x0 (20 : BitVec 13) (0 : Word) (0 : Word)
    (base + 332)
  rw [show (base + 332 : Word) + signExtend13 (20 : BitVec 13) = base + 352 from by
        rw [show signExtend13 (20 : BitVec 13) = (20 : Word) from by decide]; bv_omega,
    show (base + 332 : Word) + 4 = base + 336 from by bv_omega] at hbr
  have hbrf := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
     ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) ** ((.x16 : Reg) ↦ᵣ v16) **
     ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k))
    (by pcFree) hbr
  have hbre := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 16) (h := hbrf)
  have hnt := cpsBranchWithin_ntakenPath hbre (fun _ hQt => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
    exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  have hA : cpsTripleWithin 1 (base + 332) (base + 336) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k)) := by
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hnt
    have hq1 := sepConj_mono_left
      (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
    xperm_hyp hq1
  have h17 := liftCR (cr' := CR)
    (add_spec_gen_rd_eq_rs1_within .x30 .x28 (BitVec.ofNat 64 k) (BitVec.ofNat 64 w)
      (base + 336) (by nofun))
    (by rw [hCR]; cmem 17)
  rw [show (base + 336 : Word) + 4 = base + 340 from by bv_omega, bal_add k w] at h17
  have h18 := liftCR (cr' := CR)
    (addi_spec_gen_same_within .x30 (BitVec.ofNat 64 (k + w)) (-1 : BitVec 12)
      (base + 340) (by nofun))
    (by rw [hCR]; cmem 18)
  rw [show (base + 340 : Word) + 4 = base + 344 from by bv_omega, se12_neg1,
    bal_dec (k + w) (by omega) hkw] at h18
  have h19 := liftCR (cr' := CR)
    (sub_spec_gen_rd_eq_rs1_within .x30 .x7 (BitVec.ofNat 64 (k + w - 1))
      (BitVec.ofNat 64 b) (base + 344) (by nofun))
    (by rw [hCR]; cmem 19)
  rw [show (base + 344 : Word) + 4 = base + 348 from by bv_omega,
    bal_sub (k + w - 1) b (by omega) (by omega)] at h19
  have hB : cpsTripleWithin 3 (base + 336) (base + 348) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (k + w - 1 - b))) := by
    (runBlock h17 h18 h19)
  have hjal := jal_x0_spec_gen_within (8 : BitVec 21) (base + 348)
  rw [show (base + 348 : Word) + signExtend21 (8 : BitVec 21) = base + 356 from by
        rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
        bv_omega] at hjal
  have hjale := liftCR (cr' := CR) hjal (by rw [hCR]; cmem 20)
  have hC := cpsTripleWithin_weaken
    (fun h hp => by simpa only [sepConj_emp_left'] using hp)
    (fun h hp => by simpa only [sepConj_emp_left'] using hp)
    (cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 w) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (k + w - 1 - b))) (by pcFree) hjale)
  have hAB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hA hB
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hAB hC

/-- ⭐ **idx16 taken, then idx21** (`base+332 → base+356`), the BIG-ENDIAN arm: the
    row offset is `k + b`, the segment indexed FORWARD. Reversing a field the
    producer already canonicalised would order rows by a byte-reversed field:
    total, permutation-preserving, and not canonical. -/
private theorem balDigArmBE (base rowPtr depth desc : Word)
    (b k : Nat) (fl : Word) (hfl : fl ≠ 0) (v16 v28 : Word) :
    cpsTripleWithin 2 (base + 332) (base + 356)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ fl) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ fl) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (k + b))) := by
  set CR := CodeReq.ofProg base balCanonicalSort_prog with hCR
  have hbr := bne_spec_gen_within .x17 .x0 (20 : BitVec 13) fl (0 : Word) (base + 332)
  rw [show (base + 332 : Word) + signExtend13 (20 : BitVec 13) = base + 352 from by
        rw [show signExtend13 (20 : BitVec 13) = (20 : Word) from by decide]; bv_omega,
    show (base + 332 : Word) + 4 = base + 336 from by bv_omega] at hbr
  have hbrf := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
     ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) ** ((.x16 : Reg) ↦ᵣ v16) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k)) (by pcFree) hbr
  have hbre := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 16) (h := hbrf)
  have htaken := cpsBranchWithin_takenPath hbre (fun _ hQf => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 h_pure).2 hfl)
  have hA : cpsTripleWithin 1 (base + 332) (base + 352) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ fl) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ fl) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k)) := by
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) htaken
    have hq1 := sepConj_mono_left
      (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
    xperm_hyp hq1
  have h21 := liftCR (cr' := CR)
    (add_spec_gen_rd_eq_rs1_within .x30 .x7 (BitVec.ofNat 64 k) (BitVec.ofNat 64 b)
      (base + 352) (by nofun))
    (by rw [hCR]; cmem 21)
  rw [show (base + 352 : Word) + 4 = base + 356 from by bv_omega, bal_add k b] at h21
  have hB : cpsTripleWithin 1 (base + 352) (base + 356) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ fl) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ fl) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (k + b))) := by
    (runBlock h21)
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hA hB

/-- **idx22-idx24** (`base+356 → base+368`): add the row pointer, load the byte,
    latch the depth's parity. The row's bytes join the footprint here — the only
    block that reads memory. -/
private theorem balDigLoad (base rowPtr depth desc : Word) (row : List (BitVec 8))
    (o : Nat) (halign : rowPtr.toNat % 8 = 0) (ho : o < row.length)
    (hover : rowPtr.toNat + o < 2 ^ 64)
    (hvalid : isValidByteAccess (rowPtr + BitVec.ofNat 64 o) = true)
    (v7 v16 v17 v28 : Word) :
    cpsTripleWithin 3 (base + 356) (base + 368)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ v17) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 o) ** bytesRegion rowPtr row)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ (depth &&& (1 : Word))) **
       ((.x28 : Reg) ↦ᵣ ((row.getD o 0).zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ (rowPtr + BitVec.ofNat 64 o)) ** bytesRegion rowPtr row) := by
  set CR := CodeReq.ofProg base balCanonicalSort_prog with hCR
  have h22 := liftCR (cr' := CR)
    (add_spec_gen_rd_eq_rs2_within .x30 .x5 rowPtr (BitVec.ofNat 64 o)
      (base + 356) (by nofun))
    (by rw [hCR]; cmem 22)
  rw [show (base + 356 : Word) + 4 = base + 360 from by bv_omega] at h22
  have h23 := liftCR (cr' := CR)
    (bytesRegion_lbu_within .x28 .x30 rowPtr v28 (base + 360) row o (by nofun)
      halign ho hover hvalid)
    (by rw [hCR]; cmem 23)
  rw [show (base + 360 : Word) + 4 = base + 364 from by bv_omega,
    ← getD_eq_getElem row o (0 : BitVec 8) ho] at h23
  have h24 := liftCR (cr' := CR)
    (andi_spec_gen_within .x17 .x22 v17 depth (1 : BitVec 12) (base + 364) (by nofun))
    (by rw [hCR]; cmem 24)
  rw [show (base + 364 : Word) + 4 = base + 368 from by bv_omega, se12_1] at h24
  have hA : cpsTripleWithin 1 (base + 356) (base + 360) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ v17) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 o) ** bytesRegion rowPtr row)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ v17) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x30 : Reg) ↦ᵣ (rowPtr + BitVec.ofNat 64 o)) ** bytesRegion rowPtr row) :=
    framePerm
      (F := ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
        ((.x17 : Reg) ↦ᵣ v17) ** ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion rowPtr row)
      (by pcfr) (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h22
  have hB : cpsTripleWithin 1 (base + 360) (base + 364) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ v17) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x30 : Reg) ↦ᵣ (rowPtr + BitVec.ofNat 64 o)) ** bytesRegion rowPtr row)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ v17) ** ((.x28 : Reg) ↦ᵣ ((row.getD o 0).zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ (rowPtr + BitVec.ofNat 64 o)) ** bytesRegion rowPtr row) :=
    framePerm
      (F := ((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) **
        ((.x26 : Reg) ↦ᵣ desc) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) ** ((.x17 : Reg) ↦ᵣ v17))
      (by pcFree) (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h23
  have hC : cpsTripleWithin 1 (base + 364) (base + 368) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ v17) ** ((.x28 : Reg) ↦ᵣ ((row.getD o 0).zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ (rowPtr + BitVec.ofNat 64 o)) ** bytesRegion rowPtr row)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ (depth &&& (1 : Word))) **
       ((.x28 : Reg) ↦ᵣ ((row.getD o 0).zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ (rowPtr + BitVec.ofNat 64 o)) ** bytesRegion rowPtr row) :=
    framePerm
      (F := ((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x26 : Reg) ↦ᵣ desc) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
        ((.x28 : Reg) ↦ᵣ ((row.getD o 0).zeroExtend 64)) **
        ((.x30 : Reg) ↦ᵣ (rowPtr + BitVec.ofNat 64 o)) ** bytesRegion rowPtr row)
      (by pcfr) (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h24
  have hAB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hA hB
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hAB hC

/-- ⭐ **idx25 not taken, then idx26-idx27** (`base+368 → base+380`) at an EVEN
    depth: the byte's HIGH nibble. Pinning the high half to even depths is what
    makes the more significant nibble compared first. -/
private theorem balDigNibEven (base rowPtr depth desc : Word) (v : BitVec 8)
    (v7 v16 v30 : Word) :
    cpsTripleWithin 3 (base + 368) (base + 380)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ (v.zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ v30))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (v.toNat / 16)) **
       ((.x30 : Reg) ↦ᵣ v30)) := by
  set CR := CodeReq.ofProg base balCanonicalSort_prog with hCR
  have hbr := bne_spec_gen_within .x17 .x0 (8 : BitVec 13) (0 : Word) (0 : Word)
    (base + 368)
  rw [show (base + 368 : Word) + signExtend13 (8 : BitVec 13) = base + 376 from by
        rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]; bv_omega,
    show (base + 368 : Word) + 4 = base + 372 from by bv_omega] at hbr
  have hbrf := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
     ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
     ((.x28 : Reg) ↦ᵣ (v.zeroExtend 64)) ** ((.x30 : Reg) ↦ᵣ v30)) (by pcFree) hbr
  have hbre := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 25) (h := hbrf)
  have hnt := cpsBranchWithin_ntakenPath hbre (fun _ hQt => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
    exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  have hA : cpsTripleWithin 1 (base + 368) (base + 372) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ (v.zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ v30))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ (v.zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ v30)) := by
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hnt
    have hq1 := sepConj_mono_left
      (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
    xperm_hyp hq1
  have h26 := liftCR (cr' := CR)
    (srli_spec_gen_same_within .x28 (v.zeroExtend 64) (4 : BitVec 6)
      (base + 372) (by nofun))
    (by rw [hCR]; cmem 26)
  rw [show (base + 372 : Word) + 4 = base + 376 from by bv_omega] at h26
  have h27 := liftCR (cr' := CR)
    (andi_spec_gen_same_within .x28 ((v.zeroExtend 64) >>> (4 : BitVec 6).toNat)
      (15 : BitVec 12) (base + 376) (by nofun))
    (by rw [hCR]; cmem 27)
  rw [show (base + 376 : Word) + 4 = base + 380 from by bv_omega, se12_15,
    bal_nib_hi v] at h27
  have hB : cpsTripleWithin 2 (base + 372) (base + 380) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ (v.zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ v30))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (v.toNat / 16)) **
       ((.x30 : Reg) ↦ᵣ v30)) := by
    (runBlock h26 h27)
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hA hB

/-- ⭐ **idx25 taken, then idx27** (`base+368 → base+380`), ODD depth: the byte's
    low nibble, idx26's shift skipped. -/
private theorem balDigNibOdd (base rowPtr depth desc : Word) (v : BitVec 8)
    (fl : Word) (hfl : fl ≠ 0) (v7 v16 v30 : Word) :
    cpsTripleWithin 2 (base + 368) (base + 380)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ fl) ** ((.x28 : Reg) ↦ᵣ (v.zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ v30))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ fl) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (v.toNat % 16)) **
       ((.x30 : Reg) ↦ᵣ v30)) := by
  set CR := CodeReq.ofProg base balCanonicalSort_prog with hCR
  have hbr := bne_spec_gen_within .x17 .x0 (8 : BitVec 13) fl (0 : Word) (base + 368)
  rw [show (base + 368 : Word) + signExtend13 (8 : BitVec 13) = base + 376 from by
        rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]; bv_omega,
    show (base + 368 : Word) + 4 = base + 372 from by bv_omega] at hbr
  have hbrf := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
     ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
     ((.x28 : Reg) ↦ᵣ (v.zeroExtend 64)) ** ((.x30 : Reg) ↦ᵣ v30)) (by pcFree) hbr
  have hbre := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 25) (h := hbrf)
  have htaken := cpsBranchWithin_takenPath hbre (fun _ hQf => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 h_pure).2 hfl)
  have hA : cpsTripleWithin 1 (base + 368) (base + 376) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ fl) ** ((.x28 : Reg) ↦ᵣ (v.zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ v30))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ fl) ** ((.x28 : Reg) ↦ᵣ (v.zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ v30)) := by
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) htaken
    have hq1 := sepConj_mono_left
      (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
    xperm_hyp hq1
  have h27 := liftCR (cr' := CR)
    (andi_spec_gen_same_within .x28 (v.zeroExtend 64) (15 : BitVec 12)
      (base + 376) (by nofun))
    (by rw [hCR]; cmem 27)
  rw [show (base + 376 : Word) + 4 = base + 380 from by bv_omega, se12_15,
    bal_nib_lo v] at h27
  have hB : cpsTripleWithin 1 (base + 376) (base + 380) CR
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ fl) ** ((.x28 : Reg) ↦ᵣ (v.zeroExtend 64)) **
       ((.x30 : Reg) ↦ᵣ v30))
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ fl) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (v.toNat % 16)) **
       ((.x30 : Reg) ↦ᵣ v30)) := by
    (runBlock h27)
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hA hB

/-! ## Composites — three levels: the tail resolves the depth's PARITY,
    `balDigFrom` the segment's ENDIANNESS, the agreement theorems WHICH SEGMENT.
    Each states one step bound covering its cases, sound because
    `cpsTripleWithin n` bounds the step count from above. -/

/-- **idx22-idx27** (`base+356 → base+380`): load the byte the walk selected, take
    the nibble the depth's parity names. Six steps at even depth, five at odd. -/
private theorem balDigTail (base rowPtr depth desc : Word) (row : List (BitVec 8))
    (o : Nat) (halign : rowPtr.toNat % 8 = 0) (ho : o < row.length)
    (hover : rowPtr.toNat + o < 2 ^ 64)
    (hvalid : isValidByteAccess (rowPtr + BitVec.ofNat 64 o) = true)
    (v7 v16 v17 v28 : Word) :
    cpsTripleWithin 6 (base + 356) (base + 380)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ v17) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 o) ** bytesRegion rowPtr row)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       regOwn .x17 **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (balByteNibble (row.getD o 0) depth.toNat)) **
       regOwn .x30 ** bytesRegion rowPtr row) := by
  have hload := balDigLoad base rowPtr depth desc row o halign ho hover hvalid
    v7 v16 v17 v28
  by_cases hpar : depth.toNat % 2 = 0
  · have hz : depth &&& (1 : Word) = 0 := bal_even depth hpar
    rw [hz] at hload
    have hnib := cpsTripleWithin_frameR (bytesRegion rowPtr row)
      (bytesRegion_pcFree _ _)
      (balDigNibEven base rowPtr depth desc (row.getD o 0) v7 v16
        (rowPtr + BitVec.ofNat 64 o))
    simp only [sepConj_assoc'] at hnib
    have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hload hnib
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hcomp)
    have hnb : balByteNibble (row.getD o 0) depth.toNat = (row.getD o 0).toNat / 16 := by
      simp only [balByteNibble, hpar, if_true]
    rw [hnb]
    have hq1 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (regIs_implies_regOwn .x17))))))) h hq
    have hq2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (regIs_implies_regOwn .x30))))))))) h hq1
    xperm_hyp hq2
  · have hz : depth &&& (1 : Word) ≠ 0 := bal_odd depth (by omega)
    have hnib := cpsTripleWithin_frameR (bytesRegion rowPtr row)
      (bytesRegion_pcFree _ _)
      (balDigNibOdd base rowPtr depth desc (row.getD o 0) (depth &&& (1 : Word)) hz
        v7 v16 (rowPtr + BitVec.ofNat 64 o))
    simp only [sepConj_assoc'] at hnib
    have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hload hnib
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hcomp)
    have hnb : balByteNibble (row.getD o 0) depth.toNat = (row.getD o 0).toNat % 16 := by
      simp only [balByteNibble, hpar, if_false]
    rw [hnb]
    have hq1 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (regIs_implies_regOwn .x17))))))) h hq
    have hq2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (regIs_implies_regOwn .x30))))))))) h hq1
    xperm_hyp hq2


/-- ⭐ **idx12-idx27** (`base+316 → base+380`): with the walk stopped inside field
    `f` at byte index `b`, the routine reads **`row[balRowOffset f b]`** and takes
    the depth's nibble of it.

    The module's core: `balRowOffset` is the routine's endianness rule, and
    `beBytes_getD` (model side, no machine in sight) says that same offset is where
    the field's canonical big-endian byte `b` lives. Fifteen steps covers all four
    endianness/parity paths. -/
private theorem balDigFrom (base rowPtr depth desc : Word) (row : List (BitVec 8))
    (f : BalKeyField) (i b : Nat) (hi : i < 4)
    (hf : f.off + f.len ≤ row.length) (hlen0 : 0 < f.len) (hb : b < f.len)
    (hrowlt : row.length < 2 ^ 64) (hmem : rowPtr.toNat + row.length < 2 ^ 64)
    (halign : rowPtr.toNat % 8 = 0)
    (hvalid : ∀ j, j < row.length →
      isValidByteAccess (rowPtr + BitVec.ofNat 64 j) = true)
    (hflag : (desc >>> (16 * i + 8)) &&& (128 : Word)
      = if f.alreadyBE then (128 : Word) else 0)
    (v17 : Word) :
    cpsTripleWithin 15 (base + 316) (base + 380)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x17 : Reg) ↦ᵣ v17) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 f.len) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 f.off) ** bytesRegion rowPtr row)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 b) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** regOwn .x17 **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64
          (balByteNibble (row.getD (balRowOffset f b) 0) depth.toNat)) **
       regOwn .x30 ** bytesRegion rowPtr row) := by
  have hoff_lt : balRowOffset f b < row.length := by
    unfold balRowOffset; split <;> omega
  have htail := balDigTail base rowPtr depth desc row (balRowOffset f b) halign
    hoff_lt (by omega) (hvalid _ hoff_lt) (BitVec.ofNat 64 b) (BitVec.ofNat 64 i)
  have hflagB := cpsTripleWithin_frameR (bytesRegion rowPtr row)
    (bytesRegion_pcFree _ _)
    (balDigFlag base rowPtr depth desc i hi (BitVec.ofNat 64 b) v17
      (BitVec.ofNat 64 f.len) (BitVec.ofNat 64 f.off))
  simp only [sepConj_assoc'] at hflagB
  cases hbe : f.alreadyBE with
  | true =>
    simp only [hbe, if_true] at hflag
    have horo : balRowOffset f b = f.off + b := by
      simp only [balRowOffset, hbe, if_true]
    rw [hflag] at hflagB
    have harm := cpsTripleWithin_frameR (bytesRegion rowPtr row)
      (bytesRegion_pcFree _ _)
      (balDigArmBE base rowPtr depth desc b f.off (128 : Word) (by decide)
        (BitVec.ofNat 64 i) (BitVec.ofNat 64 f.len))
    simp only [sepConj_assoc'] at harm
    rw [← horo] at harm
    have h1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hflagB harm
    have h2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) h1
      (htail (128 : Word) (BitVec.ofNat 64 f.len))
    exact cpsTripleWithin_mono_nSteps (by omega) h2
  | false =>
    simp only [hbe, Bool.false_eq_true, if_false] at hflag
    have horo : balRowOffset f b = f.off + f.len - 1 - b := by
      simp only [balRowOffset, hbe, Bool.false_eq_true, if_false]
    rw [hflag] at hflagB
    have harm := cpsTripleWithin_frameR (bytesRegion rowPtr row)
      (bytesRegion_pcFree _ _)
      (balDigArmLE base rowPtr depth desc b f.len f.off hlen0 hb (by omega)
        (BitVec.ofNat 64 i))
    simp only [sepConj_assoc'] at harm
    rw [← horo] at harm
    have h1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hflagB harm
    have h2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) h1
      (htail (0 : Word) (BitVec.ofNat 64 f.len))
    exact cpsTripleWithin_mono_nSteps (by omega) h2

/-! ## ⭐ The agreement theorems — the deliverable. `x28` ends holding the nibble
    the **semantically decoded** key names at that depth. The descriptor enters
    only through the `hoff`/`hwid`/`hbe` hypotheses, which a caller discharges by
    `decide` against its own literal; had the descriptor disagreed with the field
    list (a swapped limb, a wrong endianness bit) those `decide`s would fail,
    rather than the theorem quietly becoming true of the wrong order. -/

/-- ⭐ **One key segment**: the extractor agrees with `balCanonicalKey [f]` at every
    depth inside the field. At most 24 steps (`24 + 10*0`, the LE/even path). -/
theorem balDigitAgree_1seg (base rowPtr depth desc : Word) (row : List (BitVec 8))
    (f : BalKeyField) (hwf : balFieldsWf [f] row.length)
    (hrowlt : row.length < 2 ^ 64) (hmem : rowPtr.toNat + row.length < 2 ^ 64)
    (halign : rowPtr.toNat % 8 = 0)
    (hvalid : ∀ j, j < row.length →
      isValidByteAccess (rowPtr + BitVec.ofNat 64 j) = true)
    (hdepth : depth.toNat < 2 * f.len)
    (hoff : (desc >>> (16 * 0)) &&& (255 : Word) = BitVec.ofNat 64 f.off)
    (hwid : (desc >>> (16 * 0 + 8)) &&& (127 : Word) = BitVec.ofNat 64 f.len)
    (hbe : (desc >>> (16 * 0 + 8)) &&& (128 : Word)
      = if f.alreadyBE then (128 : Word) else 0)
    (v7 v16 v17 v28 v30 : Word) :
    cpsTripleWithin 24 (base + 268) (base + 380)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ v17) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ v30) **
       bytesRegion rowPtr row)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (depth.toNat / 2)) **
       ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 0) ** regOwn .x17 **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64
          (balCanonicalNibble (balCanonicalKey [f] row) depth.toNat)) **
       regOwn .x30 ** bytesRegion rowPtr row) := by
  obtain ⟨hpos, hfit⟩ := hwf f (by simp)
  have hb : depth.toNat / 2 < f.len := by omega
  have hp := balDigPrologue base rowPtr depth desc v7 v16 v17 v28 v30
  have hh := balDigHead base rowPtr depth desc 0 f.off f.len (by omega)
    (BitVec.ofNat 64 (depth.toNat / 2)) v17 v28 v30 hoff hwid
  have he := balDigExit base rowPtr depth desc (depth.toNat / 2) f.len
    (by have := depth.isLt; omega) (by omega) hb (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 (16 * 0 + 8)) (BitVec.ofNat 64 f.off)
  have hw := cpsTripleWithin_seq_perm_same_cr (fun _ hp' => hp')
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp' => hp') hp hh) he
  have hwB := cpsTripleWithin_frameR (bytesRegion rowPtr row)
    (bytesRegion_pcFree _ _) hw
  simp only [sepConj_assoc'] at hwB
  have hfr := balDigFrom base rowPtr depth desc row f 0 (depth.toNat / 2) (by omega)
    hfit hpos hb hrowlt hmem halign hvalid hbe (BitVec.ofNat 64 (16 * 0 + 8))
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp' => hp') hwB hfr
  have hkey : balCanonicalNibble (balCanonicalKey [f] row) depth.toNat
      = balByteNibble (row.getD (balRowOffset f (depth.toNat / 2)) 0) depth.toNat := by
    rw [balCanonicalNibble_eq_byte, balCanonicalKey_getD_head f [] row hfit hb]
  rw [hkey]
  exact cpsTripleWithin_mono_nSteps (by omega) hall

/-- ⭐ **Two key segments** — address-major, then the second field — with the depth
    bound the program itself does NOT check as an explicit hypothesis.

    ⚠️ `hdepth` is load-bearing: the walk tests only `b < w_i` and never consults
    the segment count, so a depth past the real key would read a garbage width byte
    off the descriptor register's high end and keep walking. 34 steps covers both
    exit segments and both parities. -/
theorem balDigitAgree_2seg (base rowPtr depth desc : Word) (row : List (BitVec 8))
    (f0 f1 : BalKeyField) (hwf : balFieldsWf [f0, f1] row.length)
    (hrowlt : row.length < 2 ^ 64) (hmem : rowPtr.toNat + row.length < 2 ^ 64)
    (halign : rowPtr.toNat % 8 = 0)
    (hvalid : ∀ j, j < row.length →
      isValidByteAccess (rowPtr + BitVec.ofNat 64 j) = true)
    (hdepth : depth.toNat < 2 * (f0.len + f1.len))
    (hoff0 : (desc >>> (16 * 0)) &&& (255 : Word) = BitVec.ofNat 64 f0.off)
    (hwid0 : (desc >>> (16 * 0 + 8)) &&& (127 : Word) = BitVec.ofNat 64 f0.len)
    (hbe0 : (desc >>> (16 * 0 + 8)) &&& (128 : Word)
      = if f0.alreadyBE then (128 : Word) else 0)
    (hoff1 : (desc >>> (16 * 1)) &&& (255 : Word) = BitVec.ofNat 64 f1.off)
    (hwid1 : (desc >>> (16 * 1 + 8)) &&& (127 : Word) = BitVec.ofNat 64 f1.len)
    (hbe1 : (desc >>> (16 * 1 + 8)) &&& (128 : Word)
      = if f1.alreadyBE then (128 : Word) else 0)
    (v7 v16 v17 v28 v30 : Word) :
    cpsTripleWithin 34 (base + 268) (base + 380)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ v17) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ v30) **
       bytesRegion rowPtr row)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ depth) ** ((.x26 : Reg) ↦ᵣ desc) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x7 ** regOwn .x16 ** regOwn .x17 **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64
          (balCanonicalNibble (balCanonicalKey [f0, f1] row) depth.toNat)) **
       regOwn .x30 ** bytesRegion rowPtr row) := by
  obtain ⟨hpos0, hfit0⟩ := hwf f0 (by simp)
  obtain ⟨hpos1, hfit1⟩ := hwf f1 (by simp)
  have hdlt := depth.isLt
  have hp := balDigPrologue base rowPtr depth desc v7 v16 v17 v28 v30
  have hh0 := balDigHead base rowPtr depth desc 0 f0.off f0.len (by omega)
    (BitVec.ofNat 64 (depth.toNat / 2)) v17 v28 v30 hoff0 hwid0
  have hph := cpsTripleWithin_seq_perm_same_cr (fun _ hp' => hp') hp hh0
  by_cases hlt0 : depth.toNat / 2 < f0.len
  · have he := balDigExit base rowPtr depth desc (depth.toNat / 2) f0.len
      (by omega) (by omega) hlt0 (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 (16 * 0 + 8)) (BitVec.ofNat 64 f0.off)
    have hw := cpsTripleWithin_seq_perm_same_cr (fun _ hp' => hp') hph he
    have hwB := cpsTripleWithin_frameR (bytesRegion rowPtr row)
      (bytesRegion_pcFree _ _) hw
    simp only [sepConj_assoc'] at hwB
    have hfr := balDigFrom base rowPtr depth desc row f0 0 (depth.toNat / 2)
      (by omega) hfit0 hpos0 hlt0 hrowlt hmem halign hvalid hbe0
      (BitVec.ofNat 64 (16 * 0 + 8))
    have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp' => hp') hwB hfr
    have hkey : balCanonicalNibble (balCanonicalKey [f0, f1] row) depth.toNat
        = balByteNibble (row.getD (balRowOffset f0 (depth.toNat / 2)) 0)
            depth.toNat := by
      rw [balCanonicalNibble_eq_byte, balCanonicalKey_getD_head f0 [f1] row hfit0 hlt0]
    rw [hkey]
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hq => hq) (fun h hq => ?_) hall)
    have hq1 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x7))))) h hq
    have hq2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (regIs_implies_regOwn .x16)))))) h hq1
    xperm_hyp hq2
  · have hb1 : depth.toNat / 2 - f0.len < f1.len := by omega
    have hc := balDigCont base rowPtr depth desc 0 (depth.toNat / 2) f0.len f0.off
      (by omega) (by omega) (by omega) hlt0 (BitVec.ofNat 64 (16 * 0 + 8))
    have hh1 := balDigHead base rowPtr depth desc 1 f1.off f1.len (by omega)
      (BitVec.ofNat 64 (depth.toNat / 2 - f0.len)) (BitVec.ofNat 64 (16 * 0 + 8))
      (BitVec.ofNat 64 f0.len) (BitVec.ofNat 64 f0.off) hoff1 hwid1
    have he := balDigExit base rowPtr depth desc (depth.toNat / 2 - f0.len) f1.len
      (by omega) (by omega) hb1 (BitVec.ofNat 64 1)
      (BitVec.ofNat 64 (16 * 1 + 8)) (BitVec.ofNat 64 f1.off)
    have hw := cpsTripleWithin_seq_perm_same_cr (fun _ hp' => hp')
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp' => hp')
        (cpsTripleWithin_seq_perm_same_cr (fun _ hp' => hp') hph hc) hh1) he
    have hwB := cpsTripleWithin_frameR (bytesRegion rowPtr row)
      (bytesRegion_pcFree _ _) hw
    simp only [sepConj_assoc'] at hwB
    have hfr := balDigFrom base rowPtr depth desc row f1 1
      (depth.toNat / 2 - f0.len) (by omega) hfit1 hpos1 hb1 hrowlt hmem halign
      hvalid hbe1 (BitVec.ofNat 64 (16 * 1 + 8))
    have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp' => hp') hwB hfr
    have hkey : balCanonicalNibble (balCanonicalKey [f0, f1] row) depth.toNat
        = balByteNibble (row.getD (balRowOffset f1 (depth.toNat / 2 - f0.len)) 0)
            depth.toNat := by
      rw [balCanonicalNibble_eq_byte,
        balCanonicalKey_getD_tail f0 [f1] row hfit0 (by omega),
        balCanonicalKey_getD_head f1 [] row hfit1 hb1]
    rw [hkey]
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hq => hq) (fun h hq => ?_) hall)
    have hq1 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x7))))) h hq
    have hq2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (regIs_implies_regOwn .x16)))))) h hq1
    xperm_hyp hq2

/-! ## Key uniqueness, as a precondition — and who actually discharges it

    The 2026-08-08 ruling on #10817 made key uniqueness a **hypothesis of the
    sort's triple, discharged by the producer**, not a property proved about the
    sort: the guest sort is **not stable** — an American-flag partition on digits
    `[a:1, b:1, c:0]` swaps rows 0 and 2, giving `[c, b, a]` — while
    `block_access_lists.py:564,578` uses Python's stable `.sort`. Under distinct
    keys the two agree exactly; on duplicates they differ, so no theorem about the
    sort closes that gap.

    ⚠️ **Which producer guarantees it, and how — checked, and the answer is "two
    of the six live call sites, and no more"**
    (`RegionPredicates.balSortCallSites`):

    - `bal_builder_storage_changes` — `bal_builder_record_storage_change` **upserts**
      on `(address, slot, BAI)` (`BlockAccessListBuilder.lean:434`, scan
      `.Lbrsc_scan:441`, hit `:460`, which does not bump the count). Exactly the
      sort key ⇒ distinct, at the array level.
    - `bal_builder_accounts` — `bal_builder_ensure_account` **upserts** on the
      20-byte BE address (`:319`, scan `:322`, hit `:338`) ⇒ distinct.
    - storage-read arena `0xa1908780` — dedups on the **full 64-byte row**
      `(addrKey, slotKey)` (`StorageReadLog.lean:137/153`, `:201/215`;
      `ReadSetsPromote.lean:135`), but its sort key is the slot at `+32` **only**;
      two rows with different addresses and one slot have equal sort keys.
    - `bal_builder_{balance,nonce,code}_changes` — `bal_builder_append_*` **append
      unconditionally**, no scan (`:386`/`:395`, `:498`/`:507`, `:513`/`:522`).
      **No producer guarantee.** The only argument is caller-side:
      the emit walk (`AccountWriteMap.lean:904/923/935/951`) iterates the
      address-keyed tx map (`account_write_record:243`, an upsert) at one fixed
      BAI, so one walk yields at most one row per `(address, BAI)`. That is a
      whole-program invariant pinned by no `#guard` or theorem, and at least one
      path runs **two** walks at one BAI (the OOG hook
      `BlockVerdictMtxRuntime.lean:142`, then the normal tail `:704`); whether it
      can actually produce two rows with the same `(address, BAI)` was not
      determined.

    The Python spec *does* enforce `(address, BAI)` uniqueness for those three,
    procedurally, in `add_balance_change`/`add_nonce_change`/`add_code_change`
    (`block_access_lists.py:406-424, 443-461, 478-496`), and
    `_build_from_builder`'s docstring asserts it outright (`:532`). The guest's
    `bal_builder_append_*` omit that scan. **That is the gap.** No Lean declaration
    in the tree asserts distinctness over BAL rows today; the existing `Nodup`
    theorems (`WriteMapAssertions.lean:333,338`) are about the write *maps*, whose
    keys are strict prefixes of the corresponding sort keys.

    So: state it, name it, and do not pretend it is discharged. -/

/-- Pairwise-distinct canonical keys over a run of sort rows: a **precondition** of
    any sortedness/permutation theorem, discharged by the producer — see above for
    which producers actually do. -/
def balKeysDistinct (fs : List BalKeyField) (rows : List (List (BitVec 8))) : Prop :=
  ∀ i j, i < rows.length → j < rows.length → i ≠ j →
    balCanonicalKey fs (rows.getD i []) ≠ balCanonicalKey fs (rows.getD j [])

/-- Vacuously true on a one-row array; stated over indices rather than as a
    `Nodup`, because the sort's row count is a runtime value including 0 and 1. -/
theorem balKeysDistinct_singleton (fs : List BalKeyField) (r : List (BitVec 8)) :
    balKeysDistinct fs [r] := by
  intro i j hi hj hne
  simp only [List.length_cons, List.length_nil] at hi hj
  omega

/-! ## ⭐ Satisfiability — the anti-vacuity check. A bundled hypothesis no input
    satisfies makes a theorem vacuous, and that has happened here
    (`jalr_sail_equiv`: 68 of 128 extension constructors hit an assert-false). -/

/-- ⭐ **The whole hypothesis bundle, discharged at a live call site.** Every
    premise of `balDigitAgree_2seg` holds for a 96-byte
    `bal_builder_storage_changes` row, the live descriptor
    `balSortBuilderStorageSegments = 0x0818a0209400`, the semantic fields "address
    BE20 at +0" and "slot BE32 at +32", and depth 3 — so the theorem is not
    vacuous, and this is the check `jalr_sail_equiv` did not get (68 of its 128
    extension constructors hit an assert-false, making its bundled existential
    unsatisfiable). Only the arena facts stay hypothetical; they are properties of
    the caller's buffer, and `balSortCallSites_strides_aligned` pins the strides
    8-aligned at every live site.

    ⚠️ Scope: the descriptor's THIRD segment, `block_access_index` `(24, 8)` LE, is
    the one the sorter reverses and holds depths `104..119`. This covers `0..103`,
    the address and the slot; a third needs one more `balDigCont`, nothing else. -/
theorem balDigitAgree_2seg_live (base rowPtr : Word) (halign : rowPtr.toNat % 8 = 0)
    (hmem : rowPtr.toNat + 96 < 2 ^ 64)
    (hvalid : ∀ j, j < 96 → isValidByteAccess (rowPtr + BitVec.ofNat 64 j) = true)
    (row : List (BitVec 8)) (hrow : row.length = 96) (v7 v16 v17 v28 v30 : Word) :
    cpsTripleWithin 34 (base + 268) (base + 380)
      (CodeReq.ofProg base balCanonicalSort_prog)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ (BitVec.ofNat 64 3)) **
       ((.x26 : Reg) ↦ᵣ (BitVec.ofNat 64 balSortBuilderStorageSegments)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x16 : Reg) ↦ᵣ v16) **
       ((.x17 : Reg) ↦ᵣ v17) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x30 : Reg) ↦ᵣ v30) **
       bytesRegion rowPtr row)
      (((.x5 : Reg) ↦ᵣ rowPtr) ** ((.x22 : Reg) ↦ᵣ (BitVec.ofNat 64 3)) **
       ((.x26 : Reg) ↦ᵣ (BitVec.ofNat 64 balSortBuilderStorageSegments)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x7 ** regOwn .x16 ** regOwn .x17 **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64
          (balCanonicalNibble (balCanonicalKey [⟨0, 20, true⟩, ⟨32, 32, true⟩] row)
            (BitVec.ofNat 64 3).toNat)) **
       regOwn .x30 ** bytesRegion rowPtr row) := by
  have hd : (BitVec.ofNat 64 3 : Word).toNat = 3 := by decide
  refine balDigitAgree_2seg base rowPtr (BitVec.ofNat 64 3)
    (BitVec.ofNat 64 balSortBuilderStorageSegments) row ⟨0, 20, true⟩ ⟨32, 32, true⟩
    ?_ (by omega) (by omega) halign (by rw [hrow]; exact hvalid)
    (by rw [hd]; decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) v7 v16 v17 v28 v30
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> exact ⟨by decide, by rw [hrow]; decide⟩

end BalCanonicalSortDigitSpec

end EvmAsm.Codegen
