/-
  Whole-program caller contract for the 69-instruction
  `chain_validate_extra_data_length` accessor.

  `chainValidateExtraDataLength_prog` iterates over an array of `N` block
  headers and validates that EVERY header's `extra_data` (RLP field 12) is at
  most 32 bytes.  It is the pattern-setter for a batch of sibling
  `chainValidate*` accessors, so the loop induction here is built to be reused.

  Calling convention (see `ChainValidate.lean`):
    a0 (input)  : N (header count)
    a1 (input)  : header_lengths ptr (array of N u64 byte-lengths, 8-aligned)
    a2 (input)  : headers ptr (concatenated header blobs)
    a3 (input)  : u64 out cell (is_valid)
    a4 (input)  : u64 out cell (first_bad_index)
    ra (input)  : return
    a0 (output) : 0 = no RLP parse failure; 1 = some header failed RLP parse.

  The real validity verdict lives in the two output memory cells:
    *is_valid       : 1 iff every header's field-12 length ≤ 32, else 0 (first
                      violation).
    *first_bad_index: index of the first bad header (violation or parse-fail).

  Per iteration `i` (`i < N`) the program:
    * loads `len_i := header_lengths[i]` (aligned array load at `x9 + i*8`);
    * calls the verified strict `rlp_list_nth_item` selector on the current
      header (base `x18`, list length `len_i`, field index 12);
    * on parse failure → `a0 = 1`, `*first_bad = i`, return;
    * else reloads the field-12 content length and compares with 32
      (`bltu x7=32, x6=len` = `32 <ᵤ len`):
        - `len > 32` → `*is_valid = 0`, `*first_bad = i`, `a0 = 0`, return;
        - `len ≤ 32` → advance `x18 += header_lengths[i]`, `i += 1`, loop.
    * loop exhausted (`i = N`) → `a0 = 0`, `*is_valid` stays 1.

  This file carries the shared model, the emitted-code infrastructure, and the
  reusable loop-induction lemma.  Each per-header field-12 length is tied to the
  ACTUAL decoded length via K20's `Result` relation at index `i`, so the final
  `∀ i < N` postcondition is genuine.
-/

import EvmAsm.Codegen.Programs.ChainValidate
import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.ChainValidateExtraDataLengthSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## Base addresses and linked code -/

/-- Chain accessor base address. -/
abbrev C : Word := (GuestAddrs.chain_validate_extra_data_length : Word)

/-- The chain accessor's own program. -/
abbrev cvedlProg : Program := EvmAsm.Codegen.chainValidateExtraDataLength_prog

theorem cvedl_length : cvedlProg.length = 69 := by decide

/-- The chain accessor's re-emitted instructions at its base. -/
def cvedlCode : CodeReq := CodeReq.ofProg C cvedlProg

/-- The full linked closure: the chain accessor plus the strict K20 selector and
    its transitive callees. -/
def fullCode : CodeReq := cvedlCode.union EvmAsm.Codegen.RlpListNthItemSAsm.code

theorem cvedl_disjoint :
    cvedlCode.Disjoint EvmAsm.Codegen.RlpListNthItemSAsm.code := by
  unfold cvedlCode EvmAsm.Codegen.RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [cvedl_length]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · right
    rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide

#print axioms cvedl_disjoint

/-- K20's linked code is subsumed by the chain accessor's full closure. -/
theorem k20_mono :
    ∀ a i, EvmAsm.Codegen.RlpListNthItemSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right cvedl_disjoint (fun _ _ h => h) a i hi

theorem cvedl_mono : ∀ a i, cvedlCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

/-! ## `wordArray` : a dword-cell array region

    A separating region of consecutive 8-byte cells holding
    `BitVec.ofNat 64 xs[k]` at `base + 8*(start+k)`.  Reusable by all sibling
    `chainValidate*` accessors that stride an aligned `u64` array. -/

def wordArrayFrom (base : Word) (start : Nat) : List Nat → Assertion
  | [] => empAssertion
  | x :: xs =>
    ((base + BitVec.ofNat 64 (8 * start)) ↦ₘ BitVec.ofNat 64 x) **
      wordArrayFrom base (start + 1) xs

/-- The array region rooted at `base`, cell `k` at `base + 8*k`. -/
def wordArray (base : Word) (xs : List Nat) : Assertion := wordArrayFrom base 0 xs

/-- Concatenation splits a `wordArrayFrom` region additively in the index. -/
theorem wordArrayFrom_append (base : Word) (start : Nat) (as bs : List Nat) :
    wordArrayFrom base start (as ++ bs) =
      (wordArrayFrom base start as ** wordArrayFrom base (start + as.length) bs) := by
  induction as generalizing start with
  | nil => simp [wordArrayFrom, sepConj_emp_left']
  | cons a as ih =>
    simp only [List.cons_append, wordArrayFrom, List.length_cons]
    rw [ih (start + 1), sepConj_assoc',
      show start + 1 + as.length = start + (as.length + 1) from by omega]

/-- Extract cell `i` from a `wordArray`, leaving the rest of the region framed. -/
theorem wordArray_split (base : Word) (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    wordArray base xs =
      (wordArrayFrom base 0 (xs.take i) **
        ((base + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 xs[i]) **
        wordArrayFrom base (i + 1) (xs.drop (i + 1))) := by
  unfold wordArray
  conv_lhs => rw [← List.take_append_drop i xs]
  rw [wordArrayFrom_append]
  have hdrop : xs.drop i = xs[i] :: xs.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi]
  rw [hdrop, wordArrayFrom, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi),
    Nat.zero_add]

/-! ## Model of the header array

    The chain iterates over `lengths : List Nat` header byte-lengths (the values
    of the aligned `header_lengths[]` array at `lenBase`) and a concatenated
    `bigBytes` blob at `hdrBase`.  Header `i` occupies `bigBytes` from byte
    offset `hdrOff lengths i` (= sum of the earlier lengths), so its RLP list
    base is `hdrBaseAt hdrBase lengths i` and its declared list length is
    `lengths[i]`. -/

/-- Scratch-cell addresses (module globals written/read across the K20 call). -/
abbrev IterPtr : Word := (GuestAddrs.cvedl_iter_ptr : Word)
abbrev IterI : Word := (GuestAddrs.cvedl_iter_i : Word)
abbrev COff : Word := (GuestAddrs.cvedl_offset : Word)
abbrev CLen : Word := (GuestAddrs.cvedl_length : Word)

/-- The link address written into `ra` by the loop-body `jal` (the K20 return
    site), = `C + 136`.  Every iteration calls K20 with this `saved.ra`. -/
abbrev LinkRA : Word := C + 136

/-- Byte offset of header `i` within the concatenated blob. -/
def hdrOff (lengths : List Nat) (i : Nat) : Nat := (lengths.take i).sum

/-- RLP list base pointer of header `i`. -/
def hdrBaseAt (hdrBase : Word) (lengths : List Nat) (i : Nat) : Word :=
  hdrBase + BitVec.ofNat 64 (hdrOff lengths i)

/-- Header `i` parses field 12 successfully with content length ≤ 32. -/
def hdrValidShort (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) : Prop :=
  ∃ offset len,
    Success (bigBytes.drop (hdrOff lengths i)) (hdrBaseAt hdrBase lengths i)
      (lengths[i]!) 12 offset len ∧ ¬ BitVec.ult (32 : Word) len

/-- Header `i` parses field 12 successfully but with content length > 32. -/
def hdrLong (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) : Prop :=
  ∃ offset len,
    Success (bigBytes.drop (hdrOff lengths i)) (hdrBaseAt hdrBase lengths i)
      (lengths[i]!) 12 offset len ∧ BitVec.ult (32 : Word) len

/-- Header `i` fails RLP parse of field 12. -/
def hdrFail (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) : Prop :=
  Failure (bigBytes.drop (hdrOff lengths i)) (hdrBaseAt hdrBase lengths i)
    (lengths[i]!) 12

/-! ## Frames -/

/-- Static memory/register footprint carried unchanged through the whole loop:
    the header-length array, the concatenated header blob, and the four scratch
    cells (owned).  `chainFrame` (the accessor's saved-register slots) sits
    separately. -/
def payload (hdrBase lenBase : Word) (bigBytes : List (BitVec 8))
    (lengths : List Nat) : Assertion :=
  wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
  memOwn COff ** memOwn CLen ** memOwn IterPtr ** memOwn IterI

/-- Callee-preserved registers owned + the K20 frame slots owned + the four
    non-preserved scratch registers owned.  (`x8/x9/x18/x19/x20/x21`, the
    accessor's live loop state, are tracked explicitly in `LoopInv`.) -/
def scratchRegs (calleeNewSp : Word) : Assertion :=
  regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** frameSlotsOwn listNthFrame calleeNewSp

/-- Loop invariant at the guard (`C + 68`) entering iteration `i` (`i ≤ N`).
    The accessor's live state: `x8 = N`, `x9 = lenBase`, `x18 = current header
    base`, `x19 = validPtr`, `x20 = firstBadPtr`, `x21 = i`; the caller's saved
    registers spilled in `chainFrame`; the output cells still `1`/`0` (valid so
    far); the static `payload`; and the K20 scratch owned. -/
def LoopInv (_sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
  (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
  (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
  savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
  payload hdrBase lenBase bigBytes lengths ** scratchRegs calleeNewSp

/-- Return footprint shared by all three post arms: `ra`/`sp` restored to the
    caller's, all callee-saved registers restored, the accessor's scratch owned,
    and the static `payload` intact. -/
def commonRet (sp0 spC calleeNewSp hdrBase lenBase : Word) (csaved : Saved)
    (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  (.x1 ↦ᵣ csaved.ra) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) **
  (.x18 ↦ᵣ csaved.s2) ** (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) **
  (.x21 ↦ᵣ csaved.s5) ** savedFrame spC csaved **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  frameSlotsOwn listNthFrame calleeNewSp ** payload hdrBase lenBase bigBytes lengths

/-- All headers valid: `a0 = 0`, `*validPtr = 1`, `*firstBadPtr = 0`, and every
    header `< N` parses field 12 with length ≤ 32. -/
def postAllValid (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  ⌜∀ j, j < lengths.length → hdrValidShort hdrBase bigBytes lengths j⌝ **
  (.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
  commonRet sp0 spC calleeNewSp hdrBase lenBase csaved bigBytes lengths

/-- First violation at `k`: `a0 = 0`, `*validPtr = 0`, `*firstBadPtr = k`,
    header `k` parses long, and all earlier headers are valid-short. -/
def postViolation (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  fun h => ∃ k,
    (⌜k < lengths.length ∧ (∀ j, j < k → hdrValidShort hdrBase bigBytes lengths j) ∧
        hdrLong hdrBase bigBytes lengths k⌝ **
      (.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
      (firstBadPtr ↦ₘ BitVec.ofNat 64 k) **
      commonRet sp0 spC calleeNewSp hdrBase lenBase csaved bigBytes lengths) h

/-- First parse failure at `k`: `a0 = 1`, `*firstBadPtr = k`, `*validPtr = 1`,
    header `k` fails RLP parse, and all earlier headers are valid-short. -/
def postParseFail (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  fun h => ∃ k,
    (⌜k < lengths.length ∧ (∀ j, j < k → hdrValidShort hdrBase bigBytes lengths j) ∧
        hdrFail hdrBase bigBytes lengths k⌝ **
      (.x10 ↦ᵣ (1 : Word)) ** (validPtr ↦ₘ (1 : Word)) **
      (firstBadPtr ↦ₘ BitVec.ofNat 64 k) **
      commonRet sp0 spC calleeNewSp hdrBase lenBase csaved bigBytes lengths) h

/-- Three-way whole-program post: all-valid, first-violation, or first
    parse-failure, each genuinely tied to the actual per-header `Result`s. -/
def cvedlPost (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  fun h =>
    postAllValid sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
        bigBytes lengths h ∨
    postViolation sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
        bigBytes lengths h ∨
    postParseFail sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
        bigBytes lengths h

end EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
