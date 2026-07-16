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
import EvmAsm.Rv64.Tactics.RunBlock

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

/-! ## Prologue (instructions 0--16): set up the loop-entry state -/

set_option maxRecDepth 8000 in
/-- Allocate the 56-byte frame, spill `ra` and the six callee-saved registers,
    move the five inputs into their loop registers, initialize `*validPtr := 1`,
    `*firstBadPtr := 0`, and `x21 := 0`.  Ends at the loop guard (`C + 68`) in
    the flat loop-entry state (this is `LoopInv` at `i = 0`, modulo packaging). -/
theorem cvedlPrologue
    (sp0 spC nWord lenBase hdrBase validPtr firstBadPtr raIn
      cs0 cs1 cs2 cs3 cs4 cs5 old5 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12)) :
    cpsTripleWithin 17 C (C + 68) cvedlCode
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
        (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (.x10 ↦ᵣ nWord) ** (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) **
        (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ firstBadPtr) ** (.x5 ↦ᵣ old5) **
        (.x0 ↦ᵣ (0 : Word)) **
        memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) ** memOwn (spC + 24) **
        memOwn (spC + 32) ** memOwn (spC + 40) ** memOwn (spC + 48) **
        memOwn validPtr ** memOwn firstBadPtr)
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ nWord) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
        (.x21 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ nWord) ** (.x11 ↦ᵣ lenBase) **
        (.x12 ↦ᵣ hdrBase) ** (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ firstBadPtr) **
        (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5) ** (validPtr ↦ₘ (1 : Word)) **
        (firstBadPtr ↦ₘ (0 : Word))) := by
  subst hspC
  have h0 := addi_spec_gen_same_within .x2 sp0 (-56 : BitVec 12) C (by decide)
  have h1 := sd_spec_gen_own_within .x2 .x1
    (sp0 + signExtend12 (-56 : BitVec 12)) raIn (0 : BitVec 12) (C + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-56 : BitVec 12)) + (0 : Word)
      = sp0 + signExtend12 (-56 : BitVec 12) from by bv_omega] at h1
  have h2 := sd_spec_gen_own_within .x2 .x8
    (sp0 + signExtend12 (-56 : BitVec 12)) cs0 (8 : BitVec 12) (C + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at h2
  have h3 := sd_spec_gen_own_within .x2 .x9
    (sp0 + signExtend12 (-56 : BitVec 12)) cs1 (16 : BitVec 12) (C + 12)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at h3
  have h4 := sd_spec_gen_own_within .x2 .x18
    (sp0 + signExtend12 (-56 : BitVec 12)) cs2 (24 : BitVec 12) (C + 16)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at h4
  have h5 := sd_spec_gen_own_within .x2 .x19
    (sp0 + signExtend12 (-56 : BitVec 12)) cs3 (32 : BitVec 12) (C + 20)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at h5
  have h6 := sd_spec_gen_own_within .x2 .x20
    (sp0 + signExtend12 (-56 : BitVec 12)) cs4 (40 : BitVec 12) (C + 24)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at h6
  have h7 := sd_spec_gen_own_within .x2 .x21
    (sp0 + signExtend12 (-56 : BitVec 12)) cs5 (48 : BitVec 12) (C + 28)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at h7
  have h8 := mv_spec_gen_within .x8 .x10 nWord cs0 (C + 32) (by decide)
  have h9 := mv_spec_gen_within .x9 .x11 lenBase cs1 (C + 36) (by decide)
  have h10 := mv_spec_gen_within .x18 .x12 hdrBase cs2 (C + 40) (by decide)
  have h11 := mv_spec_gen_within .x19 .x13 validPtr cs3 (C + 44) (by decide)
  have h12 := mv_spec_gen_within .x20 .x14 firstBadPtr cs4 (C + 48) (by decide)
  have h13 := li_spec_gen_within .x5 old5 (1 : Word) (C + 52) (by decide)
  have h14 := sd_spec_gen_own_within .x19 .x5 validPtr (1 : Word) (0 : BitVec 12) (C + 56)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show validPtr + (0 : Word) = validPtr from by bv_omega] at h14
  have h15 := sd_spec_gen_own_within .x20 .x0 firstBadPtr (0 : Word) (0 : BitVec 12) (C + 60)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show firstBadPtr + (0 : Word) = firstBadPtr from by bv_omega] at h15
  have h16 := li_spec_gen_within .x21 cs5 (0 : Word) (C + 64) (by decide)
  runBlock h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16

#print axioms cvedlPrologue

/-! ## Epilogue (instructions 60--68): restore + return

    Shared by all three exit paths.  Restores `ra` and the six callee-saved
    registers from `chainFrame`, deallocates the 56-byte frame, and returns. -/

set_option maxRecDepth 8000 in
theorem cvedlEpilogue
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 9 (C + 240) raIn cvedlCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5))
      ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
        (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5)) := by
  subst hspC
  have l0 := ld_spec_gen_within .x1 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o1 raIn
    (0 : BitVec 12) (C + 240) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-56 : BitVec 12)) + (0 : Word)
      = sp0 + signExtend12 (-56 : BitVec 12) from by bv_omega] at l0
  have l1 := ld_spec_gen_within .x8 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o8 cs0
    (8 : BitVec 12) (C + 244) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at l1
  have l2 := ld_spec_gen_within .x9 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o9 cs1
    (16 : BitVec 12) (C + 248) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at l2
  have l3 := ld_spec_gen_within .x18 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o18 cs2
    (24 : BitVec 12) (C + 252) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at l3
  have l4 := ld_spec_gen_within .x19 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o19 cs3
    (32 : BitVec 12) (C + 256) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at l4
  have l5 := ld_spec_gen_within .x20 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o20 cs4
    (40 : BitVec 12) (C + 260) (by decide)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at l5
  have l6 := ld_spec_gen_within .x21 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o21 cs5
    (48 : BitVec 12) (C + 264) (by decide)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at l6
  have l7 := addi_spec_gen_same_within .x2 (sp0 + signExtend12 (-56 : BitVec 12))
    (56 : BitVec 12) (C + 268) (by decide)
  rw [show (sp0 + signExtend12 (-56 : BitVec 12)) + signExtend12 (56 : BitVec 12) = sp0
      from by rw [show signExtend12 (-56 : BitVec 12) = (-56 : Word) from by decide,
        show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]; bv_omega] at l7
  have hblock : cpsTripleWithin 8 (C + 240) (C + 272) cvedlCode
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-56 : BitVec 12))) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) **
        (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        (.x21 ↦ᵣ o21) **
        ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ cs0) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ cs1) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ cs2) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ cs3) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ cs4) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ cs5))
      ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) ** (.x2 ↦ᵣ sp0) **
        ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ cs0) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ cs1) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ cs2) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ cs3) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ cs4) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ cs5)) := by
    runBlock l0 l1 l2 l3 l4 l5 l6 l7
  -- [68] JALR x0 x1 0 : return
  have hjalr := EvmAsm.Evm64.ret_spec_within' (C + 272) raIn
  rw [hret] at hjalr
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 272) cvedlProg 68 (.JALR .x0 .x1 (0 : BitVec 12))
      (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide))
    hjalr
  have hjalrF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) **
      (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) ** (.x2 ↦ᵣ sp0) **
      ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ cs0) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ cs1) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ cs2) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ cs3) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ cs4) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ cs5)) (by pcf) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblock hjalrF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

#print axioms cvedlEpilogue

/-! ## All-valid exit (instruction 59 → epilogue): `a0 := 0`, then return -/

set_option maxRecDepth 8000 in
/-- The loop-exhausted exit reached by the guard when `i = N`: set `a0 := 0` and
    return through the epilogue.  Generic over the passed-through frame `G`. -/
theorem retAllValid
    (sp0 spC raIn : Word) (csaved : Saved) (G : Assertion) (hG : G.pcFree)
    (o10 o1 o8 o9 o18 o19 o20 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 10 (C + 236) raIn cvedlCode
      ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) ** (.x18 ↦ᵣ csaved.s2) **
        (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G) := by
  subst hraSaved
  -- [59] LI x10 0
  have h59 := li_spec_gen_within .x10 o10 (0 : Word) (C + 236) (by decide)
  have h59C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 236) cvedlProg 59 (.LI .x10 (0 : Word))
      (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide))
    h59
  have h59F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ csaved.ra) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
      ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
      ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) h59C
  -- Epilogue.
  have hepi := cvedlEpilogue sp0 spC csaved.ra csaved.s0 csaved.s1 csaved.s2 csaved.s3
    csaved.s4 csaved.s5 o1 o8 o9 o18 o19 o20 o21 hspC hret
  have hepiF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (0 : Word)) ** G)
    (by refine pcFree_sepConj ?_ hG; pcf) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h59F hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

#print axioms retAllValid

/-! ## Violation exit (instructions 52--55 → epilogue)

    Reached when a header's field-12 length exceeds 32: `*validPtr := 0`,
    `*firstBadPtr := i`, `a0 := 0`, then return. -/

set_option maxRecDepth 8000 in
theorem retViolation
    (sp0 spC raIn iWord validPtr firstBadPtr : Word) (csaved : Saved)
    (G : Assertion) (hG : G.pcFree) (o10 o1 o8 o9 o18 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 13 (C + 208) raIn cvedlCode
      ((.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iWord) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
        memOwn validPtr ** memOwn firstBadPtr **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) ** (firstBadPtr ↦ₘ iWord) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) ** (.x18 ↦ᵣ csaved.s2) **
        (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G) := by
  subst hraSaved
  -- [52] SD x19 x0 0 : *validPtr := 0
  have s52 := sd_spec_gen_own_within .x19 .x0 validPtr (0 : Word) (0 : BitVec 12) (C + 208)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show validPtr + (0 : Word) = validPtr from by bv_omega] at s52
  -- [53] SD x20 x21 0 : *firstBadPtr := i
  have s53 := sd_spec_gen_own_within .x20 .x21 firstBadPtr iWord (0 : BitVec 12) (C + 212)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show firstBadPtr + (0 : Word) = firstBadPtr from by bv_omega] at s53
  -- [54] LI x10 0
  have s54 := li_spec_gen_within .x10 o10 (0 : Word) (C + 216) (by decide)
  -- [55] JAL x0 20 : jump to epilogue
  have s55 := jal_x0_spec_gen_within (20 : BitVec 21) (C + 220)
  rw [show (C + 220) + signExtend21 (20 : BitVec 21) = C + 240 from by
    rw [show signExtend21 (20 : BitVec 21) = (20 : Word) from by decide]; bv_omega] at s55
  have hblock : cpsTripleWithin 4 (C + 208) (C + 240) cvedlCode
      ((.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn validPtr **
        (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iWord) ** memOwn firstBadPtr ** (.x10 ↦ᵣ o10))
      ((.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
        (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iWord) ** (firstBadPtr ↦ₘ iWord) **
        (.x10 ↦ᵣ (0 : Word))) := by
    runBlock s52 s53 s54 s55
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (spC ↦ₘ csaved.ra) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
      ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
      ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hblock
  have hepi := cvedlEpilogue sp0 spC csaved.ra csaved.s0 csaved.s1 csaved.s2 csaved.s3
    csaved.s4 csaved.s5 o1 o8 o9 o18 validPtr firstBadPtr iWord hspC hret
  have hepiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) ** (firstBadPtr ↦ₘ iWord) **
      (.x0 ↦ᵣ (0 : Word)) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hepi
  -- Compose block ;; epilogue.
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

#print axioms retViolation

end EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
