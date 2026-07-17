/-
  Whole-program caller contract for the 66-instruction
  `chain_validate_blob_gas_used_under_max` accessor.

  `chainValidateBlobGasUsedUnderMax_prog` iterates over an array of `N` block
  headers and validates that EVERY header's `blob_gas_used` (RLP field 17)
  decodes to a `u64` that is at most
  `MAX_BLOB_GAS_PER_BLOCK = 21 * GAS_PER_BLOB = 21 * 131072 = 2752512`.

  It is the FIRST sibling of the `chain_validate_extra_data_length`
  pattern-setter, reusing the generic array-loop infrastructure
  (`wordArray`, `hdrOff`/`hdrBaseAt`, the `ret*` exit shapes) from
  `ChainValidateExtraDataLengthSpec`.  The per-header body differs: the callee
  is the strict `rlp_field_to_u64` (K34) wrapper (field decoded to a u64 tied
  to the field bytes via K34's `Result`), and the check is an
  `MAX_BLOB_GAS_PER_BLOCK` `bltu` compare rather than a length compare.

  Calling convention (see `ChainValidateBlob.lean`):
    a0 (input)  : N (header count)
    a1 (input)  : header_lengths ptr (array of N u64 byte-lengths, 8-aligned)
    a2 (input)  : headers ptr (concatenated header blobs)
    a3 (input)  : u64 out cell (is_valid)
    a4 (input)  : u64 out cell (first_bad_index)
    ra (input)  : return
    a0 (output) : 0 = every header under max; 1 = some header failed RLP parse
                  (list-failure / noncanonical scalar); 2 = some header's
                  blob_gas_used field is wider than 8 bytes.

  The real validity verdict lives in the two output memory cells:
    *is_valid       : 1 iff every header's field-17 u64 ≤ 2752512, else 0.
    *first_bad_index: index of the first bad header (violation or parse-fail).

  Per iteration `i` (`i < N`) the program:
    * loads `len_i := header_lengths[i]` (aligned array load at `x9 + i*8`);
    * calls the verified strict `rlp_field_to_u64` on the current header
      (base `x18`, list length `len_i`, field index 17, output cell `Field`);
    * on status ≠ 0 → `a0 = status`, `*first_bad = i`, return (parse-fail);
    * else reloads the decoded value and compares with 2752512
      (`bltu x7=2752512, x6=value` = `2752512 <ᵤ value`):
        - `value > 2752512` → `*is_valid = 0`, `*first_bad = i`, `a0 = 0`;
        - `value ≤ 2752512` → advance `x18 += header_lengths[i]`, `i += 1`.
    * loop exhausted (`i = N`) → `a0 = 0`, `*is_valid` stays 1.

  Each per-header value is tied to the ACTUAL decoded u64 via K34's `Result`
  at the actual header base, so the final `∀ i < N` postcondition is genuine.
-/

import EvmAsm.Codegen.Programs.ChainValidateBlob
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthLoop
import EvmAsm.Codegen.Programs.RlpFieldToU64FlatSAsm
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Codegen.ChainValidateBlobGasUnderMaxSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm
  (Saved savedFrame savedVals listNthFrame regsAt_listNthFrame
   frameSlotsSaved_listNthFrame)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom
   wordArrayFrom_append shiftLeft3_ofNat hdrOff hdrBaseAt hdrOff_succ hdrBaseAt_succ
   ofNat_ne_of_lt ofNat_succ_tie)

/-! ## Base addresses and linked code -/

/-- Chain accessor base address. -/
abbrev D : Word := (GuestAddrs.chain_validate_blob_gas_used_under_max : Word)

/-- The chain accessor's own program. -/
abbrev cvbgumProg : Program := EvmAsm.Codegen.chainValidateBlobGasUsedUnderMax_prog

theorem cvbgum_length : cvbgumProg.length = 66 := by decide

/-- The chain accessor's re-emitted instructions at its base. -/
def cvbgumCode : CodeReq := CodeReq.ofProg D cvbgumProg

/-- The full linked closure: the chain accessor plus the strict K34
    `rlp_field_to_u64` wrapper and its transitive callees. -/
def fullCode : CodeReq := cvbgumCode.union EvmAsm.Codegen.RlpFieldToU64SAsm.code

theorem cvbgum_disjoint :
    cvbgumCode.Disjoint EvmAsm.Codegen.RlpFieldToU64SAsm.code := by
  unfold cvbgumCode EvmAsm.Codegen.RlpFieldToU64SAsm.code
    EvmAsm.Codegen.RlpFieldToU64SAsm.wrapperCode EvmAsm.Codegen.RlpFieldToU64SAsm.contentCode
  refine CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.union_right ?_ ?_)
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [cvbgum_length]; decide
    · rw [EvmAsm.Codegen.RlpFieldToU64SAsm.program_length]; decide
    · right; rw [EvmAsm.Codegen.RlpFieldToU64SAsm.program_length]; decide
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [cvbgum_length]; decide
    · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
    · right; rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · unfold EvmAsm.Rv64.RLP.rlp_content_to_u64_code
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [cvbgum_length]; decide
    · rw [EvmAsm.Rv64.RLP.rlp_content_to_u64_prog_length]; decide
    · left; rw [cvbgum_length]; decide


/-- K34's linked code is subsumed by the chain accessor's full closure. -/
theorem k34_mono :
    ∀ a i, EvmAsm.Codegen.RlpFieldToU64SAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right cvbgum_disjoint (fun _ _ h => h) a i hi

theorem cvbgum_mono : ∀ a i, cvbgumCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

/-! ## Model of the header array -/

/-- Scratch-cell addresses. -/
abbrev IterPtr : Word := (GuestAddrs.cvbgum_iter_ptr : Word)
abbrev IterI : Word := (GuestAddrs.cvbgum_iter_i : Word)
abbrev Field : Word := (GuestAddrs.cvbgum_field : Word)

/-- K34's internal scratch cells (owned across the call, threaded unchanged). -/
abbrev RfuOff : Word := (GuestAddrs.rfu_offset : Word)
abbrev RfuLen : Word := (GuestAddrs.rfu_length : Word)

/-- The link address written into `ra` by the loop-body `jal` (the K34 return
    site), = `D + 128`. -/
abbrev LinkRA : Word := D + 128

/-- The blob-gas-per-block ceiling: `21 * 131072 = 2752512`, materialized by
    `lui x7, 672` (`672 <<< 12`). -/
abbrev MaxBlobGas : Word := (2752512 : Word)

/-- Header `i` decodes field 17 to a u64 `value ≤ MAX_BLOB_GAS_PER_BLOCK`. -/
def hdrUnderMax (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) : Prop :=
  ∃ value,
    EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
      (hdrBaseAt hdrBase lengths i) (lengths[i]!) 17 0 value ∧
    ¬ BitVec.ult MaxBlobGas value

/-- Header `i` decodes field 17 to a u64 `value > MAX_BLOB_GAS_PER_BLOCK`. -/
def hdrOverMax (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) : Prop :=
  ∃ value,
    EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
      (hdrBaseAt hdrBase lengths i) (lengths[i]!) 17 0 value ∧
    BitVec.ult MaxBlobGas value

/-- Header `i` fails the strict field-17 u64 decode (status ≠ 0). -/
def hdrBadParse (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) (status : Word) : Prop :=
  ∃ value,
    EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
      (hdrBaseAt hdrBase lengths i) (lengths[i]!) 17 status value ∧ status ≠ 0

/-! ## Frames -/

/-- Static memory/register footprint carried unchanged through the whole loop:
    the header-length array, the concatenated header blob, and the five scratch
    cells (owned).  The accessor's saved-register slots sit separately. -/
def payload (hdrBase lenBase : Word) (bigBytes : List (BitVec 8))
    (lengths : List Nat) : Assertion :=
  wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
  memOwn Field ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterPtr ** memOwn IterI

/-- Callee-perturbed registers owned + the K34 frame slots owned + the callee's
    8-dword allocatable stack + `x0`. -/
def scratchRegs (calleeNewSp : Word) : Assertion :=
  regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
  stackFree calleeNewSp 8

/-- Loop invariant at the guard (`D + 68`) entering iteration `i` (`i ≤ N`). -/
def LoopInv (_sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
  (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
  (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
  savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
  payload hdrBase lenBase bigBytes lengths ** scratchRegs calleeNewSp

/-- Return footprint shared by all three post arms. -/
def commonRet (sp0 spC calleeNewSp hdrBase lenBase : Word) (csaved : Saved)
    (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  (.x1 ↦ᵣ csaved.ra) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) **
  (.x18 ↦ᵣ csaved.s2) ** (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) **
  (.x21 ↦ᵣ csaved.s5) ** savedFrame spC csaved **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
  regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
  stackFree calleeNewSp 8 ** payload hdrBase lenBase bigBytes lengths

/-- All headers under max: `a0 = 0`, `*validPtr = 1`, `*firstBadPtr = 0`, and
    every header `< N` decodes field 17 to a u64 ≤ 2752512. -/
def postAllValid (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  ⌜∀ j, j < lengths.length → hdrUnderMax hdrBase bigBytes lengths j⌝ **
  (.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
  commonRet sp0 spC calleeNewSp hdrBase lenBase csaved bigBytes lengths

/-- First violation at `k`: `a0 = 0`, `*validPtr = 0`, `*firstBadPtr = k`,
    header `k` decodes over max, and all earlier headers are under max. -/
def postViolation (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  fun h => ∃ k,
    (⌜k < lengths.length ∧ (∀ j, j < k → hdrUnderMax hdrBase bigBytes lengths j) ∧
        hdrOverMax hdrBase bigBytes lengths k⌝ **
      (.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
      (firstBadPtr ↦ₘ BitVec.ofNat 64 k) **
      commonRet sp0 spC calleeNewSp hdrBase lenBase csaved bigBytes lengths) h

/-- First parse failure at `k`: `a0 = status` (the actual nonzero K34 status),
    `*firstBadPtr = k`, `*validPtr = 1`, header `k` fails the strict field-17
    decode, and all earlier headers are under max. -/
def postParseFail (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  fun h => ∃ k status,
    (⌜k < lengths.length ∧ (∀ j, j < k → hdrUnderMax hdrBase bigBytes lengths j) ∧
        hdrBadParse hdrBase bigBytes lengths k status⌝ **
      (.x10 ↦ᵣ status) ** (validPtr ↦ₘ (1 : Word)) **
      (firstBadPtr ↦ₘ BitVec.ofNat 64 k) **
      commonRet sp0 spC calleeNewSp hdrBase lenBase csaved bigBytes lengths) h

/-- Three-way whole-program post: all-under-max, first-violation, or first
    parse-failure, each genuinely tied to the actual per-header `Result`s. -/
def cvbgumPost (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  fun h =>
    postAllValid sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
        bigBytes lengths h ∨
    postViolation sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
        bigBytes lengths h ∨
    postParseFail sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
        bigBytes lengths h

/-! ## Prologue (instructions 0--16): set up the loop-entry state

    Byte-identical to the `chain_validate_extra_data_length` prologue. -/

set_option maxRecDepth 8000 in
theorem cvbgumPrologue
    (sp0 spC nWord lenBase hdrBase validPtr firstBadPtr raIn
      cs0 cs1 cs2 cs3 cs4 cs5 old5 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12)) :
    cpsTripleWithin 17 D (D + 68) cvbgumCode
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
  have h0 := addi_spec_gen_same_within .x2 sp0 (-56 : BitVec 12) D (by decide)
  have h1 := sd_spec_gen_own_within .x2 .x1
    (sp0 + signExtend12 (-56 : BitVec 12)) raIn (0 : BitVec 12) (D + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-56 : BitVec 12)) + (0 : Word)
      = sp0 + signExtend12 (-56 : BitVec 12) from by bv_omega] at h1
  have h2 := sd_spec_gen_own_within .x2 .x8
    (sp0 + signExtend12 (-56 : BitVec 12)) cs0 (8 : BitVec 12) (D + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at h2
  have h3 := sd_spec_gen_own_within .x2 .x9
    (sp0 + signExtend12 (-56 : BitVec 12)) cs1 (16 : BitVec 12) (D + 12)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at h3
  have h4 := sd_spec_gen_own_within .x2 .x18
    (sp0 + signExtend12 (-56 : BitVec 12)) cs2 (24 : BitVec 12) (D + 16)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at h4
  have h5 := sd_spec_gen_own_within .x2 .x19
    (sp0 + signExtend12 (-56 : BitVec 12)) cs3 (32 : BitVec 12) (D + 20)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at h5
  have h6 := sd_spec_gen_own_within .x2 .x20
    (sp0 + signExtend12 (-56 : BitVec 12)) cs4 (40 : BitVec 12) (D + 24)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at h6
  have h7 := sd_spec_gen_own_within .x2 .x21
    (sp0 + signExtend12 (-56 : BitVec 12)) cs5 (48 : BitVec 12) (D + 28)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at h7
  have h8 := mv_spec_gen_within .x8 .x10 nWord cs0 (D + 32) (by decide)
  have h9 := mv_spec_gen_within .x9 .x11 lenBase cs1 (D + 36) (by decide)
  have h10 := mv_spec_gen_within .x18 .x12 hdrBase cs2 (D + 40) (by decide)
  have h11 := mv_spec_gen_within .x19 .x13 validPtr cs3 (D + 44) (by decide)
  have h12 := mv_spec_gen_within .x20 .x14 firstBadPtr cs4 (D + 48) (by decide)
  have h13 := li_spec_gen_within .x5 old5 (1 : Word) (D + 52) (by decide)
  have h14 := sd_spec_gen_own_within .x19 .x5 validPtr (1 : Word) (0 : BitVec 12) (D + 56)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show validPtr + (0 : Word) = validPtr from by bv_omega] at h14
  have h15 := sd_spec_gen_own_within .x20 .x0 firstBadPtr (0 : Word) (0 : BitVec 12) (D + 60)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show firstBadPtr + (0 : Word) = firstBadPtr from by bv_omega] at h15
  have h16 := li_spec_gen_within .x21 cs5 (0 : Word) (D + 64) (by decide)
  runBlock h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16


/-! ## Epilogue (instructions 57--65): restore + return -/

set_option maxRecDepth 8000 in
theorem cvbgumEpilogue
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 9 (D + 228) raIn cvbgumCode
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
    (0 : BitVec 12) (D + 228) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-56 : BitVec 12)) + (0 : Word)
      = sp0 + signExtend12 (-56 : BitVec 12) from by bv_omega] at l0
  have l1 := ld_spec_gen_within .x8 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o8 cs0
    (8 : BitVec 12) (D + 232) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at l1
  have l2 := ld_spec_gen_within .x9 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o9 cs1
    (16 : BitVec 12) (D + 236) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at l2
  have l3 := ld_spec_gen_within .x18 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o18 cs2
    (24 : BitVec 12) (D + 240) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at l3
  have l4 := ld_spec_gen_within .x19 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o19 cs3
    (32 : BitVec 12) (D + 244) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at l4
  have l5 := ld_spec_gen_within .x20 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o20 cs4
    (40 : BitVec 12) (D + 248) (by decide)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at l5
  have l6 := ld_spec_gen_within .x21 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o21 cs5
    (48 : BitVec 12) (D + 252) (by decide)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at l6
  have l7 := addi_spec_gen_same_within .x2 (sp0 + signExtend12 (-56 : BitVec 12))
    (56 : BitVec 12) (D + 256) (by decide)
  rw [show (sp0 + signExtend12 (-56 : BitVec 12)) + signExtend12 (56 : BitVec 12) = sp0
      from by rw [show signExtend12 (-56 : BitVec 12) = (-56 : Word) from by decide,
        show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]; bv_omega] at l7
  have hblock : cpsTripleWithin 8 (D + 228) (D + 260) cvbgumCode
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
  have hjalr := EvmAsm.Evm64.ret_spec_within' (D + 260) raIn
  rw [hret] at hjalr
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 260) cvbgumProg 65 (.JALR .x0 .x1 (0 : BitVec 12))
      (by bv_omega) (by rw [cvbgum_length]; decide) rfl (by rw [cvbgum_length]; decide))
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


/-! ## All-valid exit (instruction 56 → epilogue): `a0 := 0`, then return -/

set_option maxRecDepth 8000 in
theorem retAllValid
    (sp0 spC raIn : Word) (csaved : Saved) (G : Assertion) (hG : G.pcFree)
    (o10 o1 o8 o9 o18 o19 o20 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 10 (D + 224) raIn cvbgumCode
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
  have h56 := li_spec_gen_within .x10 o10 (0 : Word) (D + 224) (by decide)
  have h56C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 224) cvbgumProg 56 (.LI .x10 (0 : Word))
      (by bv_omega) (by rw [cvbgum_length]; decide) rfl (by rw [cvbgum_length]; decide))
    h56
  have h56F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ csaved.ra) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
      ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
      ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) h56C
  have hepi := cvbgumEpilogue sp0 spC csaved.ra csaved.s0 csaved.s1 csaved.s2 csaved.s3
    csaved.s4 csaved.s5 o1 o8 o9 o18 o19 o20 o21 hspC hret
  have hepiF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (0 : Word)) ** G)
    (by refine pcFree_sepConj ?_ hG; pcf) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h56F hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


/-! ## Violation exit (instructions 50--53 → epilogue)

    `*validPtr := 0`, `*firstBadPtr := i`, `a0 := 0`, `jal +16` to epilogue. -/

set_option maxRecDepth 8000 in
theorem retViolation
    (sp0 spC raIn iWord validPtr firstBadPtr : Word) (csaved : Saved)
    (G : Assertion) (hG : G.pcFree) (o10 o1 o8 o9 o18 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 13 (D + 200) raIn cvbgumCode
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
  have s50 := sd_spec_gen_own_within .x19 .x0 validPtr (0 : Word) (0 : BitVec 12) (D + 200)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show validPtr + (0 : Word) = validPtr from by bv_omega] at s50
  have s51 := sd_spec_gen_own_within .x20 .x21 firstBadPtr iWord (0 : BitVec 12) (D + 204)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show firstBadPtr + (0 : Word) = firstBadPtr from by bv_omega] at s51
  have s52 := li_spec_gen_within .x10 o10 (0 : Word) (D + 208) (by decide)
  have s53 := jal_x0_spec_gen_within (16 : BitVec 21) (D + 212)
  rw [show (D + 212) + signExtend21 (16 : BitVec 21) = D + 228 from by
    rw [show signExtend21 (16 : BitVec 21) = (16 : Word) from by decide]; bv_omega] at s53
  have hblock : cpsTripleWithin 4 (D + 200) (D + 228) cvbgumCode
      ((.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn validPtr **
        (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iWord) ** memOwn firstBadPtr ** (.x10 ↦ᵣ o10))
      ((.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
        (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iWord) ** (firstBadPtr ↦ₘ iWord) **
        (.x10 ↦ᵣ (0 : Word))) := by
    runBlock s50 s51 s52 s53
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (spC ↦ₘ csaved.ra) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
      ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
      ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hblock
  have hepi := cvbgumEpilogue sp0 spC csaved.ra csaved.s0 csaved.s1 csaved.s2 csaved.s3
    csaved.s4 csaved.s5 o1 o8 o9 o18 validPtr firstBadPtr iWord hspC hret
  have hepiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) ** (firstBadPtr ↦ₘ iWord) **
      (.x0 ↦ᵣ (0 : Word)) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


/-! ## Parse-fail exit (instructions 54--55 → epilogue)

    `*firstBadPtr := i`, `jal +8` to epilogue.  `a0` (=`x10`) is left holding the
    callee's nonzero status, threaded in `G`. -/

set_option maxRecDepth 8000 in
theorem retParseFail
    (sp0 spC raIn iWord firstBadPtr : Word) (csaved : Saved)
    (G : Assertion) (hG : G.pcFree) (o1 o8 o9 o18 o19 o10 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 11 (D + 216) raIn cvbgumCode
      ((.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iWord) ** (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) **
        memOwn firstBadPtr **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
      ((.x10 ↦ᵣ o10) ** (firstBadPtr ↦ₘ iWord) ** (.x1 ↦ᵣ raIn) **
        (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) **
        (.x18 ↦ᵣ csaved.s2) ** (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) **
        (.x21 ↦ᵣ csaved.s5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G) := by
  subst hraSaved
  have s54 := sd_spec_gen_own_within .x20 .x21 firstBadPtr iWord (0 : BitVec 12) (D + 216)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show firstBadPtr + (0 : Word) = firstBadPtr from by bv_omega] at s54
  have s55 := jal_x0_spec_gen_within (8 : BitVec 21) (D + 220)
  rw [show (D + 220) + signExtend21 (8 : BitVec 21) = D + 228 from by
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega] at s55
  have hblock : cpsTripleWithin 2 (D + 216) (D + 228) cvbgumCode
      ((.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iWord) ** memOwn firstBadPtr)
      ((.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iWord) ** (firstBadPtr ↦ₘ iWord)) := by
    runBlock s54 s55
  have hblockF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
      (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) **
      (spC ↦ₘ csaved.ra) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
      ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
      ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hblock
  have hepi := cvbgumEpilogue sp0 spC csaved.ra csaved.s0 csaved.s1 csaved.s2 csaved.s3
    csaved.s4 csaved.s5 o1 o8 o9 o18 o19 firstBadPtr iWord hspC hret
  have hepiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (firstBadPtr ↦ₘ iWord) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


end EvmAsm.Codegen.ChainValidateBlobGasUnderMaxSpec
