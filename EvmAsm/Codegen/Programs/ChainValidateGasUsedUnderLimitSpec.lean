/-
  Whole-program caller contract for the 83-instruction
  `chain_validate_gas_used_under_limit` accessor.

  `chainValidateGasUsedUnderLimit_prog` iterates over an array of `N` block
  headers and validates that EVERY header's `gas_used` (RLP field 10) is at
  most its `gas_limit` (RLP field 9).

  It is the THIRD sibling of the `chain_validate_extra_data_length`
  pattern-setter, reusing the generic array-loop infrastructure
  (`wordArray`, `hdrOff`/`hdrBaseAt`, the `ret*` exit shapes) from
  `ChainValidateExtraDataLengthSpec` and the strict `rlp_field_to_u64_strict` (K34)
  call composition from `ChainValidateBlobGasUnderMaxSpec`.  Unlike the blob
  sibling the per-header body makes TWO K34 calls (field 10 = gas_used, field
  9 = gas_limit) and compares the two decoded u64s with a dynamic `bltu`.

  Calling convention (see `ChainValidate.lean`):
    a0 (input)  : N (header count)
    a1 (input)  : header_lengths ptr (array of N u64 byte-lengths, 8-aligned)
    a2 (input)  : headers ptr (concatenated header blobs)
    a3 (input)  : u64 out cell (is_valid)
    a4 (input)  : u64 out cell (first_bad_index)
    ra (input)  : return
    a0 (output) : 0 = every header has gas_used ≤ gas_limit; nonzero = some
                  header's field 10 or field 9 failed the strict RLP u64 decode.

  The real validity verdict lives in the two output memory cells:
    *is_valid       : 1 iff every header's gas_used ≤ gas_limit, else 0.
    *first_bad_index: index of the first bad header (violation or parse-fail).

  Per iteration `i` (`i < N`) the program:
    * loads `len_i := header_lengths[i]` (aligned array load at `x9 + i*8`);
    * calls the verified strict `rlp_field_to_u64_strict` on the current header for
      field 10 (gas_used → the `GasUsed` cell);
    * on status ≠ 0 → `a0 = status`, `*first_bad = i`, return (parse-fail);
    * reloads iterator state and calls `rlp_field_to_u64_strict` again for field 9
      (gas_limit → the `GasLimit` cell);
    * on status ≠ 0 → `a0 = status`, `*first_bad = i`, return (parse-fail);
    * else reloads both decoded values and compares (`bltu x7=gl, x6=gu` =
      `gl <ᵤ gu`):
        - `gu > gl` → `*is_valid = 0`, `*first_bad = i`, `a0 = 0`;
        - `gu ≤ gl` → advance `x18 += header_lengths[i]`, `i += 1`.
    * loop exhausted (`i = N`) → `a0 = 0`, `*is_valid` stays 1.

  Both per-header values are tied to the ACTUAL decoded u64 via K34's `Result`
  at the actual header base, so the final `∀ i < N` postcondition is genuine.
-/

import EvmAsm.Codegen.Programs.ChainValidateBlobGasUnderMaxSpec
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthLoop
import EvmAsm.Codegen.Programs.RlpFieldToU64StrictFlatSAsm
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Codegen.ChainValidateGasUsedUnderLimitSpec

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
abbrev D : Word := (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit : Word)

/-- The chain accessor's own program. -/
abbrev cvgulProg : Program := EvmAsm.Codegen.chainValidateGasUsedUnderLimit_prog

theorem cvgul_length : cvgulProg.length = 83 := by decide

/-- The chain accessor's re-emitted instructions at its base. -/
def cvgulCode : CodeReq := CodeReq.ofProg D cvgulProg

/-- The full linked closure: the chain accessor plus the strict K34
    `rlp_field_to_u64_strict` wrapper and its transitive callees. -/
def fullCode : CodeReq := cvgulCode.union EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code

theorem cvgul_disjoint :
    cvgulCode.Disjoint EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code := by
  unfold cvgulCode EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.wrapperCode EvmAsm.Codegen.RlpFieldToU64StrictSAsm.contentCode
  refine CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.union_right ?_ ?_)
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [cvgul_length]; decide
    · rw [EvmAsm.Codegen.RlpFieldToU64StrictSAsm.program_length]; decide
    · left; rw [cvgul_length]; decide
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [cvgul_length]; decide
    · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
    · right; rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · unfold EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_code
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [cvgul_length]; decide
    · rw [EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_prog_length]; decide
    · left; rw [cvgul_length]; decide


/-- K34's linked code is subsumed by the chain accessor's full closure. -/
theorem k34_mono :
    ∀ a i, EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right cvgul_disjoint (fun _ _ h => h) a i hi

theorem cvgul_mono : ∀ a i, cvgulCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

/-! ## Model of the header array -/

/-- Scratch-cell addresses. -/
abbrev IterPtr : Word := (GuestAddrs.cvgul_iter_ptr : Word)
abbrev IterI : Word := (GuestAddrs.cvgul_iter_i : Word)
abbrev GasUsed : Word := (GuestAddrs.cvgul_gas_used : Word)
abbrev GasLimit : Word := (GuestAddrs.cvgul_gas_limit : Word)

/-- K34's internal scratch cells (owned across the call, threaded unchanged). -/
abbrev RfuOff : Word := (GuestAddrs.rfu_offset : Word)
abbrev RfuLen : Word := (GuestAddrs.rfu_length : Word)

/-- The link address written into `ra` by the first loop-body `jal` (the K34
    return site of call 1), = `D + 128`. -/
abbrev LinkRA1 : Word := D + 128

/-- The link address written into `ra` by the second loop-body `jal` (the K34
    return site of call 2), = `D + 188`. -/
abbrev LinkRA2 : Word := D + 188

/-- Header `i` decodes field 10 to `gu` and field 9 to `gl`, both strictly, with
    `gas_used ≤ gas_limit` (`¬ gl <ᵤ gu`). -/
def hdrGasOk (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) : Prop :=
  ∃ gu gl,
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result (bigBytes.drop (hdrOff lengths i))
      (hdrBaseAt hdrBase lengths i) (lengths[i]!) 10 0 gu ∧
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result (bigBytes.drop (hdrOff lengths i))
      (hdrBaseAt hdrBase lengths i) (lengths[i]!) 9 0 gl ∧
    ¬ BitVec.ult gl gu

/-- Header `i` decodes both fields but `gas_used > gas_limit` (`gl <ᵤ gu`). -/
def hdrGasBad (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) : Prop :=
  ∃ gu gl,
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result (bigBytes.drop (hdrOff lengths i))
      (hdrBaseAt hdrBase lengths i) (lengths[i]!) 10 0 gu ∧
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result (bigBytes.drop (hdrOff lengths i))
      (hdrBaseAt hdrBase lengths i) (lengths[i]!) 9 0 gl ∧
    BitVec.ult gl gu

/-- Header `i` fails a strict field decode with nonzero `status`: either field
    10 (gas_used) fails, or field 10 succeeds and field 9 (gas_limit) fails. -/
def hdrGasParseFail (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) (status : Word) : Prop :=
  (∃ gu,
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result (bigBytes.drop (hdrOff lengths i))
      (hdrBaseAt hdrBase lengths i) (lengths[i]!) 10 status gu ∧ status ≠ 0) ∨
  (∃ gu gl,
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result (bigBytes.drop (hdrOff lengths i))
      (hdrBaseAt hdrBase lengths i) (lengths[i]!) 10 0 gu ∧
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result (bigBytes.drop (hdrOff lengths i))
      (hdrBaseAt hdrBase lengths i) (lengths[i]!) 9 status gl ∧ status ≠ 0)

/-! ## Frames -/

/-- Static memory/register footprint carried unchanged through the whole loop:
    the header-length array, the concatenated header blob, and the six scratch
    cells (owned).  The accessor's saved-register slots sit separately. -/
def payload (hdrBase lenBase : Word) (bigBytes : List (BitVec 8))
    (lengths : List Nat) : Assertion :=
  wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
  memOwn GasUsed ** memOwn GasLimit ** memOwn RfuOff ** memOwn RfuLen **
  memOwn IterPtr ** memOwn IterI

/-- Callee-perturbed registers owned + the K34 frame slots owned + the callee's
    8-dword allocatable stack + `x0`. -/
def scratchRegs (calleeNewSp : Word) : Assertion :=
  regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
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
  frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
  stackFree calleeNewSp 8 ** payload hdrBase lenBase bigBytes lengths

/-- All headers valid: `a0 = 0`, `*validPtr = 1`, `*firstBadPtr = 0`, and every
    header `< N` has gas_used ≤ gas_limit. -/
def postAllValid (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  ⌜∀ j, j < lengths.length → hdrGasOk hdrBase bigBytes lengths j⌝ **
  (.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
  commonRet sp0 spC calleeNewSp hdrBase lenBase csaved bigBytes lengths

/-- First violation at `k`: `a0 = 0`, `*validPtr = 0`, `*firstBadPtr = k`,
    header `k` has gas_used > gas_limit, and all earlier headers are valid. -/
def postViolation (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  fun h => ∃ k,
    (⌜k < lengths.length ∧ (∀ j, j < k → hdrGasOk hdrBase bigBytes lengths j) ∧
        hdrGasBad hdrBase bigBytes lengths k⌝ **
      (.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
      (firstBadPtr ↦ₘ BitVec.ofNat 64 k) **
      commonRet sp0 spC calleeNewSp hdrBase lenBase csaved bigBytes lengths) h

/-- First parse failure at `k`: `a0 = status` (the actual nonzero K34 status),
    `*firstBadPtr = k`, `*validPtr = 1`, header `k` fails a strict field decode,
    and all earlier headers are valid. -/
def postParseFail (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  fun h => ∃ k status,
    (⌜k < lengths.length ∧ (∀ j, j < k → hdrGasOk hdrBase bigBytes lengths j) ∧
        hdrGasParseFail hdrBase bigBytes lengths k status⌝ **
      (.x10 ↦ᵣ status) ** (validPtr ↦ₘ (1 : Word)) **
      (firstBadPtr ↦ₘ BitVec.ofNat 64 k) **
      commonRet sp0 spC calleeNewSp hdrBase lenBase csaved bigBytes lengths) h

/-- Three-way whole-program post: all-valid, first-violation, or first
    parse-failure, each genuinely tied to the actual per-header `Result`s. -/
def cvgulPost (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
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
theorem cvgulPrologue
    (sp0 spC nWord lenBase hdrBase validPtr firstBadPtr raIn
      cs0 cs1 cs2 cs3 cs4 cs5 old5 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12)) :
    cpsTripleWithin 17 D (D + 68) cvgulCode
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


/-! ## Epilogue (instructions 74--82): restore + return -/

set_option maxRecDepth 8000 in
theorem cvgulEpilogue
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 9 (D + 296) raIn cvgulCode
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
    (0 : BitVec 12) (D + 296) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-56 : BitVec 12)) + (0 : Word)
      = sp0 + signExtend12 (-56 : BitVec 12) from by bv_omega] at l0
  have l1 := ld_spec_gen_within .x8 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o8 cs0
    (8 : BitVec 12) (D + 300) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at l1
  have l2 := ld_spec_gen_within .x9 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o9 cs1
    (16 : BitVec 12) (D + 304) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at l2
  have l3 := ld_spec_gen_within .x18 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o18 cs2
    (24 : BitVec 12) (D + 308) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at l3
  have l4 := ld_spec_gen_within .x19 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o19 cs3
    (32 : BitVec 12) (D + 312) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at l4
  have l5 := ld_spec_gen_within .x20 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o20 cs4
    (40 : BitVec 12) (D + 316) (by decide)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at l5
  have l6 := ld_spec_gen_within .x21 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o21 cs5
    (48 : BitVec 12) (D + 320) (by decide)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at l6
  have l7 := addi_spec_gen_same_within .x2 (sp0 + signExtend12 (-56 : BitVec 12))
    (56 : BitVec 12) (D + 324) (by decide)
  rw [show (sp0 + signExtend12 (-56 : BitVec 12)) + signExtend12 (56 : BitVec 12) = sp0
      from by rw [show signExtend12 (-56 : BitVec 12) = (-56 : Word) from by decide,
        show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]; bv_omega] at l7
  have hblock : cpsTripleWithin 8 (D + 296) (D + 328) cvgulCode
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
  have hjalr := EvmAsm.Evm64.ret_spec_within' (D + 328) raIn
  rw [hret] at hjalr
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 328) cvgulProg 82 (.JALR .x0 .x1 (0 : BitVec 12))
      (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide))
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


/-! ## All-valid exit (instruction 73 → epilogue): `a0 := 0`, then return -/

set_option maxRecDepth 8000 in
theorem retAllValid
    (sp0 spC raIn : Word) (csaved : Saved) (G : Assertion) (hG : G.pcFree)
    (o10 o1 o8 o9 o18 o19 o20 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 10 (D + 292) raIn cvgulCode
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
  have h73 := li_spec_gen_within .x10 o10 (0 : Word) (D + 292) (by decide)
  have h73C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 292) cvgulProg 73 (.LI .x10 (0 : Word))
      (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide))
    h73
  have h73F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ csaved.ra) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
      ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
      ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) h73C
  have hepi := cvgulEpilogue sp0 spC csaved.ra csaved.s0 csaved.s1 csaved.s2 csaved.s3
    csaved.s4 csaved.s5 o1 o8 o9 o18 o19 o20 o21 hspC hret
  have hepiF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (0 : Word)) ** G)
    (by refine pcFree_sepConj ?_ hG; pcf) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h73F hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


/-! ## Violation exit (instructions 67--70 → epilogue)

    `*validPtr := 0`, `*firstBadPtr := i`, `a0 := 0`, `jal +16` to epilogue. -/

set_option maxRecDepth 8000 in
theorem retViolation
    (sp0 spC raIn iWord validPtr firstBadPtr : Word) (csaved : Saved)
    (G : Assertion) (hG : G.pcFree) (o10 o1 o8 o9 o18 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 13 (D + 268) raIn cvgulCode
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
  have s67 := sd_spec_gen_own_within .x19 .x0 validPtr (0 : Word) (0 : BitVec 12) (D + 268)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show validPtr + (0 : Word) = validPtr from by bv_omega] at s67
  have s68 := sd_spec_gen_own_within .x20 .x21 firstBadPtr iWord (0 : BitVec 12) (D + 272)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show firstBadPtr + (0 : Word) = firstBadPtr from by bv_omega] at s68
  have s69 := li_spec_gen_within .x10 o10 (0 : Word) (D + 276) (by decide)
  have s70 := jal_x0_spec_gen_within (16 : BitVec 21) (D + 280)
  rw [show (D + 280) + signExtend21 (16 : BitVec 21) = D + 296 from by
    rw [show signExtend21 (16 : BitVec 21) = (16 : Word) from by decide]; bv_omega] at s70
  have hblock : cpsTripleWithin 4 (D + 268) (D + 296) cvgulCode
      ((.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn validPtr **
        (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iWord) ** memOwn firstBadPtr ** (.x10 ↦ᵣ o10))
      ((.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
        (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iWord) ** (firstBadPtr ↦ₘ iWord) **
        (.x10 ↦ᵣ (0 : Word))) := by
    runBlock s67 s68 s69 s70
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (spC ↦ₘ csaved.ra) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
      ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
      ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hblock
  have hepi := cvgulEpilogue sp0 spC csaved.ra csaved.s0 csaved.s1 csaved.s2 csaved.s3
    csaved.s4 csaved.s5 o1 o8 o9 o18 validPtr firstBadPtr iWord hspC hret
  have hepiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) ** (firstBadPtr ↦ₘ iWord) **
      (.x0 ↦ᵣ (0 : Word)) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


/-! ## Parse-fail exit (instructions 71--72 → epilogue)

    `*firstBadPtr := i`, `jal +8` to epilogue.  `a0` (=`x10`) is left holding the
    callee's nonzero status, threaded in `G`. -/

set_option maxRecDepth 8000 in
theorem retParseFail
    (sp0 spC raIn iWord firstBadPtr : Word) (csaved : Saved)
    (G : Assertion) (hG : G.pcFree) (o1 o8 o9 o18 o19 o10 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 11 (D + 284) raIn cvgulCode
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
  have s71 := sd_spec_gen_own_within .x20 .x21 firstBadPtr iWord (0 : BitVec 12) (D + 284)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show firstBadPtr + (0 : Word) = firstBadPtr from by bv_omega] at s71
  have s72 := jal_x0_spec_gen_within (8 : BitVec 21) (D + 288)
  rw [show (D + 288) + signExtend21 (8 : BitVec 21) = D + 296 from by
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega] at s72
  have hblock : cpsTripleWithin 2 (D + 284) (D + 296) cvgulCode
      ((.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iWord) ** memOwn firstBadPtr)
      ((.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iWord) ** (firstBadPtr ↦ₘ iWord)) := by
    runBlock s71 s72
  have hblockF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
      (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) **
      (spC ↦ₘ csaved.ra) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
      ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
      ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hblock
  have hepi := cvgulEpilogue sp0 spC csaved.ra csaved.s0 csaved.s1 csaved.s2 csaved.s3
    csaved.s4 csaved.s5 o1 o8 o9 o18 o19 firstBadPtr iWord hspC hret
  have hepiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (firstBadPtr ↦ₘ iWord) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


end EvmAsm.Codegen.ChainValidateGasUsedUnderLimitSpec
