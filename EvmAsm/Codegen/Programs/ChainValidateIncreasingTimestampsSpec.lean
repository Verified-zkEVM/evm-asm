/-
  Whole-program caller contract for the 92-instruction
  `chain_validate_increasing_timestamps` accessor.

  `chainValidateIncreasingTimestamps_prog` iterates over an array of `N` block
  headers and validates that the `timestamp` field (RLP field 11) is STRICTLY
  increasing across consecutive headers: `ts[i] > ts[i-1]` for every adjacent
  pair.  This is the CROSS-HEADER sibling of the per-header-independent
  `chain_validate_blob_gas_used_under_max` / `chain_validate_extra_data_length`
  accessors: the per-header value decoded from header `i` is compared against
  the value decoded from header `i-1` (threaded through a scratch cell).

  Conformance: the Yellow Paper (`validate_header`, see
  `EvmAsm/Stateless/SpecRef/SeamShell.lean`) rejects a block whose timestamp is
  `≤` its parent's, i.e. requires the STRICT relation `Hs > parent.Hs`.  The
  guest decodes `cur = ts[i]` into `x28`, `prev = ts[i-1]` into `x29`, and takes
  `BGEU x29 x28` (`prev ≥ᵤ cur`) as the violation branch.  So the guest accepts
  exactly `prev <ᵤ cur`, i.e. `ts[i-1] < ts[i]` — the STRICT relation.  Guest
  and spec MATCH; no conformance divergence.

  Calling convention (see the program docstring):
    a0 (input)  : N (header count)
    a1 (input)  : header_lengths ptr (array of N u64 byte-lengths, 8-aligned)
    a2 (input)  : headers ptr (concatenated header blobs)
    a3 (input)  : u64 out cell (is_valid)
    a4 (input)  : u64 out cell (first_bad_index)
    ra (input)  : return
    a0 (output) : 0 = success (every adjacent pair strictly increasing, or N<2);
                  nonzero = some header failed the strict field-11 u64 decode.

  The real validity verdict lives in the two output memory cells:
    *is_valid       : 1 iff every adjacent pair is strictly increasing, else 0.
    *first_bad_index: index of the first bad header (violation or parse-fail).

  Program structure:
    * prologue (0-16): spill saved regs, `*is_valid := 1`, `*first_bad := 0`;
    * `BLTU x8, 2` (17): if `N < 2` jump to the a0:=0 exit (vacuously valid);
    * header-0 block (18-30): decode header-0 field 11 into `cvit_ts`, save it
      as the initial `prev` (`x21`), set `x6 := base of header 1`, `x7 := 1`;
      on parse-fail jump to the parse-fail exit (77);
    * loop guard (31): `BEQ x7, x8` — if `i = N` jump to the a0:=0 exit;
    * loop body (32-69): spill `{child=base_i, i, prev}` to scratch cells, decode
      header-`i` field 11, on parse-fail exit; else compare `prev` (from the
      `cvit_iter_prev` cell) against `cur` via `BGEU x29 x28`; on `prev ≥ cur`
      jump to the violation exit (70); else `prev := cur`, `base += len_i`,
      `i += 1`, loop back to the guard;
    * violation exit (70-76): `*is_valid := 0`, `*first_bad := i`, `a0 := 0`;
    * parse-fail exit (77-81): `*first_bad := i`, `a0` keeps the callee status;
    * all-valid exit (82): `a0 := 0`;
    * epilogue (83-91): restore saved regs, return.

  The saved-prev cell (`cvit_iter_prev`) is genuinely tied to the ACTUAL decoded
  timestamp of header `i-1` (via K34's `Result` at header `i-1`'s base), so the
  final cross-header postcondition is genuine.
-/

import EvmAsm.Codegen.Programs.ChainValidateProgs
import EvmAsm.Codegen.Programs.ChainValidateBlobGasUnderMaxSpec
import EvmAsm.Codegen.Programs.RlpFieldToU64StrictFlatSAsm
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Codegen.Programs.ChainValidateOfflineAddrs

namespace EvmAsm.Codegen.ChainValidateIncreasingTimestampsSpec

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
abbrev D : Word := (ChainValidateOfflineAddrs.chain_validate_increasing_timestamps : Word)

/-- The chain accessor's own program. -/
abbrev cvitProg : Program := EvmAsm.Codegen.chainValidateIncreasingTimestamps_prog

theorem cvit_length : cvitProg.length = 92 := by decide

/-- The chain accessor's re-emitted instructions at its base. -/
def cvitCode : CodeReq := CodeReq.ofProg D cvitProg

/-- The full linked closure: the chain accessor plus the strict K34
    `rlp_field_to_u64_strict` wrapper and its transitive callees. -/
def fullCode : CodeReq := cvitCode.union EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code

theorem cvit_disjoint :
    cvitCode.Disjoint EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code := by
  unfold cvitCode EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.wrapperCode EvmAsm.Codegen.RlpFieldToU64StrictSAsm.contentCode
  refine CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.union_right ?_ ?_)
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [cvit_length]; decide
    · rw [EvmAsm.Codegen.RlpFieldToU64StrictSAsm.program_length]; decide
    · left; rw [cvit_length]; decide
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [cvit_length]; decide
    · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
    · right; rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · unfold EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_code
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [cvit_length]; decide
    · rw [EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_prog_length]; decide
    · left; rw [cvit_length]; decide


/-- K34's linked code is subsumed by the chain accessor's full closure. -/
theorem k34_mono :
    ∀ a i, EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right cvit_disjoint (fun _ _ h => h) a i hi

theorem cvit_mono : ∀ a i, cvitCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

/-! ## Model of the header array -/

/-- Scratch-cell addresses. -/
abbrev Ts : Word := (GuestAddrs.cvit_ts : Word)
abbrev IterChild : Word := (GuestAddrs.cvit_iter_child : Word)
abbrev IterI : Word := (GuestAddrs.cvit_iter_i : Word)
abbrev IterPrev : Word := (GuestAddrs.cvit_iter_prev : Word)

/-- K34's internal scratch cells (owned across the call, threaded unchanged). -/
abbrev RfuOff : Word := (GuestAddrs.rfu_offset : Word)
abbrev RfuLen : Word := (GuestAddrs.rfu_length : Word)

/-- The link address written into `ra` by the header-0 `jal` (= `D + 96`). -/
abbrev LinkRA0 : Word := D + 96

/-- The link address written into `ra` by the loop-body `jal` (= `D + 196`). -/
abbrev LinkRA : Word := D + 196

/-- Header `i` decodes RLP field 11 (`timestamp`) to a u64 `value`, with status
    0 (success), genuinely tied to K34's `Result` at header `i`'s base. -/
def hdrTsOk (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) (value : Word) : Prop :=
  EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result (bigBytes.drop (hdrOff lengths i))
    (hdrBaseAt hdrBase lengths i) (lengths[i]!) 11 0 value

/-- Adjacent pair `(i-1, i)` is strictly increasing: both headers decode field
    11 to a u64 (status 0) and `ts[i-1] <ᵤ ts[i]` (the STRICT relation the guest
    `BGEU` accepts, matching the Yellow Paper's `Hs > parent.Hs`). -/
def tsIncreasing (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) : Prop :=
  ∃ prev cur, hdrTsOk hdrBase bigBytes lengths (i - 1) prev ∧
    hdrTsOk hdrBase bigBytes lengths i cur ∧ BitVec.ult prev cur

/-- Adjacent pair `(k-1, k)` violates the strict order: both headers decode
    field 11 to a u64 (status 0) but `¬ ts[k-1] <ᵤ ts[k]`, i.e. `ts[k-1] ≥ ts[k]`
    — exactly the guest's `BGEU x29 x28` taken condition. -/
def tsViolation (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (k : Nat) : Prop :=
  ∃ prev cur, hdrTsOk hdrBase bigBytes lengths (k - 1) prev ∧
    hdrTsOk hdrBase bigBytes lengths k cur ∧ ¬ BitVec.ult prev cur

/-- Header `k` fails the strict field-11 u64 decode (status ≠ 0). -/
def hdrBadParse (hdrBase : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (k : Nat) (status : Word) : Prop :=
  ∃ value,
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result (bigBytes.drop (hdrOff lengths k))
      (hdrBaseAt hdrBase lengths k) (lengths[k]!) 11 status value ∧ status ≠ 0

/-! ## Frames -/

/-- Static memory/register footprint carried unchanged through the whole loop:
    the header-length array, the concatenated header blob, and the scratch cells
    (owned).  `cvit_iter_i` (`IterI`) starts zeroed so the header-0 parse-fail
    reports index 0. -/
def payload (hdrBase lenBase : Word) (bigBytes : List (BitVec 8))
    (lengths : List Nat) : Assertion :=
  wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
  memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild ** memOwn IterI **
  memOwn IterPrev

/-- Callee-perturbed registers owned + the K34 frame slots owned + the callee's
    8-dword allocatable stack + `x0`. -/
def scratchRegs (calleeNewSp : Word) : Assertion :=
  regOwn .x1 ** regOwn .x5 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
  stackFree calleeNewSp 8

/-- Loop invariant at the guard (`D + 124`) entering iteration `i` (`1 ≤ i ≤ N`).

    The register file holds `x6 = base of header i`, `x7 = i`, and
    `x21 = prevVal`, where `prevVal` is GENUINELY the field-11 timestamp decoded
    from header `i-1` (`⌜hdrTsOk … (i-1) prevVal⌝` — tied to K34's `Result` at
    header `i-1`'s base).  The accumulated `hprefix` (all earlier adjacent pairs
    strictly increasing) is carried as a pure fact. -/
def LoopInv (_sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (i : Nat) : Assertion :=
  fun h => ∃ prevVal,
    (⌜hdrTsOk hdrBase bigBytes lengths (i - 1) prevVal ∧
        (∀ j, 1 ≤ j → j < i → tsIncreasing hdrBase bigBytes lengths j)⌝ **
      (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
      (.x6 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
      (.x20 ↦ᵣ firstBadPtr) ** (.x7 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ prevVal) **
      savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
      payload hdrBase lenBase bigBytes lengths ** scratchRegs calleeNewSp) h

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

/-- All adjacent pairs strictly increasing (or `N < 2`): `a0 = 0`,
    `*validPtr = 1`, `*firstBadPtr = 0`, and every adjacent pair `< N` is
    strictly increasing (each tied to K34's `Result`). -/
def postAllValid (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  ⌜lengths.length < 2 ∨
    (∀ i, 1 ≤ i → i < lengths.length → tsIncreasing hdrBase bigBytes lengths i)⌝ **
  (.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
  commonRet sp0 spC calleeNewSp hdrBase lenBase csaved bigBytes lengths

/-- First violation at `k` (`1 ≤ k < N`): `a0 = 0`, `*validPtr = 0`,
    `*firstBadPtr = k`, pair `(k-1,k)` violates the strict order, and all earlier
    adjacent pairs are strictly increasing. -/
def postViolation (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  fun h => ∃ k,
    (⌜1 ≤ k ∧ k < lengths.length ∧
        (∀ j, 1 ≤ j → j < k → tsIncreasing hdrBase bigBytes lengths j) ∧
        tsViolation hdrBase bigBytes lengths k⌝ **
      (.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
      (firstBadPtr ↦ₘ BitVec.ofNat 64 k) **
      commonRet sp0 spC calleeNewSp hdrBase lenBase csaved bigBytes lengths) h

/-- First parse failure at `k`: `a0 = status` (the actual nonzero K34 status),
    `*firstBadPtr = k`, `*validPtr = 1`, header `k` fails the strict field-11
    decode, and all earlier adjacent pairs are strictly increasing.  (For `k = 0`
    the header-0 block reads the zero-initialized `cvit_iter_i` cell, so
    `*firstBadPtr = 0`.) -/
def postParseFail (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  fun h => ∃ k status,
    (⌜k < lengths.length ∧
        (∀ j, 1 ≤ j → j < k → tsIncreasing hdrBase bigBytes lengths j) ∧
        hdrBadParse hdrBase bigBytes lengths k status⌝ **
      (.x10 ↦ᵣ status) ** (validPtr ↦ₘ (1 : Word)) **
      (firstBadPtr ↦ₘ BitVec.ofNat 64 k) **
      commonRet sp0 spC calleeNewSp hdrBase lenBase csaved bigBytes lengths) h

/-- Three-way whole-program post: all-strictly-increasing (or `N<2`),
    first-violation, or first parse-failure, each genuinely tied to the actual
    per-header `Result`s and cross-header comparisons. -/
def cvitPost (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) : Assertion :=
  fun h =>
    postAllValid sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
        bigBytes lengths h ∨
    postViolation sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
        bigBytes lengths h ∨
    postParseFail sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
        bigBytes lengths h

/-! ## Prologue (instructions 0--16): set up the loop-entry state

    Instructions 0--15 are byte-identical to the `chain_validate_*` prologue;
    instruction 16 is `li x5, 2` (the `N < 2` comparand) rather than the
    sibling's iterator reset, so `x21` is left untouched here. -/

set_option maxRecDepth 8000 in
theorem cvitPrologue
    (sp0 spC nWord lenBase hdrBase validPtr firstBadPtr raIn
      cs0 cs1 cs2 cs3 cs4 cs5 old5 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12)) :
    cpsTripleWithin 17 D (D + 68) cvitCode
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
        (.x21 ↦ᵣ cs5) ** (.x10 ↦ᵣ nWord) ** (.x11 ↦ᵣ lenBase) **
        (.x12 ↦ᵣ hdrBase) ** (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ firstBadPtr) **
        (.x5 ↦ᵣ (2 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
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
  have h16 := li_spec_gen_within .x5 (1 : Word) (2 : Word) (D + 64) (by decide)
  runBlock h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16


/-! ## Epilogue (instructions 83--91): restore + return -/

set_option maxRecDepth 8000 in
theorem cvitEpilogue
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 9 (D + 332) raIn cvitCode
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
    (0 : BitVec 12) (D + 332) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-56 : BitVec 12)) + (0 : Word)
      = sp0 + signExtend12 (-56 : BitVec 12) from by bv_omega] at l0
  have l1 := ld_spec_gen_within .x8 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o8 cs0
    (8 : BitVec 12) (D + 336) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at l1
  have l2 := ld_spec_gen_within .x9 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o9 cs1
    (16 : BitVec 12) (D + 340) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at l2
  have l3 := ld_spec_gen_within .x18 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o18 cs2
    (24 : BitVec 12) (D + 344) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at l3
  have l4 := ld_spec_gen_within .x19 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o19 cs3
    (32 : BitVec 12) (D + 348) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at l4
  have l5 := ld_spec_gen_within .x20 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o20 cs4
    (40 : BitVec 12) (D + 352) (by decide)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at l5
  have l6 := ld_spec_gen_within .x21 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o21 cs5
    (48 : BitVec 12) (D + 356) (by decide)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at l6
  have l7 := addi_spec_gen_same_within .x2 (sp0 + signExtend12 (-56 : BitVec 12))
    (56 : BitVec 12) (D + 360) (by decide)
  rw [show (sp0 + signExtend12 (-56 : BitVec 12)) + signExtend12 (56 : BitVec 12) = sp0
      from by rw [show signExtend12 (-56 : BitVec 12) = (-56 : Word) from by decide,
        show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]; bv_omega] at l7
  have hblock : cpsTripleWithin 8 (D + 332) (D + 364) cvitCode
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
  have hjalr := EvmAsm.Evm64.ret_spec_within' (D + 364) raIn
  rw [hret] at hjalr
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 364) cvitProg 91 (.JALR .x0 .x1 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide))
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


/-! ## All-valid exit (instruction 82 → epilogue): `a0 := 0`, then return -/

set_option maxRecDepth 8000 in
theorem retAllValid
    (sp0 spC raIn : Word) (csaved : Saved) (G : Assertion) (hG : G.pcFree)
    (o10 o1 o8 o9 o18 o19 o20 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 10 (D + 328) raIn cvitCode
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
  have h82 := li_spec_gen_within .x10 o10 (0 : Word) (D + 328) (by decide)
  have h82C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 328) cvitProg 82 (.LI .x10 (0 : Word))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide))
    h82
  have h82F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ csaved.ra) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
      ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
      ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) h82C
  have hepi := cvitEpilogue sp0 spC csaved.ra csaved.s0 csaved.s1 csaved.s2 csaved.s3
    csaved.s4 csaved.s5 o1 o8 o9 o18 o19 o20 o21 hspC hret
  have hepiF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (0 : Word)) ** G)
    (by refine pcFree_sepConj ?_ hG; pcf) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h82F hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


/-! ## Violation exit (instructions 70--76 → epilogue)

    `*validPtr := 0`, then reload `x6 := *cvit_iter_i` (the failing index),
    `*firstBadPtr := x6`, `a0 := 0`, `jal +28` to the epilogue. -/

set_option maxRecDepth 8000 in
theorem retViolation
    (sp0 spC raIn iVal validPtr firstBadPtr : Word) (csaved : Saved)
    (G : Assertion) (hG : G.pcFree) (o10 o1 o8 o9 o18 o21 old5 o6 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 16 (D + 280) raIn cvitCode
      ((.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ o6) ** (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x21 ↦ᵣ o21) **
        memOwn validPtr ** memOwn firstBadPtr ** (IterI ↦ₘ iVal) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) ** (firstBadPtr ↦ₘ iVal) **
        (IterI ↦ₘ iVal) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ iVal) **
        (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) ** (.x18 ↦ᵣ csaved.s2) **
        (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G) := by
  subst hraSaved
  have s70 := sd_spec_gen_own_within .x19 .x0 validPtr (0 : Word) (0 : BitVec 12) (D + 280)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show validPtr + (0 : Word) = validPtr from by bv_omega] at s70
  have s70' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 280) cvitProg 70 (.SD .x19 .x0 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s70
  have hla71 := la_materialize_within .x5 old5 (D + 284) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 284) cvitProg 71 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 284) IterI)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 288) cvitProg 72 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 284) IterI)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s73 := ld_spec_gen_within .x6 .x5 IterI o6 iVal (0 : BitVec 12) (D + 292) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s73
  have s73' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 292) cvitProg 73 (.LD .x6 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s73
  have s74 := sd_spec_gen_own_within .x20 .x6 firstBadPtr iVal (0 : BitVec 12) (D + 296)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show firstBadPtr + (0 : Word) = firstBadPtr from by bv_omega] at s74
  have s74' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 296) cvitProg 74 (.SD .x20 .x6 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s74
  have s75 := li_spec_gen_within .x10 o10 (0 : Word) (D + 300) (by decide)
  have s75' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 300) cvitProg 75 (.LI .x10 (0 : Word))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s75
  have s76 := jal_x0_spec_gen_within (28 : BitVec 21) (D + 304)
  rw [show (D + 304) + signExtend21 (28 : BitVec 21) = D + 332 from by
    rw [show signExtend21 (28 : BitVec 21) = (28 : Word) from by decide]; bv_omega] at s76
  have s76' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 304) cvitProg 76 (.JAL .x0 (28 : BitVec 21))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s76
  have hblock : cpsTripleWithin 7 (D + 280) (D + 332) cvitCode
      ((.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn validPtr **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ o6) ** (IterI ↦ₘ iVal) **
        (.x20 ↦ᵣ firstBadPtr) ** memOwn firstBadPtr ** (.x10 ↦ᵣ o10))
      ((.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
        (.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ iVal) ** (IterI ↦ₘ iVal) **
        (.x20 ↦ᵣ firstBadPtr) ** (firstBadPtr ↦ₘ iVal) ** (.x10 ↦ᵣ (0 : Word))) := by
    runBlock s70' hla71 s73' s74' s75' s76'
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (.x21 ↦ᵣ o21) **
      (spC ↦ₘ csaved.ra) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
      ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
      ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hblock
  have hepi := cvitEpilogue sp0 spC csaved.ra csaved.s0 csaved.s1 csaved.s2 csaved.s3
    csaved.s4 csaved.s5 o1 o8 o9 o18 validPtr firstBadPtr o21 hspC hret
  have hepiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) ** (firstBadPtr ↦ₘ iVal) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ iVal) ** (IterI ↦ₘ iVal) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


/-! ## Parse-fail exit (instructions 77--81 → epilogue)

    Reload `x6 := *cvit_iter_i`, `*firstBadPtr := x6`, `jal +8` to the epilogue.
    `a0` (=`x10`) is left holding the callee's nonzero status, threaded in `G`. -/

set_option maxRecDepth 8000 in
theorem retParseFail
    (sp0 spC raIn iVal firstBadPtr : Word) (csaved : Saved)
    (G : Assertion) (hG : G.pcFree) (o1 o8 o9 o18 o19 o21 o10 old5 o6 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 14 (D + 308) raIn cvitCode
      ((.x20 ↦ᵣ firstBadPtr) ** (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ o6) ** (.x10 ↦ᵣ o10) **
        (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
        (.x19 ↦ᵣ o19) ** (.x21 ↦ᵣ o21) **
        memOwn firstBadPtr ** (IterI ↦ₘ iVal) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
      ((.x10 ↦ᵣ o10) ** (firstBadPtr ↦ₘ iVal) ** (IterI ↦ₘ iVal) **
        (.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ iVal) ** (.x1 ↦ᵣ raIn) **
        (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) **
        (.x18 ↦ᵣ csaved.s2) ** (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) **
        (.x21 ↦ᵣ csaved.s5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G) := by
  subst hraSaved
  have hla77 := la_materialize_within .x5 old5 (D + 308) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 308) cvitProg 77 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 308) IterI)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 312) cvitProg 78 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 308) IterI)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s79 := ld_spec_gen_within .x6 .x5 IterI o6 iVal (0 : BitVec 12) (D + 316) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s79
  have s79' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 316) cvitProg 79 (.LD .x6 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s79
  have s80 := sd_spec_gen_own_within .x20 .x6 firstBadPtr iVal (0 : BitVec 12) (D + 320)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show firstBadPtr + (0 : Word) = firstBadPtr from by bv_omega] at s80
  have s80' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 320) cvitProg 80 (.SD .x20 .x6 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s80
  have s81 := jal_x0_spec_gen_within (8 : BitVec 21) (D + 324)
  rw [show (D + 324) + signExtend21 (8 : BitVec 21) = D + 332 from by
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega] at s81
  have s81' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 324) cvitProg 81 (.JAL .x0 (8 : BitVec 21))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s81
  have hblock : cpsTripleWithin 5 (D + 308) (D + 332) cvitCode
      ((.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ o6) ** (.x20 ↦ᵣ firstBadPtr) ** memOwn firstBadPtr **
        (IterI ↦ₘ iVal))
      ((.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ iVal) ** (.x20 ↦ᵣ firstBadPtr) ** (firstBadPtr ↦ₘ iVal) **
        (IterI ↦ₘ iVal)) := by
    runBlock hla77 s79' s80' s81'
  have hblockF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
      (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ csaved.ra) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
      ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
      ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hblock
  have hepi := cvitEpilogue sp0 spC csaved.ra csaved.s0 csaved.s1 csaved.s2 csaved.s3
    csaved.s4 csaved.s5 o1 o8 o9 o18 o19 firstBadPtr o21 hspC hret
  have hepiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ iVal) ** (firstBadPtr ↦ₘ iVal) **
      (IterI ↦ₘ iVal) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


end EvmAsm.Codegen.ChainValidateIncreasingTimestampsSpec
