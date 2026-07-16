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
import EvmAsm.Codegen.Programs.RlpFieldToU64FlatSAsm
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.RunBlock

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
abbrev D : Word := (GuestAddrs.chain_validate_increasing_timestamps : Word)

/-- The chain accessor's own program. -/
abbrev cvitProg : Program := EvmAsm.Codegen.chainValidateIncreasingTimestamps_prog

theorem cvit_length : cvitProg.length = 92 := by decide

/-- The chain accessor's re-emitted instructions at its base. -/
def cvitCode : CodeReq := CodeReq.ofProg D cvitProg

/-- The full linked closure: the chain accessor plus the strict K34
    `rlp_field_to_u64` wrapper and its transitive callees. -/
def fullCode : CodeReq := cvitCode.union EvmAsm.Codegen.RlpFieldToU64SAsm.code

theorem cvit_disjoint :
    cvitCode.Disjoint EvmAsm.Codegen.RlpFieldToU64SAsm.code := by
  unfold cvitCode EvmAsm.Codegen.RlpFieldToU64SAsm.code
    EvmAsm.Codegen.RlpFieldToU64SAsm.wrapperCode EvmAsm.Codegen.RlpFieldToU64SAsm.contentCode
  refine CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.union_right ?_ ?_)
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [cvit_length]; decide
    · rw [EvmAsm.Codegen.RlpFieldToU64SAsm.program_length]; decide
    · right; rw [EvmAsm.Codegen.RlpFieldToU64SAsm.program_length]; decide
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [cvit_length]; decide
    · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
    · right; rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · unfold EvmAsm.Rv64.RLP.rlp_content_to_u64_code
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [cvit_length]; decide
    · rw [EvmAsm.Rv64.RLP.rlp_content_to_u64_prog_length]; decide
    · left; rw [cvit_length]; decide

#print axioms cvit_disjoint

/-- K34's linked code is subsumed by the chain accessor's full closure. -/
theorem k34_mono :
    ∀ a i, EvmAsm.Codegen.RlpFieldToU64SAsm.code a = some i → fullCode a = some i := by
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
  EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
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
    EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths k))
      (hdrBaseAt hdrBase lengths k) (lengths[k]!) 11 status value ∧ status ≠ 0

/-! ## Frames -/

/-- Static memory/register footprint carried unchanged through the whole loop:
    the header-length array, the concatenated header blob, and the scratch cells
    (owned).  `cvit_iter_i` (`IterI`) starts zeroed so the header-0 parse-fail
    reports index 0. -/
def payload (hdrBase lenBase : Word) (bigBytes : List (BitVec 8))
    (lengths : List Nat) : Assertion :=
  wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
  memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild ** memOwn IterPrev

/-- Callee-perturbed registers owned + the K34 frame slots owned + the callee's
    8-dword allocatable stack + `x0`. -/
def scratchRegs (calleeNewSp : Word) : Assertion :=
  regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
  stackFree calleeNewSp 8

end EvmAsm.Codegen.ChainValidateIncreasingTimestampsSpec
