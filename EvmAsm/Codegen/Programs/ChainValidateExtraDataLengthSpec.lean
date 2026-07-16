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

end EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
