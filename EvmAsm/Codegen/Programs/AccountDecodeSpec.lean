/-
  Whole-program caller-contract scaffolding for `accountDecode_prog`
  (`Programs/State.lean`, PR-K27, 136 instructions, entry
  `GuestAddrs.account_decode`).

  An account is the RLP list `[nonce, balance, storage_root, code_hash]`.
  The accessor decodes it into four caller-supplied output slots:

    a2 : nonce         out ptr (8 bytes; written LE u64, big-endian decode)
    a3 : balance       out ptr (32 bytes; BE, left-zero-padded, right-aligned)
    a4 : storage_root  out ptr (32 bytes; exact 32-byte copy)
    a5 : code_hash     out ptr (32 bytes; exact 32-byte copy)

  Calling convention (matches the program's prologue saves):
    a0 (input)  : account RLP bytes ptr        (saved into s0/x8)
    a1 (input)  : account RLP byte length       (saved into s1/x9)
    a2 (input)  : nonce out ptr                 (saved into s2/x18)
    a3 (input)  : balance out ptr               (saved into s3/x19)
    a4 (input)  : storage_root out ptr          (saved into s4/x20)
    a5 (input)  : code_hash out ptr             (saved into s5/x21)
    ra (input)  : return
    a0 (output) : 0 success / 1 parse fail

  ALL four fields are decoded via `rlp_list_nth_item` (`LI x12 = 0/1/2/3`),
  each: nth_item call → `BNE x10,x0` (parse fail) → a per-field length check →
  a byte-materialisation loop.  The four field materialisers differ:

    * field 0 (nonce): variable-length, `len ≤ 8`; a top-tested big-endian
      accumulation loop building a u64 register value, then `SD`.
    * field 1 (balance): variable-length, `len ≤ 32`; the 32-byte output is
      zeroed then the `len` content bytes are copied right-aligned (top-tested
      `BEQ`/`JAL` copy loop into `out + (32-len)`).
    * field 2 (storage_root): fixed `len = 32`; a bottom-tested 32-byte LBU/SB
      copy loop (`BNE x6,x0 -20` back-edge), like withdrawal's address copy.
    * field 3 (code_hash): fixed `len = 32`; same bottom-tested 32-byte copy.

  The only linked callee is `rlp_list_nth_item`, so the full linked closure is
  `adCode ∪ RlpListNthItemSAsm.code`.

  This module hosts the code layout, disjointness/mono lemmas, the semantic
  decode model (genuine per-field `Success`/`Failure` ties -- mirroring
  `WithdrawalDecodeSpec`), and the caller-facing success/failure outcomes.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Codegen.Programs.State
import EvmAsm.Evm64.Terminating.ReturnWindowLoopSpec

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-! ## Code layout -/

/-- The accessor body's fixed guest base address. -/
abbrev AB : Word := (GuestAddrs.account_decode : Word)

set_option maxRecDepth 8000 in
theorem ad_length : accountDecode_prog.length = 136 := by decide

/-- The wrapper's own re-emitted instructions at `account_decode`. -/
def adCode : CodeReq := CodeReq.ofProg AB accountDecode_prog

/-- The full linked closure: this accessor plus the strict `rlp_list_nth_item`
    subroutine (the only cross-`jal` callee). -/
def fullCode : CodeReq := adCode.union EvmAsm.Codegen.RlpListNthItemSAsm.code

theorem ad_disjoint :
    adCode.Disjoint EvmAsm.Codegen.RlpListNthItemSAsm.code := by
  unfold adCode EvmAsm.Codegen.RlpListNthItemSAsm.code
    EvmAsm.Codegen.RlpListNthItemSAsm.B AB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [ad_length]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · rw [ad_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide

#print axioms ad_disjoint

theorem ad_mono : ∀ a i, adCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

/-- The strict `rlp_list_nth_item` subroutine (called for every field) is a
    sub-union of the full closure. -/
theorem k20_mono :
    ∀ a i, EvmAsm.Codegen.RlpListNthItemSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right ad_disjoint (fun _ _ h => h) a i hi

#print axioms ad_mono
#print axioms k20_mono

/-! ## Semantic decode model

    Every field decodes via K20's `Success`/`Failure` relation on the same
    strict RLP list.  The two variable-length fields (nonce/balance) carry an
    upper length bound; the two fixed fields (storage_root/code_hash) require
    exactly 32 content bytes.  No decode-determinism is assumed: each failure
    arm names the *actual* failing stage (mirroring `WithdrawalDecodeSpec`). -/

open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- Big-endian accumulation of `len` content bytes starting at relative offset
    `off`, matching the nonce loop `x7 := (x7 <<< 8) ||| byte`.  After `len`
    iterations this is the big-endian numeric value the program stores (LE) into
    the 8-byte nonce slot. -/
def beAccum (bytes : List (BitVec 8)) (off : Nat) : Nat → Word
  | 0 => 0
  | (i + 1) => (beAccum bytes off i) <<< 8 |||
      ((bytes.getD (off + i) 0).zeroExtend 64)

/-- The 32-byte balance buffer after a successful decode: a fully-zeroed 32-byte
    region into which the `len` content bytes are copied *right-aligned* (forward
    copy into destination offset `32 - len`), matching the program's
    `SD x0` zeroing + `ADD x29, x19, (32-len)` + forward LBU/SB copy. -/
def balanceCopied (bytes : List (BitVec 8)) (o1 : Word) (l1 : Nat) : List (BitVec 8) :=
  copyIntoRegion (List.replicate 32 (0 : BitVec 8)) bytes (32 - l1) o1.toNat l1

theorem balanceCopied_length (bytes : List (BitVec 8)) (o1 : Word) (l1 : Nat) :
    (balanceCopied bytes o1 l1).length = 32 := by
  unfold balanceCopied; rw [copyIntoRegion_length]; simp

/-- A fixed 32-byte content copy (storage_root / code_hash): the 32 content
    bytes at relative offset `o` copied forward into the caller's old 32-byte
    output slot. -/
def fixed32Copied (bytes oldOut : List (BitVec 8)) (o : Word) : List (BitVec 8) :=
  copyIntoRegion oldOut bytes 0 o.toNat 32

theorem fixed32Copied_length (bytes oldOut : List (BitVec 8)) (o : Word)
    (hlen : oldOut.length = 32) :
    (fixed32Copied bytes oldOut o).length = 32 := by
  unfold fixed32Copied; rw [copyIntoRegion_length]; exact hlen

/-- The genuine success verdict: all four fields decode as K20 successes, with
    the two variable fields within their length caps and the two fixed fields
    exactly 32 bytes.  The output values are tied to the actual content:
      * nonce   = `beAccum` of the `l0` content bytes at `o0`,
      * balance = right-aligned 32-byte copy of the `l1` content bytes at `o1`,
      * root    = 32-byte copy at `o2`,  code_hash = 32-byte copy at `o3`. -/
def Decoded (bytes : List (BitVec 8)) (listBase : Word) (listLen : Nat)
    (o0 l0 o1 l1 o2 l2 o3 l3 : Word) : Prop :=
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 0 o0 l0 ∧
  l0.toNat ≤ 8 ∧
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 1 o1 l1 ∧
  l1.toNat ≤ 32 ∧
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2 o2 l2 ∧
  l2.toNat = 32 ∧
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 3 o3 l3 ∧
  l3.toNat = 32

/-- The four output slots after a **successful** decode, each cell tied to the
    actual decoded field value. -/
def outputSuccess (nonceOut balanceOut rootOut codeOut o0 o1 o2 o3 : Word)
    (l0 l1 : Nat) (bytes oldRoot oldCode : List (BitVec 8)) : Assertion :=
  (nonceOut ↦ₘ beAccum bytes o0.toNat l0) **
  bytesRegion balanceOut (balanceCopied bytes o1 l1) **
  bytesRegion rootOut (fixed32Copied bytes oldRoot o2) **
  bytesRegion codeOut (fixed32Copied bytes oldCode o3)

/-- An account-decode **failure** outcome, matching the program's short-circuit
    dispatch (field 0 list → field 0 len>8 → field 1 list → field 1 len>32 →
    field 2 list → field 2 len≠32 → field 3 list → field 3 len≠32).  Each arm
    names the *actual* failing stage via K20's semantics (no determinism
    assumed).  Mirrors `WithdrawalDecodeSpec.DecodeFailure`. -/
inductive DecodeFailure (bytes : List (BitVec 8)) (listBase : Word)
    (listLen : Nat) : Prop
  | field0List
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen 0) :
      DecodeFailure bytes listBase listLen
  | field0Len (o0 l0 : Word)
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 0 o0 l0)
      (hlen : 8 < l0.toNat) :
      DecodeFailure bytes listBase listLen
  | field1List
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen 1) :
      DecodeFailure bytes listBase listLen
  | field1Len (o1 l1 : Word)
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 1 o1 l1)
      (hlen : 32 < l1.toNat) :
      DecodeFailure bytes listBase listLen
  | field2List
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen 2) :
      DecodeFailure bytes listBase listLen
  | field2Len (o2 l2 : Word)
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2 o2 l2)
      (hlen : l2.toNat ≠ 32) :
      DecodeFailure bytes listBase listLen
  | field3List
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen 3) :
      DecodeFailure bytes listBase listLen
  | field3Len (o3 l3 : Word)
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 3 o3 l3)
      (hlen : l3.toNat ≠ 32) :
      DecodeFailure bytes listBase listLen

end EvmAsm.Codegen.AccountDecodeSpec
