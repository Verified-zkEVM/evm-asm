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
theorem ad_length : accountDecode_prog.length = 162 := by decide

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

/-! ### The zero-length hash fold (GH #11483)

`witness_state.py:118-119` folds a **zero-length** `storage_root` / `code_hash`
to `EMPTY_TRIE_ROOT` / `EMPTY_CODE_HASH` rather than rejecting it; the guest
previously required exactly 32 bytes, so it false-rejected a leaf the spec
accepts.  The assembly now dispatches `len = 0` to a block that stores the
constant (four `LD`/`SD` pairs from `iw_empty_trie_root` / `aie_empty_code_hash`);
lengths outside `{0, 32}` still fail exactly as before.

These are the two constants as baked into those `.data` sections. -/

/-- `EMPTY_TRIE_ROOT = keccak256(rlp(b''))`, matching `iw_empty_trie_root`
    (`MptInsertWalk.lean:349`). -/
def adEmptyTrieRootBytes : List (BitVec 8) :=
  [ 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6,
    0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e,
    0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0,
    0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21 ]

theorem adEmptyTrieRootBytes_length : adEmptyTrieRootBytes.length = 32 := by decide

/-- `EMPTY_CODE_HASH = keccak256(b'')`, matching `aie_empty_code_hash`. -/
def adEmptyCodeHashBytes : List (BitVec 8) :=
  [ 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
    0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
    0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
    0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70 ]

theorem adEmptyCodeHashBytes_length : adEmptyCodeHashBytes.length = 32 := by decide

/-- A hash output cell: the 32 copied content bytes, or the fold constant when
    the field was zero-length.  `fixed32Copied` cannot express the folded case
    for any offset — it is an unconditional copy from the input buffer — which
    is why the cell needs the length, not just the offset. -/
def hashCell (bytes oldOut : List (BitVec 8)) (o : Word) (l : Nat)
    (fold : List (BitVec 8)) : List (BitVec 8) :=
  if l = 0 then fold else fixed32Copied bytes oldOut o

theorem hashCell_length (bytes oldOut : List (BitVec 8)) (o : Word) (l : Nat)
    (fold : List (BitVec 8)) (hold : oldOut.length = 32) (hfold : fold.length = 32) :
    (hashCell bytes oldOut o l fold).length = 32 := by
  unfold hashCell; split
  · exact hfold
  · exact fixed32Copied_length bytes oldOut o hold

/-- On a nonzero field length the cell is the ordinary 32-byte content copy — the
    fold arm is unreachable.  This is what lets the `AccountRecord` composition
    keep its `fixed32Copied` reasoning unchanged: a record's `rlp` encodes
    `a.storageRoot` with `WF`-guaranteed length 32, so the folded arm names a
    leaf outside `AccountRecord.rlp`'s image (GH #11484). -/
theorem hashCell_of_ne_zero (bytes oldOut : List (BitVec 8)) (o : Word) (l : Nat)
    (fold : List (BitVec 8)) (hl : l ≠ 0) :
    hashCell bytes oldOut o l fold = fixed32Copied bytes oldOut o := by
  simp only [hashCell, hl, if_false]

/-- On a zero field length the cell is the fold constant. -/
theorem hashCell_zero (bytes oldOut : List (BitVec 8)) (o : Word)
    (fold : List (BitVec 8)) :
    hashCell bytes oldOut o 0 fold = fold := by
  simp only [hashCell, if_pos]

/-- The genuine success verdict: all four fields decode as K20 successes, with
    the two variable fields within their length caps and the two hash fields
    either exactly 32 bytes or zero-length (the #11483 fold).  The output values
    are tied to the actual content:
      * nonce   = `beAccum` of the `l0` content bytes at `o0`,
      * balance = right-aligned 32-byte copy of the `l1` content bytes at `o1`,
      * root / code_hash = 32-byte copy at `o2` / `o3`, or the EMPTY constant
        when the field was zero-length. -/
def Decoded (bytes : List (BitVec 8)) (listBase : Word) (listLen : Nat)
    (o0 l0 o1 l1 o2 l2 o3 l3 : Word) : Prop :=
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 0 o0 l0 ∧
  l0.toNat ≤ 8 ∧
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 1 o1 l1 ∧
  l1.toNat ≤ 32 ∧
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2 o2 l2 ∧
  (l2.toNat = 32 ∨ l2.toNat = 0) ∧
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 3 o3 l3 ∧
  (l3.toNat = 32 ∨ l3.toNat = 0)

/-- The four output slots after a **successful** decode, each cell tied to the
    actual decoded field value. -/
def outputSuccess (nonceOut balanceOut rootOut codeOut o0 o1 o2 o3 : Word)
    (l0 l1 l2 l3 : Nat) (bytes oldRoot oldCode : List (BitVec 8)) : Assertion :=
  (nonceOut ↦ₘ beAccum bytes o0.toNat l0) **
  bytesRegion balanceOut (balanceCopied bytes o1 l1) **
  bytesRegion rootOut (hashCell bytes oldRoot o2 l2 adEmptyTrieRootBytes) **
  bytesRegion codeOut (hashCell bytes oldCode o3 l3 adEmptyCodeHashBytes)

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
