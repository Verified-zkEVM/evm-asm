/-
  EvmAsm.Codegen.Programs.AccountDecodeCorrespondence

  **#11517's template pair, stated:** the asm-side account-leaf decode against SpecRef's
  `decode_account_from_leaf` (`witness_state.py:102` @ pin `e5a8caf1b`).

  #11517 asks for one of three outcomes per pairing — a correspondence theorem, a
  documented pairing with a stated gap, or a divergence — and names this pair as the one
  to start with, *"because the answer is already known and it establishes the template"*.
  This module delivers a **kernel correspondence for the code-hash sentinel** and a
  **numeral drift pin for the trie-root sentinel**, plus a **documented gap with a named
  blocker** for the field contents (outcome 2). No divergence was found; the one that
  motivated #11517 (#11516) is already repaired.

  ## ⭐ What was actually unpinned: the constants, in triplicate

  `EMPTY_TRIE_ROOT` and `EMPTY_CODE_HASH` exist in **three** independent copies:

  | copy | form |
  |---|---|
  | `SpecRef.EMPTY_TRIE_ROOT` / `EMPTY_CODE_HASH` (`WitnessState.lean:36,39`) | computed — `keccak256 [0x80]` / `keccak256 []` |
  | `adEmptyTrieRootBytes` / `adEmptyCodeHashBytes` (`AccountDecodeSpec.lean:418,427`) | 32 baked literal bytes |
  | `aieEmptyCodeHashBytes` (`AccountIsEip161EmptySpec.lean:62`) | 32 baked literal bytes, again |

  Nothing tied any of them to any other. A typo in one literal typechecks everywhere,
  produces a well-formed account, and yields a wrong state root — which is the #11516
  failure shape (*"the asm-side predicate contradicted the reference model of the same
  spec function, and no gate noticed"*) applied to a constant instead of a length bound.

  `adEmptyCodeHashBytes = EMPTY_CODE_HASH` is now a genuine kernel-checked theorem.
  Its proof isolates the concrete one-block absorption and consumes the pre-existing
  `Accel.keccakF_kat_empty`; the new lemmas add no recursion-depth or heartbeat option.
  The KAT's existing `maxRecDepth 8000` is documented in `ZiskAccel.lean` as the
  intrinsic evaluation depth of its 24 rounds.

  `adEmptyTrieRootBytes = EMPTY_TRIE_ROOT` remains a numeral pin.  Its input is
  `keccak256 [0x80]`, which needs a different 24-round KAT; a direct concrete proof
  exhausts the default recursion depth, and this change deliberately adds no new limit
  raise. Thus the trie-root half stays an honest drift gate until an independently
  justified intrinsic-depth KAT exists, while the code-hash half is proved to be keccak.

  ## The fold, and where the pairing bottoms out

  Both sides fold an empty hash field to the sentinel and otherwise take the field
  verbatim — `decode_account_from_leaf` via `decodeFixedHash32`, the guest via `hashCell`.
  `hashCell_corresponds_shape` records that the two conditionals branch on the same test
  with the same sentinel.

  ⛔ The residual is **not** about folding: it is the link between `fixed32Copied bytes
  oldOut o2` (the guest's region copy at the offset `rlp_list_nth_item` reported) and `sr`
  (the field bytes `decodeFully` produced). That is the `Success` ↔ `decodeFully`
  correspondence — the same RLP bridge tracked by #11341 and, for the list arms, #12021.
  So this pairing bottoms out in an already-named blocker rather than a new one, which is
  the useful thing to have learned from it.
-/
import EvmAsm.Codegen.Programs.AccountDecodeSpec
import EvmAsm.Codegen.Programs.AccountIsEip161EmptySpec
import EvmAsm.Stateless.SpecRef.WitnessState

namespace EvmAsm.Codegen

namespace AccountDecodeCorrespondence

open EvmAsm.Codegen.AccountDecodeSpec (adEmptyTrieRootBytes adEmptyCodeHashBytes hashCell)
open EvmAsm.Codegen.AccountIsEip161EmptySpec (aieEmptyCodeHashBytes)
open EvmAsm.Stateless.SpecRef (bytesBEtoNat)

/-! ## The sentinel pins

    The literal-value pins are `decide`-checked 32-byte big-endian folds, which the
    kernel's GMP-backed `Nat` handles directly. The numerals are the ones
    `WitnessState.lean:41-46` checks `EMPTY_CODE_HASH` and `EMPTY_TRIE_ROOT` against;
    the code-hash copy additionally has the direct Keccak theorem above. -/

/-- `adEmptyTrieRootBytes` is `keccak256(rlp(""))`, pinned through the numeral SpecRef's
    `#guard` uses for `EMPTY_TRIE_ROOT`. -/
theorem adEmptyTrieRootBytes_value :
    bytesBEtoNat adEmptyTrieRootBytes
      = 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421 := by
  decide

/-- `adEmptyCodeHashBytes` is `keccak256("")`, pinned through the numeral SpecRef's
    `#guard` uses for `EMPTY_CODE_HASH`. -/
theorem adEmptyCodeHashBytes_value :
    bytesBEtoNat adEmptyCodeHashBytes
      = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 := by
  decide

/-- The account-decoder code-hash sentinel is the SpecRef `EMPTY_CODE_HASH` value. -/
theorem adEmptyCodeHashBytes_eq_spec :
    adEmptyCodeHashBytes = EvmAsm.Stateless.SpecRef.EMPTY_CODE_HASH := by
  exact EvmAsm.Codegen.AccountDecodeSpec.adEmptyCodeHashBytes_eq_spec

/-- The `account_is_eip161_empty` copy is pinned to the same numeral. -/
theorem aieEmptyCodeHashBytes_value :
    bytesBEtoNat aieEmptyCodeHashBytes
      = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 := by
  decide

/-- ⭐ **The two baked asm copies of `EMPTY_CODE_HASH` are the same 32 bytes.**

    This one is a genuine kernel-checked equality rather than a numeral pin, because both
    sides are literals — no keccak evaluation is involved. It is the tie that was missing:
    `account_decode` and `account_is_eip161_empty` each carried their own copy, and
    `account_is_eip161_empty`'s verdict is *defined* by comparing a decoded field against
    its copy, so the two drifting apart would make an account EIP-161-empty for one
    routine and not the other. -/
theorem adEmptyCodeHashBytes_eq_aie :
    adEmptyCodeHashBytes = aieEmptyCodeHashBytes := by decide

/-- Both sentinels are 32 bytes, which is what makes them substitutable into a
    `bytesRegion` of a fixed-width hash cell. -/
theorem sentinel_lengths :
    adEmptyTrieRootBytes.length = 32 ∧ adEmptyCodeHashBytes.length = 32 := by
  constructor <;> decide

/-! ## The fold correspondence

    SpecRef folds an empty hash field to the sentinel and otherwise takes the field
    verbatim; `decode_account_from_leaf_inv` (`WitnessState.lean:158`) exposes exactly
    that as `root = if sr.isEmpty then EMPTY_TRIE_ROOT else sr`. The guest's `hashCell`
    (`AccountDecodeSpec.lean:439`) is `if l = 0 then fold else fixed32Copied …`. -/

/-- The guest's hash cell **is** a fold on the emptiness test, with the sentinel in the
    empty arm — the same shape SpecRef's decoder has. Stated as an `if`-split rather than
    proved against `decode_account_from_leaf` directly, because the non-empty arms are
    related by the RLP `Success` ↔ `decodeFully` bridge, not by this equation. -/
theorem hashCell_corresponds_shape (bytes oldOut : List (BitVec 8)) (o : Word)
    (l : Nat) (fold : List (BitVec 8)) :
    hashCell bytes oldOut o l fold
      = if l = 0 then fold else AccountDecodeSpec.fixed32Copied bytes oldOut o := rfl

/-- The empty arm agrees on the nose for the storage root: guest length `0` yields exactly
    the bytes SpecRef's `EMPTY_TRIE_ROOT` is pinned to. -/
theorem hashCell_empty_root (bytes oldOut : List (BitVec 8)) (o : Word) :
    bytesBEtoNat (hashCell bytes oldOut o 0 adEmptyTrieRootBytes)
      = 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421 := by
  rw [hashCell_corresponds_shape, if_pos rfl]
  exact adEmptyTrieRootBytes_value

/-- Same for the code hash. -/
theorem hashCell_empty_code (bytes oldOut : List (BitVec 8)) (o : Word) :
    bytesBEtoNat (hashCell bytes oldOut o 0 adEmptyCodeHashBytes)
      = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 := by
  rw [hashCell_corresponds_shape, if_pos rfl]
  exact adEmptyCodeHashBytes_value

/-! ## ⛔ The stated gap (#11517 outcome 2), and one deliberate strength difference

    **Gap.** The non-empty arm needs `fixed32Copied bytes oldOut o = sr`, tying the guest's
    region copy at the offset `rlp_list_nth_item` reported to the field bytes `decodeFully`
    produced. That is the `Success` ↔ `decodeFully` correspondence — #11341, and for the
    list arms #12021. Not a new blocker, which is the useful finding: the account pairing
    reduces to the RLP pairing rather than adding an obligation.

    **Strength difference, deliberate.** SpecRef accepts nonce and balance fields of *any*
    length — `decode_account_from_leaf_inv`'s own docstring says so (*"`bytesBEtoNat` has
    no width cap"*) — while the guest carries `nonceValueOk` / `balanceValueOk`. The asm is
    **stronger**, and legitimately: the guest writes into fixed-width buffers. #11517 is
    explicit that this is not a licence to relax the asm to match, and #11523 is where the
    length-versus-value form of those bounds is decided. Recorded here so the difference is
    a known quantity rather than an unexamined mismatch.

    **No divergence found.** #11516's — `Decoded` requiring `l2 = l3 = 32` where the
    reference folds a zero-length field — is repaired: `Decoded` (`AccountDecodeSpec.lean:528,530`)
    now reads `(l2.toNat = 32 ∨ l2.toNat = 0)`, and `outputSuccess` routes both hash cells
    through `hashCell` with the sentinels. That repair is what makes the fold shape above
    match at all. -/

end AccountDecodeCorrespondence

end EvmAsm.Codegen
