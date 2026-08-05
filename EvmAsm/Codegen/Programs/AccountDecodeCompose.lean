/-
  EvmAsm.Codegen.Programs.AccountDecodeCompose

  #11345, composition step: the machine's success-side output struct
  (`AccountDecodeSpec.outputSuccess`) **is** the record-level assertion
  `Stateless.accountDecodedIs`, for the `AccountRecord` whose RLP the guest
  consumed.

  This is the join that was missing.  Both halves already existed and neither
  mentioned the other:

    * machine side — `account_decode`'s triple leaves `outputSuccess`, whose
      four cells are stated as *byte-copy functions of offsets the guest
      computed* (`beAccum` / `balanceCopied` / `fixed32Copied` applied to
      `o0..o3`);
    * record side — `accountDecodedIs` states the same four cells as *field
      values of an `AccountRecord`*.

  Getting from one to the other needs the offsets pinned to the model's decode,
  which is what `success_content_of_decodeFully_list` (model → guest, with
  content) and `success_deterministic` (guest offsets are unique) supply
  together.  The per-cell arithmetic is `AccountDecodeBridge`'s three
  `*_of_content` lemmas.

  ⚠️ Scope, stated rather than hidden: everything here is gated on `a.WF`.
  `Decoded` is four `Success` facts plus `l0 ≤ 8`, `l1 ≤ 32`, `l2 = 32`,
  `l3 = 32` — which is literally `AccountRecord.WF`.  So `a.WF` is not a
  convenience hypothesis, it is exactly the guest's own parse-time check,
  and the correspondence row must record what it excludes rather than let
  `a.WF` absorb it silently.
-/

import EvmAsm.Codegen.Programs.AccountDecodeBridge
import EvmAsm.Codegen.Programs.RlpDecodeFullyForward
import EvmAsm.Codegen.Programs.RlpWalkDeterminism
import EvmAsm.Stateless.State.AccountAssertions

namespace EvmAsm.Codegen.AccountDecodeCompose

open EvmAsm.Rv64 EvmAsm.EL.RLP
open EvmAsm.Stateless (AccountRecord accountDecodedIs accountDecodedIs_eq beBytes32)
open EvmAsm.Codegen.RlpListNthItemSAsm (Success)
open EvmAsm.Codegen.AccountDecodeSpec (Decoded outputSuccess beAccum balanceCopied fixed32Copied)
open EvmAsm.Codegen.AccountDecodeBridge
  (beAccum_of_content balanceCopied_of_content fixed32Copied_of_content)

/-! ## The record's four RLP children -/

/-- The record's children, in the field order `account_decode`'s
    `rlp_list_nth_item` indices 0..3 pin. -/
def accountItems (a : AccountRecord) : List RLPItem :=
  [.bytes (Nat.toBytesBE a.nonce), .bytes (Nat.toBytesBE a.balance),
   .bytes a.storageRoot, .bytes a.codeHash]

theorem rlpItem_eq (a : AccountRecord) : a.rlpItem = .list (accountItems a) := rfl

theorem accountItems_bytes (a : AccountRecord) :
    ∀ it ∈ accountItems a, ∃ q, it = RLPItem.bytes q := by
  intro it hit
  simp only [accountItems, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- The record's encoding decodes back to its children. -/
theorem decodeFully_accountRlp (a : AccountRecord) (hwf : a.WF) :
    decodeFully a.rlp = some (.list (accountItems a)) := by
  have hlen : (encode a.rlpItem).length < 256 ^ 8 := by
    have := EvmAsm.Stateless.accountRlp_length_le a hwf
    unfold AccountRecord.rlp at this
    omega
  rw [show a.rlp = encode a.rlpItem from rfl, decodeFully_encode a.rlpItem hlen,
    rlpItem_eq]

/-! ## Pinning the guest's offsets to the model's children

A `Success` at `index` is unique (`success_deterministic`), and the model
independently produces one whose content is the child (#11351's
`success_content_of_decodeFully_list`).  So the guest's `(o, l)` must be that
one — which is what turns a byte-copy at an opaque offset into a field value.

⚠️ The `o.toNat + p.length ≤ a.rlp.length` bound the content lemmas need can
**not** be recovered from the content equation.  `take p.length` returning
`p` says nothing about the offset when `p = []`, and an empty field is
reachable here — `Nat.toBytesBE 0 = []`, so a zero nonce or zero balance hits
exactly that case.  The bound instead comes from the walk
(`p.length ≤ off' ≤ bytes.length`), which is why
`success_content_of_decodeFully_list` now returns it as a third conjunct
rather than callers re-deriving it. -/

/-- The guest's reported offset/length for child `index` are the model's. -/
theorem content_of_success (a : AccountRecord) (hwf : a.WF) (listBase : Word)
    (hover : listBase.toNat + a.rlp.length < 2 ^ 64)
    (index : Nat) (p : List (BitVec 8))
    (hidx : (accountItems a)[index]? = some (RLPItem.bytes p))
    {o l : Word} (hsucc : Success a.rlp listBase a.rlp.length index o l) :
    l = BitVec.ofNat 64 p.length ∧
      (a.rlp.drop o.toNat).take p.length = p ∧
      o.toNat + p.length ≤ a.rlp.length := by
  obtain ⟨off, hs, hc, hb⟩ :=
    EvmAsm.Codegen.RlpListNthItemSAsm.success_content_of_decodeFully_list
      a.rlp listBase (accountItems a) index p (decodeFully_accountRlp a hwf)
      (accountItems_bytes a) hidx hover
  obtain ⟨rfl, rfl⟩ := EvmAsm.Codegen.RlpListNthItemSAsm.success_deterministic hsucc hs
  exact ⟨rfl, hc, hb⟩

/-! ## The join -/

/-- ⭐ **The machine's success-side output struct *is* the record assertion.**

    Left side: four cells stated as byte copies at offsets the guest computed.
    Right side: the same four cells stated as `AccountRecord` field values.
    Equal — so a caller holding `account_decode`'s postcondition holds
    `accountDecodedIs`, and can then use
    `decode_account_from_leaf_accountRlp` to reach
    `SpecRef.decode_account_from_leaf`. -/
theorem outputSuccess_eq_accountDecodedIs
    (a : AccountRecord) (hwf : a.WF) (listBase : Word)
    (nonceOut balanceOut rootOut codeOut : Word)
    (o0 l0 o1 l1 o2 l2 o3 l3 : Word)
    (oldRoot oldCode : List (BitVec 8))
    (holdRoot : oldRoot.length = 32) (holdCode : oldCode.length = 32)
    (hover : listBase.toNat + a.rlp.length < 2 ^ 64)
    (hdec : Decoded a.rlp listBase a.rlp.length o0 l0 o1 l1 o2 l2 o3 l3) :
    outputSuccess nonceOut balanceOut rootOut codeOut o0 o1 o2 o3 l0.toNat l1.toNat
        a.rlp oldRoot oldCode
      = accountDecodedIs nonceOut balanceOut rootOut codeOut a := by
  obtain ⟨hs0, -, hs1, -, hs2, -, hs3, -⟩ := hdec
  -- field lengths, from `WF` — the same bounds the guest checks at parse time
  have hnlen : (Nat.toBytesBE a.nonce).length ≤ 8 :=
    Nat.toBytesBE_length_le a.nonce 8 (by exact_mod_cast hwf.1)
  have hblen : (Nat.toBytesBE a.balance).length ≤ 32 :=
    Nat.toBytesBE_length_le a.balance 32 (by exact_mod_cast hwf.2.1)
  have hrlen : a.storageRoot.length = 32 := hwf.2.2.1
  have hclen : a.codeHash.length = 32 := hwf.2.2.2
  -- pin each guest offset/length to the model's child
  obtain ⟨he0, hc0, hb0⟩ :=
    content_of_success a hwf listBase hover 0 (Nat.toBytesBE a.nonce) rfl hs0
  obtain ⟨he1, hc1, hb1⟩ :=
    content_of_success a hwf listBase hover 1 (Nat.toBytesBE a.balance) rfl hs1
  obtain ⟨he2, hc2, hb2⟩ :=
    content_of_success a hwf listBase hover 2 a.storageRoot rfl hs2
  obtain ⟨he3, hc3, hb3⟩ :=
    content_of_success a hwf listBase hover 3 a.codeHash rfl hs3
  -- the reported lengths are the field lengths
  have hn0 : l0.toNat = (Nat.toBytesBE a.nonce).length := by
    rw [he0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hn1 : l1.toNat = (Nat.toBytesBE a.balance).length := by
    rw [he1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  -- the four cell-value equations
  have hvNonce : beAccum a.rlp o0.toNat l0.toNat = BitVec.ofNat 64 a.nonce := by
    rw [hn0, beAccum_of_content a.rlp o0 (Nat.toBytesBE a.nonce).length
      (Nat.toBytesBE a.nonce) hnlen hb0 hc0, Nat.fromBytesBE_toBytesBE]
  have hvBal : balanceCopied a.rlp o1 l1.toNat = beBytes32 a.balance := by
    rw [hn1, balanceCopied_of_content a.rlp o1 (Nat.toBytesBE a.balance).length
      (Nat.toBytesBE a.balance) hblen hb1 hc1]
    rfl
  have hvRoot : fixed32Copied a.rlp oldRoot o2 = a.storageRoot :=
    fixed32Copied_of_content a.rlp oldRoot o2 a.storageRoot holdRoot
      (by omega) (by rw [← hrlen]; exact hc2)
  have hvCode : fixed32Copied a.rlp oldCode o3 = a.codeHash :=
    fixed32Copied_of_content a.rlp oldCode o3 a.codeHash holdCode
      (by omega) (by rw [← hclen]; exact hc3)
  rw [accountDecodedIs_eq hwf]
  unfold outputSuccess
  rw [hvNonce, hvBal, hvRoot, hvCode]

/-! ## The SpecRef consumer

`decode_account_from_leaf_accountRlp` has been available since before this
change but nothing consumed it, and by the standard this tree already applies
(*availability is not use*), an unconsumed lemma earns no basis grade.  This is
the theorem the correspondence row cites: the guest's four output cells and the
reference decoder's four results are the **same** fields of the **same**
record. -/

theorem decoded_matches_specRef
    (a : AccountRecord) (hwf : a.WF) (listBase : Word)
    (nonceOut balanceOut rootOut codeOut : Word)
    (o0 l0 o1 l1 o2 l2 o3 l3 : Word)
    (oldRoot oldCode : List (BitVec 8))
    (holdRoot : oldRoot.length = 32) (holdCode : oldCode.length = 32)
    (hover : listBase.toNat + a.rlp.length < 2 ^ 64)
    (hdec : Decoded a.rlp listBase a.rlp.length o0 l0 o1 l1 o2 l2 o3 l3) :
    outputSuccess nonceOut balanceOut rootOut codeOut o0 o1 o2 o3 l0.toNat l1.toNat
        a.rlp oldRoot oldCode
      = accountDecodedIs nonceOut balanceOut rootOut codeOut a ∧
    EvmAsm.Stateless.SpecRef.decode_account_from_leaf a.rlp
      = .ok ({ nonce := a.nonce, balance := a.balance, codeHash := a.codeHash },
             a.storageRoot) :=
  ⟨outputSuccess_eq_accountDecodedIs a hwf listBase nonceOut balanceOut rootOut codeOut
     o0 l0 o1 l1 o2 l2 o3 l3 oldRoot oldCode holdRoot holdCode hover hdec,
   EvmAsm.Stateless.decode_account_from_leaf_accountRlp a hwf⟩

end EvmAsm.Codegen.AccountDecodeCompose
