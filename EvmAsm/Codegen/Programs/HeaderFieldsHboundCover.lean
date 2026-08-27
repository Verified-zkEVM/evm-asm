/-
  EvmAsm.Codegen.Programs.HeaderFieldsHboundCover

  **What `hbound` actually asks for** — the residual input-domain gate on the
  three header root-extract rows (`header_extract_state_root`,
  `header_extract_receipts_root`, `header_extract_withdrawals_root`), all of
  which cite the same hypothesis of `header_extract_*_spec_within`
  (`HeaderFieldsSpec.lean`, hypothesis named `hbound`):

      ∀ o next len, o ≤ listLenN →
        rlpItemDecode headerBytes o (listBase + o) (listBase + listLenN) next len →
        (next - len - listBase).toNat + 32 ≤ headerBytes.length

  Until now the registry described this gate in prose only, with the coverRef
  *"any well-formed header whose field-3 payload is a 32-byte string"*.  That
  description is **not sufficient**, and this module says why with theorems
  rather than with prose.

  ## `hbound` is a condition on the buffer, not on the header

  Read the quantifier: `o` ranges over **every** offset `o ≤ listLenN`, not over
  the offsets the routine's walk actually visits.  `rlpItemDecode` does not
  require `o` to be an item boundary — it reads `headerBytes[o]` and classifies
  it — so mid-item offsets decode too, and each one has to satisfy the bound.

  What is `next - len`?  `next_sub_len_classified` proves it is exactly `cursor`
  on three of the five arms — the single-byte form and **both list forms**,
  where `len` is the item's full span rather than its payload, so the
  subtraction lands back on the item's own first byte.  On the two string arms
  it is `cursor` advanced past the length header (`+1` short, `+lol+1` long).
  So the bound says, near enough: *from wherever the item decoded at `o`
  begins, the buffer still has 32 bytes* — and the "wherever" never gets far
  from `o` itself.

  ⚠️ The gate's own text in the registry called `next - len` the *content*
  start.  That is right for the string forms and wrong for the list forms; the
  theorem is stated over what the definition actually computes.

  The single-byte form is the sharp one.  Its only fit conjunct is
  `ult cursor endPtr`, so it fires at `o = listLenN - 1` whenever the last byte
  of the list is `< 0x80` — and then the bound reads
  `(listLenN - 1) + 32 ≤ headerBytes.length`.  That is
  `hbound_forces_trailing_slack`:

      listLenN + 31 ≤ headerBytes.length

  ⇒ `hbound` demands **31 bytes of buffer past the end of the RLP list**.  The
  spec's own slack hypothesis, `h_slack : listLenN + 9 ≤ headerBytes.length`,
  supplies nine.  The gap is real, not an artifact of how the bound is
  phrased — `hbound_fails_under_slack_only` exhibits a buffer that satisfies
  every other domain hypothesis and falsifies `hbound`.

  Nothing about being a *well-formed header* rules that trigger out: the
  hypothesis `hbound_forces_trailing_slack` needs is one byte below `0x80` at
  the list's last offset, which a trailing small-integer field supplies
  outright and a trailing hash supplies whenever its final byte happens to be
  low.  Whether the gate holds is therefore decided by how much room the
  **caller** leaves after the list, and not by the header's field structure.

  ## Scope — read this before citing the module

  * This is about the shape of the gate, **not** a defect: `hbound` is a
    hypothesis, so the triples are sound.  What changes is the registry's
    description of which inputs they cover.
  * `hbound_instance` witnesses satisfiability of the **domain** hypotheses
    (`h_src_align`, `h_slack`, `h_src_over`, `h_src_valid`, `hbound`).  It does
    **not** instantiate the ABI hypotheses (`h_dst_*`, `h_newSp`, the frame),
    which the rows themselves declare are not domain gates.  Nothing here
    claims the whole hypothesis bundle of `header_extract_state_root_spec_within`
    has been discharged.
  * The instance is non-vacuous in the sense that matters: a decode really does
    occur inside it (`hbound_instance_has_a_decode`), so `hbound` is not being
    satisfied by there being nothing to satisfy it.  `hbound_vacuous_control`
    shows the trap it avoids — at `listLenN = 0` the bound holds for the reason
    that *no* offset decodes at all.
  * ⛔ **Whether real callers satisfy the gate is not settled here.**  The
    extractors have callers of both forms: String-emitted ones
    (`state_root_in_witness`, `state_slot_at_block_hash`, …) over which no
    triple can be stated at all, and **`Program`-valued** ones that emit a real
    `.JAL` — `withdrawals_root_indexed`, `receipts_root_indexed`,
    `witness_headers_state_root_at_index`, the `*_at_header_state_root` family
    in `StateCompose`/`StatePredicates`/`EvmOpcodes`/`EvmNonce`/`EvmCodes`,
    `extract_parent_header_and_state_root`, and the `ChainEndpoints` pair.  A
    triple is *attachable* to the second group, but none of them carries one
    today (no `cpsTripleWithin` mentions any of their programs), so nothing
    currently discharges `hbound` at a call site.  This module says what the
    gate demands; it does not claim the demand is met or unmet in the deployed
    guest.

  Issues: #12867 (prose-only gates), #12313 (the rows).
-/
import EvmAsm.Rv64.RLP.WalkNext

namespace EvmAsm.Codegen.HeaderFieldsHboundCover

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-- The gate of the three `header_extract_*_root` rows, spelled once.  Matches
    the `hbound` hypothesis of `header_extract_state_root_spec_within`,
    `header_extract_receipts_root_spec_within` and
    `header_extract_withdrawals_root_spec_within` verbatim — all three are the
    same proposition, which is why one family theorem drains all three rows. -/
def Hbound (listBase : Word) (headerBytes : List (BitVec 8)) (listLenN : Nat) : Prop :=
  ∀ o next len, o ≤ listLenN →
    rlpItemDecode headerBytes o (listBase + BitVec.ofNat 64 o)
      (listBase + BitVec.ofNat 64 listLenN) next len →
    (next - len - listBase).toNat + 32 ≤ headerBytes.length

/-- `x + y - y = x` over `Word`, stated on **abstract** atoms so the rewrite
    below never hands `bv_omega` a `Nat.fromBytesBE` term.  (Doing the
    cancellation with `bv_omega` directly on the long-form arms does not
    terminate in any reasonable time — the cost is driven by term size.) -/
private theorem word_add_sub_self (x y : Word) : x + y - y = x := by bv_omega

/-- **Where `next - len` lands**, over the real relation rather than over a
    restatement of its arms.  Exactly three outcomes:

    * `cursor` — the single-byte form and **both list forms**.  For lists `len`
      is the item's *full span*, not its payload, so the subtraction returns the
      item's own first byte;
    * `cursor + 1` — short string, past the one-byte prefix;
    * `cursor + (lol + 1)` — long string, past the prefix and its length field.

    ⚠️ The registry gate text calls `next - len` the *content start*.  That
    holds on the two string arms and is **wrong on the list arms**, where it is
    the item start.  It makes no difference to `hbound_forces_trailing_slack`,
    which fires on the single-byte arm, but the gate's description of its own
    quantity should say what the definition computes. -/
theorem next_sub_len_classified {bytes : List (BitVec 8)} {off : Nat}
    {cursor endPtr next len : Word}
    (h : rlpItemDecode bytes off cursor endPtr next len) :
    next - len = cursor
    ∨ next - len = cursor + signExtend12 (1 : BitVec 12)
    ∨ ∃ b : BitVec 8, bytes[off]? = some b ∧
        next - len = cursor + ((b.zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12)) := by
  obtain ⟨b, hb, harm⟩ := h
  rcases harm with ⟨_, _, h3, h4⟩ | ⟨_, _, _, _, h5, h6⟩ | ⟨_, _, _, _, _, _, h7, h8⟩ |
      ⟨_, _, _, h4, h5⟩ | ⟨_, _, _, _, _, h6, h7⟩
  · -- single byte: `next = cursor + 1`, `len = 1`
    subst h3; subst h4
    exact Or.inl (by rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      word_add_sub_self])
  · -- short string: `next = (cursor + 1) + L`, `len = L`
    subst h5; subst h6
    exact Or.inr (Or.inl (word_add_sub_self _ _))
  · -- long string: `next = (cursor + (lol + 1)) + L`, `len = L`
    subst h7; subst h8
    exact Or.inr (Or.inr ⟨b, hb, word_add_sub_self _ _⟩)
  · -- short list: `next = cursor + span`, `len = span`
    subst h4; subst h5
    exact Or.inl (word_add_sub_self _ _)
  · -- long list: `next = cursor + span`, `len = span`
    subst h6; subst h7
    exact Or.inl (word_add_sub_self _ _)

/-- **`hbound` forces 31 bytes of slack past the list**, whenever the last byte
    of the list is `< 0x80`.

    The instantiation is at `o = listLenN - 1` in the single-byte form, whose
    only fit conjunct is `ult cursor endPtr`.  Compare the spec's own
    `h_slack`, which gives `listLenN + 9 ≤ headerBytes.length`: this is
    strictly stronger, and it constrains the caller's **buffer**, not the
    header's field structure. -/
theorem hbound_forces_trailing_slack
    {listBase : Word} {headerBytes : List (BitVec 8)} {listLenN : Nat}
    (hpos : 0 < listLenN)
    (hle : listLenN ≤ headerBytes.length)
    (hover : listBase.toNat + headerBytes.length < 2 ^ 64)
    {b : BitVec 8}
    (hb : headerBytes[listLenN - 1]? = some b)
    (hsmall : BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true)
    (hbound : Hbound listBase headerBytes listLenN) :
    listLenN + 31 ≤ headerBytes.length := by
  have hlt : BitVec.ult (listBase + BitVec.ofNat 64 (listLenN - 1))
      (listBase + BitVec.ofNat 64 listLenN) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := listBase.isLt
    omega
  have h := hbound (listLenN - 1)
    ((listBase + BitVec.ofNat 64 (listLenN - 1)) + signExtend12 (1 : BitVec 12)) (1 : Word)
    (by omega) ⟨b, hb, Or.inl ⟨hsmall, hlt, rfl, rfl⟩⟩
  have hsimp : ((listBase + BitVec.ofNat 64 (listLenN - 1)) + signExtend12 (1 : BitVec 12)
      - (1 : Word) - listBase) = BitVec.ofNat 64 (listLenN - 1) := by
    have h1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [h1]; bv_omega
  rw [hsimp] at h
  simp only [BitVec.toNat_ofNat] at h
  have := listBase.isLt
  omega

/-- The gap is inhabited: a buffer meeting every other domain hypothesis of
    `header_extract_*_spec_within` — 8-byte-aligned base in the RAM zone,
    `h_slack` **exactly** saturated at nine bytes, no address overflow, every
    byte a valid access — on which `hbound` is **false**.

    This is the negative control for the registry's coverRef prose: being a
    well-formed header with a 32-byte field payload is a statement about the
    header, and no statement about the header decides this gate. -/
theorem hbound_fails_under_slack_only :
    let listBase : Word := BitVec.ofNat 64 0xa0000000
    let headerBytes : List (BitVec 8) := (0x01 : BitVec 8) :: List.replicate 9 (0x00 : BitVec 8)
    let listLenN : Nat := 1
    listBase.toNat % 8 = 0 ∧
    listLenN + 9 ≤ headerBytes.length ∧
    listBase.toNat + headerBytes.length < 2 ^ 64 ∧
    (∀ k, k < headerBytes.length → isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) ∧
    ¬ Hbound listBase headerBytes listLenN := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro k hk
    simp only [isValidByteAccess, isValidMemAddr, MEM_START, MEM_END, INPUT_MEM_START,
      INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [List.length_cons, List.length_replicate] at hk
    omega
  · intro hb
    have := hb 0 ((BitVec.ofNat 64 0xa0000000 + BitVec.ofNat 64 0) + signExtend12 (1 : BitVec 12))
      (1 : Word) (by omega)
      ⟨(0x01 : BitVec 8), by decide, Or.inl ⟨by decide, by decide, rfl, rfl⟩⟩
    revert this
    decide

/-- A buffer on which `hbound` genuinely **holds**, with the same domain
    hypotheses discharged.  The list is one byte long and the buffer is 41
    bytes, i.e. `listLenN + 40` — comfortably past the 31 that
    `hbound_forces_trailing_slack` demands. -/
theorem hbound_instance :
    let listBase : Word := BitVec.ofNat 64 0xa0000000
    let headerBytes : List (BitVec 8) := (0x01 : BitVec 8) :: List.replicate 40 (0x00 : BitVec 8)
    let listLenN : Nat := 1
    listBase.toNat % 8 = 0 ∧
    listLenN + 9 ≤ headerBytes.length ∧
    listBase.toNat + headerBytes.length < 2 ^ 64 ∧
    (∀ k, k < headerBytes.length → isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) ∧
    Hbound listBase headerBytes listLenN := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro k hk
    simp only [isValidByteAccess, isValidMemAddr, MEM_START, MEM_END, INPUT_MEM_START,
      INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [List.length_cons, List.length_replicate] at hk
    omega
  · intro o next len ho hdec
    obtain ⟨b, hbget, harm⟩ := hdec
    -- `o ≤ 1`, so the prefix byte is `0x01` (o = 0) or `0x00` (o = 1); both are
    -- `< 0x80`, so only the single-byte arm can fire, and at `o = 1` its
    -- `ult cursor endPtr` conjunct is false.
    rcases o with _ | _ | o
    · -- o = 0: prefix `0x01`, single-byte arm fires, content start is offset 0
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hbget
      subst hbget
      rcases harm with ⟨_, _, h3, h4⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · subst h3; subst h4; decide
      all_goals exact absurd (by decide) h1
    · -- o = 1: prefix `0x00`; every arm's guard on the prefix byte fails
      simp only [List.getElem?_cons_succ, List.getElem?_replicate] at hbget
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hbget
      obtain ⟨-, hbget⟩ := hbget
      subst hbget
      rcases harm with ⟨_, h2, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd h2 (by decide)
      all_goals exact absurd (by decide) h1
    · exact absurd ho (by omega)

/-- `hbound_instance` is not satisfied by there being nothing to satisfy: a
    decode really does occur inside it, at offset 0, in the single-byte form.
    Without this the instance would be indistinguishable from
    `hbound_vacuous_control` below. -/
theorem hbound_instance_has_a_decode :
    rlpItemDecode ((0x01 : BitVec 8) :: List.replicate 40 (0x00 : BitVec 8)) 0
      (BitVec.ofNat 64 0xa0000000 + BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0xa0000000 + BitVec.ofNat 64 1)
      ((BitVec.ofNat 64 0xa0000000 + BitVec.ofNat 64 0) + signExtend12 (1 : BitVec 12))
      (1 : Word) :=
  ⟨(0x01 : BitVec 8), by decide, Or.inl ⟨by decide, by decide, rfl, rfl⟩⟩

/-- ⚠️ The vacuity trap `hbound_instance` is written to avoid.  At `listLenN = 0`
    the gate holds for a reason that has nothing to do with the bound: the
    cursor equals the end pointer, so **no** offset decodes — every fit conjunct
    of every arm fails.  A "witness" of that shape would report the gate as
    covered while covering nothing. -/
theorem hbound_vacuous_control :
    let listBase : Word := BitVec.ofNat 64 0xa0000000
    let headerBytes : List (BitVec 8) := List.replicate 40 (0x00 : BitVec 8)
    Hbound listBase headerBytes 0 ∧
      ∀ next len, ¬ rlpItemDecode headerBytes 0 (listBase + BitVec.ofNat 64 0)
        (listBase + BitVec.ofNat 64 0) next len := by
  have hno : ∀ next len, ¬ rlpItemDecode (List.replicate 40 (0x00 : BitVec 8)) 0
      (BitVec.ofNat 64 0xa0000000 + BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0xa0000000 + BitVec.ofNat 64 0) next len := by
    intro next len hdec
    obtain ⟨b, hbget, harm⟩ := hdec
    simp only [List.getElem?_replicate] at hbget
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hbget
    obtain ⟨-, hbget⟩ := hbget
    subst hbget
    rcases harm with ⟨_, h2, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact absurd h2 (by decide)
    all_goals exact absurd (by decide) h1
  exact ⟨fun o next len ho hdec => by
    have : o = 0 := by omega
    subst this
    exact absurd hdec (hno next len), hno⟩

end EvmAsm.Codegen.HeaderFieldsHboundCover
