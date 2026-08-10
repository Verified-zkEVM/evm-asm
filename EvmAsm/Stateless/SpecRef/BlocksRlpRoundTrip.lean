/-
  EvmAsm.Stateless.SpecRef.BlocksRlpRoundTrip

  **Withdrawal RLP round trip, both directions** (GH #11692).

  `withdrawal_decode`'s `Correspondence` row is `.agrees`/`.machineOnly`, with the stated
  reason that SpecRef carries withdrawal ENCODE (`withdrawalToRlpItem`) and SSZ decode
  (`sszToWithdrawal`) but **no RLP decoder**, so there is nothing to bridge to and the
  differential does not transfer.

  #11692 observed that composing `withdrawalToRlpItem` with the RLP round trip gives a
  reference decoder rather than lacking one. Its ⚠️ was that the round-trip direction
  alone is not enough for a `.bridged` upgrade — the *converse* is where the content is,
  and it needs canonicality. As of #11896 the canonicality direction is proven
  (`EL.RLP.encode_decode`), so this module supplies both halves that are now available.

  ## What is here

  * `withdrawal_decode_encode` — every well-formed withdrawal encoding re-decodes to its
    item. Direct specialisation of `decode_encode`; the length side condition is
    inherited, not invented.
  * ⭐ `withdrawal_bytes_of_decode` — **the converse's payoff**: bytes that decode to a
    withdrawal item ARE that item's encoding. Immediate from `encode_decode`, and this is
    the fact a differential transfer consumes, because it turns agreement on the decoded
    *item* into agreement on *bytes*.
  * `withdrawal_decode_injective` — two byte strings decoding to the same withdrawal item
    are equal.

  ## ⚠️ What is NOT here, and what it needs

  The **reconstruction** step: *"if `decode bs` yields a 4-item list of the right shapes,
  then that list is `withdrawalToRlpItem w` for some `w`."* Without it the results below
  apply only once you already know the decoded item is a withdrawal item.

  Two concrete frictions for whoever does it:

  1. `scalarItem` (`BlocksRlp.lean:35`) is **`private`**, so a downstream module cannot
     name it. Reconstruction has to go through `withdrawalToRlpItem` itself, or
     `scalarItem` needs to lose `private`.
  2. The scalar fields need `Nat.toBytesBE`-inversion: for a decoded `.bytes b`, setting
     `n := Nat.fromBytesBE b` gives `scalarItem n = .bytes b` **only if `b` is canonical**
     (no leading zero). The tool exists —
     `EL.RLP.Nat.toBytesBE_fromBytesBE_of_canonical` — and the canonicality hypothesis is
     genuinely needed, not a proof artefact: `[0x00, 0x01]` and `[0x01]` decode to
     distinct RLP items, and only the latter is a `scalarItem`. So a withdrawal whose
     `index` was encoded with a leading zero is not in the image of
     `withdrawalToRlpItem`, and the guest must reject it for the row to be `.bridged`.

  ⇒ Per #11692's own instruction the row is **not** regraded here, and its
  "nothing to bridge to" note is now half-true rather than false: a reference decoder is
  derivable, but differential transfer still wants the reconstruction.
-/

import EvmAsm.Stateless.SpecRef.BlocksRlp
import EvmAsm.EL.RLP.EncodeDecode

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP

/-- **Round-trip direction.** A withdrawal's RLP encoding re-decodes to its item.

    The `< 256 ^ 8` bound is `decode_encode`'s own, inherited rather than invented: it is
    what lets the decoder's 8-byte length field represent the encoding, and its docstring
    notes it implies the same bound for every nested payload. -/
theorem withdrawal_decode_encode (w : Withdrawal)
    (h : (encode (withdrawalToRlpItem w)).length < 256 ^ 8) :
    decode (encode (withdrawalToRlpItem w)) = some (withdrawalToRlpItem w, []) :=
  decode_encode _ h

/-- ⭐ **The converse's payoff.** Bytes that decode completely to a withdrawal's item
    *are* that item's encoding — no length hypothesis needed, because the successful
    decode already implies it.

    This is the direction a differential transfer consumes: it converts agreement on the
    decoded **item** into agreement on **bytes**, which is what `.machineOnly → .bridged`
    requires and what the round-trip direction alone cannot give. -/
theorem withdrawal_bytes_of_decode {bs : List Byte} {w : Withdrawal}
    (h : decode bs = some (withdrawalToRlpItem w, [])) :
    bs = encode (withdrawalToRlpItem w) :=
  (encode_decode h).symm

/-- Two byte strings that decode to the same withdrawal item are equal — so the decoder
    cannot map distinct inputs to one withdrawal. -/
theorem withdrawal_decode_injective {bs₁ bs₂ : List Byte} {w : Withdrawal}
    (h₁ : decode bs₁ = some (withdrawalToRlpItem w, []))
    (h₂ : decode bs₂ = some (withdrawalToRlpItem w, [])) :
    bs₁ = bs₂ :=
  decode_injective h₁ h₂

/-- **The reconstruction obligation, named.** A decoded item is a withdrawal item exactly
    when some `w` produces it. Stated as a predicate so #11692's residual is one citable
    obligation rather than prose.

    ⚠️ Not proved here — see the module header for the two frictions (`scalarItem` is
    `private`; the scalar fields need canonicality via
    `Nat.toBytesBE_fromBytesBE_of_canonical`). Composing it with
    `withdrawal_bytes_of_decode` is what closes #11692. -/
def WithdrawalItemReconstructs (item : RLPItem) : Prop :=
  ∃ w : Withdrawal, item = withdrawalToRlpItem w

/-- With reconstruction available, the bytes-side conclusion follows for an arbitrary
    decodable input — which is the full shape #11692 asks for. -/
theorem withdrawal_bytes_of_decode_of_reconstructs {bs : List Byte} {item : RLPItem}
    (hdec : decode bs = some (item, [])) (hrec : WithdrawalItemReconstructs item) :
    ∃ w : Withdrawal, bs = encode (withdrawalToRlpItem w) := by
  obtain ⟨w, rfl⟩ := hrec
  exact ⟨w, withdrawal_bytes_of_decode hdec⟩

/-! ## Non-vacuity

    A concrete withdrawal whose item is exhibited, so the statements above are about
    something. Kept to the shape rather than concrete bytes: `encode`'s output for a
    32-byte `amount` is long, and the point is that `withdrawalToRlpItem` is a 4-item
    list, which is what reconstruction has to invert. -/

section NonVacuity

private def sampleWithdrawal : Withdrawal :=
  { index := 1, validatorIndex := 2, address := List.replicate 20 0, amount := 3 }

/-- The item really is a 4-element list — the arity reconstruction must match. -/
example : ∃ items : List RLPItem,
    withdrawalToRlpItem sampleWithdrawal = .list items ∧ items.length = 4 := by
  refine ⟨_, rfl, ?_⟩
  rfl

/-- `WithdrawalItemReconstructs` is satisfiable — so a future proof of it is not a proof
    of a false statement, and `withdrawal_bytes_of_decode_of_reconstructs` is not
    vacuous. -/
example : WithdrawalItemReconstructs (withdrawalToRlpItem sampleWithdrawal) :=
  ⟨sampleWithdrawal, rfl⟩

end NonVacuity

end EvmAsm.Stateless.SpecRef
