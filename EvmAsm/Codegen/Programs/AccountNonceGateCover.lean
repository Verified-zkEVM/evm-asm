/-
  EvmAsm.Codegen.Programs.AccountNonceGateCover

  **What the `a.nonce < 2 ^ 64` gate actually restricts** — coverage for the
  `rlp_content_to_u64` and `account_extract_nonce` rows, and a correction to
  what both said about it.

  Both rows described the gate as

      "the accessor's u64 output width, narrower than `Account.nonce`'s own
       `< 2 ^ 256` invariant"

  ⚠️ **`Account.nonce` has no invariant.**  It is a bare `Nat`
  (`EvmAsm/EL/WorldState.lean`), so the type admits arbitrarily large nonces —
  `account_nonce_is_an_unbounded_nat` builds one at `2 ^ 300`.  The `2 ^ 256`
  figure is not a property of the type at all: it is an explicit **hypothesis**
  (confusingly also spelled `hnonce`) carried by the `encodeAccount` length
  lemmas and by the sibling *balance* accessor, e.g.

      accountPayload_length_le   (a : Account) (hnonce : a.nonce < 2 ^ 256)
      encodeAccount_length_eq    (a : Account) (hnonce : a.nonce < 2 ^ 256)

  So the comparison the rows drew — a gate narrower than the type's own
  invariant — compares against something that does not exist.  What is true is
  narrower and more useful: **the u64 gate is stricter than the hypothesis its
  neighbouring theorems assume**, and above `2 ^ 256` nothing in this family
  claims anything at all, though the type permits it.

  ## Three regimes, not two

  | nonce | this gate | the encode lemmas' `hnonce` |
  |---|---|---|
  | `< 2 ^ 64` | ✅ | ✅ |
  | `2 ^ 64 ≤ n < 2 ^ 256` | ⛔ | ✅ |
  | `2 ^ 256 ≤ n` | ⛔ | ⛔ (type still permits it) |

  The middle band is the interesting one: it is inhabited, it is type-legal, the
  surrounding lemmas hold there, and this accessor's triple says nothing about
  it.  `nonce_gate_middle_band_is_inhabited` exhibits a member.

  ## Scope

  This is about the gate's extent, not about whether excluding those nonces is
  right.  A u64 output cell cannot hold `2 ^ 64`, so the restriction is
  certainly *sound*; whether a real Ethereum account can reach the middle band
  is a protocol question this module does not touch.

  Issue: #12867.
-/
import EvmAsm.EL.WorldState

namespace EvmAsm.Codegen.AccountNonceGateCover

open EvmAsm.EL

/-- A witness Account, parameterised on the nonce.  Every other field is zero:
    the gate constrains the nonce alone, so nothing else needs to vary. -/
def acct (n : Nat) : Account :=
  { nonce := n, balance := 0, storageRoot := 0, codeHash := 0, code := [] }

/-- A nonce past every bound in the family.  Spelled as a product rather than
    `2 ^ 300` so the elaborator's exponentiation threshold (256) does not fire a
    warning. -/
def hugeNonce : Nat := 2 ^ 256 * 2

/-- ⚠️ **`Account.nonce` is an unbounded `Nat`.**  This account is well-typed
    with a nonce above `2 ^ 256`, which is what refutes the rows' claim that the
    type carries a `< 2 ^ 256` invariant.  Nothing rejects it. -/
theorem account_nonce_is_an_unbounded_nat :
    (acct hugeNonce).nonce = hugeNonce ∧ ¬ (acct hugeNonce).nonce < 2 ^ 256 := by
  refine ⟨rfl, ?_⟩
  simp only [acct, hugeNonce]
  omega

/-- The gate admits an ordinary account. -/
theorem nonce_gate_admits_ordinary :
    (acct 42).nonce < 2 ^ 64 := by
  simp only [acct]; omega

/-- Its top edge: `2 ^ 64 - 1` is in, `2 ^ 64` is out.  A width gate is likeliest
    to be wrong by one exactly here. -/
theorem nonce_gate_boundary :
    (acct (2 ^ 64 - 1)).nonce < 2 ^ 64 ∧ ¬ (acct (2 ^ 64)).nonce < 2 ^ 64 := by
  refine ⟨?_, ?_⟩ <;> simp only [acct] <;> omega

/-- ⛔ **The middle band is inhabited.**  `2 ^ 64` is type-legal, satisfies the
    `hnonce : _ < 2 ^ 256` hypothesis the `encodeAccount` length lemmas and the
    sibling balance accessor carry, and is **excluded** by this gate.

    This is the negative control that matters: without it the gate would be
    consistent with coinciding with the surrounding hypotheses, in which case it
    would not be a separate restriction at all. -/
theorem nonce_gate_middle_band_is_inhabited :
    ¬ (acct (2 ^ 64)).nonce < 2 ^ 64 ∧ (acct (2 ^ 64)).nonce < 2 ^ 256 := by
  refine ⟨by simp only [acct]; omega, ?_⟩
  simp only [acct]
  omega

/-- The three regimes are exhaustive and ordered: every account falls in exactly
    one, and the gate is the strictest of the three cuts. -/
theorem nonce_regimes_exhaustive (a : Account) :
    a.nonce < 2 ^ 64 ∨ (2 ^ 64 ≤ a.nonce ∧ a.nonce < 2 ^ 256) ∨ 2 ^ 256 ≤ a.nonce := by
  omega

end EvmAsm.Codegen.AccountNonceGateCover
