/-
  EvmAsm.EL.RLP.FuelMono

  **Fuel monotonicity for the RLP decoder** (GH #11711).

  `decodeAux`/`decodeItems` carry a structural fuel budget `nDepth`. This module
  proves the fact everything about fuel-sensitive decoding rests on: *extra fuel
  never changes a successful decode*.

      decodeAux   n bs = some r → n ≤ m → decodeAux   m bs = some r
      decodeItems n bs = some r → n ≤ m → decodeItems m bs = some r

  ## Why this is the load-bearing lemma for #11711

  `Rv64/RLP/WalkDecodeBridge.lean`'s `DecodeChain` states each link
  **fuel-insensitively**, as `∀ m, decodeAux (m + 1) … = some …`. That form is
  provable for byte-string items (`decodeAux_bytes_all_fuel_of_decode`) and is
  *false* for a nested list, whose decode recurses into `decodeItems nDepth` and
  so genuinely depends on the budget. #11711 records the consequence: every
  nested-list bridge is blocked, and `rlp_list_count_items` cannot reach
  `.bridged` — which matters because #11675 put that routine on the
  `mpt_node_kind` path, where an inline embedded branch child is a *nested list*
  and therefore the normal shape rather than an edge case.

  The issue asks for a fuel-sensitive chain predicate that threads a budget
  through the links, and warns that "the fuel bookkeeping is the whole
  difficulty". Monotonicity is what removes that difficulty rather than managing
  it: with it, a link need only be exhibited at **one** fuel, and any larger
  budget follows. So the fuel-sensitive predicate needs no per-link arithmetic at
  all — see `DecodeChainFrom` in `WalkDecodeBridge`, whose links are plain
  `decodeAux floor … = some …` obligations.

  ## Shape of the proof

  `decodeAux` and `decodeItems` are mutually recursive and **both** step the
  budget down by exactly one, so a single induction on the budget carries both
  statements at once (`decodeAux_decodeItems_mono`). Within the `decodeAux` step:

  * the four byte-string branches (`p < 0x80`, `≤ 0xB7`, `≤ 0xBF`) never mention
    `nDepth`, so they are handled once and for all by
    `decodeAux_succ_eq_of_lt_c0` — the branch bodies are literally equal at two
    different budgets;
  * the two list branches (`≤ 0xF7`, else) recurse into `decodeItems nDepth`, and
    that is exactly where the induction hypothesis is used.

  `takeBytes`/`readLength` take no fuel, so they need no separate treatment.

  ## Scope

  This is the model-side half only. It says nothing about which items the guest
  routine decodes; it makes the *statement* of a nested-list bridge possible.
  Deliberately no weakening of `DecodeChain` — #11711 is explicit that the
  existing predicate is correct and must not be relaxed so that it silently
  accepts lists, so the fuel-sensitive form is a **new, strictly more general**
  predicate and the old one is derived as its `floor = 1` instance.
-/

import EvmAsm.EL.RLP.Properties

namespace EvmAsm.EL.RLP

/-! ## The fuel-free branches of `decodeAux`

    Every prefix below `0xC0` selects a branch whose body does not mention
    `nDepth`, so at two different budgets those branches are *equal*, not merely
    both-successful. Isolating that here keeps the mutual induction below down to
    the two branches that genuinely recurse. -/

/-- For a prefix byte below `0xC0` (single byte, short string, or long string),
    `decodeAux` gives the same answer at any two nonzero budgets. -/
theorem decodeAux_succ_eq_of_lt_c0 (n n' : Nat) (pfx : Byte) (rest : List Byte)
    (h : pfx.toNat < 0xC0) :
    decodeAux (n + 1) (pfx :: rest) = decodeAux (n' + 1) (pfx :: rest) := by
  simp only [decodeAux]
  -- The prefix tests are on `pfx.toNat` alone; `h` kills the two list branches.
  by_cases h1 : pfx.toNat < 0x80
  · simp only [h1, if_true]
  · by_cases h2 : pfx.toNat ≤ 0xB7
    · simp only [h1, h2, if_false, if_true]
    · by_cases h3 : pfx.toNat ≤ 0xBF
      · simp only [h1, h2, h3, if_false, if_true]
      · omega

/-! ## Monotonicity

    Stated as a conjunction so one induction on the shared budget discharges the
    mutual recursion. The individual corollaries below are what callers use. -/

/-- **Fuel monotonicity, mutual form.** Extra budget never changes a successful
    `decodeAux`/`decodeItems`. One induction on `n` covers both, because both
    functions step the budget down by exactly one. -/
theorem decodeAux_decodeItems_mono : ∀ n : Nat,
    (∀ (m : Nat) (bs : List Byte) (r : RLPItem × List Byte),
        n ≤ m → decodeAux n bs = some r → decodeAux m bs = some r)
    ∧ (∀ (m : Nat) (bs : List Byte) (r : List RLPItem × List Byte),
        n ≤ m → decodeItems n bs = some r → decodeItems m bs = some r) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- `decodeAux 0` never succeeds, so there is nothing to transport.
      intro m bs r _ hsome
      rw [decodeAux_zero_fuel] at hsome
      exact absurd hsome (by simp)
    · -- `decodeItems 0` succeeds only on `[]`, where every budget agrees.
      intro m bs r _ hsome
      match bs with
      | [] =>
        simp only [decodeItems] at hsome ⊢
        exact hsome
      | b :: bs' =>
        simp only [decodeItems] at hsome
        exact absurd hsome (by simp)
  | succ n ih =>
    obtain ⟨ihAux, ihItems⟩ := ih
    refine ⟨?_, ?_⟩
    · -- `decodeAux (n+1) bs = some r → decodeAux m bs = some r` for `n+1 ≤ m`.
      intro m bs r hle hsome
      -- `m` is a successor, with `n ≤ m'`.
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hnm : n ≤ m' := by omega
      match bs with
      | [] =>
        rw [decodeAux_nil] at hsome
        exact absurd hsome (by simp)
      | pfx :: rest =>
        by_cases hc0 : pfx.toNat < 0xC0
        · -- Fuel-free branch: the two budgets give literally the same answer.
          rw [← decodeAux_succ_eq_of_lt_c0 n m' pfx rest hc0]
          exact hsome
        · -- List branches: the recursive `decodeItems n` is where `ihItems` lands.
          simp only [decodeAux] at hsome ⊢
          have h1 : ¬ (pfx.toNat < 0x80) := by omega
          have h2 : ¬ (pfx.toNat ≤ 0xB7) := by omega
          have h3 : ¬ (pfx.toNat ≤ 0xBF) := by omega
          simp only [h1, h2, h3, if_false] at hsome ⊢
          -- ⚠️ `cases h : e` generalises `e` in the GOAL only; `hsome` predates the
          -- tactic and keeps the unsubstituted term, so each peel needs an explicit
          -- `rw … at hsome`. The goal meanwhile is the `m'` version, whose
          -- `decodeItems m' payload` is left untouched by `cases hdi : decodeItems n
          -- payload` — and that surviving occurrence is precisely what `ihItems`
          -- rewrites. Getting this backwards is why an earlier draft looked like a
          -- numeral-normalisation problem: `rw … at ⊢` failed because the goal had
          -- ALREADY been substituted, not because the pattern differed.
          by_cases h4 : pfx.toNat ≤ 0xF7
          · -- Short list: payload from `takeBytes`, then transport `decodeItems`.
            simp only [h4, if_true] at hsome ⊢
            cases htb : takeBytes rest (pfx.toNat - 0xC0) with
            | none => rw [htb] at hsome; simp at hsome
            | some pr =>
              obtain ⟨payload, rest'⟩ := pr
              rw [htb] at hsome
              simp only [Option.bind_eq_bind, Option.bind_some] at hsome ⊢
              cases hdi : decodeItems n payload with
              | none => rw [hdi] at hsome; simp at hsome
              | some ir =>
                obtain ⟨items, leftover⟩ := ir
                rw [hdi] at hsome
                simp only [Option.bind_some] at hsome
                rw [ihItems m' payload (items, leftover) hnm hdi]
                simpa only [Option.bind_eq_bind, Option.bind_some] using hsome
          · -- Long list: `readLength`, the canonical `> 55` guard, then as above.
            simp only [h4, if_false] at hsome ⊢
            cases hrl : readLength rest (pfx.toNat - 0xF7) with
            | none => rw [hrl] at hsome; simp at hsome
            | some lr =>
              obtain ⟨lenVal, rest'⟩ := lr
              rw [hrl] at hsome
              simp only [Option.bind_eq_bind, Option.bind_some] at hsome ⊢
              by_cases h55 : lenVal ≤ 55
              · simp only [h55, if_true] at hsome; simp at hsome
              · simp only [h55, if_false] at hsome ⊢
                cases htb : takeBytes rest' lenVal with
                | none => rw [htb] at hsome; simp at hsome
                | some pr =>
                  obtain ⟨payload, rest''⟩ := pr
                  rw [htb] at hsome
                  simp only [Option.bind_some] at hsome ⊢
                  cases hdi : decodeItems n payload with
                  | none => rw [hdi] at hsome; simp at hsome
                  | some ir =>
                    obtain ⟨items, leftover⟩ := ir
                    rw [hdi] at hsome
                    simp only [Option.bind_some] at hsome
                    rw [ihItems m' payload (items, leftover) hnm hdi]
                    simpa only [Option.bind_eq_bind, Option.bind_some] using hsome
    · -- `decodeItems (n+1) bs = some r → decodeItems m bs = some r`.
      intro m bs r hle hsome
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hnm : n ≤ m' := by omega
      match bs with
      | [] =>
        simp only [decodeItems] at hsome ⊢
        exact hsome
      | b :: bs' =>
        simp only [decodeItems] at hsome ⊢
        cases hda : decodeAux n (b :: bs') with
        | none => rw [hda] at hsome; exact absurd hsome (by simp)
        | some ar =>
          obtain ⟨item, rest⟩ := ar
          rw [hda] at hsome
          simp only [Option.bind_eq_bind, Option.bind_some] at hsome
          cases hdi : decodeItems n rest with
          | none => rw [hdi] at hsome; exact absurd hsome (by simp)
          | some ir =>
            obtain ⟨items, rest'⟩ := ir
            rw [hdi] at hsome
            simp only [Option.bind_some] at hsome
            rw [ihAux m' (b :: bs') (item, rest) hnm hda]
            simp only [Option.bind_eq_bind, Option.bind_some]
            rw [ihItems m' rest (items, rest') hnm hdi]
            simpa only [Option.bind_eq_bind, Option.bind_some] using hsome

/-- **Fuel monotonicity for `decodeAux`.** A successful decode stays successful,
    with the same result, at any larger budget. -/
theorem decodeAux_mono_fuel {n m : Nat} {bs : List Byte} {r : RLPItem × List Byte}
    (hle : n ≤ m) (h : decodeAux n bs = some r) : decodeAux m bs = some r :=
  (decodeAux_decodeItems_mono n).1 m bs r hle h

/-- **Fuel monotonicity for `decodeItems`.** -/
theorem decodeItems_mono_fuel {n m : Nat} {bs : List Byte}
    {r : List RLPItem × List Byte}
    (hle : n ≤ m) (h : decodeItems n bs = some r) : decodeItems m bs = some r :=
  (decodeAux_decodeItems_mono n).2 m bs r hle h

/-! ## Consequences

    Two facts that #11711's design sketch needed as separate bookkeeping and that
    monotonicity now supplies directly. -/

/-- A decode at *any* budget lifts to the `∀ m` fuel-insensitive form above its
    own budget. This is the general statement of which
    `decodeAux_bytes_all_fuel_of_decode` is the byte-string special case — and
    unlike that lemma it holds for **lists** too, at the cost of the honest
    `n ≤ m + 1` side condition rather than an unrestricted `∀ m`. -/
theorem decodeAux_all_fuel_of_decode_ge {n : Nat} {bs : List Byte}
    {r : RLPItem × List Byte} (h : decodeAux n bs = some r) :
    ∀ m, n ≤ m + 1 → decodeAux (m + 1) bs = some r :=
  fun _ hm => decodeAux_mono_fuel hm h

/-- The top-level `decode` budget dominates any budget that already succeeded on
    the same input, so a decode witnessed at a small budget agrees with `decode`.
    This is what lets a bridge exhibit a link cheaply and still speak about the
    wrapper the guest is compared against. -/
theorem decode_of_decodeAux {n : Nat} {bs : List Byte} {r : RLPItem × List Byte}
    (hle : n ≤ 2 * bs.length) (h : decodeAux n bs = some r) : decode bs = some r := by
  rw [decode_eq_decodeAux_length]
  exact decodeAux_mono_fuel hle h

end EvmAsm.EL.RLP
