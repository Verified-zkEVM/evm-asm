/-
  EvmAsm.Codegen.Programs.CryptoFieldLtPBridge

  Model ties for #11574: the two field-bound scan routines against their
  `SpecRef` counterparts.

  The machine sides are `Bls12G1LtPSAsm.blsgLtP_spec` and
  `Bn254FieldLtPSAsm.bnfLtP_spec` — both whole-routine, `sorry`-free, and both
  **already merged long before this file** (`docs/leaf-routine-targets.md:98-106`
  records that the missing piece was never the triple). What was missing is the
  vocabulary in which their `a0` can be read as a statement about the reference,
  and the `Progress/*` rows that make them witnessed.

  ## ⚠️ Predicate agreement is all `lt_p` can support

  Both routines return a **boolean in `a0`**, not the field element. So the
  strongest honest claim is that `a0` is the reference's accept/reject
  indicator. Value agreement is *not* available from these routines and is not
  claimed. Where a value appears below (`bytes_to_fq`'s `ok` payload) it is a
  fact about the **reference alone**, stated because a reader will want to know
  what the reference accepted — never sourced from the guest.

  ## ⭐ The two families agree to different depths, and the asymmetry is real

  - **BLS12-381 is full accept/reject agreement.** Under `w.length = 64`,
    `bytes_to_fq` (`SpecRef/PrecompilesBls.lean:78`) has exactly one remaining
    check — `c ≥ blsP` — which is precisely what `blsg_lt_p` computes.
  - **BN254 is *clause* agreement.** `bytes_to_g1`
    (`SpecRef/PrecompilesCurve.lean:83`) also bounds `y` and then tests the curve
    equation, so the guest scan corresponds to the **`x`-bound conjunct** of its
    guard and not to its overall verdict. Stating it as whole-function agreement
    would be an overclaim; it is stated as the clause it is.

  ## The wire pad is why the BLS tie is statable at all

  `bytes_to_fq` consumes a **64-byte** EIP-2537 wire felt; `blsg_lt_p` scans the
  **48** compact bytes. `Stateless.Crypto.eip2537_wire_pad_value` (#11703) is the
  relation between them; without it the two sides here would be different lists
  and this file would typecheck while relating different objects. BN254 needs no
  such step — `bytes_to_g1` slices 32 bytes directly.

  ## ⚠️ The `hpad` hypothesis is discharged by a real guest check — and the
  ## composition is NOT proved here

  Every calldata reader of a wire felt calls `blsg_is_zero_n(ptr, 16)` and
  rejects on nonzero **before** the 48-byte scan: `blsg_decode_g1`
  (`Bls12G1.lean:692-700`, both coordinates), `blsg2_decode_g2`
  (`Bls12G2.lean:774-784`, all four felts), `zkvm_bls12_map_fp_to_g1`
  (`Bls12MapG1Real.lean:23-29`), `zkvm_bls12_map_fp2_to_g2`
  (`Bls12MapG2Real.lean:23-38`). All are live — the precompile dispatch table
  wires 0x0b..0x11 (`PrecompileSharedExecute.lean:136-142`). So the guest is not
  over-accepting: it rejects a nonzero pad exactly where the reference does.

  ⚠️ But **that composition is not a theorem**, and cannot be one yet: those
  decoders exist only as assembly **strings** — no `Program`, no `_eq_prog` drift
  guard, no fixture — so nothing is statable over them. The result is an
  inversion worth naming: the range check underneath is a *proved* routine while
  the pad guard above it is *unverified assembly text*. Converting
  `blsg_decode_g1` is the prerequisite for regrading the row to `agrees`.

  ⚠️ An earlier draft cited only `blsk_g1_wire` — the **writer** — as evidence
  that the pad is a real guest step. That is true about the wire *layout* but is
  the weaker citation for the *hypothesis*: `blsk_g1_wire` never sees calldata.
  The reader-side guards above are the load-bearing evidence. Recorded rather
  than silently swapped, because reaching for the first citation that fits is how
  the wrong one ends up load-bearing.

  ## ⚠️ Base field, not scalar order

  `blsg_lt_p` compares against `blsg_p_be`, the **base-field** prime `blsP`
  (381-bit). #11574 as filed, and `docs/leaf-routine-targets.md` before #11676,
  both paired it with `Kzg.bytes_to_bls_field` / `BLS_MODULUS` — the **scalar
  field order** (255-bit), a different prime checked by a different routine
  (`blsk_lt_be`). `Stateless.Crypto.blsP_ne_blsModulus` pins that they differ.
-/

import EvmAsm.Codegen.Programs.Bls12G1LtPSAsm
import EvmAsm.Codegen.Programs.Bn254FieldLtPSAsm
import EvmAsm.Stateless.Crypto.FieldAssertions
import EvmAsm.Stateless.SpecRef.PrecompilesCurve

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto
open EvmAsm.Stateless.SpecRef (Bytes bytesBEtoNat)

/-! ## The constants, as theorems rather than `#guard`s

    `Bls12G1LtPSAsm.lean:85` and `Bn254FieldLtPSAsm.lean:83` each pin their
    prime with a `#guard` against a hex literal. A `#guard` evaluates at
    elaboration and yields **no reusable term** — it cannot be rewritten with.
    These are the same facts as proof terms, and stated against the `SpecRef`
    name rather than a repeated literal, so a divergence between the guest
    constant and the reference constant is a build failure rather than two
    literals nobody diffed. -/

/-- The `blsg_p_be` data fragment IS `SpecRef`'s BLS12-381 base-field prime. -/
theorem bls12PBytes_eq_blsP :
    beBytesToNat Bls12G1LtPSAsm.bls12PBytes = Stateless.SpecRef.Bls12.blsP := by
  decide

/-- The `bnf_p_be` data fragment IS `SpecRef`'s BN254 base-field prime. -/
theorem bn254PBytes_eq_fieldModulus :
    beBytesToNat Bn254FieldLtPSAsm.bn254PBytes
      = Stateless.SpecRef.Bn128.fieldModulus := by
  decide

/-! ## BLS12-381 — full accept/reject agreement -/

/-- `bytes_to_fq` at a correctly sized input reduces to its single remaining
    check. Factored out so the ties below rewrite with one lemma rather than
    re-unfolding the `do` block each time. -/
theorem bytes_to_fq_of_length_eq (w : Bytes) (hlen : w.length = 64) :
    Stateless.SpecRef.Bls12.bytes_to_fq w =
      if Stateless.SpecRef.Bls12.blsP ≤ bytesBEtoNat w then
        .error (.invalidParameter "Invalid field element")
      else .ok (bytesBEtoNat w) := by
  unfold Stateless.SpecRef.Bls12.bytes_to_fq
  simp [hlen]
  split <;> rfl

/-- **`bytes_to_fq` accepts exactly the wire felts whose compact suffix
    `blsg_lt_p` reports as `< p`.**

    The `ok` payload on the right is the reference's own accepted value; it is
    recorded because a reader wants to know *what* was accepted, and it is
    deliberately the compact suffix's value — the pad contributes nothing.
    ⚠️ It is **not** sourced from the guest, which produces only a boolean. -/
theorem blsg_lt_p_agrees_bytes_to_fq (w : Bytes)
    (hlen : w.length = 64) (hpad : ∀ i, i < 16 → w.getD i 0 = 0) :
    (beBytesToNat (w.drop 16) < beBytesToNat Bls12G1LtPSAsm.bls12PBytes)
      ↔ Stateless.SpecRef.Bls12.bytes_to_fq w
          = .ok (beBytesToNat (w.drop 16)) := by
  have hpv : bytesBEtoNat w = beBytesToNat (w.drop 16) :=
    Stateless.Crypto.eip2537_wire_pad_specref w hlen hpad
  rw [bytes_to_fq_of_length_eq w hlen, hpv, bls12PBytes_eq_blsP]
  by_cases hlt : beBytesToNat (w.drop 16) < Stateless.SpecRef.Bls12.blsP
  · simp [hlt, Nat.not_le_of_lt hlt]
  · simp [hlt, Nat.le_of_not_lt hlt]

/-- **The guest's `a0` IS the reference's accept/reject indicator.**

    This is the form that composes with `blsgLtP_spec`'s post, whose `a0` is
    literally the left-hand `if`. -/
theorem blsg_lt_p_a0_eq_bytes_to_fq_indicator (w : Bytes)
    (hlen : w.length = 64) (hpad : ∀ i, i < 16 → w.getD i 0 = 0) :
    (if beBytesToNat (w.drop 16) < beBytesToNat Bls12G1LtPSAsm.bls12PBytes
      then (1 : Word) else (0 : Word))
      = (match Stateless.SpecRef.Bls12.bytes_to_fq w with
         | .ok _ => (1 : Word)
         | .error _ => (0 : Word)) := by
  have hpv : bytesBEtoNat w = beBytesToNat (w.drop 16) :=
    Stateless.Crypto.eip2537_wire_pad_specref w hlen hpad
  rw [bytes_to_fq_of_length_eq w hlen, hpv, bls12PBytes_eq_blsP]
  by_cases hlt : beBytesToNat (w.drop 16) < Stateless.SpecRef.Bls12.blsP
  · simp [hlt, Nat.not_le_of_lt hlt]
  · simp [hlt, Nat.le_of_not_lt hlt]

/-- **The whole-routine triple, restated against `SpecRef`.**

    `blsgLtP_spec` with its `a0` rewritten to the reference indicator — the same
    theorem, in the vocabulary a correspondence row is read in. The
    `bytesRegion` still holds the **48** compact bytes, because that is what the
    routine reads; the 64-byte wire felt appears only in the hypotheses and in
    the post's reference call. -/
theorem blsgLtP_spec_specref (inPtr ret : Word) (w : Bytes)
    (hlen : w.length = 64) (hpad : ∀ i, i < 16 → w.getD i 0 = 0)
    (halignIn : inPtr.toNat % 8 = 0)
    (hovIn : inPtr.toNat + 48 < 2 ^ 64)
    (hvalidIn : ∀ k, k < 48 → isValidByteAccess (inPtr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 441 Bls12G1LtPSAsm.ltPBase ret
      (CodeReq.ofProg Bls12G1LtPSAsm.ltPBase blsgLtP_prog)
      (((.x10 : Reg) ↦ᵣ inPtr) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion inPtr (w.drop 16) **
       globalConst Bls12G1LtPSAsm.pConstAddr Bls12G1LtPSAsm.bls12PBytes)
      (((.x10 : Reg) ↦ᵣ (match Stateless.SpecRef.Bls12.bytes_to_fq w with
         | .ok _ => (1 : Word)
         | .error _ => (0 : Word))) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion inPtr (w.drop 16) **
       globalConst Bls12G1LtPSAsm.pConstAddr Bls12G1LtPSAsm.bls12PBytes) := by
  have hsuf : (w.drop 16).length = 48 :=
    Stateless.Crypto.eip2537_wire_suffix_length w hlen
  have hbase := Bls12G1LtPSAsm.blsgLtP_spec inPtr ret (w.drop 16) hsuf halignIn
    hovIn hvalidIn halignRet
  rwa [blsg_lt_p_a0_eq_bytes_to_fq_indicator w hlen hpad] at hbase

/-! ## BN254 — clause agreement, not whole-function agreement -/

/-- **The guest scan computes exactly `bytes_to_g1`'s `x`-bound conjunct.**

    ⚠️ Deliberately *not* stated as agreement with `bytes_to_g1`'s verdict:
    that function also bounds `y` and tests `y² = x³ + 3`, neither of which
    `bnf_lt_p` looks at. This is the clause, and only the clause. -/
theorem bnf_lt_p_agrees_field_bound (xs : Bytes) :
    (beBytesToNat xs < beBytesToNat Bn254FieldLtPSAsm.bn254PBytes)
      ↔ (bytesBEtoNat xs < Stateless.SpecRef.Bn128.fieldModulus) := by
  rw [bn254PBytes_eq_fieldModulus, Crypto.beBytesToNat_eq_fromBytesBE]

/-- The same clause in the polarity the reference literally writes it in —
    `if x ≥ fieldModulus then throw` (`PrecompilesCurve.lean:86`) — so a reader
    diffing against the Python does not have to flip it mentally. -/
theorem bnf_lt_p_rejects_iff_out_of_range (xs : Bytes) :
    ¬ (beBytesToNat xs < beBytesToNat Bn254FieldLtPSAsm.bn254PBytes)
      ↔ (bytesBEtoNat xs ≥ Stateless.SpecRef.Bn128.fieldModulus) := by
  rw [bnf_lt_p_agrees_field_bound xs]
  exact Nat.not_lt

/-- The clause at `bytes_to_g1`'s actual argument: it reads `data.take 32`, so a
    32-byte guest buffer is that slice of a well-formed input. -/
theorem bnf_lt_p_agrees_field_bound_take (data : Bytes) :
    (beBytesToNat (data.take 32) < beBytesToNat Bn254FieldLtPSAsm.bn254PBytes)
      ↔ (bytesBEtoNat (data.take 32) < Stateless.SpecRef.Bn128.fieldModulus) :=
  bnf_lt_p_agrees_field_bound _

/-- **`bnfLtP_spec` restated against `SpecRef`**: `a0` is `1` exactly when the
    reference's `x`-bound clause passes. -/
theorem bnfLtP_spec_specref (inPtr ret : Word) (xs : Bytes)
    (hlenX : xs.length = 32)
    (halignIn : inPtr.toNat % 8 = 0)
    (hovIn : inPtr.toNat + 32 < 2 ^ 64)
    (hvalidIn : ∀ k, k < 32 → isValidByteAccess (inPtr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 297 Bn254FieldLtPSAsm.ltPBase ret
      (CodeReq.ofProg Bn254FieldLtPSAsm.ltPBase bnfLtP_prog)
      (((.x10 : Reg) ↦ᵣ inPtr) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion inPtr xs **
       globalConst Bn254FieldLtPSAsm.pConstAddr Bn254FieldLtPSAsm.bn254PBytes)
      (((.x10 : Reg) ↦ᵣ (if bytesBEtoNat xs < Stateless.SpecRef.Bn128.fieldModulus
         then (1 : Word) else (0 : Word))) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion inPtr xs **
       globalConst Bn254FieldLtPSAsm.pConstAddr Bn254FieldLtPSAsm.bn254PBytes) := by
  have hbase := Bn254FieldLtPSAsm.bnfLtP_spec inPtr ret xs hlenX halignIn hovIn
    hvalidIn halignRet
  have hval : (if beBytesToNat xs < beBytesToNat Bn254FieldLtPSAsm.bn254PBytes
        then (1 : Word) else (0 : Word))
      = (if bytesBEtoNat xs < Stateless.SpecRef.Bn128.fieldModulus
        then (1 : Word) else (0 : Word)) := by
    by_cases h : bytesBEtoNat xs < Stateless.SpecRef.Bn128.fieldModulus
    · rw [if_pos h, if_pos ((bnf_lt_p_agrees_field_bound xs).mpr h)]
    · rw [if_neg h, if_neg (fun hh => h ((bnf_lt_p_agrees_field_bound xs).mp hh))]
  rwa [hval] at hbase

end EvmAsm.Codegen
