/-
  EvmAsm.Rv64.RLP.ScalarFieldWalkInfra

  EL.3 / Phase 5 — infrastructure for the recursive N-field scalar walk.

  The three-field walk (`unified_three_scalar_field_walk`) was unrolled by hand. To
  decode a fixed schema of N scalar fields by recursion, we need three pieces, all
  assembled here (the recursive walk theorem itself follows in a later step):

  1. `unified_scalar_field_decode_and_store_at_regOwn_memOwn` — the decode-and-store
     unit with BOTH its scratch registers (`regOwn`) AND its output cell (`memOwn`)
     owned abstractly. This is the atomic unit the recursive walk iterates: a field's
     output slot holds an unknown old value (it gets overwritten), so the walk's
     precondition is a fold of `memOwn` cells, peeled one per step.

  2. `nFieldWalkCR base rOut fields` — the recursive CodeReq of the unrolled N-unit
     program (unit `i` at `base + 184*i`).

  3. `scalarFieldUnitCR_disjoint_walkCR` — a single unit's CodeReq is disjoint from the
     whole rest-of-walk CodeReq (proved by induction on the field list, each step a
     `scalarFieldUnitCR_disjoint`). This discharges the `cpsTripleWithin_seq` obligation
     in the recursive walk's inductive step with one lemma.
-/

import EvmAsm.Rv64.RLP.ScalarFieldWalkChain

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **`regOwn` + `memOwn` re-entry unit.** Like `unified_scalar_field_decode_and_store_at_regOwn`
    but the output cell is also owned abstractly (`memOwn`) rather than at a known old
    value — the atomic unit a multi-field walk iterates over a fold of `memOwn` slots. -/
theorem unified_scalar_field_decode_and_store_at_regOwn_memOwn
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (offset : BitVec 12)
    (bs : List Byte) (O : Nat) (data : List Byte) (tail : List Byte)
    (v11Old v15Old : Word)
    (hlen1 : 1 ≤ data.length) (hlen8 : data.length ≤ 8)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    cpsTripleWithin (64 + 6 * data.length) base (base + 184)
      (scalarFieldUnitCR base rOut offset)
      (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (.x11 ↦ᵣ v11Old) **
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (regOwn .x14) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** memOwn (outBase + signExtend12 offset)))
      (((rOut ↦ᵣ outBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE data)) **
        ((outBase + signExtend12 offset) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE data))) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        regOwn .x14 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old)))
    ∧ decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail) := by
  refine ⟨?_, ?_⟩
  · refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_memIs_to_memOwn (a := outBase + signExtend12 offset)
        (P := ((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (.x11 ↦ᵣ v11Old) **
          (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (regOwn .x14) **
          (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) ** (rOut ↦ᵣ outBase))
        (fun vOld => ?_))
    have h := (unified_scalar_field_decode_and_store_at_regOwn base regionBase rOut outBase vOld
      offset bs O data tail v11Old v15Old hlen1 hlen8 halign hover hwin hdrop).1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (show cpsTripleWithin _ _ _ (scalarFieldUnitCR base rOut offset) _ _ from h)
  · exact (unified_scalar_field_decode_and_store_at_regOwn base regionBase rOut outBase 0 offset
      bs O data tail v11Old v15Old hlen1 hlen8 halign hover hwin hdrop).2

/-- The CodeReq of the unrolled N-field walk: unit `i` (a `scalarFieldUnitCR`) lives at
    `base + 184*i`. -/
def nFieldWalkCR (base : Word) (rOut : Reg) : List (BitVec 12 × List Byte) → CodeReq
  | [] => CodeReq.empty
  | (off, _) :: rest => (scalarFieldUnitCR base rOut off).union (nFieldWalkCR (base + 184) rOut rest)

/-- **Single unit ⊥ rest-of-walk.** A scalar-field unit at `base` is disjoint from the
    CodeReq of an N-field walk starting at `bw ≥ base + 184`. Proved by induction on the
    field list; the building block for the recursive walk's `cpsTripleWithin_seq`. -/
theorem scalarFieldUnitCR_disjoint_walkCR (base bw : Word) (rOut rOut' : Reg) (off : BitVec 12)
    (fields : List (BitVec 12 × List Byte))
    (hsep : base.toNat + 184 ≤ bw.toNat)
    (hov : bw.toNat + 184 * fields.length < 2 ^ 64) :
    (scalarFieldUnitCR base rOut off).Disjoint (nFieldWalkCR bw rOut' fields) := by
  induction fields generalizing bw with
  | nil => simpa [nFieldWalkCR] using CodeReq.Disjoint.empty_right (scalarFieldUnitCR base rOut off)
  | cons f rest ih =>
    obtain ⟨offf, _dataf⟩ := f
    rw [nFieldWalkCR]
    refine CodeReq.Disjoint.union_right ?_ ?_
    · exact scalarFieldUnitCR_disjoint base bw rOut rOut' off offf hsep
        (by simp only [List.length_cons] at hov; omega)
    · exact ih (bw + 184)
        (by have : bw.toNat + 184 < 2 ^ 64 := by
              simp only [List.length_cons] at hov; omega
            bv_omega)
        (by have hb : (bw + 184).toNat = bw.toNat + 184 := by
              have : bw.toNat + 184 < 2 ^ 64 := by simp only [List.length_cons] at hov; omega
              bv_omega
            simp only [List.length_cons] at hov; omega)

end EvmAsm.Rv64.RLP
