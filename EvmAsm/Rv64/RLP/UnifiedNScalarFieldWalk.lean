/-
  EvmAsm.Rv64.RLP.UnifiedNScalarFieldWalk

  EL.3 / Phase 5 — the recursive N-field scalar walk. The keystone for fixed-schema
  STF decoders: decode-and-store a whole LIST of consecutive scalar fields, each to its
  own output slot, through one output base pointer `rOut`.

  Generalizes `unified_three_scalar_field_walk` from a hand-unrolled 3 to an arbitrary
  list `fields : List (BitVec 12 × List Byte)` (output offset, field data) by recursion:
  the inductive step runs the `regOwn`+`memOwn` unit on the head field, then the IH on
  the tail, framing the tail's output cells (a `memOwn` fold) through the head unit and
  the head's written cell through the tail walk. Disjointness of the head unit's CodeReq
  from the rest-of-walk is the step-13 `scalarFieldUnitCR_disjoint_walkCR` lemma. The
  whole program is `nFieldWalkCR` (unit `i` at `base + 184*i`).

  Output slots: pre = a fold of `memOwn` cells (each holds some old value, overwritten);
  post = a fold of `↦ₘ` cells holding the decoded field values.
-/

import EvmAsm.Rv64.RLP.ScalarFieldWalkInfra

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- Total step count of the N-field walk: `Σ (64 + 6 * len_i)`. -/
def nFieldSteps : List (BitVec 12 × List Byte) → Nat
  | [] => 0
  | (_, data) :: rest => (64 + 6 * data.length) + nFieldSteps rest

/-- The output cells of an N-field walk BEFORE the walk: a `**`-fold of `memOwn` slots
    (each holds an unknown old value, to be overwritten). -/
def nFieldOutOwn (outBase : Word) : List (BitVec 12 × List Byte) → Assertion
  | [] => empAssertion
  | (off, _) :: rest => memOwn (outBase + signExtend12 off) ** nFieldOutOwn outBase rest

/-- The output cells AFTER the walk: a `**`-fold of `↦ₘ` slots holding the decoded
    field values. -/
def nFieldOutVal (outBase : Word) : List (BitVec 12 × List Byte) → Assertion
  | [] => empAssertion
  | (off, data) :: rest =>
      ((outBase + signExtend12 off) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE data)) **
        nFieldOutVal outBase rest

theorem nFieldOutOwn_pcFree (outBase : Word) (fields : List (BitVec 12 × List Byte)) :
    (nFieldOutOwn outBase fields).pcFree := by
  induction fields with
  | nil => exact pcFree_emp
  | cons f rest ih => exact pcFree_sepConj pcFree_memOwn ih

theorem nFieldOutVal_pcFree (outBase : Word) (fields : List (BitVec 12 × List Byte)) :
    (nFieldOutVal outBase fields).pcFree := by
  induction fields with
  | nil => exact pcFree_emp
  | cons f rest ih => exact pcFree_sepConj pcFree_memIs ih

set_option maxRecDepth 8000 in
/-- **Recursive N-field scalar walk.** Decode-and-store every field in `fields` (at
    consecutive buffer offsets starting at `O`) to its own output slot, through one
    output base pointer `rOut`. The output cells start as `memOwn` (unknown old values)
    and end holding the decoded values; `x13` advances past the whole concatenation. -/
theorem unified_n_scalar_field_walk
    (regionBase outBase : Word) (rOut : Reg) (bs tail : List Byte)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    ∀ (fields : List (BitVec 12 × List Byte)) (base : Word) (O : Nat) (v11Old v15Old : Word),
      (∀ f ∈ fields, 1 ≤ f.2.length ∧ f.2.length ≤ 8) →
      base.toNat + 184 * fields.length < 2 ^ 64 →
      bs.drop O = (fields.flatMap (fun f => encode (.bytes f.2))) ++ tail →
      cpsTripleWithin (nFieldSteps fields) base (base + BitVec.ofNat 64 (184 * fields.length))
        (nFieldWalkCR base rOut fields)
        (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (.x11 ↦ᵣ v11Old) **
          (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (regOwn .x14) **
          (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
         ((rOut ↦ᵣ outBase) ** nFieldOutOwn outBase fields))
        (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
          (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64
             (O + (fields.flatMap (fun f => encode (.bytes f.2))).length))) ** (regOwn .x14) **
          (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
         ((rOut ↦ᵣ outBase) ** nFieldOutVal outBase fields)) := by
  intro fields
  induction fields with
  | nil =>
    intro base O v11Old v15Old _ _ _
    simp only [nFieldSteps, nFieldWalkCR, nFieldOutOwn, nFieldOutVal, List.flatMap_nil,
      List.length_nil, Nat.mul_zero, Nat.add_zero]
    rw [show base + BitVec.ofNat 64 0 = base from by bv_omega]
    refine cpsTripleWithin_refl (fun h hp => ?_)
    exact sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (regIs_implies_regOwn .x11))))) h hp
  | cons f rest ih =>
    intro base O v11Old v15Old hfields hcode hdrop
    obtain ⟨off, data⟩ := f
    have hf := hfields (off, data) (by simp)
    -- buffer split for the head field
    have hflat : (((off, data) :: rest).flatMap (fun f => encode (.bytes f.2)))
        = encode (.bytes data) ++ (rest.flatMap (fun f => encode (.bytes f.2))) := by
      simp [List.flatMap_cons]
    rw [hflat] at hdrop
    have hdropF : bs.drop O =
        encode (.bytes data) ++ ((rest.flatMap (fun f => encode (.bytes f.2))) ++ tail) := by
      rw [hdrop, List.append_assoc]
    have hdropRest : bs.drop (O + (encode (.bytes data)).length) =
        (rest.flatMap (fun f => encode (.bytes f.2))) ++ tail := by
      rw [← List.drop_drop, hdropF, List.drop_append_length]
    -- no-overflow facts
    have hbw : base.toNat + 184 < 2 ^ 64 := by
      simp only [List.length_cons] at hcode; omega
    -- head field: the regOwn+memOwn unit at `base`
    obtain ⟨tF, _⟩ := unified_scalar_field_decode_and_store_at_regOwn_memOwn base regionBase rOut
      outBase off bs O data ((rest.flatMap (fun f => encode (.bytes f.2))) ++ tail) v11Old v15Old
      hf.1 hf.2 halign hover hwin hdropF
    -- tail walk: the IH at `base + 184`
    have hIH := ih (base + 184) (O + (encode (.bytes data)).length)
      (BitVec.ofNat 64 (Nat.fromBytesBE data)) v15Old
      (fun g hg => hfields g (List.mem_cons_of_mem _ hg))
      (by have : (base + 184).toNat = base.toNat + 184 := by bv_omega
          simp only [List.length_cons] at hcode; omega)
      hdropRest
    -- frame the tail's output cells through the head unit, head's cell through the tail
    have tF' := cpsTripleWithin_frameR (nFieldOutOwn outBase rest)
      (nFieldOutOwn_pcFree outBase rest) tF
    have hIH' := cpsTripleWithin_frameR
      ((outBase + signExtend12 off) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE data))
      (by exact pcFree_memIs) hIH
    rw [show (base + 184) + BitVec.ofNat 64 (184 * rest.length)
        = base + BitVec.ofNat 64 (184 * (rest.length + 1)) from by
          have : base.toNat + 184 * (rest.length + 1) < 2 ^ 64 := by
            simpa only [List.length_cons] using hcode
          bv_omega] at hIH'
    -- disjointness: head unit ⊥ rest-of-walk
    have hd := scalarFieldUnitCR_disjoint_walkCR base (base + 184) rOut rOut off rest
      (by bv_omega)
      (by have : (base + 184).toNat = base.toNat + 184 := by bv_omega
          simp only [List.length_cons] at hcode; omega)
    -- assemble: head ⨾ tail, then reconcile to the goal's folded pre/post
    simp only [nFieldSteps, nFieldWalkCR, nFieldOutOwn, nFieldOutVal, hflat, List.length_append,
      List.length_cons]
    rw [show O + ((encode (.bytes data)).length
            + (rest.flatMap (fun f => encode (.bytes f.2))).length)
          = (O + (encode (.bytes data)).length)
            + (rest.flatMap (fun f => encode (.bytes f.2))).length from by omega]
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_seq hd
        (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) tF') hIH')

-- Concrete cross-check: the recursive walk over the 3-field schema
-- `[(0, [0x2a]), (8, [0x07]), (16, [0x09])]` decodes `[0x2a, 0x07, 0x09]` at `0x2000`
-- and stores 42/7/9 to `0x3000`/`0x3008`/`0x3010` via `x18` — matching the hand-unrolled
-- `unified_three_scalar_field_walk`, now as an instance of the general N-field walk.
example :=
  unified_n_scalar_field_walk (0x2000 : Word) (0x3000 : Word) .x18
    [(0x2a : Byte), (0x07 : Byte), (0x09 : Byte)] []
    (by decide) (by decide)
    (by intro i hi
        have hlen : ([(0x2a : Byte), (0x07 : Byte), (0x09 : Byte)]).length = 3 := by decide
        rw [hlen] at hi
        interval_cases i <;> decide)
    [((0 : BitVec 12), [(0x2a : Byte)]), ((8 : BitVec 12), [(0x07 : Byte)]),
      ((16 : BitVec 12), [(0x09 : Byte)])]
    (0x1000 : Word) 0 0 0
    (by decide) (by decide) (by decide)

end EvmAsm.Rv64.RLP
