/-
  EvmAsm.Rv64.RLP.ScalarFieldWalkChain

  EL.3 / Phase 5 — reusable scalar-field-unit CodeReq + chaining beyond two fields.

  The two-field walk (`unified_two_scalar_field_walk`) discharged the unit-A ⊥ unit-B
  disjointness with an explicit 36-leaf term. Chaining a *third* unit that way would
  need 72+ leaves, and an N-field walk is hopeless. This file factors the decode-and-
  store unit's 46-slot CodeReq into a named `scalarFieldUnitCR` and proves, ONCE, a
  range-based disjointness lemma `scalarFieldUnitCR_disjoint` (à la `descend_cr_disjoint`):
  two units whose 184-byte code ranges don't overlap have disjoint CodeReqs. Composing
  any number of units is then a handful of `union_left`/`union_right` + one lemma
  application per pair.

  `unified_three_scalar_field_walk` demonstrates it: compose `unified_two_scalar_field_walk`
  (fields A, B) with one more `regOwn` unit (field C), each storing to its own output
  slot. This is the concrete inductive step toward the fixed-schema N-field decoders.

  Unit layout (46 instruction slots `base + 4*k`, k = 0..45):
      k=0       LBU x5, x13, 0
      k=1..36   unified_decoder_prog       (base+4 .. base+144)
      k=37      ADDI x14, x11, 0           (base+148)
      k=38      ADDI x11, x0, 0            (base+152)
      k=39..44  rlp_phase2_long_loop_body  (base+156 .. base+176)
      k=45      SD rOut, x11, offset       (base+180)
-/

import EvmAsm.Rv64.RLP.UnifiedTwoScalarFieldWalk

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- The 46-slot CodeReq of one scalar-field decode-and-store unit at `base`
    (`unified_scalar_field_decode_and_store`'s code requirement, named for reuse). -/
def scalarFieldUnitCR (base : Word) (rOut : Reg) (offset : BitVec 12) : CodeReq :=
  (((CodeReq.singleton base (.LBU .x5 .x13 0)).union
      (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
      (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
          (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
          (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20))))).union
      (CodeReq.singleton (base + 180) (.SD rOut .x11 offset))

/-- A scalar-field unit maps to `none` at any address outside its 46 instruction slots
    `{base + 4*k : k < 46}`. -/
theorem scalarFieldUnitCR_none (base : Word) (rOut : Reg) (offset : BitVec 12) (a : Word)
    (h : ∀ k, k < 46 → a ≠ base + BitVec.ofNat 64 (4 * k)) :
    scalarFieldUnitCR base rOut offset a = none := by
  have ep1 : CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
    CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 a unified_decoder_prog_length
      (fun k hk => by
        have := h (k + 1) (by omega)
        rwa [show base + BitVec.ofNat 64 (4 * (k + 1)) = (base + 4) + BitVec.ofNat 64 (4 * k)
          from by bv_omega] at this)
  have ep2 : CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20)) a = none :=
    CodeReq.ofProg_none_range_len (base + 156) (rlp_phase2_long_loop_body_prog (-20)) 6 a (by rfl)
      (fun k hk => by
        have := h (k + 39) (by omega)
        rwa [show base + BitVec.ofNat 64 (4 * (k + 39)) = (base + 156) + BitVec.ofNat 64 (4 * k)
          from by bv_omega] at this)
  have s0 : CodeReq.singleton base (.LBU .x5 .x13 0) a = none :=
    CodeReq.singleton_miss (by have := h 0 (by omega); simpa using this)
  have s37 : CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0) a = none :=
    CodeReq.singleton_miss (by have := h 37 (by omega); bv_omega)
  have s38 : CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0) a = none :=
    CodeReq.singleton_miss (by have := h 38 (by omega); bv_omega)
  have s45 : CodeReq.singleton (base + 180) (.SD rOut .x11 offset) a = none :=
    CodeReq.singleton_miss (by have := h 45 (by omega); bv_omega)
  simp only [scalarFieldUnitCR, CodeReq.union, s0, ep1, s37, s38, ep2, s45]

/-- **Reusable scalar-field-unit disjointness.** Two units whose 184-byte code ranges
    don't overlap (`base2 ≥ base1 + 184`) have disjoint CodeReqs. The building block for
    chaining any number of decode-and-store units. -/
theorem scalarFieldUnitCR_disjoint (base1 base2 : Word) (rOut1 rOut2 : Reg)
    (off1 off2 : BitVec 12)
    (hsep : base1.toNat + 184 ≤ base2.toNat) (hov : base2.toNat + 184 < 2 ^ 64) :
    (scalarFieldUnitCR base1 rOut1 off1).Disjoint (scalarFieldUnitCR base2 rOut2 off2) := by
  intro a
  by_cases hin : ∀ k, k < 46 → a ≠ base1 + BitVec.ofNat 64 (4 * k)
  · exact Or.inl (scalarFieldUnitCR_none base1 rOut1 off1 a hin)
  · push Not at hin
    obtain ⟨k, hk, rfl⟩ := hin
    exact Or.inr (scalarFieldUnitCR_none base2 rOut2 off2 _ (fun k2 hk2 => by bv_omega))

set_option maxRecDepth 8000 in
/-- **Three-field walk.** Decode-and-store scalar fields A, B, C (at consecutive buffer
    offsets) into output slots `offA`, `offB`, `offC` through one output pointer `rOut`.
    Composes `unified_two_scalar_field_walk` (A, B) with one more `regOwn` unit (C);
    each prior cell is framed through the later units. The unit-AB ⊥ unit-C disjointness
    is two `scalarFieldUnitCR_disjoint` applications. Carries all three `decodeScalar`
    peels. -/
theorem unified_three_scalar_field_walk
    (base regionBase : Word) (rOut : Reg) (outBase memOldA memOldB memOldC : Word)
    (offA offB offC : BitVec 12)
    (bs : List Byte) (OA : Nat) (dataA dataB dataC tail : List Byte)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hlenA1 : 1 ≤ dataA.length) (hlenA8 : dataA.length ≤ 8)
    (hlenB1 : 1 ≤ dataB.length) (hlenB8 : dataB.length ≤ 8)
    (hlenC1 : 1 ≤ dataC.length) (hlenC8 : dataC.length ≤ 8)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hcode : base.toNat + 552 < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdrop : bs.drop OA =
      encode (.bytes dataA) ++ encode (.bytes dataB) ++ encode (.bytes dataC) ++ tail) :
    cpsTripleWithin
        (((64 + 6 * dataA.length) + (64 + 6 * dataB.length)) + (64 + 6 * dataC.length))
        base (base + 552)
      ((scalarFieldUnitCR base rOut offA).union (scalarFieldUnitCR (base + 184) rOut offB)
        |>.union (scalarFieldUnitCR (base + 368) rOut offC))
      (((((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
          (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 OA)) ** (.x14 ↦ᵣ v14Old) **
          (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
         ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offA) ↦ₘ memOldA))) **
        ((outBase + signExtend12 offB) ↦ₘ memOldB)) **
       ((outBase + signExtend12 offC) ↦ₘ memOldC))
      ((((rOut ↦ᵣ outBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE dataC)) **
          ((outBase + signExtend12 offC) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE dataC))) **
         ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64
              (((OA + (encode (.bytes dataA)).length) + (encode (.bytes dataB)).length)
                + (encode (.bytes dataC)).length))) **
          regOwn .x14 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
          regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old))) **
       (((outBase + signExtend12 offA) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE dataA)) **
        ((outBase + signExtend12 offB) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE dataB))))
    ∧ decodeScalar (bs.drop OA)
        = some (Nat.fromBytesBE dataA,
            encode (.bytes dataB) ++ (encode (.bytes dataC) ++ tail))
    ∧ decodeScalar (bs.drop (OA + (encode (.bytes dataA)).length))
        = some (Nat.fromBytesBE dataB, encode (.bytes dataC) ++ tail)
    ∧ decodeScalar (bs.drop ((OA + (encode (.bytes dataA)).length)
          + (encode (.bytes dataB)).length))
        = some (Nat.fromBytesBE dataC, tail) := by
  -- Buffer-offset / drop bookkeeping for the three consecutive fields.
  have hdropR : bs.drop OA =
      encode (.bytes dataA) ++ (encode (.bytes dataB) ++ (encode (.bytes dataC) ++ tail)) := by
    rw [hdrop]; simp only [List.append_assoc]
  have hdrop2 : bs.drop OA =
      encode (.bytes dataA) ++ encode (.bytes dataB) ++ (encode (.bytes dataC) ++ tail) := by
    rw [hdropR, ← List.append_assoc]
  have hdropBmid : bs.drop (OA + (encode (.bytes dataA)).length) =
      encode (.bytes dataB) ++ (encode (.bytes dataC) ++ tail) := by
    rw [← List.drop_drop, hdropR, List.drop_append_length]
  have hdropC : bs.drop ((OA + (encode (.bytes dataA)).length) + (encode (.bytes dataB)).length) =
      encode (.bytes dataC) ++ tail := by
    rw [← List.drop_drop, hdropBmid, List.drop_append_length]
  -- Fields A, B via the two-field walk (its `tail` is C's encoding ++ the real tail).
  obtain ⟨tAB, hpA, hpB⟩ := unified_two_scalar_field_walk base regionBase rOut outBase memOldA
    memOldB offA offB bs OA dataA dataB (encode (.bytes dataC) ++ tail)
    v5Old v10 v11Old v12Old v14Old v15Old hlenA1 hlenA8 hlenB1 hlenB8 halign hover hwin hdrop2
  -- Field C via the regOwn unit (its scratch is regOwn after A, B; x11 = B's value).
  obtain ⟨tC, hpC⟩ := unified_scalar_field_decode_and_store_at_regOwn (base + 368) regionBase rOut
    outBase memOldC offC bs ((OA + (encode (.bytes dataA)).length) + (encode (.bytes dataB)).length)
    dataC tail (BitVec.ofNat 64 (Nat.fromBytesBE dataB)) v15Old hlenC1 hlenC8 halign hover hwin
    hdropC
  -- Frame field C's cell through A,B and fields A,B's (written) cells through C.
  have tAB' := cpsTripleWithin_frameR ((outBase + signExtend12 offC) ↦ₘ memOldC) (by pcFree) tAB
  have tC' := cpsTripleWithin_frameR
    (((outBase + signExtend12 offA) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE dataA)) **
     ((outBase + signExtend12 offB) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE dataB))) (by pcFree) tC
  rw [show base + 368 + 184 = base + 552 from by bv_omega] at tC'
  -- Disjointness: (unit-A ∪ unit-B) ⊥ unit-C, via the reusable range lemma.
  have hd : ((scalarFieldUnitCR base rOut offA).union
      (scalarFieldUnitCR (base + 184) rOut offB)).Disjoint
      (scalarFieldUnitCR (base + 368) rOut offC) :=
    CodeReq.Disjoint.union_left
      (scalarFieldUnitCR_disjoint base (base + 368) rOut rOut offA offC (by bv_omega) (by bv_omega))
      (scalarFieldUnitCR_disjoint (base + 184) (base + 368) rOut rOut offB offC
        (by bv_omega) (by bv_omega))
  refine ⟨?_, hpA, hpB, hpC⟩
  exact cpsTripleWithin_seq hd
    (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) tAB') tC'

-- Concrete cross-check: decode three single-byte scalars `0x2a`, `0x07`, `0x09`
-- (= 42, 7, 9) from `[0x2a, 0x07, 0x09]` at `0x2000`, storing them to `0x3000`,
-- `0x3008`, `0x3010` via `x18` ⇒ all three output cells written.
example :=
  unified_three_scalar_field_walk (0x1000 : Word) (0x2000 : Word) .x18 (0x3000 : Word) 0 0 0
    0 8 16 [(0x2a : Byte), (0x07 : Byte), (0x09 : Byte)] 0
    [(0x2a : Byte)] [(0x07 : Byte)] [(0x09 : Byte)] [] 0 0 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by intro i hi
        have hlen : ([(0x2a : Byte), (0x07 : Byte), (0x09 : Byte)]).length = 3 := by decide
        rw [hlen] at hi
        interval_cases i <;> decide)
    (by decide)

end EvmAsm.Rv64.RLP
