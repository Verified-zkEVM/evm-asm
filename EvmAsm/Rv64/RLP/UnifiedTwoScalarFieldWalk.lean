/-
  EvmAsm.Rv64.RLP.UnifiedTwoScalarFieldWalk

  EL.3 / Phase 5 — the first end-to-end MULTI-FIELD walk. Two contributions:

  1. `unified_scalar_field_decode_and_store_at_regOwn` — a `regOwn`-precondition
     variant of `unified_scalar_field_decode_and_store`. The decode clobbers its
     scratch registers (`x5, x10, x12, x14`) and so RELEASES them as `regOwn` in its
     post; the concrete unit, however, REQUIRES them concrete in its pre, so a second
     field's unit cannot consume the first's output. Peeling those four scratch
     registers to `regOwn` (via `cpsTripleWithin_of_forall_regIs_to_regOwn`) makes the
     unit callable after a prior field has run.

  2. `unified_two_scalar_field_walk` — decode-and-store field A → output slot `offA`,
     then field B → slot `offB`, through one output base pointer `rOut` (the STF
     calling convention: output struct base in `a2`, one slot offset per field). The
     concrete unit handles field A; the `regOwn` variant handles field B (its scratch
     is `regOwn` after A). The first unit's `x13` (advanced to the next field) feeds
     the second's payload pointer with no glue code, exactly as the sibling-descent
     walk (`unified_list_descend_two_siblings_bridge`) chains two descents.

  Layout (program base `base`; aligned `regionBase`, buffer `bs`, field-A offset `OA`):
      base       < unified_scalar_field_decode_and_store : field A >   (base .. base+184)
      base+184   < unified_scalar_field_decode_and_store : field B >   (base+184 .. base+368)
      base+368   (exit)
-/

import EvmAsm.Rv64.RLP.UnifiedScalarFieldStore

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **`regOwn`-re-entry decode-and-store (chainable).** `unified_scalar_field_decode_and_store`
    restated so the four clobbered scratch registers (`x5, x10, x12, x14`) are owned
    abstractly (`regOwn`) in the precondition instead of held at concrete values. A
    decode-and-store's post already releases exactly those four to `regOwn`, so this
    lets one field unit feed DIRECTLY into the next. `x11`/`x15` stay concrete
    (the prior unit supplies them: the value and the preserved scratch). Derived from
    the concrete unit by consuming the four owned scratch registers via
    `cpsTripleWithin_of_forall_regIs_to_regOwn`. -/
theorem unified_scalar_field_decode_and_store_at_regOwn
    (base regionBase : Word) (rOut : Reg) (outBase memOld : Word) (offset : BitVec 12)
    (bs : List Byte) (O : Nat) (data : List Byte) (tail : List Byte)
    (v11Old v15Old : Word)
    (hlen1 : 1 ≤ data.length) (hlen8 : data.length ≤ 8)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    cpsTripleWithin (64 + 6 * data.length) base (base + 184)
      ((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
          (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
              (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
              (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20))))).union
          (CodeReq.singleton (base + 180) (.SD rOut .x11 offset)))
      (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (.x11 ↦ᵣ v11Old) **
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (regOwn .x14) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld)))
      (((rOut ↦ᵣ outBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE data)) **
        ((outBase + signExtend12 offset) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE data))) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        regOwn .x14 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old)))
    ∧ decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail) := by
  refine ⟨?_, ?_⟩
  · refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
        (P := (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11Old) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x15 ↦ᵣ v15Old) **
          bytesRegion regionBase bs **
          ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld)) **
          regOwn .x10 ** regOwn .x12 ** regOwn .x14)
        (fun v5 => ?_))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
        (P := (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11Old) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x15 ↦ᵣ v15Old) **
          bytesRegion regionBase bs **
          ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld)) **
          (.x5 ↦ᵣ v5) ** regOwn .x12 ** regOwn .x14)
        (fun v10 => ?_))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x12)
        (P := (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11Old) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x15 ↦ᵣ v15Old) **
          bytesRegion regionBase bs **
          ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld)) **
          (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** regOwn .x14)
        (fun v12 => ?_))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x14)
        (P := (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11Old) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x15 ↦ᵣ v15Old) **
          bytesRegion regionBase bs **
          ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld)) **
          (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x12 ↦ᵣ v12))
        (fun v14 => ?_))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (unified_scalar_field_decode_and_store base regionBase rOut outBase memOld offset
        bs O data tail v5 v10 v11Old v12 v14 v15Old hlen1 hlen8 halign hover hwin hdrop).1
  · exact (unified_scalar_field_decode_and_store base regionBase rOut outBase memOld offset
      bs O data tail 0 0 v11Old 0 0 v15Old hlen1 hlen8 halign hover hwin hdrop).2

set_option maxRecDepth 8000 in
/-- **Two-field walk.** Decode-and-store scalar field A (at buffer offset `OA`) into
    output slot `offA`, then field B (at `OA + len(field A)`) into slot `offB`, through
    one output base pointer `rOut`. The concrete unit handles field A; the `regOwn`
    variant handles field B, whose scratch is `regOwn` after A ran. Field A advances
    `x13` to exactly field B's payload pointer — no glue code. The first cell (holding
    A's value) is framed through B, and B's cell through A, so both output slots end up
    written. Coincides with the two pure `decodeScalar` peels. -/
theorem unified_two_scalar_field_walk
    (base regionBase : Word) (rOut : Reg) (outBase memOldA memOldB : Word) (offA offB : BitVec 12)
    (bs : List Byte) (OA : Nat) (dataA dataB tail : List Byte)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hlenA1 : 1 ≤ dataA.length) (hlenA8 : dataA.length ≤ 8)
    (hlenB1 : 1 ≤ dataB.length) (hlenB8 : dataB.length ≤ 8)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdrop : bs.drop OA = encode (.bytes dataA) ++ encode (.bytes dataB) ++ tail) :
    cpsTripleWithin ((64 + 6 * dataA.length) + (64 + 6 * dataB.length)) base (base + 368)
      (((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
            (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
                (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
                (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20))))).union
            (CodeReq.singleton (base + 180) (.SD rOut .x11 offA))).union
        ((((CodeReq.singleton (base + 184) (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 184 + 4) unified_decoder_prog)).union
            (((CodeReq.singleton (base + 184 + 148) (.ADDI .x14 .x11 0)).union
                (CodeReq.singleton (base + 184 + 152) (.ADDI .x11 .x0 0))).union
                (CodeReq.ofProg (base + 184 + 156) (rlp_phase2_long_loop_body_prog (-20))))).union
            (CodeReq.singleton (base + 184 + 180) (.SD rOut .x11 offB))))
      ((((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
          (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 OA)) ** (.x14 ↦ᵣ v14Old) **
          (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
         ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offA) ↦ₘ memOldA))) **
       ((outBase + signExtend12 offB) ↦ₘ memOldB))
      ((((rOut ↦ᵣ outBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE dataB)) **
          ((outBase + signExtend12 offB) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE dataB))) **
         ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64
              ((OA + (encode (.bytes dataA)).length) + (encode (.bytes dataB)).length))) **
          regOwn .x14 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
          regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old))) **
       ((outBase + signExtend12 offA) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE dataA)))
    ∧ decodeScalar (bs.drop OA) = some (Nat.fromBytesBE dataA, encode (.bytes dataB) ++ tail)
    ∧ decodeScalar (bs.drop (OA + (encode (.bytes dataA)).length))
        = some (Nat.fromBytesBE dataB, tail) := by
  -- Field A's payload is followed by field B's encoding (re-associate the append).
  have hdropA : bs.drop OA = encode (.bytes dataA) ++ (encode (.bytes dataB) ++ tail) := by
    rw [hdrop, List.append_assoc]
  -- Field B starts exactly after field A's encoding.
  have hdropB : bs.drop (OA + (encode (.bytes dataA)).length) = encode (.bytes dataB) ++ tail := by
    rw [← List.drop_drop, hdropA, List.drop_append_length]
  obtain ⟨tA, hpureA⟩ := unified_scalar_field_decode_and_store base regionBase rOut outBase memOldA
    offA bs OA dataA (encode (.bytes dataB) ++ tail) v5Old v10 v11Old v12Old v14Old v15Old
    hlenA1 hlenA8 halign hover hwin hdropA
  obtain ⟨tB, hpureB⟩ := unified_scalar_field_decode_and_store_at_regOwn (base + 184) regionBase rOut
    outBase memOldB offB bs (OA + (encode (.bytes dataA)).length) dataB tail
    (BitVec.ofNat 64 (Nat.fromBytesBE dataA)) v15Old hlenB1 hlenB8 halign hover hwin hdropB
  -- Frame field B's output cell through field A, and field A's (written) cell through field B.
  have tA' := cpsTripleWithin_frameR ((outBase + signExtend12 offB) ↦ₘ memOldB) (by pcFree) tA
  have tB' := cpsTripleWithin_frameR
    ((outBase + signExtend12 offA) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE dataA)) (by pcFree) tB
  rw [show base + 184 + 184 = base + 368 from by bv_omega] at tB'
  -- Field-A unit (base .. base+184) ⊥ field-B unit (base+184 .. base+368): full 6×6 leaf split.
  have hd : (((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
            (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
            (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20))))).union
        (CodeReq.singleton (base + 180) (.SD rOut .x11 offA)))).Disjoint
      ((((CodeReq.singleton (base + 184) (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 184 + 4) unified_decoder_prog)).union
          (((CodeReq.singleton (base + 184 + 148) (.ADDI .x14 .x11 0)).union
              (CodeReq.singleton (base + 184 + 152) (.ADDI .x11 .x0 0))).union
              (CodeReq.ofProg (base + 184 + 156) (rlp_phase2_long_loop_body_prog (-20))))).union
          (CodeReq.singleton (base + 184 + 180) (.SD rOut .x11 offB))) := by
    -- A singleton A-leaf at `aX` (avoiding all of field-B's slots) ⊥ the field-B unit
    -- (split right into its 6 leaves). The four singleton A-leaves reuse this.
    have sDisj : ∀ (aX : Word) (iX : Instr),
        aX ≠ base + 184 → aX ≠ base + 184 + 148 → aX ≠ base + 184 + 152 →
        aX ≠ base + 184 + 180 →
        (∀ k, k < 36 → aX ≠ (base + 184 + 4) + BitVec.ofNat 64 (4 * k)) →
        (∀ k, k < 6 → aX ≠ (base + 184 + 156) + BitVec.ofNat 64 (4 * k)) →
        (CodeReq.singleton aX iX).Disjoint
          ((((CodeReq.singleton (base + 184) (.LBU .x5 .x13 0)).union
              (CodeReq.ofProg (base + 184 + 4) unified_decoder_prog)).union
              (((CodeReq.singleton (base + 184 + 148) (.ADDI .x14 .x11 0)).union
                  (CodeReq.singleton (base + 184 + 152) (.ADDI .x11 .x0 0))).union
                  (CodeReq.ofProg (base + 184 + 156) (rlp_phase2_long_loop_body_prog (-20))))).union
              (CodeReq.singleton (base + 184 + 180) (.SD rOut .x11 offB))) :=
      fun _ _ h1 h148 h152 h180 hp4 hp156 =>
        CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.union_right
              (CodeReq.Disjoint.singleton h1)
              (CodeReq.Disjoint.singleton_ofProg
                (CodeReq.ofProg_none_range_len _ _ 36 _ unified_decoder_prog_length hp4)))
            (CodeReq.Disjoint.union_right
              (CodeReq.Disjoint.union_right
                (CodeReq.Disjoint.singleton h148)
                (CodeReq.Disjoint.singleton h152))
              (CodeReq.Disjoint.singleton_ofProg
                (CodeReq.ofProg_none_range_len _ _ 6 _ (by rfl) hp156))))
          (CodeReq.Disjoint.singleton h180)
    refine CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left (CodeReq.Disjoint.union_left ?_ ?_)
        (CodeReq.Disjoint.union_left (CodeReq.Disjoint.union_left ?_ ?_) ?_)) ?_
    · -- LBU singleton (base) vs field-B unit:
      exact sDisj _ _ (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by intro k hk; bv_omega) (by intro k hk; bv_omega)
    · -- decoder ofProg (base+4, length 36) vs the field-B union:
      exact CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.ofProg_singleton
              (CodeReq.ofProg_none_range_len _ _ 36 _ unified_decoder_prog_length
                (by intro k hk; bv_omega)))
            (CodeReq.ofProg_disjoint_range_len _ _ 36 _ _ 36 unified_decoder_prog_length
              unified_decoder_prog_length (by intro k1 k2 hk1 hk2; bv_omega)))
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.union_right
              (CodeReq.Disjoint.ofProg_singleton
                (CodeReq.ofProg_none_range_len _ _ 36 _ unified_decoder_prog_length
                  (by intro k hk; bv_omega)))
              (CodeReq.Disjoint.ofProg_singleton
                (CodeReq.ofProg_none_range_len _ _ 36 _ unified_decoder_prog_length
                  (by intro k hk; bv_omega))))
            (CodeReq.ofProg_disjoint_range_len _ _ 36 _ _ 6 unified_decoder_prog_length (by rfl)
              (by intro k1 k2 hk1 hk2; bv_omega))))
        (CodeReq.Disjoint.ofProg_singleton
          (CodeReq.ofProg_none_range_len _ _ 36 _ unified_decoder_prog_length
            (by intro k hk; bv_omega)))
    · -- ADDI x14 singleton (base+148) vs field-B unit:
      exact sDisj _ _ (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by intro k hk; bv_omega) (by intro k hk; bv_omega)
    · -- ADDI x11 singleton (base+152) vs field-B unit:
      exact sDisj _ _ (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by intro k hk; bv_omega) (by intro k hk; bv_omega)
    · -- loop ofProg (base+156, length 6) vs the field-B union:
      exact CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.ofProg_singleton
              (CodeReq.ofProg_none_range_len _ _ 6 _ (by rfl) (by intro k hk; bv_omega)))
            (CodeReq.ofProg_disjoint_range_len _ _ 6 _ _ 36 (by rfl) unified_decoder_prog_length
              (by intro k1 k2 hk1 hk2; bv_omega)))
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.union_right
              (CodeReq.Disjoint.ofProg_singleton
                (CodeReq.ofProg_none_range_len _ _ 6 _ (by rfl) (by intro k hk; bv_omega)))
              (CodeReq.Disjoint.ofProg_singleton
                (CodeReq.ofProg_none_range_len _ _ 6 _ (by rfl) (by intro k hk; bv_omega))))
            (CodeReq.ofProg_disjoint_range_len _ _ 6 _ _ 6 (by rfl) (by rfl)
              (by intro k1 k2 hk1 hk2; bv_omega))))
        (CodeReq.Disjoint.ofProg_singleton
          (CodeReq.ofProg_none_range_len _ _ 6 _ (by rfl) (by intro k hk; bv_omega)))
    · -- SD singleton (base+180) vs field-B unit:
      exact sDisj _ _ (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by intro k hk; bv_omega) (by intro k hk; bv_omega)
  refine ⟨?_, hpureA, hpureB⟩
  exact cpsTripleWithin_seq hd
    (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) tA') tB'

-- Concrete cross-check: decode two single-byte scalars `0x2a` (= 42) and `0x07` (= 7)
-- from the buffer `[0x2a, 0x07]` at `0x2000`, storing 42 → `0x3000` (offset 0) and
-- 7 → `0x3008` (offset 8) via `x18` ⇒ both output cells written, both `decodeScalar` peels.
example :=
  unified_two_scalar_field_walk (0x1000 : Word) (0x2000 : Word) .x18 (0x3000 : Word) 0 0 0 8
    [(0x2a : Byte), (0x07 : Byte)] 0 [(0x2a : Byte)] [(0x07 : Byte)] [] 0 0 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro i hi
        have hlen : ([(0x2a : Byte), (0x07 : Byte)]).length = 2 := by decide
        rw [hlen] at hi
        interval_cases i <;> decide)
    (by decide)

end EvmAsm.Rv64.RLP
