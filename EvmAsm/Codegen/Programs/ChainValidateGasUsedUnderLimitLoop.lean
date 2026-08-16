/-
  Per-iteration body + loop induction for `chain_validate_gas_used_under_limit`.

  Builds on `ChainValidateGasUsedUnderLimitSpec` (model, prologue, epilogue,
  exit blocks) and reuses the generic array pieces from
  `ChainValidateExtraDataLengthSpec` plus the K34 call composition from the blob
  sibling.  The per-header body makes TWO strict `rlp_field_to_u64_strict` (K34) calls
  (field 10 = gas_used → the `GasUsed` cell, field 9 = gas_limit → the
  `GasLimit` cell) and compares the two decoded u64s with a dynamic `bltu`.
-/

import EvmAsm.Codegen.Programs.ChainValidateGasUsedUnderLimitSpec
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Evm64.StateAssertions

namespace EvmAsm.Codegen.ChainValidateGasUsedUnderLimitSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm
  (Saved savedFrame savedVals listNthFrame regsAt_listNthFrame
   frameSlotsSaved_listNthFrame)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom
   wordArrayFrom_append shiftLeft3_ofNat hdrOff hdrBaseAt hdrOff_succ hdrBaseAt_succ
   ofNat_ne_of_lt ofNat_succ_tie)

/-- K34's whole-routine step count for field index `index` (matching the flat
    spec's `((7 + 4 + callSteps) + ((1 + tailSteps) + 5))`). -/
def nCall (index _bytesLen : Nat) : Nat :=
  (7 + 4 + (1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)))
    + ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5)

theorem lengths_getElem_bang {lengths : List Nat} {i : Nat} (hi : i < lengths.length) :
    lengths[i]! = lengths[i] := getElem!_pos lengths i hi

/-! ## Setup block for call 1 (instructions 18--30)

    From the loop-guard fall-through (`D+72`) to just before the first `jal`
    (`D+124`).  Materializes `*IterPtr := hbi`, `*IterI := iW`, loads
    `x11 := lengths[i]`, `x10 := hbi`, `x12 := 10` (gas_used), `x13 := GasUsed`. -/

set_option maxRecDepth 8000 in
theorem cvgulSetup1 (hbi lenBase spC iW : Word) (Li : Nat)
    (old5 o10 o11 o12 o13 o28 : Word) :
    cpsTripleWithin 13 (D + 72) (D + 124) cvgulCode
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) **
        (.x13 ↦ᵣ o13) ** (.x28 ↦ᵣ o28) **
        memOwn IterPtr ** memOwn IterI **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ IterI) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
        (.x12 ↦ᵣ (10 : Word)) ** (.x13 ↦ᵣ GasUsed) **
        (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  have hla18 := la_materialize_within .x5 old5 (D + 72) IterPtr (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 72) cvgulProg 18 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 72) IterPtr)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 76) cvgulProg 19 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 72) IterPtr)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
  have s20 := sd_spec_gen_own_within .x5 .x18 IterPtr hbi (0 : BitVec 12) (D + 80)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPtr + (0 : Word) = IterPtr from by bv_omega] at s20
  have s20' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 80) cvgulProg 20 (.SD .x5 .x18 (0 : BitVec 12)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s20
  have hla21 := la_materialize_within .x5 IterPtr (D + 84) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 84) cvgulProg 21 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 84) IterI)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 88) cvgulProg 22 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 84) IterI)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
  have s23 := sd_spec_gen_own_within .x5 .x21 IterI iW (0 : BitVec 12) (D + 92)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s23
  have s23' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 92) cvgulProg 23 (.SD .x5 .x21 (0 : BitVec 12)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s23
  have s24 := slli_spec_gen_within .x28 .x21 o28 iW (3 : BitVec 6) (D + 96) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s24
  have s24' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 96) cvgulProg 24 (.SLLI .x28 .x21 (3 : BitVec 6)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s24
  have s25 := add_spec_gen_rd_eq_rs2_within .x28 .x9 lenBase (iW <<< 3) (D + 100) (by decide)
  have s25' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 100) cvgulProg 25 (.ADD .x28 .x9 .x28) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s25
  have s26 := ld_spec_gen_within .x11 .x28 (lenBase + (iW <<< 3)) o11 (BitVec.ofNat 64 Li)
    (0 : BitVec 12) (D + 104) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iW <<< 3)) + (0 : Word) = lenBase + (iW <<< 3) from by bv_omega] at s26
  have s26' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 104) cvgulProg 26 (.LD .x11 .x28 (0 : BitVec 12)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s26
  have s27 := mv_spec_gen_within .x10 .x18 hbi o10 (D + 108) (by decide)
  have s27' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 108) cvgulProg 27 (.MV .x10 .x18) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s27
  have s28 := li_spec_gen_within .x12 o12 (10 : Word) (D + 112) (by decide)
  have s28' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 112) cvgulProg 28 (.LI .x12 (10 : Word)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s28
  have hla29 := la_materialize_within .x13 o13 (D + 116) GasUsed (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 116) cvgulProg 29 (.AUIPC .x13 (EvmAsm.Rv64.laHi (D + 116) GasUsed)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 120) cvgulProg 30 (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (D + 116) GasUsed)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
  runBlock hla18 s20' hla21 s23' s24' s25' s26' s27' s28' hla29


/-! ## Reload + setup block for call 2 (instructions 33--45)

    On the call-1-success (`bne` not-taken) path from `D+132` to `D+184`: reload
    `x18 := *IterPtr`, `x21 := *IterI`, reload `x11 := lengths[i]`, set
    `x10 := hbi`, `x12 := 9` (gas_limit), `x13 := GasLimit`. -/

set_option maxRecDepth 8000 in
theorem cvgulReloadSetup2 (hbi lenBase iW : Word) (Li : Nat)
    (old5 o10 o11 o12 o13 o18 o21 o28 : Word) :
    cpsTripleWithin 13 (D + 132) (D + 184) cvgulCode
      ((.x9 ↦ᵣ lenBase) ** (.x5 ↦ᵣ old5) ** (.x18 ↦ᵣ o18) ** (.x21 ↦ᵣ o21) **
        (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) ** (.x13 ↦ᵣ o13) ** (.x28 ↦ᵣ o28) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) ** ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x9 ↦ᵣ lenBase) ** (.x5 ↦ᵣ IterI) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
        (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (9 : Word)) **
        (.x13 ↦ᵣ GasLimit) ** (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) ** ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  have hla33 := la_materialize_within .x5 old5 (D + 132) IterPtr (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 132) cvgulProg 33 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 132) IterPtr)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 136) cvgulProg 34 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 132) IterPtr)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
  have s35 := ld_spec_gen_within .x18 .x5 IterPtr o18 hbi (0 : BitVec 12) (D + 140) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPtr + (0 : Word) = IterPtr from by bv_omega] at s35
  have s35' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 140) cvgulProg 35 (.LD .x18 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s35
  have hla36 := la_materialize_within .x5 IterPtr (D + 144) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 144) cvgulProg 36 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 144) IterI)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 148) cvgulProg 37 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 144) IterI)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
  have s38 := ld_spec_gen_within .x21 .x5 IterI o21 iW (0 : BitVec 12) (D + 152) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s38
  have s38' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 152) cvgulProg 38 (.LD .x21 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s38
  have s39 := slli_spec_gen_within .x28 .x21 o28 iW (3 : BitVec 6) (D + 156) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s39
  have s39' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 156) cvgulProg 39 (.SLLI .x28 .x21 (3 : BitVec 6)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s39
  have s40 := add_spec_gen_rd_eq_rs2_within .x28 .x9 lenBase (iW <<< 3) (D + 160) (by decide)
  have s40' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 160) cvgulProg 40 (.ADD .x28 .x9 .x28) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s40
  have s41 := ld_spec_gen_within .x11 .x28 (lenBase + (iW <<< 3)) o11 (BitVec.ofNat 64 Li)
    (0 : BitVec 12) (D + 164) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iW <<< 3)) + (0 : Word) = lenBase + (iW <<< 3) from by bv_omega] at s41
  have s41' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 164) cvgulProg 41 (.LD .x11 .x28 (0 : BitVec 12)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s41
  have s42 := mv_spec_gen_within .x10 .x18 hbi o10 (D + 168) (by decide)
  have s42' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 168) cvgulProg 42 (.MV .x10 .x18) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s42
  have s43 := li_spec_gen_within .x12 o12 (9 : Word) (D + 172) (by decide)
  have s43' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 172) cvgulProg 43 (.LI .x12 (9 : Word)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s43
  have hla44 := la_materialize_within .x13 o13 (D + 176) GasLimit (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 176) cvgulProg 44 (.AUIPC .x13 (EvmAsm.Rv64.laHi (D + 176) GasLimit)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 180) cvgulProg 45 (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (D + 176) GasLimit)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
  runBlock hla33 s35' hla36 s38' s39' s40' s41' s42' s43' hla44


/-! ## Compare block (instructions 48--59): reload iterator + both values

    On the call-2-success (`bne` not-taken) path from `D+192` to `D+240`: reload
    `x18 := *IterPtr`, `x21 := *IterI`, `x6 := *GasUsed`, `x7 := *GasLimit`. -/

set_option maxRecDepth 8000 in
theorem cvgulCompare (hbi iW gu gl : Word) (old5 o18 o21 o6 o7 : Word) :
    cpsTripleWithin 12 (D + 192) (D + 240) cvgulCode
      ((.x5 ↦ᵣ old5) ** (.x18 ↦ᵣ o18) ** (.x21 ↦ᵣ o21) ** (.x6 ↦ᵣ o6) ** (.x7 ↦ᵣ o7) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (GasUsed ↦ₘ gu) ** (GasLimit ↦ₘ gl))
      ((.x5 ↦ᵣ GasLimit) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) ** (.x6 ↦ᵣ gu) ** (.x7 ↦ᵣ gl) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (GasUsed ↦ₘ gu) ** (GasLimit ↦ₘ gl)) := by
  have hla48 := la_materialize_within .x5 old5 (D + 192) IterPtr (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 192) cvgulProg 48 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 192) IterPtr)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 196) cvgulProg 49 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 192) IterPtr)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
  have s50 := ld_spec_gen_within .x18 .x5 IterPtr o18 hbi (0 : BitVec 12) (D + 200) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPtr + (0 : Word) = IterPtr from by bv_omega] at s50
  have s50' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 200) cvgulProg 50 (.LD .x18 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s50
  have hla51 := la_materialize_within .x5 IterPtr (D + 204) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 204) cvgulProg 51 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 204) IterI)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 208) cvgulProg 52 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 204) IterI)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
  have s53 := ld_spec_gen_within .x21 .x5 IterI o21 iW (0 : BitVec 12) (D + 212) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s53
  have s53' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 212) cvgulProg 53 (.LD .x21 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s53
  have hla54 := la_materialize_within .x5 IterI (D + 216) GasUsed (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 216) cvgulProg 54 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 216) GasUsed)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 220) cvgulProg 55 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 216) GasUsed)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
  have s56 := ld_spec_gen_within .x6 .x5 GasUsed o6 gu (0 : BitVec 12) (D + 224) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show GasUsed + (0 : Word) = GasUsed from by bv_omega] at s56
  have s56' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 224) cvgulProg 56 (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s56
  have hla57 := la_materialize_within .x5 GasUsed (D + 228) GasLimit (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 228) cvgulProg 57 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 228) GasLimit)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 232) cvgulProg 58 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 228) GasLimit)) (by bv_omega) (by rw [cvgul_length]; decide) (by decide) (by rw [cvgul_length]; decide))
  have s59 := ld_spec_gen_within .x7 .x5 GasLimit o7 gl (0 : BitVec 12) (D + 236) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show GasLimit + (0 : Word) = GasLimit from by bv_omega] at s59
  have s59' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 236) cvgulProg 59 (.LD .x7 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s59
  runBlock hla48 s50' hla51 s53' hla54 s56' hla57 s59'


/-! ## Advance block (instructions 61--66): step the iterator, loop back

    On the under-limit (`bltu` not-taken) path from `D+244`: `x18 += lengths[i]`,
    `x21 += 1`, then `jal x0, -196` back to the loop guard at `D+68`. -/

set_option maxRecDepth 8000 in
theorem cvgulAdvance (hbi lenBase iW : Word) (Li : Nat) (o28 o29 : Word) :
    cpsTripleWithin 6 (D + 244) (D + 68) cvgulCode
      ((.x21 ↦ᵣ iW) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x28 ↦ᵣ o28) **
        (.x29 ↦ᵣ o29) ** ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x21 ↦ᵣ (iW + signExtend12 (1 : BitVec 12))) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ (hbi + BitVec.ofNat 64 Li)) ** (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
        (.x29 ↦ᵣ BitVec.ofNat 64 Li) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  have s61 := slli_spec_gen_within .x28 .x21 o28 iW (3 : BitVec 6) (D + 244) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s61
  have s61' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 244) cvgulProg 61 (.SLLI .x28 .x21 (3 : BitVec 6)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s61
  have s62 := add_spec_gen_rd_eq_rs2_within .x28 .x9 lenBase (iW <<< 3) (D + 248) (by decide)
  have s62' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 248) cvgulProg 62 (.ADD .x28 .x9 .x28) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s62
  have s63 := ld_spec_gen_within .x29 .x28 (lenBase + (iW <<< 3)) o29 (BitVec.ofNat 64 Li)
    (0 : BitVec 12) (D + 252) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iW <<< 3)) + (0 : Word) = lenBase + (iW <<< 3) from by bv_omega] at s63
  have s63' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 252) cvgulProg 63 (.LD .x29 .x28 (0 : BitVec 12)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s63
  have s64 := add_spec_gen_rd_eq_rs1_within .x18 .x29 hbi (BitVec.ofNat 64 Li) (D + 256) (by decide)
  have s64' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 256) cvgulProg 64 (.ADD .x18 .x18 .x29) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s64
  have s65 := addi_spec_gen_same_within .x21 iW (1 : BitVec 12) (D + 260) (by decide)
  have s65' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 260) cvgulProg 65 (.ADDI .x21 .x21 (1 : BitVec 12)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s65
  have s66 := jal_x0_spec_gen_within (-196 : BitVec 21) (D + 264)
  rw [show (D + 264) + signExtend21 (-196 : BitVec 21) = D + 68 from by
    rw [show signExtend21 (-196 : BitVec 21) = (-196 : Word) from by decide]; bv_omega] at s66
  have s66' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 264) cvgulProg 66 (.JAL .x0 (-196 : BitVec 21)) (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) s66
  runBlock s61' s62' s63' s64' s65' s66'


/-! ## Call block 1 (instructions 18--31 + K34): setup1 ;; jal ;; rlp_field_to_u64_strict

    From the loop-guard fall-through (`D+72`) to the first return site (`D+128`),
    producing K34's `flatPost` for header `hbi` field 10 (gas_used → `GasUsed`),
    with the spill cells, the array cell, and the chain frame carried through. -/

set_option maxRecDepth 8000 in
theorem cvgulCall1 (hbi lenBase spC iW : Word) (Li : Nat)
    (nN s3 s4 oldOut oldOff oldLen old14 oldX1 old5 o10 o11 o12 o13 o28 : Word)
    (bytes : List (BitVec 8)) (csaved : Saved)
    (hsalign : hbi.toNat % 8 = 0)
    (hslack : Li + 9 ≤ bytes.length)
    (hover : hbi.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (hbi + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (13 + 1 + nCall 10 bytes.length) (D + 72) (D + 128) fullCode
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) **
        (.x13 ↦ᵣ o13) ** (.x28 ↦ᵣ o28) **
        memOwn IterPtr ** memOwn IterI **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
        (.x1 ↦ᵣ oldX1) ** (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
        (GasUsed ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        bytesRegion hbi bytes ** savedFrame spC csaved)
      ((.x1 ↦ᵣ LinkRA1) **
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA1, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hbi, GasUsed, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 10 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) := by
  set calleeNewSp : Word := spC + signExtend12 (-32 : BitVec 12) with hcalleeNewSp
  have hsetup := cpsTripleWithin_extend_code cvgul_mono
    (cvgulSetup1 hbi lenBase spC iW Li old5 o10 o11 o12 o13 o28)
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ oldX1) ** (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
      (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (GasUsed ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hbi bytes ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
                      | exact bytesRegion_pcFree _ _) hsetup
  have hjal := jal_link_spec_within
    (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64_strict
      (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 124)) (D + 124) oldX1
  rw [show (D + 124) + signExtend21 (jalOff GuestAddrs.rlp_field_to_u64_strict
      (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 124)) = EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B from by
    change BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + BitVec.ofNat 64 124 + _ =
      BitVec.ofNat 64 GuestAddrs.rlp_field_to_u64_strict
    exact jalOff_correct_add GuestAddrs.rlp_field_to_u64_strict ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit 124
      (by decide) (by decide) (by decide) (by decide),
    show (D + 124 + 4 : Word) = LinkRA1 from by
      change (D + 124 + 4 : Word) = D + 128; bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code cvgul_mono
    (cpsTripleWithin_extend_code (cr' := cvgulCode)
      (CodeReq.ofProg_mem_at D (D + 124) cvgulProg 31
        (.JAL .x1 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64_strict
          (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 124))) (by bv_omega)
        (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
      (.x5 ↦ᵣ IterI) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
      (.x12 ↦ᵣ (10 : Word)) ** (.x13 ↦ᵣ GasUsed) **
      (.x28 ↦ᵣ (lenBase + (iW <<< 3))) ** (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
      ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
      (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x14 ↦ᵣ old14) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (GasUsed ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hbi bytes ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
                      | exact bytesRegion_pcFree _ _) hjalC
  have hcallee0 := EvmAsm.Codegen.RlpFieldToU64StrictSAsm.rlpFieldToU64_flat_spec_within
    spC calleeNewSp hbi (BitVec.ofNat 64 Li) (10 : Word) GasUsed oldOut oldOff oldLen old14
    (⟨LinkRA1, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved) hbi s3 s4 iW bytes Li 10
    hcalleeNewSp rfl (by decide) (by decide)
    hsalign (by omega) (by omega) hover hvalid (by omega) (by show LinkRA1 &&& ~~~(1 : Word) = LinkRA1; decide)
  have hcalleeC := cpsTripleWithin_extend_code k34_mono hcallee0
  have hcallee : cpsTripleWithin (nCall 10 bytes.length) EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B LinkRA1 fullCode
      (regOwn .x5 ** regOwn .x28 **
        ((.x1 ↦ᵣ LinkRA1) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
          (.x18 ↦ᵣ hbi) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ iW) **
          (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (10 : Word)) **
          (.x13 ↦ᵣ GasUsed) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
          stackFree calleeNewSp 8 ** bytesRegion hbi bytes **
          (GasUsed ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen)))
      ((.x1 ↦ᵣ LinkRA1) **
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC calleeNewSp hbi oldOff oldLen
          (⟨LinkRA1, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hbi, GasUsed, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 10) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPre EvmAsm.Codegen.RlpFieldToU64StrictSAsm.wholeRest
      xperm_hyp hp) (fun _ hq => hq) hcalleeC
  have hcalleeF := cpsTripleWithin_frameR
    ((IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
      ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_memIs) hcallee
  have hsj := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupF hjalF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => ?_) hsj hcalleeF)
  have hp' : ((.x5 ↦ᵣ IterI) ** (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
      ((.x1 ↦ᵣ LinkRA1) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hbi) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ iW) **
        (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (10 : Word)) **
        (.x13 ↦ᵣ GasUsed) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
        stackFree calleeNewSp 8 ** bytesRegion hbi bytes **
        (GasUsed ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)) h := by
    xperm_hyp hp
  have hp'' := sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x)) h hp'
  xperm_hyp hp''


/-! ## Call block 1 with the consumed scratch registers owned -/

set_option maxRecDepth 8000 in
theorem cvgulCall1Owned (hbi lenBase spC iW : Word) (Li : Nat)
    (nN s3 s4 oldOut oldOff oldLen : Word) (bytes : List (BitVec 8)) (csaved : Saved)
    (hsalign : hbi.toNat % 8 = 0)
    (hslack : Li + 9 ≤ bytes.length)
    (hover : hbi.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (hbi + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (13 + 1 + nCall 10 bytes.length) (D + 72) (D + 128) fullCode
      ((((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
          memOwn IterPtr ** memOwn IterI **
          ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
          (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          (GasUsed ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
          bytesRegion hbi bytes ** savedFrame spC csaved) **
        regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28) ** regOwn .x1)
      ((.x1 ↦ᵣ LinkRA1) **
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA1, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hbi, GasUsed, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 10 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v1 => ?_)
  refine cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => h)
    (show cpsTripleWithin (13 + 1 + nCall 10 bytes.length) (D + 72) (D + 128) fullCode
      ((((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
          memOwn IterPtr ** memOwn IterI **
          ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
          (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          (GasUsed ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
          bytesRegion hbi bytes ** savedFrame spC csaved) ** (.x1 ↦ᵣ v1)) **
        regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28)
      ((.x1 ↦ᵣ LinkRA1) **
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA1, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hbi, GasUsed, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 10 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) from ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_of_forall_regIs_to_regOwn7
    (fun v5 v10 v11 v12 v13 v14 v28 => ?_)
  exact cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => by xperm_hyp h)
    (cvgulCall1 hbi lenBase spC iW Li nN s3 s4 oldOut oldOff oldLen v14 v1 v5 v10 v11 v12 v13 v28
      bytes csaved hsalign hslack hover hvalid)


/-! ## Call block 2 (instructions 33--46 + K34): reloadSetup2 ;; jal ;; rlp_field_to_u64_strict

    On the call-1-success path from `D+132` to the second return site (`D+188`),
    producing K34's `flatPost` for header `hbi` field 9 (gas_limit → `GasLimit`).
    The iterator is reloaded from the spill cells, so `x18`/`x21` on entry are
    arbitrary; the `GasUsed` cell (holding the first field's value) is carried
    unchanged by the caller. -/

set_option maxRecDepth 8000 in
theorem cvgulCall2 (hbi lenBase spC iW : Word) (Li : Nat)
    (nN s3 s4 oldOut oldOff oldLen old14 oldX1 old5 o10 o11 o12 o13 o18 o21 o28 : Word)
    (bytes : List (BitVec 8)) (csaved : Saved)
    (hsalign : hbi.toNat % 8 = 0)
    (hslack : Li + 9 ≤ bytes.length)
    (hover : hbi.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (hbi + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (13 + 1 + nCall 9 bytes.length) (D + 132) (D + 188) fullCode
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ o18) ** (.x21 ↦ᵣ o21) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) **
        (.x13 ↦ᵣ o13) ** (.x28 ↦ᵣ o28) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
        (.x1 ↦ᵣ oldX1) ** (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
        (GasLimit ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        bytesRegion hbi bytes ** savedFrame spC csaved)
      ((.x1 ↦ᵣ LinkRA2) **
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA2, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hbi, GasLimit, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 9 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) := by
  set calleeNewSp : Word := spC + signExtend12 (-32 : BitVec 12) with hcalleeNewSp
  have hsetup := cpsTripleWithin_extend_code cvgul_mono
    (cvgulReloadSetup2 hbi lenBase iW Li old5 o10 o11 o12 o13 o18 o21 o28)
  have hsetupF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ oldX1) ** (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
      (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (GasLimit ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hbi bytes ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
                      | exact bytesRegion_pcFree _ _) hsetup
  have hjal := jal_link_spec_within
    (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64_strict
      (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 184)) (D + 184) oldX1
  rw [show (D + 184) + signExtend21 (jalOff GuestAddrs.rlp_field_to_u64_strict
      (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 184)) = EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B from by
    change BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + BitVec.ofNat 64 184 + _ =
      BitVec.ofNat 64 GuestAddrs.rlp_field_to_u64_strict
    exact jalOff_correct_add GuestAddrs.rlp_field_to_u64_strict ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit 184
      (by decide) (by decide) (by decide) (by decide),
    show (D + 184 + 4 : Word) = LinkRA2 from by
      change (D + 184 + 4 : Word) = D + 188; bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code cvgul_mono
    (cpsTripleWithin_extend_code (cr' := cvgulCode)
      (CodeReq.ofProg_mem_at D (D + 184) cvgulProg 46
        (.JAL .x1 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64_strict
          (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 184))) (by bv_omega)
        (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
      (.x5 ↦ᵣ IterI) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
      (.x12 ↦ᵣ (9 : Word)) ** (.x13 ↦ᵣ GasLimit) **
      (.x28 ↦ᵣ (lenBase + (iW <<< 3))) ** (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
      ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
      (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x14 ↦ᵣ old14) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (GasLimit ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hbi bytes ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
                      | exact bytesRegion_pcFree _ _) hjalC
  have hcallee0 := EvmAsm.Codegen.RlpFieldToU64StrictSAsm.rlpFieldToU64_flat_spec_within
    spC calleeNewSp hbi (BitVec.ofNat 64 Li) (9 : Word) GasLimit oldOut oldOff oldLen old14
    (⟨LinkRA2, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved) hbi s3 s4 iW bytes Li 9
    hcalleeNewSp rfl (by decide) (by decide)
    hsalign (by omega) (by omega) hover hvalid (by omega) (by show LinkRA2 &&& ~~~(1 : Word) = LinkRA2; decide)
  have hcalleeC := cpsTripleWithin_extend_code k34_mono hcallee0
  have hcallee : cpsTripleWithin (nCall 9 bytes.length) EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B LinkRA2 fullCode
      (regOwn .x5 ** regOwn .x28 **
        ((.x1 ↦ᵣ LinkRA2) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
          (.x18 ↦ᵣ hbi) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ iW) **
          (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (9 : Word)) **
          (.x13 ↦ᵣ GasLimit) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
          stackFree calleeNewSp 8 ** bytesRegion hbi bytes **
          (GasLimit ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen)))
      ((.x1 ↦ᵣ LinkRA2) **
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC calleeNewSp hbi oldOff oldLen
          (⟨LinkRA2, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hbi, GasLimit, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 9) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPre EvmAsm.Codegen.RlpFieldToU64StrictSAsm.wholeRest
      xperm_hyp hp) (fun _ hq => hq) hcalleeC
  have hcalleeF := cpsTripleWithin_frameR
    ((IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
      ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_memIs) hcallee
  have hsj := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupF hjalF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => ?_) hsj hcalleeF)
  have hp' : ((.x5 ↦ᵣ IterI) ** (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
      ((.x1 ↦ᵣ LinkRA2) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hbi) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ iW) **
        (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (9 : Word)) **
        (.x13 ↦ᵣ GasLimit) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
        stackFree calleeNewSp 8 ** bytesRegion hbi bytes **
        (GasLimit ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)) h := by
    xperm_hyp hp
  have hp'' := sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x)) h hp'
  xperm_hyp hp''


/-! ## Normalizing K34's `flatPost` into a single Result-carrying assertion

    Generic in the output `cell` and the return-site `linkRA`.  Both arms of
    `flatPost` collapse to `dispNorm`, exposing `x10 = status` (for the `bne`)
    and `cell ↦ value` (for the reload) while owning the callee-perturbed
    remainder. -/
def dispNorm (spC calleeNewSp hbi validPtr firstBadPtr nN lenBase iW linkRA cell value status : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
  (.x18 ↦ᵣ hbi) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iW) **
  (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (cell ↦ₘ value) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  memOwn RfuOff ** memOwn RfuLen ** stackFree calleeNewSp 8 **
  bytesRegion hbi bytes **
  EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame calleeNewSp ⟨linkRA, nN, lenBase⟩

set_option maxRecDepth 8000 in
theorem flatPost_normalize (spC hbi validPtr firstBadPtr nN lenBase iW linkRA cell
    oldOff oldLen : Word) (bytes : List (BitVec 8)) (Li index : Nat) : ∀ h,
    (EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
      oldOff oldLen (⟨linkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
      (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hbi, cell, hbi, validPtr, firstBadPtr, iW⟩ : Saved)
      bytes Li index) h →
    (∃ status value,
      (dispNorm spC (spC + signExtend12 (-32 : BitVec 12)) hbi validPtr firstBadPtr nN lenBase iW
          linkRA cell value status bytes **
        ⌜EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result bytes hbi Li index status value⌝) h) := by
  intro h hp
  unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost at hp
  rcases hp with hs | hf
  · unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatSuccessReturned at hs
    obtain ⟨offset, len, v12, x5v, scalarStatus, wrapperStatus, outputValue, hs⟩ := hs
    unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.successPayload at hs
    refine ⟨wrapperStatus, outputValue, ?_⟩
    obtain ⟨h1, h2, hd, hu, hO, hP⟩ := hs
    obtain ⟨hBig, hRes⟩ := (sepConj_pure_right _).1 hP
    refine (sepConj_pure_right _).2 ⟨?_, hRes⟩
    have hOB : (_ ** _) h := ⟨h1, h2, hd, hu, hO, hBig⟩
    unfold dispNorm
    have hp1 : ((RfuOff ↦ₘ offset) ** (RfuLen ↦ₘ len) ** (.x5 ↦ᵣ x5v) **
        (.x11 ↦ᵣ scalarStatus) ** (.x12 ↦ᵣ v12) **
        ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) **
          (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iW) **
          (.x10 ↦ᵣ wrapperStatus) ** (.x0 ↦ᵣ (0 : Word)) ** (cell ↦ₘ outputValue) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 ** bytesRegion hbi bytes **
          EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
            ⟨linkRA, nN, lenBase⟩)) h := by xperm_hyp hOB
    have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
      (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12) (fun _ x => x))))) h hp1
    xperm_hyp hp2
  · unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatFailureReturned at hf
    obtain ⟨v11, v12, hf⟩ := hf
    unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.failurePayload at hf
    refine ⟨(1 : Word), (0 : Word), ?_⟩
    obtain ⟨h1, h2, hd, hu, hO, hP⟩ := hf
    obtain ⟨hBig, hRes⟩ := (sepConj_pure_right _).1 hP
    refine (sepConj_pure_right _).2 ⟨?_, hRes⟩
    have hOB : (_ ** _) h := ⟨h1, h2, hd, hu, hO, hBig⟩
    unfold dispNorm
    have hp1 : ((RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) ** (.x11 ↦ᵣ v11) **
        (.x12 ↦ᵣ v12) **
        ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) **
          (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iW) **
          (.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (cell ↦ₘ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 ** bytesRegion hbi bytes **
          EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
            ⟨linkRA, nN, lenBase⟩)) h := by xperm_hyp hOB
    have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
      (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x12)
        (fun _ x => x)))) h hp1
    xperm_hyp hp2


/-- K34's 3-slot saved frame, once restored, weakens to the merely-owned frame
    slots the loop invariant carries. -/
theorem k34SavedFrame_implies_frameSlotsOwn (newSp : Word)
    (saved : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved) : ∀ h,
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame newSp saved h →
    frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame newSp h := by
  intro h hp
  rw [← EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frameSlotsSaved_frame] at hp
  exact EvmAsm.Codegen.ChainValidateExtraDataLengthSpec.frameSlotsSaved_implies_frameSlotsOwn
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame newSp
    (EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedVals saved) h hp

/-- pcFree discharger covering the assertion atoms used in the dispatch. -/
local macro "pcfx" : tactic =>
  `(tactic| repeat' first
      | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs | exact pcFree_memOwn | exact pcFree_emp | exact pcFree_pure
      | exact bytesRegion_pcFree _ _ | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_wordArrayFrom _ _ _ | unfold savedFrame
      | unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame)

/-! ## Entry half of one iteration: guard → call 1 → K34 flatPost

    From the loop guard (`D+68`, `i < N`) through the first `jal` to K34's
    return (`D+128`), with the header slice handed to K34 for field 10 and the
    untouched `wordArray`/`bytesRegion` prefixes and the `GasLimit` cell framed. -/

set_option maxRecDepth 8000 in
theorem cvgulIterEntry (spC hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) (i : Nat)
    (oldOut oldLimit oldOff oldLen : Word)
    (hi : i < lengths.length)
    (hN : lengths.length < 2 ^ 64)
    (hsalign : (hdrBaseAt hdrBase lengths i).toNat % 8 = 0)
    (hslack : lengths[i]! + 9 ≤ (bigBytes.drop (hdrOff lengths i)).length)
    (hover : (hdrBaseAt hdrBase lengths i).toNat +
      (bigBytes.drop (hdrOff lengths i)).length < 2 ^ 64)
    (hvalid : ∀ k, k < (bigBytes.drop (hdrOff lengths i)).length →
      isValidByteAccess (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + (13 + 1 + nCall 10 (bigBytes.drop (hdrOff lengths i)).length)) (D + 68) (D + 128) fullCode
      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
        (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** savedFrame spC csaved **
        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
        (GasUsed ↦ₘ oldOut) ** (GasLimit ↦ₘ oldLimit) **
        (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        memOwn IterPtr ** memOwn IterI **
        regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)
      ((.x1 ↦ᵣ LinkRA1) **
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12))
          (hdrBaseAt hdrBase lengths i) oldOff oldLen
          (⟨LinkRA1, BitVec.ofNat 64 lengths.length, lenBase⟩ :
            EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hdrBaseAt hdrBase lengths i, GasUsed,
            hdrBaseAt hdrBase lengths i, validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ : Saved)
          (bigBytes.drop (hdrOff lengths i)) lengths[i]! 10 **
        (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        (GasLimit ↦ₘ oldLimit) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        savedFrame spC csaved) := by
  have hbeq := beq_spec_gen_within .x21 .x8 (224 : BitVec 13) (BitVec.ofNat 64 i)
    (BitVec.ofNat 64 lengths.length) (D + 68)
  have hbeqC := cpsBranchWithin_extend_code cvgul_mono
    (cpsBranchWithin_extend_code (cr' := cvgulCode)
      (CodeReq.ofProg_mem_at D (D + 68) cvgulProg 17 (.BEQ .x21 .x8 (224 : BitVec 13))
        (by bv_omega) (by rw [cvgul_length]; decide) rfl (by rw [cvgul_length]; decide)) hbeq)
  have hguard0 := cpsBranchWithin_ntakenStripPure2 hbeqC (fun hp hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact ofNat_ne_of_lt i lengths.length hi hN ((sepConj_pure_right _).1 hrest).2)
  rw [show (D + 68 + 4 : Word) = D + 72 from by bv_omega] at hguard0
  have hguardF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) **
      (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** savedFrame spC csaved **
      (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
      wordArrayFrom lenBase 0 (lengths.take i) **
      ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
      bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
      (GasUsed ↦ₘ oldOut) ** (GasLimit ↦ₘ oldLimit) **
      (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      memOwn IterPtr ** memOwn IterI **
      regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
      stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
                      | exact bytesRegion_pcFree _ _
                      | exact pcFree_wordArrayFrom _ _ _) hguard0
  have hcall := cvgulCall1Owned (hdrBaseAt hdrBase lengths i) lenBase spC (BitVec.ofNat 64 i)
    lengths[i]! (BitVec.ofNat 64 lengths.length) validPtr firstBadPtr oldOut oldOff oldLen
    (bigBytes.drop (hdrOff lengths i)) csaved hsalign hslack hover hvalid
  have hcallF := cpsTripleWithin_frameR
    (wordArrayFrom lenBase 0 (lengths.take i) **
      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
      (GasLimit ↦ₘ oldLimit) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)))
    (by repeat' first | apply pcFree_sepConj | exact pcFree_wordArrayFrom _ _ _
                      | exact bytesRegion_pcFree _ _ | exact pcFree_memIs) hcall
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
      rw [show (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) from shiftLeft3_ofNat i] at hq
      xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      rw [show (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) from shiftLeft3_ofNat i]
      xperm_hyp hp) hguardF hcallF)


end EvmAsm.Codegen.ChainValidateGasUsedUnderLimitSpec
