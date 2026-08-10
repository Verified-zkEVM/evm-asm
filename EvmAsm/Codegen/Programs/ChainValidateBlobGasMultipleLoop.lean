/-
  Per-iteration body + loop induction for `chain_validate_blob_gas_used_multiple`.

  Builds on `ChainValidateBlobGasMultipleSpec` (model, prologue, epilogue, exit
  blocks) and reuses the generic array pieces from
  `ChainValidateExtraDataLengthSpec`.  The per-header body decodes field 17 via
  the strict `rlp_field_to_u64` K34 wrapper, then checks that the decoded u64 is
  a multiple of `GAS_PER_BLOB = 2^17` with `and x30, x6, x7 ; bne x30, x0`
  (`x7 = Mask = GAS_PER_BLOB - 1 = 131071`), i.e. `(value &&& Mask) = 0`.
-/

import EvmAsm.Codegen.Programs.ChainValidateBlobGasMultipleSpec
import EvmAsm.Evm64.StateAssertions

namespace EvmAsm.Codegen.ChainValidateBlobGasMultipleSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm
  (Saved savedFrame savedVals listNthFrame regsAt_listNthFrame
   frameSlotsSaved_listNthFrame)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom
   wordArrayFrom_append shiftLeft3_ofNat hdrOff hdrBaseAt hdrOff_succ hdrBaseAt_succ
   ofNat_ne_of_lt ofNat_succ_tie)

/-! ## Setup block (instructions 18--30): spill + array load + call-arg setup

    From the loop-guard fall-through (`D+72`) to just before the `jal` (`D+124`).
    Materializes `*IterPtr := hbi`, `*IterI := iW`, loads `x11 := lengths[i]`,
    `x10 := hbi`, `x12 := 17`, `x13 := Field`. -/

set_option maxRecDepth 8000 in
theorem cvbgmSetup (hbi lenBase spC iW : Word) (Li : Nat)
    (old5 o10 o11 o12 o13 o28 : Word) :
    cpsTripleWithin 13 (D + 72) (D + 124) cvbgmCode
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) **
        (.x13 ↦ᵣ o13) ** (.x28 ↦ᵣ o28) **
        memOwn IterPtr ** memOwn IterI **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ IterI) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
        (.x12 ↦ᵣ (17 : Word)) ** (.x13 ↦ᵣ Field) **
        (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  have hla18 := la_materialize_within .x5 old5 (D + 72) IterPtr (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 72) cvbgmProg 18 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 72) IterPtr)) (by bv_omega) (by rw [cvbgm_length]; decide) (by decide) (by rw [cvbgm_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 76) cvbgmProg 19 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 72) IterPtr)) (by bv_omega) (by rw [cvbgm_length]; decide) (by decide) (by rw [cvbgm_length]; decide))
  have s20 := sd_spec_gen_own_within .x5 .x18 IterPtr hbi (0 : BitVec 12) (D + 80)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPtr + (0 : Word) = IterPtr from by bv_omega] at s20
  have s20' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 80) cvbgmProg 20 (.SD .x5 .x18 (0 : BitVec 12)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s20
  have hla21 := la_materialize_within .x5 IterPtr (D + 84) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 84) cvbgmProg 21 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 84) IterI)) (by bv_omega) (by rw [cvbgm_length]; decide) (by decide) (by rw [cvbgm_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 88) cvbgmProg 22 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 84) IterI)) (by bv_omega) (by rw [cvbgm_length]; decide) (by decide) (by rw [cvbgm_length]; decide))
  have s23 := sd_spec_gen_own_within .x5 .x21 IterI iW (0 : BitVec 12) (D + 92)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s23
  have s23' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 92) cvbgmProg 23 (.SD .x5 .x21 (0 : BitVec 12)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s23
  have s24 := slli_spec_gen_within .x28 .x21 o28 iW (3 : BitVec 6) (D + 96) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s24
  have s24' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 96) cvbgmProg 24 (.SLLI .x28 .x21 (3 : BitVec 6)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s24
  have s25 := add_spec_gen_rd_eq_rs2_within .x28 .x9 lenBase (iW <<< 3) (D + 100) (by decide)
  have s25' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 100) cvbgmProg 25 (.ADD .x28 .x9 .x28) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s25
  have s26 := ld_spec_gen_within .x11 .x28 (lenBase + (iW <<< 3)) o11 (BitVec.ofNat 64 Li)
    (0 : BitVec 12) (D + 104) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iW <<< 3)) + (0 : Word) = lenBase + (iW <<< 3) from by bv_omega] at s26
  have s26' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 104) cvbgmProg 26 (.LD .x11 .x28 (0 : BitVec 12)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s26
  have s27 := mv_spec_gen_within .x10 .x18 hbi o10 (D + 108) (by decide)
  have s27' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 108) cvbgmProg 27 (.MV .x10 .x18) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s27
  have s28 := li_spec_gen_within .x12 o12 (17 : Word) (D + 112) (by decide)
  have s28' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 112) cvbgmProg 28 (.LI .x12 (17 : Word)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s28
  have hla29 := la_materialize_within .x13 o13 (D + 116) Field (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 116) cvbgmProg 29 (.AUIPC .x13 (EvmAsm.Rv64.laHi (D + 116) Field)) (by bv_omega) (by rw [cvbgm_length]; decide) (by decide) (by rw [cvbgm_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 120) cvbgmProg 30 (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (D + 116) Field)) (by bv_omega) (by rw [cvbgm_length]; decide) (by decide) (by rw [cvbgm_length]; decide))
  runBlock hla18 s20' hla21 s23' s24' s25' s26' s27' s28' hla29


/-- AND rd, rs1, rs2 with all three registers distinct: `rd := rs1 &&& rs2`. -/
theorem and_spec_within (rd rs1 rs2 : Reg) (v1 v2 vOld : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.AND rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 &&& v2))) :=
  generic_3reg_spec_within (.AND rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ base hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))

/-! ## Reload block (instructions 33--44): restore iter state + load value + mask

    Runs on the K34-success (`bne` not-taken) path from `D+132` to `D+180`:
    reload `x18 := *IterPtr`, `x21 := *IterI`, `x6 := *Field` (the decoded
    value), set `x7 := Mask = 131071` (`lui x7, 32` = `2^17` then
    `addiw x7, x7, -1`), and `x30 := x6 &&& x7 = value &&& Mask` for the upcoming
    multiple-of-`GAS_PER_BLOB` `bne x30, x0`. -/

set_option maxRecDepth 8000 in
theorem cvbgmReload (hbi iW value : Word) (old5 o18 o21 o6 o7 o30 : Word) :
    cpsTripleWithin 12 (D + 132) (D + 180) cvbgmCode
      ((.x5 ↦ᵣ old5) ** (.x18 ↦ᵣ o18) ** (.x21 ↦ᵣ o21) ** (.x6 ↦ᵣ o6) **
        (.x7 ↦ᵣ o7) ** (.x30 ↦ᵣ o30) ** (.x0 ↦ᵣ (0 : Word)) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (Field ↦ₘ value))
      ((.x5 ↦ᵣ Field) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) ** (.x6 ↦ᵣ value) **
        (.x7 ↦ᵣ Mask) ** (.x30 ↦ᵣ (value &&& Mask)) ** (.x0 ↦ᵣ (0 : Word)) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (Field ↦ₘ value)) := by
  have hla33 := la_materialize_within .x5 old5 (D + 132) IterPtr (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 132) cvbgmProg 33 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 132) IterPtr)) (by bv_omega) (by rw [cvbgm_length]; decide) (by decide) (by rw [cvbgm_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 136) cvbgmProg 34 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 132) IterPtr)) (by bv_omega) (by rw [cvbgm_length]; decide) (by decide) (by rw [cvbgm_length]; decide))
  have s35 := ld_spec_gen_within .x18 .x5 IterPtr o18 hbi (0 : BitVec 12) (D + 140) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPtr + (0 : Word) = IterPtr from by bv_omega] at s35
  have s35' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 140) cvbgmProg 35 (.LD .x18 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s35
  have hla36 := la_materialize_within .x5 IterPtr (D + 144) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 144) cvbgmProg 36 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 144) IterI)) (by bv_omega) (by rw [cvbgm_length]; decide) (by decide) (by rw [cvbgm_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 148) cvbgmProg 37 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 144) IterI)) (by bv_omega) (by rw [cvbgm_length]; decide) (by decide) (by rw [cvbgm_length]; decide))
  have s38 := ld_spec_gen_within .x21 .x5 IterI o21 iW (0 : BitVec 12) (D + 152) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s38
  have s38' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 152) cvbgmProg 38 (.LD .x21 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s38
  have hla39 := la_materialize_within .x5 IterI (D + 156) Field (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 156) cvbgmProg 39 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 156) Field)) (by bv_omega) (by rw [cvbgm_length]; decide) (by decide) (by rw [cvbgm_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 160) cvbgmProg 40 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 156) Field)) (by bv_omega) (by rw [cvbgm_length]; decide) (by decide) (by rw [cvbgm_length]; decide))
  have s41 := ld_spec_gen_within .x6 .x5 Field o6 value (0 : BitVec 12) (D + 164) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show Field + (0 : Word) = Field from by bv_omega] at s41
  have s41' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 164) cvbgmProg 41 (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s41
  have s42 := lui_spec_gen_within .x7 o7 (32 : BitVec 20) (D + 168) (by decide)
  have s42' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 168) cvbgmProg 42 (.LUI .x7 (32 : BitVec 20)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s42
  have s43 := addiw_spec_gen_same_within .x7
    ((((32 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)
    (-1 : BitVec 12) (D + 172) (by decide)
  rw [show ((((((32 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64).truncate 32
        + (signExtend12 (-1 : BitVec 12)).truncate 32 : BitVec 32).signExtend 64)
      = Mask from by decide] at s43
  have s43' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 172) cvbgmProg 43 (.ADDIW .x7 .x7 (-1 : BitVec 12)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s43
  have s44 := and_spec_within .x30 .x6 .x7 value Mask o30 (D + 176) (by decide)
  have s44' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 176) cvbgmProg 44 (.AND .x30 .x6 .x7) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s44
  runBlock hla33 s35' hla36 s38' hla39 s41' s42' s43' s44'


/-! ## Advance block (instructions 46--51): step the iterator, loop back

    On the multiple (`bne x30, x0` not-taken) path from `D+184`:
    `x18 += lengths[i]`, `x21 += 1`, then `jal x0, -136` back to the loop guard
    at `D+68`. -/

set_option maxRecDepth 8000 in
theorem cvbgmAdvance (hbi lenBase iW : Word) (Li : Nat) (o28 o29 : Word) :
    cpsTripleWithin 6 (D + 184) (D + 68) cvbgmCode
      ((.x21 ↦ᵣ iW) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x28 ↦ᵣ o28) **
        (.x29 ↦ᵣ o29) ** ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x21 ↦ᵣ (iW + signExtend12 (1 : BitVec 12))) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ (hbi + BitVec.ofNat 64 Li)) ** (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
        (.x29 ↦ᵣ BitVec.ofNat 64 Li) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  have s46 := slli_spec_gen_within .x28 .x21 o28 iW (3 : BitVec 6) (D + 184) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s46
  have s46' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 184) cvbgmProg 46 (.SLLI .x28 .x21 (3 : BitVec 6)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s46
  have s47 := add_spec_gen_rd_eq_rs2_within .x28 .x9 lenBase (iW <<< 3) (D + 188) (by decide)
  have s47' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 188) cvbgmProg 47 (.ADD .x28 .x9 .x28) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s47
  have s48 := ld_spec_gen_within .x29 .x28 (lenBase + (iW <<< 3)) o29 (BitVec.ofNat 64 Li)
    (0 : BitVec 12) (D + 192) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iW <<< 3)) + (0 : Word) = lenBase + (iW <<< 3) from by bv_omega] at s48
  have s48' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 192) cvbgmProg 48 (.LD .x29 .x28 (0 : BitVec 12)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s48
  have s49 := add_spec_gen_rd_eq_rs1_within .x18 .x29 hbi (BitVec.ofNat 64 Li) (D + 196) (by decide)
  have s49' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 196) cvbgmProg 49 (.ADD .x18 .x18 .x29) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s49
  have s50 := addi_spec_gen_same_within .x21 iW (1 : BitVec 12) (D + 200) (by decide)
  have s50' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 200) cvbgmProg 50 (.ADDI .x21 .x21 (1 : BitVec 12)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s50
  have s51 := jal_x0_spec_gen_within (-136 : BitVec 21) (D + 204)
  rw [show (D + 204) + signExtend21 (-136 : BitVec 21) = D + 68 from by
    rw [show signExtend21 (-136 : BitVec 21) = (-136 : Word) from by decide]; bv_omega] at s51
  have s51' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 204) cvbgmProg 51 (.JAL .x0 (-136 : BitVec 21)) (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) s51
  runBlock s46' s47' s48' s49' s50' s51'


/-! ## Arithmetic helper for the value comparison. -/

theorem lengths_getElem_bang {lengths : List Nat} {i : Nat} (hi : i < lengths.length) :
    lengths[i]! = lengths[i] := getElem!_pos lengths i hi

/-! ## Call block (instructions 18--31 + K34): setup ;; jal ;; rlp_field_to_u64

    From the loop-guard fall-through (`D+72`) to the return site (`D+128`),
    producing K34's `flatPost` for header `hbi` (field 17), with the spill
    cells, the array cell, and the chain frame carried through unchanged. -/

/-- K34's whole-routine step count for field index 17 (matching the flat
    spec's `((7 + 4 + callSteps) + ((1 + tailSteps) + 5))` with `index = 17`). -/
def nCall (bytesLen : Nat) : Nat :=
  (7 + 4 + (1 + ((12 + ((85 + 93 * (17 + 2)) + 6)) + 9)))
    + ((1 + ((7 + (1 + (7 * bytesLen + 11))) + 5)) + 5)

set_option maxRecDepth 8000 in
theorem cvbgmCall (hbi lenBase spC iW : Word) (Li : Nat)
    (nN s3 s4 oldOut oldOff oldLen old14 oldX1 old5 o10 o11 o12 o13 o28 : Word)
    (bytes : List (BitVec 8)) (csaved : Saved)
    (hsalign : hbi.toNat % 8 = 0)
    (hslack : Li + 9 ≤ bytes.length)
    (hover : hbi.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (hbi + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (13 + 1 + nCall bytes.length) (D + 72) (D + 128) fullCode
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) **
        (.x13 ↦ᵣ o13) ** (.x28 ↦ᵣ o28) **
        memOwn IterPtr ** memOwn IterI **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
        (.x1 ↦ᵣ oldX1) ** (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
        (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        bytesRegion hbi bytes ** savedFrame spC csaved)
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Field, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 17 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) := by
  set calleeNewSp : Word := spC + signExtend12 (-32 : BitVec 12) with hcalleeNewSp
  -- Setup block, lifted to fullCode, framed with the callee footprint.
  have hsetup := cpsTripleWithin_extend_code cvbgm_mono
    (cvbgmSetup hbi lenBase spC iW Li old5 o10 o11 o12 o13 o28)
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ oldX1) ** (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
      (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hbi bytes ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
                      | exact bytesRegion_pcFree _ _) hsetup
  -- [31] jal x1, rlp_field_to_u64
  have hjal := jal_link_spec_within
    (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64
      (GuestAddrs.chain_validate_blob_gas_used_multiple + 124)) (D + 124) oldX1
  rw [show (D + 124) + signExtend21 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64
      (GuestAddrs.chain_validate_blob_gas_used_multiple + 124))
      = EvmAsm.Codegen.RlpFieldToU64SAsm.B from by decide,
    show (D + 124 + 4 : Word) = LinkRA from by
      change (D + 124 + 4 : Word) = D + 128; bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code cvbgm_mono
    (cpsTripleWithin_extend_code (cr' := cvbgmCode)
      (CodeReq.ofProg_mem_at D (D + 124) cvbgmProg 31
        (.JAL .x1 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64
          (GuestAddrs.chain_validate_blob_gas_used_multiple + 124))) (by bv_omega)
        (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
      (.x5 ↦ᵣ IterI) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
      (.x12 ↦ᵣ (17 : Word)) ** (.x13 ↦ᵣ Field) **
      (.x28 ↦ᵣ (lenBase + (iW <<< 3))) ** (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
      ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
      (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x14 ↦ᵣ old14) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hbi bytes ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
                      | exact bytesRegion_pcFree _ _) hjalC
  -- K34 flat callee, lifted to fullCode, framed with the spill/array/chain payload.
  have hcallee0 := EvmAsm.Codegen.RlpFieldToU64SAsm.rlpFieldToU64_flat_spec_within
    spC calleeNewSp hbi (BitVec.ofNat 64 Li) (17 : Word) Field oldOut oldOff oldLen old14
    (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved) hbi s3 s4 iW bytes Li 17
    hcalleeNewSp rfl (by decide) (by decide)
    hsalign hslack hover hvalid (by show LinkRA &&& ~~~(1 : Word) = LinkRA; decide)
  have hcalleeC := cpsTripleWithin_extend_code k34_mono hcallee0
  -- Present K34's entry footprint as explicit atoms, with `x5`/`x28` shown owned.
  have hcallee : cpsTripleWithin (nCall bytes.length) EvmAsm.Codegen.RlpFieldToU64SAsm.B LinkRA fullCode
      (regOwn .x5 ** regOwn .x28 **
        ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
          (.x18 ↦ᵣ hbi) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ iW) **
          (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (17 : Word)) **
          (.x13 ↦ᵣ Field) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
          stackFree calleeNewSp 8 ** bytesRegion hbi bytes **
          (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen)))
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC calleeNewSp hbi oldOff oldLen
          (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Field, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 17) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold EvmAsm.Codegen.RlpFieldToU64SAsm.flatPre EvmAsm.Codegen.RlpFieldToU64SAsm.wholeRest
      xperm_hyp hp) (fun _ hq => hq) hcalleeC
  have hcalleeF := cpsTripleWithin_frameR
    ((IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
      ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_memIs) hcallee
  -- Compose setup ;; jal ;; callee (weakening `x5`/`x28` to owned at the midpoint).
  have hsj := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupF hjalF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => ?_) hsj hcalleeF)
  have hp' : ((.x5 ↦ᵣ IterI) ** (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
      ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hbi) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ iW) **
        (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (17 : Word)) **
        (.x13 ↦ᵣ Field) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
        stackFree calleeNewSp 8 ** bytesRegion hbi bytes **
        (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)) h := by
    xperm_hyp hp
  have hp'' := sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x)) h hp'
  xperm_hyp hp''


/-! ## Call block with the consumed scratch registers owned

    `cvbgmCall` with `x1/x5/x10/x11/x12/x13/x14/x28` presented as `regOwn`,
    matching how they sit in `LoopInv`. -/

set_option maxRecDepth 8000 in
theorem cvbgmCallOwned (hbi lenBase spC iW : Word) (Li : Nat)
    (nN s3 s4 oldOut oldOff oldLen : Word) (bytes : List (BitVec 8)) (csaved : Saved)
    (hsalign : hbi.toNat % 8 = 0)
    (hslack : Li + 9 ≤ bytes.length)
    (hover : hbi.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (hbi + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (13 + 1 + nCall bytes.length) (D + 72) (D + 128) fullCode
      ((((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
          memOwn IterPtr ** memOwn IterI **
          ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
          (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
          bytesRegion hbi bytes ** savedFrame spC csaved) **
        regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28) ** regOwn .x1)
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Field, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 17 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v1 => ?_)
  refine cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => h)
    (show cpsTripleWithin (13 + 1 + nCall bytes.length) (D + 72) (D + 128) fullCode
      ((((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
          memOwn IterPtr ** memOwn IterI **
          ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
          (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
          bytesRegion hbi bytes ** savedFrame spC csaved) ** (.x1 ↦ᵣ v1)) **
        regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28)
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Field, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 17 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) from ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_of_forall_regIs_to_regOwn7
    (fun v5 v10 v11 v12 v13 v14 v28 => ?_)
  exact cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => by xperm_hyp h)
    (cvbgmCall hbi lenBase spC iW Li nN s3 s4 oldOut oldOff oldLen v14 v1 v5 v10 v11 v12 v13 v28
      bytes csaved hsalign hslack hover hvalid)


/-! ## Entry half of one iteration: guard → call → K34 flatPost

    From the loop guard (`D+68`, `i < N`) through the `jal` to K34's return
    (`D+128`), with the header slice handed to K34 and the untouched
    `wordArray`/`bytesRegion` prefixes framed. -/

set_option maxRecDepth 8000 in
theorem cvbgmIterEntry (spC hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) (i : Nat)
    (oldOut oldOff oldLen : Word)
    (hi : i < lengths.length)
    (hN : lengths.length < 2 ^ 64)
    (hsalign : (hdrBaseAt hdrBase lengths i).toNat % 8 = 0)
    (hslack : lengths[i]! + 9 ≤ (bigBytes.drop (hdrOff lengths i)).length)
    (hover : (hdrBaseAt hdrBase lengths i).toNat +
      (bigBytes.drop (hdrOff lengths i)).length < 2 ^ 64)
    (hvalid : ∀ k, k < (bigBytes.drop (hdrOff lengths i)).length →
      isValidByteAccess (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + (13 + 1 + nCall (bigBytes.drop (hdrOff lengths i)).length)) (D + 68) (D + 128) fullCode
      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
        (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** savedFrame spC csaved **
        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
        (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        memOwn IterPtr ** memOwn IterI **
        regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12))
          (hdrBaseAt hdrBase lengths i) oldOff oldLen
          (⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ :
            EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hdrBaseAt hdrBase lengths i, Field,
            hdrBaseAt hdrBase lengths i, validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ : Saved)
          (bigBytes.drop (hdrOff lengths i)) lengths[i]! 17 **
        (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        savedFrame spC csaved) := by
  -- [17] BEQ x21 x8 : i ≠ N ⇒ not taken → D+72.
  have hbeq := beq_spec_gen_within .x21 .x8 (164 : BitVec 13) (BitVec.ofNat 64 i)
    (BitVec.ofNat 64 lengths.length) (D + 68)
  have hbeqC := cpsBranchWithin_extend_code cvbgm_mono
    (cpsBranchWithin_extend_code (cr' := cvbgmCode)
      (CodeReq.ofProg_mem_at D (D + 68) cvbgmProg 17 (.BEQ .x21 .x8 (164 : BitVec 13))
        (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) hbeq)
  have hguard0 := cpsBranchWithin_ntakenStripPure2 hbeqC (fun hp hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact ofNat_ne_of_lt i lengths.length hi hN ((sepConj_pure_right _).1 hrest).2)
  rw [show (D + 68 + 4 : Word) = D + 72 from by bv_omega] at hguard0
  -- Frame the guard with the untouched loop-invariant state (everything but x21/x8).
  have hguardF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) **
      (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** savedFrame spC csaved **
      (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
      wordArrayFrom lenBase 0 (lengths.take i) **
      ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
      bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
      (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      memOwn IterPtr ** memOwn IterI **
      regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
      stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
                      | exact bytesRegion_pcFree _ _
                      | exact pcFree_wordArrayFrom _ _ _) hguard0
  -- The call, framed with the untouched wordArray/bytesRegion prefixes.
  have hcall := cvbgmCallOwned (hdrBaseAt hdrBase lengths i) lenBase spC (BitVec.ofNat 64 i)
    lengths[i]! (BitVec.ofNat 64 lengths.length) validPtr firstBadPtr oldOut oldOff oldLen
    (bigBytes.drop (hdrOff lengths i)) csaved hsalign hslack hover hvalid
  have hcallF := cpsTripleWithin_frameR
    (wordArrayFrom lenBase 0 (lengths.take i) **
      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
      (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)))
    (by repeat' first | apply pcFree_sepConj | exact pcFree_wordArrayFrom _ _ _
                      | exact bytesRegion_pcFree _ _ | exact pcFree_memIs) hcall
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
      rw [show (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) from shiftLeft3_ofNat i] at hq
      xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      rw [show (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) from shiftLeft3_ofNat i]
      xperm_hyp hp) hguardF hcallF)


/-! ## Normalizing K34's `flatPost` into a single Result-carrying assertion

    Both arms of `flatPost` (success with `wrapperStatus ∈ {0,2}`, failure with
    status 1) carry the semantic `⌜Result …⌝` and a register/memory footprint
    that weakens to a common owned shape.  `dispNorm status value` is that shape;
    it exposes `x10 = status` (for the `bne`) and `Field ↦ value` (for the
    reload) while owning the callee-perturbed remainder. -/
def dispNorm (spC calleeNewSp hbi validPtr firstBadPtr nN lenBase iW value status : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
  (.x18 ↦ᵣ hbi) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iW) **
  (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (Field ↦ₘ value) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  memOwn RfuOff ** memOwn RfuLen ** stackFree calleeNewSp 8 **
  bytesRegion hbi bytes **
  EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame calleeNewSp ⟨LinkRA, nN, lenBase⟩

set_option maxRecDepth 8000 in
theorem flatPost_normalize (spC hbi validPtr firstBadPtr nN lenBase iW oldOff oldLen : Word)
    (bytes : List (BitVec 8)) (Li : Nat) : ∀ h,
    (EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
      oldOff oldLen (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
      (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Field, hbi, validPtr, firstBadPtr, iW⟩ : Saved)
      bytes Li 17) h →
    (∃ status value,
      (dispNorm spC (spC + signExtend12 (-32 : BitVec 12)) hbi validPtr firstBadPtr nN lenBase iW
          value status bytes **
        ⌜EvmAsm.Codegen.RlpFieldToU64SAsm.Result bytes hbi Li 17 status value⌝) h) := by
  intro h hp
  unfold EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost at hp
  rcases hp with hs | hf
  · -- success arm: status = wrapperStatus, value = outputValue.
    unfold EvmAsm.Codegen.RlpFieldToU64SAsm.flatSuccessReturned at hs
    obtain ⟨offset, len, v12, x5v, scalarStatus, wrapperStatus, outputValue, hs⟩ := hs
    unfold EvmAsm.Codegen.RlpFieldToU64SAsm.successPayload at hs
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
          (.x10 ↦ᵣ wrapperStatus) ** (.x0 ↦ᵣ (0 : Word)) ** (Field ↦ₘ outputValue) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 ** bytesRegion hbi bytes **
          EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
            ⟨LinkRA, nN, lenBase⟩)) h := by xperm_hyp hOB
    have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
      (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12) (fun _ x => x))))) h hp1
    xperm_hyp hp2
  · -- failure arm: status = 1, value = 0.
    unfold EvmAsm.Codegen.RlpFieldToU64SAsm.flatFailureReturned at hf
    obtain ⟨v11, v12, hf⟩ := hf
    unfold EvmAsm.Codegen.RlpFieldToU64SAsm.failurePayload at hf
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
          (.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (Field ↦ₘ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 ** bytesRegion hbi bytes **
          EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
            ⟨LinkRA, nN, lenBase⟩)) h := by xperm_hyp hOB
    have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
      (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x12)
        (fun _ x => x)))) h hp1
    xperm_hyp hp2


/-- K34's 3-slot saved frame, once restored, weakens to the merely-owned frame
    slots the loop invariant carries. -/
theorem k34SavedFrame_implies_frameSlotsOwn (newSp : Word)
    (saved : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved) : ∀ h,
    EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame newSp saved h →
    frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame newSp h := by
  intro h hp
  rw [← EvmAsm.Codegen.RlpFieldToU64SAsm.frameSlotsSaved_frame] at hp
  exact EvmAsm.Codegen.ChainValidateExtraDataLengthSpec.frameSlotsSaved_implies_frameSlotsOwn
    EvmAsm.Codegen.RlpFieldToU64SAsm.frame newSp
    (EvmAsm.Codegen.RlpFieldToU64SAsm.savedVals saved) h hp

/-- pcFree discharger covering the assertion atoms used in the dispatch. -/
local macro "pcfx" : tactic =>
  `(tactic| repeat' first
      | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs | exact pcFree_memOwn | exact pcFree_emp | exact pcFree_pure
      | exact bytesRegion_pcFree _ _ | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_wordArrayFrom _ _ _ | unfold savedFrame
      | unfold EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame)

/-! ## Status dispatch (instruction 32 onward): tie K34's `Result` to the post

    From K34's `flatPost` at the `bne` return site (`D+128`) to the caller's
    post.  `flatPost_normalize` collapses the callee return into one
    `Result`-carrying shape; `bne x10, x0` splits on the status, and on success
    the value compare (`bltu 2752512, value`) routes to violation or
    continue+loop. -/

set_option maxRecDepth 8000 in
theorem cvbgmIterDispatch
    (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr raIn : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) (i : Nat)
    (oldOff oldLen : Word) (nTail : Nat)
    (hi : i < lengths.length)
    (_hN : lengths.length < 2 ^ 64)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hcns : calleeNewSp = spC + signExtend12 (-32 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (halign : hdrOff lengths i % 8 = 0)
    (hlen : hdrOff lengths i ≤ bigBytes.length)
    (hprefix : ∀ j, j < i → hdrMultiple hdrBase bigBytes lengths j)
    (htail : (∀ j, j < i + 1 → hdrMultiple hdrBase bigBytes lengths j) →
      cpsTripleWithin nTail (D + 68) raIn fullCode
        (LoopInv sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
          bigBytes lengths (i + 1))
        (cvbgmPost sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
          bigBytes lengths)) :
    cpsTripleWithin (27 + nTail) (D + 128) raIn fullCode
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12))
          (hdrBaseAt hdrBase lengths i) oldOff oldLen
          (⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ :
            EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hdrBaseAt hdrBase lengths i, Field,
            hdrBaseAt hdrBase lengths i, validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ : Saved)
          (bigBytes.drop (hdrOff lengths i)) lengths[i]! 17 **
        (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        savedFrame spC csaved)
      (cvbgmPost sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
        bigBytes lengths) := by
  subst hcns
  have hLi : lengths[i]! = lengths[i] := getElem!_pos lengths i hi
  have hHB : hdrBaseAt hdrBase lengths i = hdrBase + BitVec.ofNat 64 (hdrOff lengths i) := rfl
  have hsf : savedFrame spC csaved =
      ((spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) := by
    unfold savedFrame; rw [hraSaved]
  -- Normalize K34's flatPost, stripping the (status, value) existentials.
  refine cpsTripleWithin_weaken (fun h hp => ?hstrip) (fun _ hq => hq)
    (EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun status =>
      EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun value =>
        (show cpsTripleWithin (27 + nTail) (D + 128) raIn fullCode
          ((.x1 ↦ᵣ LinkRA) **
            (dispNorm spC (spC + signExtend12 (-32 : BitVec 12)) (hdrBaseAt hdrBase lengths i)
                validPtr firstBadPtr (BitVec.ofNat 64 lengths.length) lenBase (BitVec.ofNat 64 i)
                value status (bigBytes.drop (hdrOff lengths i)) **
              ⌜EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
                (hdrBaseAt hdrBase lengths i) lengths[i]! 17 status value⌝) **
            ((IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              savedFrame spC csaved))
          (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
            firstBadPtr csaved bigBytes lengths) from ?core))))
  case hstrip =>
    obtain ⟨s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hfp, hREST⟩ := hp
    obtain ⟨status, value, hnorm⟩ := flatPost_normalize spC (hdrBaseAt hdrBase lengths i)
      validPtr firstBadPtr (BitVec.ofNat 64 lengths.length) lenBase (BitVec.ofNat 64 i)
      oldOff oldLen (bigBytes.drop (hdrOff lengths i)) lengths[i]! s3 hfp
    exact ⟨status, value, s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hnorm, hREST⟩
  case core =>
    -- Pull the semantic `Result` out of the precondition.
    refine cpsTripleWithin_weaken (fun h hp => ?hpull) (fun _ hq => hq)
      (cpsTripleWithin_pure_pre
        (P := EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
          (hdrBaseAt hdrBase lengths i) lengths[i]! 17 status value)
        (H := (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
          (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
          (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (.x10 ↦ᵣ status) **
          (.x0 ↦ᵣ (0 : Word)) ** (Field ↦ₘ value) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
          EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
            ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
          (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
          ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
          wordArrayFrom lenBase 0 (lengths.take i) **
          wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
          bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
          (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
          savedFrame spC csaved)
        (fun hResult => ?body))
    case hpull =>
      unfold dispNorm at hp
      xperm_hyp hp
    case body =>
      rw [hsf]
      by_cases hstatus : status = 0
      · -- SUCCESS arm: `bne` not taken → reload → value compare.
        subst hstatus
        set RframeOk : Assertion :=
          ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (Field ↦ₘ value) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
            ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
            wordArrayFrom lenBase 0 (lengths.take i) **
            wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
            bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
            (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
            ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
            ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) with hRframeOk
        have hbne := bne_spec_gen_within .x10 .x0 (96 : BitVec 13) (0 : Word) (0 : Word)
          (D + 128)
        have hbneC := cpsBranchWithin_extend_code cvbgm_mono
          (cpsBranchWithin_extend_code (cr' := cvbgmCode)
            (CodeReq.ofProg_mem_at D (D + 128) cvbgmProg 32 (.BNE .x10 .x0 (96 : BitVec 13))
              (by bv_omega) (by rw [cvbgm_length]; decide) rfl
              (by rw [cvbgm_length]; decide)) hbne)
        have hntaken := cpsBranchWithin_ntakenStripPure2 hbneC (fun hp hq => by
          obtain ⟨_, _, _, _, _, hrest⟩ := hq
          exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
        rw [show (D + 128 + 4 : Word) = D + 132 from by bv_omega] at hntaken
        have hcont : cpsTripleWithin (26 + nTail) (D + 132) raIn fullCode
            (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** RframeOk)
            (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
              validPtr firstBadPtr csaved bigBytes lengths) := by
          rw [hRframeOk]
          refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
            (show cpsTripleWithin (26 + nTail) (D + 132) raIn fullCode
              (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA) **
                (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
                (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
                (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (Field ↦ₘ value) **
                regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
                memOwn RfuOff ** memOwn RfuLen **
                stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                  ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                wordArrayFrom lenBase 0 (lengths.take i) **
                wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) **
                regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
                regOwn .x30 ** regOwn .x31)
              (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
                validPtr firstBadPtr csaved bigBytes lengths) from ?_)
          refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_of_forall_regIs_to_regOwn7
            (fun v5 v6 v7 v28 v29 v30 v31 => ?_)
          set Rreload : Assertion :=
            ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) ** (.x19 ↦ᵣ validPtr) **
              (.x20 ↦ᵣ firstBadPtr) ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
              regOwn .x14 ** memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
              ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
              ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
              (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x31 ↦ᵣ v31)) with hRreload
          set Rstate2 : Assertion :=
            ((.x5 ↦ᵣ Field) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) **
              (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (.x6 ↦ᵣ value) ** (.x7 ↦ᵣ Mask) **
              (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) **
              (IterI ↦ₘ BitVec.ofNat 64 i) ** (Field ↦ₘ value)) ** Rreload with hRstate2
          have hreload := cpsTripleWithin_extend_code cvbgm_mono
            (cvbgmReload (hdrBaseAt hdrBase lengths i) (BitVec.ofNat 64 i) value v5
              (hdrBaseAt hdrBase lengths i) (BitVec.ofNat 64 i) v6 v7 v30)
          have hreloadF := cpsTripleWithin_frameR Rreload (by rw [hRreload]; pcfx) hreload
          have hbne2 := bne_spec_gen_within .x30 .x0 (28 : BitVec 13) (value &&& Mask)
            (0 : Word) (D + 180)
          rw [show (D + 180) + signExtend13 (28 : BitVec 13) = D + 208 from by
            rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega] at hbne2
          have hbne2C := cpsBranchWithin_extend_code cvbgm_mono
            (cpsBranchWithin_extend_code (cr' := cvbgmCode)
              (CodeReq.ofProg_mem_at D (D + 180) cvbgmProg 45 (.BNE .x30 .x0 (28 : BitVec 13))
                (by bv_omega) (by rw [cvbgm_length]; decide) rfl
                (by rw [cvbgm_length]; decide)) hbne2)
          have hbne2F := cpsBranchWithin_frameR Rstate2 (by rw [hRstate2, hRreload]; pcfx) hbne2C
          have hbranch := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
            (fun h hp => by rw [hRstate2]; xperm_hyp hp) hreloadF hbne2F
          have h_t : cpsTripleWithin (13 + nTail) (D + 208) raIn fullCode
              (((.x30 ↦ᵣ (value &&& Mask)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(value &&& Mask) ≠ 0⌝) ** Rstate2)
              (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
                validPtr firstBadPtr csaved bigBytes lengths) := by
            rw [hRstate2, hRreload]
            refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
              (cpsTripleWithin_pure_pre (P := (value &&& Mask) ≠ 0)
                (H := (.x30 ↦ᵣ (value &&& Mask)) ** (.x0 ↦ᵣ (0 : Word)) **
                  (.x6 ↦ᵣ value) ** (.x7 ↦ᵣ Mask) ** (.x5 ↦ᵣ Field) **
                  (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  (Field ↦ₘ value) ** (.x10 ↦ᵣ (0 : Word)) **
                  (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                  (.x9 ↦ᵣ lenBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
                  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
                  memOwn RfuOff ** memOwn RfuLen **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                    ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                  ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                  ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x31 ↦ᵣ v31))
                (fun hult => ?_))
            have hviol := cpsTripleWithin_extend_code cvbgm_mono
              (retViolation sp0 spC raIn (BitVec.ofNat 64 i) validPtr firstBadPtr csaved
                ((.x7 ↦ᵣ Mask) ** (.x6 ↦ᵣ value) ** (.x5 ↦ᵣ Field) **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  (Field ↦ₘ value) ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
                  memOwn RfuOff ** memOwn RfuLen **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                    ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ (value &&& Mask)) ** (.x31 ↦ᵣ v31))
                (by pcfx) (0 : Word) LinkRA (BitVec.ofNat 64 lengths.length) lenBase
                (hdrBaseAt hdrBase lengths i) hspC hraSaved hret)
            refine cpsTripleWithin_weaken (fun h hp => by
              have hp1 : ((validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                  ((.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
                    (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
                    (.x1 ↦ᵣ LinkRA) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                    (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) **
                    (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                    ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                    ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                    ((.x7 ↦ᵣ Mask) ** (.x6 ↦ᵣ value) ** (.x5 ↦ᵣ Field) **
                      (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                      (Field ↦ₘ value) ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
                      regOwn .x14 ** memOwn RfuOff ** memOwn RfuLen **
                      stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                      bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                      EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame
                        (spC + signExtend12 (-32 : BitVec 12))
                        ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                      ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                      wordArrayFrom lenBase 0 (lengths.take i) **
                      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ (value &&& Mask)) ** (.x31 ↦ᵣ v31)))) h := by
                xperm_hyp hp
              have hp2 := sepConj_mono memIs_implies_memOwn
                (sepConj_mono memIs_implies_memOwn (fun _ x => x)) h hp1
              xperm_hyp hp2) (fun h hq => ?_)
              (cpsTripleWithin_mono_nSteps (show 13 ≤ 13 + nTail by omega) hviol)
            refine Or.inr (Or.inl ⟨i, ?_⟩)
            refine (sepConj_pure_left h).mpr ⟨⟨hi, hprefix, ⟨value, hResult, hult⟩⟩, ?_⟩
            unfold commonRet payload
            rw [hsf, hraSaved, wordArray_split lenBase lengths i hi,
              EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen, ← hHB]
            have hp1 : ((.x5 ↦ᵣ Field) ** (.x6 ↦ᵣ value) ** (.x7 ↦ᵣ Mask) **
                (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ (value &&& Mask)) ** (.x31 ↦ᵣ v31) **
                (Field ↦ₘ value) ** (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) **
                (IterI ↦ₘ BitVec.ofNat 64 i) **
                EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                  ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
                  (firstBadPtr ↦ₘ BitVec.ofNat 64 i) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
                  (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) ** (.x18 ↦ᵣ csaved.s2) **
                  (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
                  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                  ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                  ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                  (.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
                  regOwn .x14 ** memOwn RfuOff ** memOwn RfuLen **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)))) h := by
              rw [← hLi]; xperm_hyp hq
            have hp2 := sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono
              (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x7)
              (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x29)
              (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (regIs_implies_regOwn .x31)
              (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn
              (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _)
              (fun _ x => x))))))))))) h hp1
            xperm_hyp hp2
          have h_f : cpsTripleWithin (13 + nTail) (D + 184) raIn fullCode
              (((.x30 ↦ᵣ (value &&& Mask)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(value &&& Mask) = 0⌝) ** Rstate2)
              (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
                validPtr firstBadPtr csaved bigBytes lengths) := by
            rw [hRstate2, hRreload]
            refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
              (cpsTripleWithin_pure_pre (P := (value &&& Mask) = 0)
                (H := (.x30 ↦ᵣ (value &&& Mask)) ** (.x0 ↦ᵣ (0 : Word)) **
                  (.x6 ↦ᵣ value) ** (.x7 ↦ᵣ Mask) ** (.x5 ↦ᵣ Field) **
                  (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  (Field ↦ₘ value) ** (.x10 ↦ᵣ (0 : Word)) **
                  (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                  (.x9 ↦ᵣ lenBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
                  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
                  memOwn RfuOff ** memOwn RfuLen **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                    ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                  ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                  ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x31 ↦ᵣ v31))
                (fun hnult => ?_))
            have hprefix' : ∀ j, j < i + 1 → hdrMultiple hdrBase bigBytes lengths j := by
              intro j hj
              rcases (by omega : j < i ∨ j = i) with hlt | heq
              · exact hprefix j hlt
              · subst heq; exact ⟨value, hResult, hnult⟩
            have hadv := cpsTripleWithin_extend_code cvbgm_mono
              (cvbgmAdvance (hdrBaseAt hdrBase lengths i) lenBase (BitVec.ofNat 64 i)
                lengths[i]! v28 v29)
            rw [shiftLeft3_ofNat i] at hadv
            have hadvF := cpsTripleWithin_frameR
              ((.x7 ↦ᵣ Mask) ** (.x6 ↦ᵣ value) ** (.x5 ↦ᵣ Field) **
                (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                (Field ↦ₘ value) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** regOwn .x11 ** regOwn .x12 **
                regOwn .x13 ** regOwn .x14 ** memOwn RfuOff ** memOwn RfuLen **
                stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                  ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                wordArrayFrom lenBase 0 (lengths.take i) **
                wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                (.x30 ↦ᵣ (value &&& Mask)) ** (.x31 ↦ᵣ v31)) (by pcfx) hadv
            refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
              (cpsTripleWithin_mono_nSteps (show 6 + nTail ≤ 13 + nTail by omega)
                (cpsTripleWithin_seq_perm_same_cr (fun h hp => by
                  unfold LoopInv payload scratchRegs
                  rw [hsf, wordArray_split lenBase lengths i hi,
                    EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen,
                    ← hHB, hdrBaseAt_succ hdrBase lengths i hi, ← ofNat_succ_tie i, ← hLi]
                  have hp1 : ((.x1 ↦ᵣ LinkRA) ** (.x5 ↦ᵣ Field) ** (.x6 ↦ᵣ value) **
                      (.x7 ↦ᵣ Mask) ** (.x10 ↦ᵣ (0 : Word)) **
                      (.x28 ↦ᵣ (lenBase + BitVec.ofNat 64 (8 * i))) **
                      (.x29 ↦ᵣ BitVec.ofNat 64 lengths[i]!) ** (.x30 ↦ᵣ (value &&& Mask)) ** (.x31 ↦ᵣ v31) **
                      (Field ↦ₘ value) ** (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) **
                      (IterI ↦ₘ BitVec.ofNat 64 i) **
                      EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame
                        (spC + signExtend12 (-32 : BitVec 12))
                        ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                        (.x9 ↦ᵣ lenBase) **
                        (.x18 ↦ᵣ (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 lengths[i]!)) **
                        (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
                        (.x21 ↦ᵣ (BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12))) **
                        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
                        (.x0 ↦ᵣ (0 : Word)) ** memOwn RfuOff ** memOwn RfuLen **
                        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                        wordArrayFrom lenBase 0 (lengths.take i) **
                        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                        bytesRegion (hdrBaseAt hdrBase lengths i)
                          (bigBytes.drop (hdrOff lengths i)))) h := by
                    xperm_hyp hp
                  have hp2 := sepConj_mono (regIs_implies_regOwn .x1) (sepConj_mono
                    (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
                    (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x10)
                    (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x29)
                    (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (regIs_implies_regOwn .x31)
                    (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
                    (sepConj_mono memIs_implies_memOwn
                    (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _)
                    (fun _ x => x))))))))))))) h hp1
                  xperm_hyp hp2) hadvF (htail hprefix')))
          refine cpsTripleWithin_weaken (fun h hp => by rw [hRreload]; xperm_hyp hp)
            (fun _ hq => hq)
            (cpsTripleWithin_mono_nSteps (show 12 + 1 + (13 + nTail) ≤ 26 + nTail by omega)
              (cpsBranchWithin_merge_same_cr hbranch h_t h_f))
        have hntakenF := cpsTripleWithin_frameR RframeOk (by rw [hRframeOk]; pcfx) hntaken
        refine cpsTripleWithin_weaken (fun h hp => by rw [hRframeOk]; xperm_hyp hp)
          (fun _ hq => hq)
          (cpsTripleWithin_mono_nSteps (show 1 + (26 + nTail) ≤ 27 + nTail by omega)
            (cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hntakenF hcont))
      · -- PARSE-FAIL arm: `bne` taken → status ≠ 0 exit.
        have hbne := bne_spec_gen_within .x10 .x0 (96 : BitVec 13) status (0 : Word) (D + 128)
        have hbneC := cpsBranchWithin_extend_code cvbgm_mono
          (cpsBranchWithin_extend_code (cr' := cvbgmCode)
            (CodeReq.ofProg_mem_at D (D + 128) cvbgmProg 32 (.BNE .x10 .x0 (96 : BitVec 13))
              (by bv_omega) (by rw [cvbgm_length]; decide) rfl
              (by rw [cvbgm_length]; decide)) hbne)
        have htaken := cpsBranchWithin_takenStripPure2 hbneC (fun hp hq => by
          obtain ⟨_, _, _, _, _, hrest⟩ := hq
          exact absurd ((sepConj_pure_right _).1 hrest).2 hstatus)
        rw [show (D + 128) + signExtend13 (96 : BitVec 13) = D + 224 from by
          rw [show signExtend13 (96 : BitVec 13) = (96 : Word) from by decide]; bv_omega] at htaken
        have htakenF := cpsTripleWithin_frameR
          ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (Field ↦ₘ value) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
            ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
            wordArrayFrom lenBase 0 (lengths.take i) **
            wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
            bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
            (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
            ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
            ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) (by pcfx) htaken
        have hpfC := cpsTripleWithin_extend_code cvbgm_mono
          (retParseFail sp0 spC raIn (BitVec.ofNat 64 i) firstBadPtr csaved
            ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
              regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
              regOwn .x30 ** regOwn .x31 ** (Field ↦ₘ value) ** memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) ** (validPtr ↦ₘ (1 : Word)))
            (by pcfx) LinkRA (BitVec.ofNat 64 lengths.length) lenBase
            (hdrBaseAt hdrBase lengths i) validPtr status hspC hraSaved hret)
        have hcompose := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
          have hp1 : ((firstBadPtr ↦ₘ (0 : Word)) **
              ((.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (.x10 ↦ᵣ status) **
                (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ LinkRA) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
                  regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
                  regOwn .x30 ** regOwn .x31 ** (Field ↦ₘ value) ** memOwn RfuOff **
                  memOwn RfuLen ** stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                    ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (validPtr ↦ₘ (1 : Word))))) h := by xperm_hyp hp
          have hp2 := sepConj_mono_left memIs_implies_memOwn h hp1
          xperm_hyp hp2) htakenF hpfC
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
          (cpsTripleWithin_mono_nSteps (show 1 + 11 ≤ 27 + nTail by omega) hcompose)
        refine Or.inr (Or.inr ⟨i, status, ?_⟩)
        refine (sepConj_pure_left h).mpr ⟨⟨hi, hprefix, ⟨value, hResult, hstatus⟩⟩, ?_⟩
        unfold commonRet payload
        rw [hsf, hraSaved, wordArray_split lenBase lengths i hi,
          EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen, ← hHB]
        have hp1 : ((Field ↦ₘ value) ** (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) **
            (IterI ↦ₘ BitVec.ofNat 64 i) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            ((.x10 ↦ᵣ status) ** (validPtr ↦ₘ (1 : Word)) **
              (firstBadPtr ↦ₘ BitVec.ofNat 64 i) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
              (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) ** (.x18 ↦ᵣ csaved.s2) **
              (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
              (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
              ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
              ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
              (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
              regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
              regOwn .x30 ** regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)))) h := by
          rw [← hLi]; xperm_hyp hq
        have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
          (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _) (fun _ x => x)))) h hp1
        xperm_hyp hp2


/-! ## One full iteration: guard → call → dispatch (`D+68 → raIn`, `i < N`)

    Shapes `LoopInv i` into `cvbgmIterEntry`'s split precondition (peeling the
    three K34 scratch cells to arbitrary incumbents and splitting the arrays),
    runs the entry half to K34's `flatPost`, then the dispatch. -/

set_option maxRecDepth 8000 in
theorem cvbgmIter (sp0 spC hdrBase lenBase validPtr firstBadPtr raIn : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) (i nTail : Nat)
    (hi : i < lengths.length)
    (hN : lengths.length < 2 ^ 64)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (halign : hdrOff lengths i % 8 = 0)
    (hlen : hdrOff lengths i ≤ bigBytes.length)
    (hsalign : (hdrBaseAt hdrBase lengths i).toNat % 8 = 0)
    (hslack : lengths[i]! + 9 ≤ (bigBytes.drop (hdrOff lengths i)).length)
    (hover : (hdrBaseAt hdrBase lengths i).toNat +
      (bigBytes.drop (hdrOff lengths i)).length < 2 ^ 64)
    (hvalid : ∀ k, k < (bigBytes.drop (hdrOff lengths i)).length →
      isValidByteAccess (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 k) = true)
    (hprefix : ∀ j, j < i → hdrMultiple hdrBase bigBytes lengths j)
    (htail : (∀ j, j < i + 1 → hdrMultiple hdrBase bigBytes lengths j) →
      cpsTripleWithin nTail (D + 68) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths (i + 1))
        (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths)) :
    cpsTripleWithin ((1 + (13 + 1 + nCall (bigBytes.drop (hdrOff lengths i)).length)) + (27 + nTail)) (D + 68) raIn fullCode
      (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths i)
      (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) := by
  have hLi : lengths[i]! = lengths[i] := getElem!_pos lengths i hi
  have hHB : hdrBaseAt hdrBase lengths i = hdrBase + BitVec.ofNat 64 (hdrOff lengths i) := rfl
  -- The entry-half footprint minus the three K34 scratch cells.
  set EBody : Assertion :=
    ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
      (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
      (.x21 ↦ᵣ BitVec.ofNat 64 i) ** savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) **
      (firstBadPtr ↦ₘ (0 : Word)) ** wordArrayFrom lenBase 0 (lengths.take i) **
      ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
      bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
      memOwn IterPtr ** memOwn IterI ** regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
      stackFree (spC + signExtend12 (-32 : BitVec 12)) 8) with hEBody
  refine cpsTripleWithin_weaken (fun h hp => by
    unfold LoopInv payload scratchRegs at hp
    rw [wordArray_split lenBase lengths i hi,
      EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen,
      ← hHB, ← hLi] at hp
    rw [hEBody]; xperm_hyp hp) (fun _ hq => hq)
    (show cpsTripleWithin ((1 + (13 + 1 + nCall (bigBytes.drop (hdrOff lengths i)).length)) + (27 + nTail)) (D + 68) raIn fullCode
      (((EBody ** memOwn Field) ** memOwn RfuOff) ** memOwn RfuLen)
      (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) from ?_)
  refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldLen => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (show cpsTripleWithin ((1 + (13 + 1 + nCall (bigBytes.drop (hdrOff lengths i)).length)) + (27 + nTail)) (D + 68) raIn fullCode
      (((EBody ** (RfuLen ↦ₘ oldLen)) ** memOwn Field) ** memOwn RfuOff)
      (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) from ?_)
  refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldOff => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (show cpsTripleWithin ((1 + (13 + 1 + nCall (bigBytes.drop (hdrOff lengths i)).length)) + (27 + nTail)) (D + 68) raIn fullCode
      (((EBody ** (RfuLen ↦ₘ oldLen)) ** (RfuOff ↦ₘ oldOff)) ** memOwn Field)
      (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) from ?_)
  refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldOut => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by rw [hEBody] at hp; xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_seq_same_cr
      (cvbgmIterEntry spC hdrBase lenBase validPtr firstBadPtr csaved bigBytes lengths i
        oldOut oldOff oldLen hi hN hsalign hslack hover hvalid)
      (cvbgmIterDispatch sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr raIn csaved bigBytes lengths i oldOff oldLen nTail hi hN hspC rfl hraSaved
        hret halign hlen hprefix htail))


end EvmAsm.Codegen.ChainValidateBlobGasMultipleSpec
