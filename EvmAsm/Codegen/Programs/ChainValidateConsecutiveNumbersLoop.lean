/-
  Per-iteration straight-line building blocks for
  `chain_validate_consecutive_numbers`.

  Builds on `ChainValidateConsecutiveNumbersSpec` (model, prologue, epilogue,
  exit blocks).  The distinguishing feature of this CROSS-HEADER accessor is the
  spill/reload of the iterator state — `{base_i, i, prev = ts[i-1]}` — through
  the scratch cells `cvcn_iter_child` / `cvcn_iter_i` / `cvcn_iter_prev` around
  each `rlp_field_to_u64` (field 11) call, and the `BGEU x29 x28` comparison of
  the reloaded `prev` (`cvcn_iter_prev`) against the freshly-decoded `cur`
  (`cvcn_num`).  The `prev` cell genuinely holds the ACTUAL decoded timestamp of
  header `i-1` (tied to K34's `Result`), so the invariant threads the real value.
-/

import EvmAsm.Codegen.Programs.ChainValidateConsecutiveNumbersSpec
import EvmAsm.Evm64.StateAssertions

namespace EvmAsm.Codegen.ChainValidateConsecutiveNumbersSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm
  (Saved savedFrame savedVals listNthFrame regsAt_listNthFrame
   frameSlotsSaved_listNthFrame)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom
   wordArrayFrom_append shiftLeft3_ofNat hdrOff hdrBaseAt hdrOff_succ hdrBaseAt_succ
   ofNat_ne_of_lt ofNat_succ_tie)

/-! ## Spill block (instructions 32--40): spill `{child, i, prev}` to scratch

    From the loop-guard fall-through (`D+128`) to just before the argument setup
    (`D+164`).  Materializes `*cvcn_iter_child := base_i`, `*cvcn_iter_i := i`,
    and — crucially — `*cvcn_iter_prev := prev` where `prev` is `x21`, the
    timestamp decoded from header `i-1`. -/

set_option maxRecDepth 8000 in
theorem cvcnSpill (hbi iW prevVal old5 : Word) :
    cpsTripleWithin 9 (D + 128) (D + 164) cvcnCode
      ((.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x21 ↦ᵣ prevVal) **
        memOwn IterChild ** memOwn IterI ** memOwn IterPrev)
      ((.x5 ↦ᵣ IterPrev) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x21 ↦ᵣ prevVal) **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal)) := by
  have hla32 := la_materialize_within .x5 old5 (D + 128) IterChild (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 128) cvcnProg 32 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 128) IterChild)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 132) cvcnProg 33 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 128) IterChild)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
  have s34 := sd_spec_gen_own_within .x5 .x6 IterChild hbi (0 : BitVec 12) (D + 136)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterChild + (0 : Word) = IterChild from by bv_omega] at s34
  have s34' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 136) cvcnProg 34 (.SD .x5 .x6 (0 : BitVec 12))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s34
  have hla35 := la_materialize_within .x5 IterChild (D + 140) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 140) cvcnProg 35 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 140) IterI)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 144) cvcnProg 36 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 140) IterI)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
  have s37 := sd_spec_gen_own_within .x5 .x7 IterI iW (0 : BitVec 12) (D + 148)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s37
  have s37' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 148) cvcnProg 37 (.SD .x5 .x7 (0 : BitVec 12))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s37
  have hla38 := la_materialize_within .x5 IterI (D + 152) IterPrev (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 152) cvcnProg 38 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 152) IterPrev)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 156) cvcnProg 39 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 152) IterPrev)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
  have s40 := sd_spec_gen_own_within .x5 .x21 IterPrev prevVal (0 : BitVec 12) (D + 160)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPrev + (0 : Word) = IterPrev from by bv_omega] at s40
  have s40' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 160) cvcnProg 40 (.SD .x5 .x21 (0 : BitVec 12))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s40
  runBlock hla32 s34' hla35 s37' hla38 s40'

#print axioms cvcnSpill

/-! ## Reload block (instructions 50--55): load `cur` and `prev` for the compare

    Runs on the K34-success (`bne` not-taken) path from `D+200` to `D+224`
    (just before the `BGEU`): `x28 := *cvcn_num` (the freshly-decoded `ts[i]`,
    `cur`) and `x29 := *cvcn_iter_prev` (the saved `ts[i-1]`, `prev`). -/

set_option maxRecDepth 8000 in
theorem cvcnReload (curVal prevVal old5 o28 o29 : Word) :
    cpsTripleWithin 6 (D + 200) (D + 224) cvcnCode
      ((.x5 ↦ᵣ old5) ** (.x28 ↦ᵣ o28) ** (.x29 ↦ᵣ o29) **
        (Num ↦ₘ curVal) ** (IterPrev ↦ₘ prevVal))
      ((.x5 ↦ᵣ IterPrev) ** (.x28 ↦ᵣ curVal) ** (.x29 ↦ᵣ prevVal) **
        (Num ↦ₘ curVal) ** (IterPrev ↦ₘ prevVal)) := by
  have hla50 := la_materialize_within .x5 old5 (D + 200) Num (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 200) cvcnProg 50 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 200) Num)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 204) cvcnProg 51 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 200) Num)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
  have s52 := ld_spec_gen_within .x28 .x5 Num o28 curVal (0 : BitVec 12) (D + 208) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show Num + (0 : Word) = Num from by bv_omega] at s52
  have s52' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 208) cvcnProg 52 (.LD .x28 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s52
  have hla53 := la_materialize_within .x5 Num (D + 212) IterPrev (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 212) cvcnProg 53 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 212) IterPrev)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 216) cvcnProg 54 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 212) IterPrev)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
  have s55 := ld_spec_gen_within .x29 .x5 IterPrev o29 prevVal (0 : BitVec 12) (D + 220) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPrev + (0 : Word) = IterPrev from by bv_omega] at s55
  have s55' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 220) cvcnProg 55 (.LD .x29 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s55
  runBlock hla50 s52' hla53 s55'

#print axioms cvcnReload

/-! ## Advance block (instructions 57--69): update `prev`, step iterator, loop

    On the increasing (`BGEU` not-taken, `prev <ᵤ cur`) path from `D+228`:
    reload `x6 := base_i` and `x7 := i`, set `x21 := cur` (the new `prev` for the
    next iteration — the just-decoded `ts[i]`), advance `x6 += lengths[i]`,
    `x7 += 1`, then `jal x0, -152` back to the loop guard at `D+124`. -/

set_option maxRecDepth 8000 in
theorem cvcnAdvance (hbi lenBase iW curVal old5 o6 o7 o21 o30 o31 : Word) (Li : Nat) :
    cpsTripleWithin 13 (D + 232) (D + 124) cvcnCode
      ((.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ o6) ** (.x7 ↦ᵣ o7) ** (.x9 ↦ᵣ lenBase) **
        (.x21 ↦ᵣ o21) ** (.x28 ↦ᵣ curVal) ** (.x30 ↦ᵣ o30) ** (.x31 ↦ᵣ o31) **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ (hbi + BitVec.ofNat 64 Li)) **
        (.x7 ↦ᵣ (iW + signExtend12 (1 : BitVec 12))) ** (.x9 ↦ᵣ lenBase) **
        (.x21 ↦ᵣ curVal) ** (.x28 ↦ᵣ curVal) ** (.x30 ↦ᵣ (lenBase + (iW <<< 3))) **
        (.x31 ↦ᵣ BitVec.ofNat 64 Li) **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  have hla57 := la_materialize_within .x5 old5 (D + 232) IterChild (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 232) cvcnProg 58 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 232) IterChild)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 236) cvcnProg 59 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 232) IterChild)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
  have s59 := ld_spec_gen_within .x6 .x5 IterChild o6 hbi (0 : BitVec 12) (D + 240) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterChild + (0 : Word) = IterChild from by bv_omega] at s59
  have s59' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 240) cvcnProg 60 (.LD .x6 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s59
  have hla60 := la_materialize_within .x5 IterChild (D + 244) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 244) cvcnProg 61 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 244) IterI)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 248) cvcnProg 62 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 244) IterI)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
  have s62 := ld_spec_gen_within .x7 .x5 IterI o7 iW (0 : BitVec 12) (D + 252) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s62
  have s62' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 252) cvcnProg 63 (.LD .x7 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s62
  have s63 := mv_spec_gen_within .x21 .x28 curVal o21 (D + 256) (by decide)
  have s63' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 256) cvcnProg 64 (.MV .x21 .x28)
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s63
  have s64 := slli_spec_gen_within .x30 .x7 o30 iW (3 : BitVec 6) (D + 260) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s64
  have s64' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 260) cvcnProg 65 (.SLLI .x30 .x7 (3 : BitVec 6))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s64
  have s65 := add_spec_gen_rd_eq_rs2_within .x30 .x9 lenBase (iW <<< 3) (D + 264) (by decide)
  have s65' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 264) cvcnProg 66 (.ADD .x30 .x9 .x30)
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s65
  have s66 := ld_spec_gen_within .x31 .x30 (lenBase + (iW <<< 3)) o31 (BitVec.ofNat 64 Li)
    (0 : BitVec 12) (D + 268) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iW <<< 3)) + (0 : Word) = lenBase + (iW <<< 3) from by bv_omega] at s66
  have s66' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 268) cvcnProg 67 (.LD .x31 .x30 (0 : BitVec 12))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s66
  have s67 := add_spec_gen_rd_eq_rs1_within .x6 .x31 hbi (BitVec.ofNat 64 Li) (D + 272) (by decide)
  have s67' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 272) cvcnProg 68 (.ADD .x6 .x6 .x31)
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s67
  have s68 := addi_spec_gen_same_within .x7 iW (1 : BitVec 12) (D + 276) (by decide)
  have s68' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 276) cvcnProg 69 (.ADDI .x7 .x7 (1 : BitVec 12))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s68
  have s69 := jal_x0_spec_gen_within (-156 : BitVec 21) (D + 280)
  rw [show (D + 280) + signExtend21 (-156 : BitVec 21) = D + 124 from by
    rw [show signExtend21 (-156 : BitVec 21) = (-156 : Word) from by decide]; bv_omega] at s69
  have s69' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 280) cvcnProg 70 (.JAL .x0 (-156 : BitVec 21))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s69
  runBlock hla57 s59' hla60 s62' s63' s64' s65' s66' s67' s68' s69'

#print axioms cvcnAdvance

/-! ## Loop-body argument setup (instructions 41--47): load call args

    From just after the spill (`D+164`) to just before the `jal` (`D+192`):
    `x28 := lenBase + i<<3`, `x11 := lengths[i]`, `x10 := base_i`, `x12 := 11`,
    `x13 := Num` (the K34 output cell). -/

set_option maxRecDepth 8000 in
theorem cvcnArgSetup (hbi lenBase iW : Word) (Li : Nat)
    (old10 old11 old12 old13 old28 : Word) :
    cpsTripleWithin 7 (D + 164) (D + 192) cvcnCode
      ((.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x9 ↦ᵣ lenBase) **
        (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) ** (.x13 ↦ᵣ old13) **
        (.x28 ↦ᵣ old28) ** ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x9 ↦ᵣ lenBase) **
        (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (8 : Word)) **
        (.x13 ↦ᵣ Num) ** (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  have s41 := slli_spec_gen_within .x28 .x7 old28 iW (3 : BitVec 6) (D + 164) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s41
  have s41' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 164) cvcnProg 41 (.SLLI .x28 .x7 (3 : BitVec 6))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s41
  have s42 := add_spec_gen_rd_eq_rs2_within .x28 .x9 lenBase (iW <<< 3) (D + 168) (by decide)
  have s42' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 168) cvcnProg 42 (.ADD .x28 .x9 .x28)
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s42
  have s43 := ld_spec_gen_within .x11 .x28 (lenBase + (iW <<< 3)) old11 (BitVec.ofNat 64 Li)
    (0 : BitVec 12) (D + 172) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iW <<< 3)) + (0 : Word) = lenBase + (iW <<< 3) from by bv_omega] at s43
  have s43' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 172) cvcnProg 43 (.LD .x11 .x28 (0 : BitVec 12))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s43
  have s44 := mv_spec_gen_within .x10 .x6 hbi old10 (D + 176) (by decide)
  have s44' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 176) cvcnProg 44 (.MV .x10 .x6)
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s44
  have s45 := li_spec_gen_within .x12 old12 (8 : Word) (D + 180) (by decide)
  have s45' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 180) cvcnProg 45 (.LI .x12 (8 : Word))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s45
  have hla46 := la_materialize_within .x13 old13 (D + 184) Num (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 184) cvcnProg 46 (.AUIPC .x13 (EvmAsm.Rv64.laHi (D + 184) Num)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 188) cvcnProg 47 (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (D + 184) Num)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
  runBlock s41' s42' s43' s44' s45' hla46

#print axioms cvcnArgSetup

/-! ## Header-0 argument setup (instructions 18--22): load call args for header 0

    From the `N ≥ 2` fall-through (`D+72`) to just before the header-0 `jal`
    (`D+92`): `x11 := lengths[0]` (loaded directly from `*lenBase`),
    `x10 := hdrBase` (header 0's base), `x12 := 11`, `x13 := Num`. -/

set_option maxRecDepth 8000 in
theorem cvcnHdr0Setup (hdrBase lenBase : Word) (L0 : Nat) (old10 old11 old12 old13 : Word) :
    cpsTripleWithin 5 (D + 72) (D + 92) cvcnCode
      ((.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x12 ↦ᵣ old12) ** (.x13 ↦ᵣ old13) ** (lenBase ↦ₘ BitVec.ofNat 64 L0))
      ((.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x10 ↦ᵣ hdrBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 L0) ** (.x12 ↦ᵣ (8 : Word)) ** (.x13 ↦ᵣ Num) **
        (lenBase ↦ₘ BitVec.ofNat 64 L0)) := by
  have s18 := ld_spec_gen_within .x11 .x9 lenBase old11 (BitVec.ofNat 64 L0)
    (0 : BitVec 12) (D + 72) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show lenBase + (0 : Word) = lenBase from by bv_omega] at s18
  have s18' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 72) cvcnProg 18 (.LD .x11 .x9 (0 : BitVec 12))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s18
  have s19 := mv_spec_gen_within .x10 .x18 hdrBase old10 (D + 76) (by decide)
  have s19' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 76) cvcnProg 19 (.MV .x10 .x18)
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s19
  have s20 := li_spec_gen_within .x12 old12 (8 : Word) (D + 80) (by decide)
  have s20' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 80) cvcnProg 20 (.LI .x12 (8 : Word))
      (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) s20
  have hla21 := la_materialize_within .x13 old13 (D + 84) Num (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 84) cvcnProg 21 (.AUIPC .x13 (EvmAsm.Rv64.laHi (D + 84) Num)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 88) cvcnProg 22 (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (D + 84) Num)) (by bv_omega) (by rw [cvcn_length]; decide) (by decide) (by rw [cvcn_length]; decide))
  runBlock s18' s19' s20' hla21

#print axioms cvcnHdr0Setup

/-- pcFree discharger covering the assertion atoms used throughout the loop. -/
local macro "pcfx" : tactic =>
  `(tactic| repeat' first
      | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs | exact pcFree_memOwn | exact pcFree_emp | exact pcFree_pure
      | exact bytesRegion_pcFree _ _ | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_wordArray _ _ | exact pcFree_wordArrayFrom _ _ _ | unfold savedFrame
      | unfold EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame)

/-! ## Combined loop-body setup (instructions 32--47): spill ;; arg setup

    Composes `cvcnSpill` (spill `{child, i, prev}`) with `cvcnArgSetup` (load the
    K34 call args) into one block from `D+128` to `D+192`. -/

set_option maxRecDepth 8000 in
theorem cvcnSetup (hbi lenBase iW prevVal : Word) (Li : Nat)
    (old5 old10 old11 old12 old13 old28 : Word) :
    cpsTripleWithin 16 (D + 128) (D + 192) cvcnCode
      ((.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x21 ↦ᵣ prevVal) **
        (.x9 ↦ᵣ lenBase) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        (.x13 ↦ᵣ old13) ** (.x28 ↦ᵣ old28) **
        memOwn IterChild ** memOwn IterI ** memOwn IterPrev **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x5 ↦ᵣ IterPrev) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x21 ↦ᵣ prevVal) **
        (.x9 ↦ᵣ lenBase) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
        (.x12 ↦ᵣ (8 : Word)) ** (.x13 ↦ᵣ Num) ** (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  have hspillF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ lenBase) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
      (.x13 ↦ᵣ old13) ** (.x28 ↦ᵣ old28) ** ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
    (by pcfx) (cvcnSpill hbi iW prevVal old5)
  have hargsF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ IterPrev) ** (.x21 ↦ᵣ prevVal) **
      (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal))
    (by pcfx) (cvcnArgSetup hbi lenBase iW Li old10 old11 old12 old13 old28)
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hspillF hargsF)

#print axioms cvcnSetup

/-! ## K34's whole-routine step count for field index 11. -/
abbrev nCall : Nat :=
  (7 + 4 + (1 + ((12 + ((85 + 93 * (8 + 2)) + 6)) + 9)))
    + ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5)

/-! ## Call block (instructions 32--48 + K34): setup ;; jal ;; rlp_field_to_u64

    From the loop-body entry (`D+128`) to the return site (`D+196`), producing
    K34's `flatPost` for header `hbi` (field 11).  `x18` holds the ORIGINAL
    `hdrBase` (K34's saved `s2`), `x21` the threaded `prev` (saved `s5`); the
    header base being decoded is `hbi` (moved into `x10`). -/

set_option maxRecDepth 8000 in
theorem cvcnCall (spC hdrBase lenBase hbi iW validPtr firstBadPtr prevVal : Word) (Li : Nat)
    (nN oldOut oldOff oldLen old14 oldX1 old5 o10 o11 o12 o13 o28 : Word)
    (bytes : List (BitVec 8)) (csaved : Saved)
    (hsalign : hbi.toNat % 8 = 0)
    (hslack : Li + 9 ≤ bytes.length)
    (hover : hbi.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (hbi + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (16 + 1 + nCall) (D + 128) (D + 196) fullCode
      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) **
        (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) ** (.x13 ↦ᵣ o13) **
        (.x14 ↦ᵣ old14) ** (.x28 ↦ᵣ o28) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x1 ↦ᵣ oldX1) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn IterChild ** memOwn IterI ** memOwn IterPrev **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
        (Num ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        bytesRegion hbi bytes ** savedFrame spC csaved)
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Num, hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
          bytes Li 8 **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) := by
  set calleeNewSp : Word := spC + signExtend12 (-32 : BitVec 12) with hcalleeNewSp
  -- Setup block, lifted to fullCode, framed with the callee footprint.
  have hsetup := cpsTripleWithin_extend_code cvcn_mono
    (cvcnSetup hbi lenBase iW prevVal Li old5 o10 o11 o12 o13 o28)
  have hsetupF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
      (.x20 ↦ᵣ firstBadPtr) ** (.x14 ↦ᵣ old14) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x1 ↦ᵣ oldX1) ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (Num ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hbi bytes ** savedFrame spC csaved)
    (by pcfx) hsetup
  -- [48] jal x1, rlp_field_to_u64
  have hjal := jal_link_spec_within
    (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64
      (GuestAddrs.chain_validate_consecutive_numbers + 192)) (D + 192) oldX1
  rw [show (D + 192) + signExtend21 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64
      (GuestAddrs.chain_validate_consecutive_numbers + 192))
      = EvmAsm.Codegen.RlpFieldToU64SAsm.B from by decide,
    show (D + 192 + 4 : Word) = LinkRA from by
      change (D + 192 + 4 : Word) = D + 196; bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code cvcn_mono
    (cpsTripleWithin_extend_code (cr' := cvcnCode)
      (CodeReq.ofProg_mem_at D (D + 192) cvcnProg 48
        (.JAL .x1 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64
          (GuestAddrs.chain_validate_consecutive_numbers + 192))) (by bv_omega)
        (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) **
      (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
      (.x5 ↦ᵣ IterPrev) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
      (.x12 ↦ᵣ (8 : Word)) ** (.x13 ↦ᵣ Num) ** (.x14 ↦ᵣ old14) **
      (.x28 ↦ᵣ (lenBase + (iW <<< 3))) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (Num ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hbi bytes **
      (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal) **
      ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)
    (by pcfx) hjalC
  -- K34 flat callee, lifted to fullCode, framed with the spill/array/chain payload.
  have hcallee0 := EvmAsm.Codegen.RlpFieldToU64SAsm.rlpFieldToU64_flat_spec_within
    spC calleeNewSp hbi (BitVec.ofNat 64 Li) (8 : Word) Num oldOut oldOff oldLen old14
    (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved) hdrBase validPtr firstBadPtr
    prevVal bytes Li 8
    hcalleeNewSp rfl (by decide) (by decide)
    hsalign hslack hover hvalid (by show LinkRA &&& ~~~(1 : Word) = LinkRA; decide)
  have hcalleeC := cpsTripleWithin_extend_code k34_mono hcallee0
  -- Present K34's entry footprint as explicit atoms, with x5/x6/x7/x28 shown owned.
  have hcallee : cpsTripleWithin nCall EvmAsm.Codegen.RlpFieldToU64SAsm.B LinkRA fullCode
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
          (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
          (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (8 : Word)) **
          (.x13 ↦ᵣ Num) ** (.x14 ↦ᵣ old14) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
          stackFree calleeNewSp 8 ** bytesRegion hbi bytes **
          (Num ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen)))
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC calleeNewSp hbi oldOff oldLen
          (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Num, hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
          bytes Li 8) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold EvmAsm.Codegen.RlpFieldToU64SAsm.flatPre EvmAsm.Codegen.RlpFieldToU64SAsm.wholeRest
      xperm_hyp hp) (fun _ hq => hq) hcalleeC
  have hcalleeF := cpsTripleWithin_frameR
    ((IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal) **
      ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)
    (by pcfx) hcallee
  -- Compose setup ;; jal ;; callee (weakening x5/x6/x7/x28 to owned at the midpoint).
  have hsj := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupF hjalF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => ?_) hsj hcalleeF)
  have hp' : ((.x5 ↦ᵣ IterPrev) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) **
      (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
      ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
        (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (8 : Word)) **
        (.x13 ↦ᵣ Num) ** (.x14 ↦ᵣ old14) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
        stackFree calleeNewSp 8 ** bytesRegion hbi bytes **
        (Num ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)) h := by
    xperm_hyp hp
  have hp'' := sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x)))) h hp'
  xperm_hyp hp''

#print axioms cvcnCall

/-! ## Call block with the consumed scratch registers owned

    `cvcnCall` with `x1/x5/x10/x11/x12/x13/x14/x28` presented as `regOwn`,
    matching how they sit in `LoopInv`/`scratchRegs`. -/

set_option maxRecDepth 8000 in
theorem cvcnCallOwned (spC hdrBase lenBase hbi iW validPtr firstBadPtr prevVal : Word) (Li : Nat)
    (nN oldOut oldOff oldLen : Word) (bytes : List (BitVec 8)) (csaved : Saved)
    (hsalign : hbi.toNat % 8 = 0)
    (hslack : Li + 9 ≤ bytes.length)
    (hover : hbi.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (hbi + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (16 + 1 + nCall) (D + 128) (D + 196) fullCode
      ((((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) **
          (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
          (.x21 ↦ᵣ prevVal) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          memOwn IterChild ** memOwn IterI ** memOwn IterPrev **
          ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          (Num ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
          bytesRegion hbi bytes ** savedFrame spC csaved) **
        regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28) ** regOwn .x1)
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Num, hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
          bytes Li 8 **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v1 => ?_)
  refine cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => h)
    (show cpsTripleWithin (16 + 1 + nCall) (D + 128) (D + 196) fullCode
      ((((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) **
          (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
          (.x21 ↦ᵣ prevVal) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          memOwn IterChild ** memOwn IterI ** memOwn IterPrev **
          ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          (Num ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
          bytesRegion hbi bytes ** savedFrame spC csaved) ** (.x1 ↦ᵣ v1)) **
        regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28)
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Num, hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
          bytes Li 8 **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) from ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_of_forall_regIs_to_regOwn7
    (fun v5 v10 v11 v12 v13 v14 v28 => ?_)
  exact cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => by xperm_hyp h)
    (cvcnCall spC hdrBase lenBase hbi iW validPtr firstBadPtr prevVal Li nN oldOut oldOff oldLen
      v14 v1 v5 v10 v11 v12 v13 v28 bytes csaved hsalign hslack hover hvalid)

#print axioms cvcnCallOwned

/-! ## Normalizing K34's `flatPost` into a single Result-carrying assertion

    `dispNorm status value` is the common owned shape both `flatPost` arms weaken
    to; it exposes `x10 = status` (for the `bne`) and `Num ↦ value` (for the
    reload) while owning the callee-perturbed remainder.  The restored saved regs
    are `x18 = hdrBase` (`s2`), `x19 = validPtr` (`s3`), `x20 = firstBadPtr`
    (`s4`), `x21 = prev` (`s5`). -/
def dispNorm (spC calleeNewSp hbi hdrBase validPtr firstBadPtr nN lenBase prevVal
    value status : Word) (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
  (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
  (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (Num ↦ₘ value) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  memOwn RfuOff ** memOwn RfuLen ** stackFree calleeNewSp 8 **
  bytesRegion hbi bytes **
  EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame calleeNewSp ⟨LinkRA, nN, lenBase⟩

set_option maxRecDepth 8000 in
theorem flatPost_normalize (spC hbi hdrBase validPtr firstBadPtr nN lenBase prevVal
    oldOff oldLen : Word) (bytes : List (BitVec 8)) (Li : Nat) : ∀ h,
    (EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
      oldOff oldLen (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
      (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Num, hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
      bytes Li 8) h →
    (∃ status value,
      (dispNorm spC (spC + signExtend12 (-32 : BitVec 12)) hbi hdrBase validPtr firstBadPtr nN
          lenBase prevVal value status bytes **
        ⌜EvmAsm.Codegen.RlpFieldToU64SAsm.Result bytes hbi Li 8 status value⌝) h) := by
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
        ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
          (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
          (.x10 ↦ᵣ wrapperStatus) ** (.x0 ↦ᵣ (0 : Word)) ** (Num ↦ₘ outputValue) **
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
        ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
          (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
          (.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (Num ↦ₘ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 ** bytesRegion hbi bytes **
          EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
            ⟨LinkRA, nN, lenBase⟩)) h := by xperm_hyp hOB
    have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
      (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x12)
        (fun _ x => x)))) h hp1
    xperm_hyp hp2

#print axioms flatPost_normalize

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

#print axioms k34SavedFrame_implies_frameSlotsOwn

/-! ## Entry half of one loop iteration: guard → call → K34 flatPost

    From the loop guard (`D+124`, `i < N` so not taken) through the `jal` to
    K34's return (`D+196`), with the header-`i` slice handed to K34 and the
    untouched `wordArray`/`bytesRegion` prefixes framed. -/

set_option maxRecDepth 8000 in
theorem cvcnIterEntry (spC hdrBase lenBase validPtr firstBadPtr prevVal : Word)
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
    cpsTripleWithin (1 + (16 + 1 + nCall)) (D + 124) (D + 196) fullCode
      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
        (.x6 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
        (.x20 ↦ᵣ firstBadPtr) ** (.x7 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ prevVal) **
        savedFrame spC csaved **
        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
        (Num ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        memOwn IterChild ** memOwn IterI ** memOwn IterPrev **
        regOwn .x1 ** regOwn .x5 ** regOwn .x10 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12))
          (hdrBaseAt hdrBase lengths i) oldOff oldLen
          (⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ :
            EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hdrBaseAt hdrBase lengths i, Num,
            hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
          (bigBytes.drop (hdrOff lengths i)) lengths[i]! 8 **
        (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
        (IterPrev ↦ₘ prevVal) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        savedFrame spC csaved) := by
  -- [31] BEQ x7 x8 : i ≠ N ⇒ not taken → D+128.
  have hbeq := beq_spec_gen_within .x7 .x8 (208 : BitVec 13) (BitVec.ofNat 64 i)
    (BitVec.ofNat 64 lengths.length) (D + 124)
  have hbeqC := cpsBranchWithin_extend_code cvcn_mono
    (cpsBranchWithin_extend_code (cr' := cvcnCode)
      (CodeReq.ofProg_mem_at D (D + 124) cvcnProg 31 (.BEQ .x7 .x8 (208 : BitVec 13))
        (by bv_omega) (by rw [cvcn_length]; decide) rfl (by rw [cvcn_length]; decide)) hbeq)
  have hguard0 := cpsBranchWithin_ntakenStripPure2 hbeqC (fun hp hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact ofNat_ne_of_lt i lengths.length hi hN ((sepConj_pure_right _).1 hrest).2)
  rw [show (D + 124 + 4 : Word) = D + 128 from by bv_omega] at hguard0
  -- Frame the guard with the untouched loop-invariant state (everything but x7/x8).
  have hguardF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x6 ↦ᵣ hdrBaseAt hdrBase lengths i) **
      (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
      savedFrame spC csaved **
      (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
      wordArrayFrom lenBase 0 (lengths.take i) **
      ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
      bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
      (Num ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      memOwn IterChild ** memOwn IterI ** memOwn IterPrev **
      regOwn .x1 ** regOwn .x5 ** regOwn .x10 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
      stackFree (spC + signExtend12 (-32 : BitVec 12)) 8) (by pcfx) hguard0
  -- The call, framed with the untouched wordArray/bytesRegion prefixes.
  have hcall := cvcnCallOwned spC hdrBase lenBase (hdrBaseAt hdrBase lengths i)
    (BitVec.ofNat 64 i) validPtr firstBadPtr prevVal lengths[i]!
    (BitVec.ofNat 64 lengths.length) oldOut oldOff oldLen
    (bigBytes.drop (hdrOff lengths i)) csaved hsalign hslack hover hvalid
  have hcallF := cpsTripleWithin_frameR
    (wordArrayFrom lenBase 0 (lengths.take i) **
      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
      (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)))
    (by pcfx) hcall
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
      rw [show (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) from shiftLeft3_ofNat i] at hq
      xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      rw [show (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) from shiftLeft3_ofNat i]
      xperm_hyp hp) hguardF hcallF)

#print axioms cvcnIterEntry

/-! ## Status/order dispatch (instruction 49 onward): tie K34's `Result` to the post

    From K34's `flatPost` at the `bne` return site (`D+196`) to the caller's post.
    `flatPost_normalize` collapses the callee return into one `Result`-carrying
    shape; `bne x10, x0` [49] splits on the status; on success the reload
    [50-55] loads `cur`(`x28`)/`prev`(`x29`) and `bgeu x29, x28` [56] routes to
    the violation exit (`prev ≥ᵤ cur`) or advance+loop (`prev <ᵤ cur`).  The
    `prev` here is the GENUINE `ts[i-1]` (via `hprevOk`), tying the cross-header
    compare to the actual per-header `Result`s. -/

set_option maxRecDepth 8000 in
theorem cvcnIterDispatch
    (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr raIn prevVal : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) (i : Nat)
    (oldOff oldLen : Word) (nTail : Nat)
    (hi1 : 1 ≤ i)
    (hi : i < lengths.length)
    (_hN : lengths.length < 2 ^ 64)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hcns : calleeNewSp = spC + signExtend12 (-32 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (halign : hdrOff lengths i % 8 = 0)
    (hlen : hdrOff lengths i ≤ bigBytes.length)
    (hprevOk : hdrNumOk hdrBase bigBytes lengths (i - 1) prevVal)
    (hprefix : ∀ j, 1 ≤ j → j < i → numConsecutive hdrBase bigBytes lengths j)
    (htail : (∀ j, 1 ≤ j → j < i + 1 → numConsecutive hdrBase bigBytes lengths j) →
      cpsTripleWithin nTail (D + 124) raIn fullCode
        (LoopInv sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
          bigBytes lengths (i + 1))
        (cvcnPost sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
          bigBytes lengths)) :
    cpsTripleWithin (24 + nTail) (D + 196) raIn fullCode
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12))
          (hdrBaseAt hdrBase lengths i) oldOff oldLen
          (⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ :
            EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hdrBaseAt hdrBase lengths i, Num,
            hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
          (bigBytes.drop (hdrOff lengths i)) lengths[i]! 8 **
        (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
        (IterPrev ↦ₘ prevVal) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        savedFrame spC csaved)
      (cvcnPost sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
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
        (show cpsTripleWithin (24 + nTail) (D + 196) raIn fullCode
          ((.x1 ↦ᵣ LinkRA) **
            (dispNorm spC (spC + signExtend12 (-32 : BitVec 12)) (hdrBaseAt hdrBase lengths i)
                hdrBase validPtr firstBadPtr (BitVec.ofNat 64 lengths.length) lenBase prevVal
                value status (bigBytes.drop (hdrOff lengths i)) **
              ⌜EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
                (hdrBaseAt hdrBase lengths i) lengths[i]! 8 status value⌝) **
            ((IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              (IterPrev ↦ₘ prevVal) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              savedFrame spC csaved))
          (cvcnPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
            firstBadPtr csaved bigBytes lengths) from ?core))))
  case hstrip =>
    obtain ⟨s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hfp, hREST⟩ := hp
    obtain ⟨status, value, hnorm⟩ := flatPost_normalize spC (hdrBaseAt hdrBase lengths i)
      hdrBase validPtr firstBadPtr (BitVec.ofNat 64 lengths.length) lenBase prevVal
      oldOff oldLen (bigBytes.drop (hdrOff lengths i)) lengths[i]! s3 hfp
    exact ⟨status, value, s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hnorm, hREST⟩
  case core =>
    -- Pull the semantic `Result` out of the precondition.
    refine cpsTripleWithin_weaken (fun h hp => ?hpull) (fun _ hq => hq)
      (cpsTripleWithin_pure_pre
        (P := EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
          (hdrBaseAt hdrBase lengths i) lengths[i]! 8 status value)
        (H := (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
          (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
          (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) ** (.x10 ↦ᵣ status) **
          (.x0 ↦ᵣ (0 : Word)) ** (Num ↦ₘ value) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
          EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
            ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
          (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
          (IterPrev ↦ₘ prevVal) **
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
      · -- SUCCESS arm: `bne` not taken → reload → order compare.
        subst hstatus
        set RframeOk : Assertion :=
          ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) ** (Num ↦ₘ value) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
            (IterPrev ↦ₘ prevVal) **
            ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
            wordArrayFrom lenBase 0 (lengths.take i) **
            wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
            bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
            (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
            ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
            ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) with hRframeOk
        have hbne := bne_spec_gen_within .x10 .x0 (116 : BitVec 13) (0 : Word) (0 : Word)
          (D + 196)
        have hbneC := cpsBranchWithin_extend_code cvcn_mono
          (cpsBranchWithin_extend_code (cr' := cvcnCode)
            (CodeReq.ofProg_mem_at D (D + 196) cvcnProg 49 (.BNE .x10 .x0 (116 : BitVec 13))
              (by bv_omega) (by rw [cvcn_length]; decide) rfl
              (by rw [cvcn_length]; decide)) hbne)
        have hntaken := cpsBranchWithin_ntakenStripPure2 hbneC (fun hp hq => by
          obtain ⟨_, _, _, _, _, hrest⟩ := hq
          exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
        rw [show (D + 196 + 4 : Word) = D + 200 from by bv_omega] at hntaken
        have hntakenF := cpsTripleWithin_frameR RframeOk (by rw [hRframeOk]; pcfx) hntaken
        refine cpsTripleWithin_weaken (fun h hp => by rw [hRframeOk]; xperm_hyp hp) (fun _ hq => hq)
          (cpsTripleWithin_mono_nSteps (show 1 + (23 + nTail) ≤ 24 + nTail by omega)
            (cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hntakenF ?hcont))
        rw [hRframeOk]
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (show cpsTripleWithin (23 + nTail) (D + 200) raIn fullCode
            (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
              (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) ** (Num ↦ₘ value) **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              memOwn RfuOff ** memOwn RfuLen ** stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              (IterPrev ↦ₘ prevVal) **
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
            (cvcnPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
              firstBadPtr csaved bigBytes lengths) from ?_)
        refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_of_forall_regIs_to_regOwn7
          (fun v5 v6 v7 v28 v29 v30 v31 => ?_)
        set Rreload : Assertion :=
          ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
            (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            memOwn RfuOff ** memOwn RfuLen ** stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
            ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
            wordArrayFrom lenBase 0 (lengths.take i) **
            wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
            bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
            (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
            ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
            ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
            (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) with hRreload
        set Rstate2 : Assertion :=
          ((.x5 ↦ᵣ IterPrev) ** (Num ↦ₘ value) ** (IterPrev ↦ₘ prevVal)) ** Rreload
          with hRstate2
        -- reload [50-55]
        have hreload := cpsTripleWithin_extend_code cvcn_mono
          (cvcnReload value prevVal v5 v28 v29)
        have hreloadF := cpsTripleWithin_frameR Rreload (by rw [hRreload]; pcfx) hreload
        -- bgeu [56]
        have hbgeu := bgeu_spec_gen_within .x29 .x28 (56 : BitVec 13) prevVal value (D + 224)
        rw [show (D + 224) + signExtend13 (56 : BitVec 13) = D + 284 from by
          rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]; bv_omega] at hbgeu
        have hbgeuC := cpsBranchWithin_extend_code cvcn_mono
          (cpsBranchWithin_extend_code (cr' := cvcnCode)
            (CodeReq.ofProg_mem_at D (D + 224) cvcnProg 56 (.BGEU .x29 .x28 (56 : BitVec 13))
              (by bv_omega) (by rw [cvcn_length]; decide) rfl
              (by rw [cvcn_length]; decide)) hbgeu)
        have hbgeuF := cpsBranchWithin_frameR Rstate2 (by rw [hRstate2, hRreload]; pcfx) hbgeuC
        have hbranch := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
          (fun h hp => by rw [hRstate2]; xperm_hyp hp) hreloadF hbgeuF
        -- Violation arm: prev ≥ᵤ cur.
        have h_t : cpsTripleWithin (16 + nTail) (D + 284) raIn fullCode
            (((.x29 ↦ᵣ prevVal) ** (.x28 ↦ᵣ value) ** ⌜¬ BitVec.ult prevVal value⌝) ** Rstate2)
            (cvcnPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
              validPtr firstBadPtr csaved bigBytes lengths) := by
          rw [hRstate2, hRreload]
          refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
            (cpsTripleWithin_pure_pre (P := ¬ BitVec.ult prevVal value)
              (H := (.x29 ↦ᵣ prevVal) ** (.x28 ↦ᵣ value) ** (.x5 ↦ᵣ IterPrev) ** (Num ↦ₘ value) **
                (IterPrev ↦ₘ prevVal) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
                (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) ** regOwn .x11 ** regOwn .x12 **
                regOwn .x13 ** regOwn .x14 ** memOwn RfuOff ** memOwn RfuLen **
                stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                  ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                wordArrayFrom lenBase 0 (lengths.take i) **
                wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
              (fun hnult => ?_))
          have hviol := cpsTripleWithin_extend_code cvcn_mono
            (retViolation sp0 spC raIn (BitVec.ofNat 64 i) validPtr firstBadPtr csaved
              ((.x29 ↦ᵣ prevVal) ** (.x28 ↦ᵣ value) ** (Num ↦ₘ value) ** (IterPrev ↦ₘ prevVal) **
                regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
                memOwn RfuOff ** memOwn RfuLen **
                stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                  ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) **
                ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                wordArrayFrom lenBase 0 (lengths.take i) **
                wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                (.x7 ↦ᵣ v7) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
              (by pcfx) (0 : Word) LinkRA (BitVec.ofNat 64 lengths.length) lenBase hdrBase prevVal
              IterPrev v6 hspC hraSaved hret)
          refine cpsTripleWithin_weaken (fun h hp => by
            have hp1 : ((validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                ((.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x0 ↦ᵣ (0 : Word)) **
                  (.x5 ↦ᵣ IterPrev) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
                  (.x1 ↦ᵣ LinkRA) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                  (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x21 ↦ᵣ prevVal) **
                  (IterI ↦ₘ BitVec.ofNat 64 i) **
                  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                  ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                  ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                  ((.x29 ↦ᵣ prevVal) ** (.x28 ↦ᵣ value) ** (Num ↦ₘ value) ** (IterPrev ↦ₘ prevVal) **
                    regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
                    memOwn RfuOff ** memOwn RfuLen **
                    stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                    bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                    EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame
                      (spC + signExtend12 (-32 : BitVec 12))
                      ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                    (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) **
                    ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                    wordArrayFrom lenBase 0 (lengths.take i) **
                    wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                    bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                    (.x7 ↦ᵣ v7) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)))) h := by
              xperm_hyp hp
            have hp2 := sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn (fun _ x => x)) h hp1
            xperm_hyp hp2) (fun h hq => ?_)
            (cpsTripleWithin_mono_nSteps (show 16 ≤ 16 + nTail by omega) hviol)
          refine Or.inr (Or.inl ⟨i, ?_⟩)
          refine (sepConj_pure_left h).mpr ⟨⟨hi1, hi, hprefix, ⟨prevVal, value, hprevOk, hResult, hnult⟩⟩, ?_⟩
          unfold commonRet payload
          rw [hsf, hraSaved, wordArray_split lenBase lengths i hi,
            EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen, ← hHB]
          have hp1 : ((.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ BitVec.ofNat 64 i) ** (.x7 ↦ᵣ v7) **
              (.x28 ↦ᵣ value) ** (.x29 ↦ᵣ prevVal) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
              (Num ↦ₘ value) ** (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) **
              (IterI ↦ₘ BitVec.ofNat 64 i) ** (IterPrev ↦ₘ prevVal) **
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
            (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
            (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _)
            (fun _ x => x)))))))))))) h hp1
          xperm_hyp hp2
        -- Advance arm: prev <ᵤ cur.
        have h_f : cpsTripleWithin (16 + nTail) (D + 232) raIn fullCode
            (((.x29 ↦ᵣ prevVal) ** (.x28 ↦ᵣ value) ** ⌜BitVec.ult prevVal value⌝) ** Rstate2)
            (cvcnPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
              validPtr firstBadPtr csaved bigBytes lengths) := by
          rw [hRstate2, hRreload]
          refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
            (cpsTripleWithin_pure_pre (P := BitVec.ult prevVal value)
              (H := (.x29 ↦ᵣ prevVal) ** (.x28 ↦ᵣ value) ** (.x5 ↦ᵣ IterPrev) ** (Num ↦ₘ value) **
                (IterPrev ↦ₘ prevVal) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
                (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) ** regOwn .x11 ** regOwn .x12 **
                regOwn .x13 ** regOwn .x14 ** memOwn RfuOff ** memOwn RfuLen **
                stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                  ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                wordArrayFrom lenBase 0 (lengths.take i) **
                wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
              (fun hult => ?_))
          have hprefix' : ∀ j, 1 ≤ j → j < i + 1 → numConsecutive hdrBase bigBytes lengths j := by
            intro j hj1 hj
            rcases (by omega : j < i ∨ j = i) with hlt | heq
            · exact hprefix j hj1 hlt
            · subst heq; exact ⟨prevVal, value, hprevOk, hResult, hult⟩
          have hadv := cpsTripleWithin_extend_code cvcn_mono
            (cvcnAdvance (hdrBaseAt hdrBase lengths i) lenBase (BitVec.ofNat 64 i) value IterPrev
              v6 v7 prevVal v30 v31 lengths[i]!)
          rw [shiftLeft3_ofNat i] at hadv
          have hadvF := cpsTripleWithin_frameR
            ((.x29 ↦ᵣ prevVal) ** (Num ↦ₘ value) ** (IterPrev ↦ₘ prevVal) ** (.x10 ↦ᵣ (0 : Word)) **
              (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
              (.x20 ↦ᵣ firstBadPtr) ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              memOwn RfuOff ** memOwn RfuLen ** stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
              ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
              ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) (by pcfx) hadv
          refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
            (cpsTripleWithin_mono_nSteps (show 13 + nTail ≤ 16 + nTail by omega)
              (cpsTripleWithin_seq_perm_same_cr (fun h hp => by
                unfold LoopInv payload scratchRegs
                rw [hsf, wordArray_split lenBase lengths i hi,
                  EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen,
                  ← hHB, hdrBaseAt_succ hdrBase lengths i hi, ← ofNat_succ_tie i, ← hLi]
                refine ⟨value, (sepConj_pure_left h).mpr ⟨⟨hResult, hprefix'⟩, ?_⟩⟩
                have hp1 : ((.x1 ↦ᵣ LinkRA) ** (.x5 ↦ᵣ IterI) ** (.x10 ↦ᵣ (0 : Word)) **
                    (.x28 ↦ᵣ value) ** (.x29 ↦ᵣ prevVal) **
                    (.x30 ↦ᵣ (lenBase + BitVec.ofNat 64 (8 * i))) **
                    (.x31 ↦ᵣ BitVec.ofNat 64 lengths[i]!) **
                    (Num ↦ₘ value) ** (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) **
                    (IterI ↦ₘ BitVec.ofNat 64 i) ** (IterPrev ↦ₘ prevVal) **
                    EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                      ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                    ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
                      (.x6 ↦ᵣ (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 lengths[i]!)) **
                      (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
                      (.x7 ↦ᵣ (BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12))) **
                      (.x21 ↦ᵣ value) **
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
                have hp2 := sepConj_mono (regIs_implies_regOwn .x1)
                  (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x10)
                  (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x29)
                  (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (regIs_implies_regOwn .x31)
                  (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
                  (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
                  (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _)
                  (fun _ x => x)))))))))))) h hp1
                xperm_hyp hp2) hadvF (htail hprefix')))
        refine cpsTripleWithin_weaken (fun h hp => by rw [hRreload]; xperm_hyp hp)
          (fun _ hq => hq)
          (cpsTripleWithin_mono_nSteps (show 7 + (16 + nTail) ≤ 23 + nTail by omega)
            (cpsBranchWithin_merge_same_cr hbranch h_t h_f))
      · -- PARSE-FAIL arm: `bne` taken → status ≠ 0 exit.
        -- retParseFail needs x5/x6 as concrete scratch; peel them from `regOwn` first.
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (show cpsTripleWithin (24 + nTail) (D + 196) raIn fullCode
            (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
              (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) ** (Num ↦ₘ value) **
              regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              (IterPrev ↦ₘ prevVal) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
              ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
              ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) ** regOwn .x6) **
              regOwn .x5)
            (cvcnPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
              firstBadPtr csaved bigBytes lengths) from ?_)
        refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v5 => ?_)
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (show cpsTripleWithin (24 + nTail) (D + 196) raIn fullCode
            (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
              (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) ** (Num ↦ₘ value) **
              (.x5 ↦ᵣ v5) ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
              regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              (IterPrev ↦ₘ prevVal) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
              ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
              ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) ** regOwn .x6)
            (cvcnPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
              firstBadPtr csaved bigBytes lengths) from ?_)
        refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v6 => ?_)
        have hbne := bne_spec_gen_within .x10 .x0 (116 : BitVec 13) status (0 : Word) (D + 196)
        have hbneC := cpsBranchWithin_extend_code cvcn_mono
          (cpsBranchWithin_extend_code (cr' := cvcnCode)
            (CodeReq.ofProg_mem_at D (D + 196) cvcnProg 49 (.BNE .x10 .x0 (116 : BitVec 13))
              (by bv_omega) (by rw [cvcn_length]; decide) rfl
              (by rw [cvcn_length]; decide)) hbne)
        have htaken := cpsBranchWithin_takenStripPure2 hbneC (fun hp hq => by
          obtain ⟨_, _, _, _, _, hrest⟩ := hq
          exact absurd ((sepConj_pure_right _).1 hrest).2 hstatus)
        rw [show (D + 196) + signExtend13 (116 : BitVec 13) = D + 312 from by
          rw [show signExtend13 (116 : BitVec 13) = (116 : Word) from by decide]; bv_omega] at htaken
        have htakenF := cpsTripleWithin_frameR
          ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) ** (Num ↦ₘ value) **
            (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
            (IterPrev ↦ₘ prevVal) **
            ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
            wordArrayFrom lenBase 0 (lengths.take i) **
            wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
            bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
            (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
            ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
            ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) (by pcfx) htaken
        have hpfC := cpsTripleWithin_extend_code cvcn_mono
          (retParseFail sp0 spC raIn (BitVec.ofNat 64 i) firstBadPtr csaved
            ((.x0 ↦ᵣ (0 : Word)) ** (Num ↦ₘ value) ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
              regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
              regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterPrev ↦ₘ prevVal) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) ** (validPtr ↦ₘ (1 : Word)))
            (by pcfx) LinkRA (BitVec.ofNat 64 lengths.length) lenBase hdrBase validPtr prevVal
            status v5 v6 hspC hraSaved hret)
        have hcompose := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
          have hp1 : ((firstBadPtr ↦ₘ (0 : Word)) **
              ((.x20 ↦ᵣ firstBadPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ status) **
                (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ LinkRA) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
                (.x21 ↦ᵣ prevVal) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                ((.x0 ↦ᵣ (0 : Word)) ** (Num ↦ₘ value) ** regOwn .x7 ** regOwn .x11 **
                  regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
                  regOwn .x30 ** regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                    ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                  (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterPrev ↦ₘ prevVal) **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (validPtr ↦ₘ (1 : Word))))) h := by xperm_hyp hp
          have hp2 := sepConj_mono_left memIs_implies_memOwn h hp1
          xperm_hyp hp2) htakenF hpfC
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
          (cpsTripleWithin_mono_nSteps (show 1 + 14 ≤ 24 + nTail by omega) hcompose)
        refine Or.inr (Or.inr ⟨i, status, ?_⟩)
        refine (sepConj_pure_left h).mpr ⟨⟨hi, hprefix, ⟨value, hResult, hstatus⟩⟩, ?_⟩
        unfold commonRet payload
        rw [hsf, hraSaved, wordArray_split lenBase lengths i hi,
          EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen, ← hHB]
        have hp1 : ((.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ BitVec.ofNat 64 i) ** (Num ↦ₘ value) **
            (IterChild ↦ₘ hdrBaseAt hdrBase lengths i) **
            (IterI ↦ₘ BitVec.ofNat 64 i) ** (IterPrev ↦ₘ prevVal) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            ((.x10 ↦ᵣ status) ** (validPtr ↦ₘ (1 : Word)) **
              (firstBadPtr ↦ₘ BitVec.ofNat 64 i) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
              (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) ** (.x18 ↦ᵣ csaved.s2) **
              (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
              (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
              ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
              ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
              (.x0 ↦ᵣ (0 : Word)) **
              regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
              regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)))) h := by
          rw [← hLi]; xperm_hyp hq
        have hp2 := sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono
          (regIs_implies_regOwn .x6) (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
          (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _) (fun _ x => x))))))) h hp1
        xperm_hyp hp2

#print axioms cvcnIterDispatch

/-! ## One full loop iteration: guard → call → dispatch (`D+124 → raIn`, `1 ≤ i < N`)

    Strips `LoopInv i`'s `∃ prevVal` and its `⌜hdrNumOk (i-1) prevVal ∧ …⌝`
    binding, peels the K34 scratch cells, splits the arrays, then runs the entry
    half to K34's `flatPost` and the dispatch (threading the genuine `prevVal`
    into the cross-header compare). -/

set_option maxRecDepth 8000 in
theorem cvcnIter (sp0 spC hdrBase lenBase validPtr firstBadPtr raIn : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) (i nTail : Nat)
    (hi1 : 1 ≤ i)
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
    (htail : (∀ j, 1 ≤ j → j < i + 1 → numConsecutive hdrBase bigBytes lengths j) →
      cpsTripleWithin nTail (D + 124) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths (i + 1))
        (cvcnPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths)) :
    cpsTripleWithin ((1 + (16 + 1 + nCall)) + (24 + nTail)) (D + 124) raIn fullCode
      (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths i)
      (cvcnPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) := by
  have hLi : lengths[i]! = lengths[i] := getElem!_pos lengths i hi
  have hHB : hdrBaseAt hdrBase lengths i = hdrBase + BitVec.ofNat 64 (hdrOff lengths i) := rfl
  unfold LoopInv
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun prevVal => ?_)
  refine cpsTripleWithin_pure_pre (fun hP => ?_)
  obtain ⟨hprevOk, hprefix⟩ := hP
  set EBody : Assertion :=
    ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
      (.x6 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
      (.x20 ↦ᵣ firstBadPtr) ** (.x7 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ prevVal) **
      savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
      wordArrayFrom lenBase 0 (lengths.take i) **
      ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
      bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
      memOwn IterChild ** memOwn IterI ** memOwn IterPrev **
      regOwn .x1 ** regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
      stackFree (spC + signExtend12 (-32 : BitVec 12)) 8) with hEBody
  refine cpsTripleWithin_weaken (fun h hp => by
    unfold payload scratchRegs at hp
    rw [wordArray_split lenBase lengths i hi,
      EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen,
      ← hHB, ← hLi] at hp
    rw [hEBody]; xperm_hyp hp) (fun _ hq => hq)
    (show cpsTripleWithin ((1 + (16 + 1 + nCall)) + (24 + nTail)) (D + 124) raIn fullCode
      (((EBody ** memOwn Num) ** memOwn RfuOff) ** memOwn RfuLen)
      (cvcnPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) from ?_)
  refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldLen => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (show cpsTripleWithin ((1 + (16 + 1 + nCall)) + (24 + nTail)) (D + 124) raIn fullCode
      (((EBody ** (RfuLen ↦ₘ oldLen)) ** memOwn Num) ** memOwn RfuOff)
      (cvcnPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) from ?_)
  refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldOff => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (show cpsTripleWithin ((1 + (16 + 1 + nCall)) + (24 + nTail)) (D + 124) raIn fullCode
      (((EBody ** (RfuLen ↦ₘ oldLen)) ** (RfuOff ↦ₘ oldOff)) ** memOwn Num)
      (cvcnPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) from ?_)
  refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldOut => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by rw [hEBody] at hp; xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_seq_same_cr
      (cvcnIterEntry spC hdrBase lenBase validPtr firstBadPtr prevVal csaved bigBytes lengths i
        oldOut oldOff oldLen hi hN hsalign hslack hover hvalid)
      (cvcnIterDispatch sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr raIn prevVal csaved bigBytes lengths i oldOff oldLen nTail hi1 hi hN hspC rfl
        hraSaved hret halign hlen hprevOk hprefix htail))

#print axioms cvcnIter

end EvmAsm.Codegen.ChainValidateConsecutiveNumbersSpec
