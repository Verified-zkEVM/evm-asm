/-
  Per-iteration straight-line building blocks for
  `chain_validate_increasing_timestamps`.

  Builds on `ChainValidateIncreasingTimestampsSpec` (model, prologue, epilogue,
  exit blocks).  The distinguishing feature of this CROSS-HEADER accessor is the
  spill/reload of the iterator state — `{base_i, i, prev = ts[i-1]}` — through
  the scratch cells `cvit_iter_child` / `cvit_iter_i` / `cvit_iter_prev` around
  each `rlp_field_to_u64` (field 11) call, and the `BGEU x29 x28` comparison of
  the reloaded `prev` (`cvit_iter_prev`) against the freshly-decoded `cur`
  (`cvit_ts`).  The `prev` cell genuinely holds the ACTUAL decoded timestamp of
  header `i-1` (tied to K34's `Result`), so the invariant threads the real value.
-/

import EvmAsm.Codegen.Programs.ChainValidateIncreasingTimestampsSpec
import EvmAsm.Evm64.StateAssertions

namespace EvmAsm.Codegen.ChainValidateIncreasingTimestampsSpec

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
    (`D+164`).  Materializes `*cvit_iter_child := base_i`, `*cvit_iter_i := i`,
    and — crucially — `*cvit_iter_prev := prev` where `prev` is `x21`, the
    timestamp decoded from header `i-1`. -/

set_option maxRecDepth 8000 in
theorem cvitSpill (hbi iW prevVal old5 : Word) :
    cpsTripleWithin 9 (D + 128) (D + 164) cvitCode
      ((.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x21 ↦ᵣ prevVal) **
        memOwn IterChild ** memOwn IterI ** memOwn IterPrev)
      ((.x5 ↦ᵣ IterPrev) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x21 ↦ᵣ prevVal) **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal)) := by
  have hla32 := la_materialize_within .x5 old5 (D + 128) IterChild (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 128) cvitProg 32 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 128) IterChild)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 132) cvitProg 33 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 128) IterChild)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s34 := sd_spec_gen_own_within .x5 .x6 IterChild hbi (0 : BitVec 12) (D + 136)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterChild + (0 : Word) = IterChild from by bv_omega] at s34
  have s34' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 136) cvitProg 34 (.SD .x5 .x6 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s34
  have hla35 := la_materialize_within .x5 IterChild (D + 140) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 140) cvitProg 35 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 140) IterI)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 144) cvitProg 36 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 140) IterI)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s37 := sd_spec_gen_own_within .x5 .x7 IterI iW (0 : BitVec 12) (D + 148)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s37
  have s37' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 148) cvitProg 37 (.SD .x5 .x7 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s37
  have hla38 := la_materialize_within .x5 IterI (D + 152) IterPrev (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 152) cvitProg 38 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 152) IterPrev)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 156) cvitProg 39 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 152) IterPrev)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s40 := sd_spec_gen_own_within .x5 .x21 IterPrev prevVal (0 : BitVec 12) (D + 160)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPrev + (0 : Word) = IterPrev from by bv_omega] at s40
  have s40' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 160) cvitProg 40 (.SD .x5 .x21 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s40
  runBlock hla32 s34' hla35 s37' hla38 s40'

#print axioms cvitSpill

/-! ## Reload block (instructions 50--55): load `cur` and `prev` for the compare

    Runs on the K34-success (`bne` not-taken) path from `D+200` to `D+224`
    (just before the `BGEU`): `x28 := *cvit_ts` (the freshly-decoded `ts[i]`,
    `cur`) and `x29 := *cvit_iter_prev` (the saved `ts[i-1]`, `prev`). -/

set_option maxRecDepth 8000 in
theorem cvitReload (curVal prevVal old5 o28 o29 : Word) :
    cpsTripleWithin 6 (D + 200) (D + 224) cvitCode
      ((.x5 ↦ᵣ old5) ** (.x28 ↦ᵣ o28) ** (.x29 ↦ᵣ o29) **
        (Ts ↦ₘ curVal) ** (IterPrev ↦ₘ prevVal))
      ((.x5 ↦ᵣ IterPrev) ** (.x28 ↦ᵣ curVal) ** (.x29 ↦ᵣ prevVal) **
        (Ts ↦ₘ curVal) ** (IterPrev ↦ₘ prevVal)) := by
  have hla50 := la_materialize_within .x5 old5 (D + 200) Ts (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 200) cvitProg 50 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 200) Ts)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 204) cvitProg 51 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 200) Ts)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s52 := ld_spec_gen_within .x28 .x5 Ts o28 curVal (0 : BitVec 12) (D + 208) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show Ts + (0 : Word) = Ts from by bv_omega] at s52
  have s52' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 208) cvitProg 52 (.LD .x28 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s52
  have hla53 := la_materialize_within .x5 Ts (D + 212) IterPrev (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 212) cvitProg 53 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 212) IterPrev)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 216) cvitProg 54 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 212) IterPrev)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s55 := ld_spec_gen_within .x29 .x5 IterPrev o29 prevVal (0 : BitVec 12) (D + 220) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPrev + (0 : Word) = IterPrev from by bv_omega] at s55
  have s55' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 220) cvitProg 55 (.LD .x29 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s55
  runBlock hla50 s52' hla53 s55'

#print axioms cvitReload

/-! ## Advance block (instructions 57--69): update `prev`, step iterator, loop

    On the increasing (`BGEU` not-taken, `prev <ᵤ cur`) path from `D+228`:
    reload `x6 := base_i` and `x7 := i`, set `x21 := cur` (the new `prev` for the
    next iteration — the just-decoded `ts[i]`), advance `x6 += lengths[i]`,
    `x7 += 1`, then `jal x0, -152` back to the loop guard at `D+124`. -/

set_option maxRecDepth 8000 in
theorem cvitAdvance (hbi lenBase iW curVal old5 o6 o7 o21 o30 o31 : Word) (Li : Nat) :
    cpsTripleWithin 13 (D + 228) (D + 124) cvitCode
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
  have hla57 := la_materialize_within .x5 old5 (D + 228) IterChild (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 228) cvitProg 57 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 228) IterChild)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 232) cvitProg 58 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 228) IterChild)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s59 := ld_spec_gen_within .x6 .x5 IterChild o6 hbi (0 : BitVec 12) (D + 236) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterChild + (0 : Word) = IterChild from by bv_omega] at s59
  have s59' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 236) cvitProg 59 (.LD .x6 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s59
  have hla60 := la_materialize_within .x5 IterChild (D + 240) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 240) cvitProg 60 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 240) IterI)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 244) cvitProg 61 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 240) IterI)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s62 := ld_spec_gen_within .x7 .x5 IterI o7 iW (0 : BitVec 12) (D + 248) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s62
  have s62' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 248) cvitProg 62 (.LD .x7 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s62
  have s63 := mv_spec_gen_within .x21 .x28 curVal o21 (D + 252) (by decide)
  have s63' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 252) cvitProg 63 (.MV .x21 .x28)
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s63
  have s64 := slli_spec_gen_within .x30 .x7 o30 iW (3 : BitVec 6) (D + 256) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s64
  have s64' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 256) cvitProg 64 (.SLLI .x30 .x7 (3 : BitVec 6))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s64
  have s65 := add_spec_gen_rd_eq_rs2_within .x30 .x9 lenBase (iW <<< 3) (D + 260) (by decide)
  have s65' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 260) cvitProg 65 (.ADD .x30 .x9 .x30)
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s65
  have s66 := ld_spec_gen_within .x31 .x30 (lenBase + (iW <<< 3)) o31 (BitVec.ofNat 64 Li)
    (0 : BitVec 12) (D + 264) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iW <<< 3)) + (0 : Word) = lenBase + (iW <<< 3) from by bv_omega] at s66
  have s66' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 264) cvitProg 66 (.LD .x31 .x30 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s66
  have s67 := add_spec_gen_rd_eq_rs1_within .x6 .x31 hbi (BitVec.ofNat 64 Li) (D + 268) (by decide)
  have s67' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 268) cvitProg 67 (.ADD .x6 .x6 .x31)
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s67
  have s68 := addi_spec_gen_same_within .x7 iW (1 : BitVec 12) (D + 272) (by decide)
  have s68' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 272) cvitProg 68 (.ADDI .x7 .x7 (1 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s68
  have s69 := jal_x0_spec_gen_within (-152 : BitVec 21) (D + 276)
  rw [show (D + 276) + signExtend21 (-152 : BitVec 21) = D + 124 from by
    rw [show signExtend21 (-152 : BitVec 21) = (-152 : Word) from by decide]; bv_omega] at s69
  have s69' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 276) cvitProg 69 (.JAL .x0 (-152 : BitVec 21))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s69
  runBlock hla57 s59' hla60 s62' s63' s64' s65' s66' s67' s68' s69'

#print axioms cvitAdvance

/-! ## Loop-body argument setup (instructions 41--47): load call args

    From just after the spill (`D+164`) to just before the `jal` (`D+192`):
    `x28 := lenBase + i<<3`, `x11 := lengths[i]`, `x10 := base_i`, `x12 := 11`,
    `x13 := Ts` (the K34 output cell). -/

set_option maxRecDepth 8000 in
theorem cvitArgSetup (hbi lenBase iW : Word) (Li : Nat)
    (old10 old11 old12 old13 old28 : Word) :
    cpsTripleWithin 7 (D + 164) (D + 192) cvitCode
      ((.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x9 ↦ᵣ lenBase) **
        (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) ** (.x13 ↦ᵣ old13) **
        (.x28 ↦ᵣ old28) ** ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x9 ↦ᵣ lenBase) **
        (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (11 : Word)) **
        (.x13 ↦ᵣ Ts) ** (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  have s41 := slli_spec_gen_within .x28 .x7 old28 iW (3 : BitVec 6) (D + 164) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s41
  have s41' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 164) cvitProg 41 (.SLLI .x28 .x7 (3 : BitVec 6))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s41
  have s42 := add_spec_gen_rd_eq_rs2_within .x28 .x9 lenBase (iW <<< 3) (D + 168) (by decide)
  have s42' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 168) cvitProg 42 (.ADD .x28 .x9 .x28)
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s42
  have s43 := ld_spec_gen_within .x11 .x28 (lenBase + (iW <<< 3)) old11 (BitVec.ofNat 64 Li)
    (0 : BitVec 12) (D + 172) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iW <<< 3)) + (0 : Word) = lenBase + (iW <<< 3) from by bv_omega] at s43
  have s43' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 172) cvitProg 43 (.LD .x11 .x28 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s43
  have s44 := mv_spec_gen_within .x10 .x6 hbi old10 (D + 176) (by decide)
  have s44' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 176) cvitProg 44 (.MV .x10 .x6)
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s44
  have s45 := li_spec_gen_within .x12 old12 (11 : Word) (D + 180) (by decide)
  have s45' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 180) cvitProg 45 (.LI .x12 (11 : Word))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s45
  have hla46 := la_materialize_within .x13 old13 (D + 184) Ts (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 184) cvitProg 46 (.AUIPC .x13 (EvmAsm.Rv64.laHi (D + 184) Ts)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 188) cvitProg 47 (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (D + 184) Ts)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  runBlock s41' s42' s43' s44' s45' hla46

#print axioms cvitArgSetup

/-! ## Header-0 argument setup (instructions 18--22): load call args for header 0

    From the `N ≥ 2` fall-through (`D+72`) to just before the header-0 `jal`
    (`D+92`): `x11 := lengths[0]` (loaded directly from `*lenBase`),
    `x10 := hdrBase` (header 0's base), `x12 := 11`, `x13 := Ts`. -/

set_option maxRecDepth 8000 in
theorem cvitHdr0Setup (hdrBase lenBase : Word) (L0 : Nat) (old10 old11 old12 old13 : Word) :
    cpsTripleWithin 5 (D + 72) (D + 92) cvitCode
      ((.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x12 ↦ᵣ old12) ** (.x13 ↦ᵣ old13) ** (lenBase ↦ₘ BitVec.ofNat 64 L0))
      ((.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x10 ↦ᵣ hdrBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 L0) ** (.x12 ↦ᵣ (11 : Word)) ** (.x13 ↦ᵣ Ts) **
        (lenBase ↦ₘ BitVec.ofNat 64 L0)) := by
  have s18 := ld_spec_gen_within .x11 .x9 lenBase old11 (BitVec.ofNat 64 L0)
    (0 : BitVec 12) (D + 72) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show lenBase + (0 : Word) = lenBase from by bv_omega] at s18
  have s18' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 72) cvitProg 18 (.LD .x11 .x9 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s18
  have s19 := mv_spec_gen_within .x10 .x18 hdrBase old10 (D + 76) (by decide)
  have s19' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 76) cvitProg 19 (.MV .x10 .x18)
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s19
  have s20 := li_spec_gen_within .x12 old12 (11 : Word) (D + 80) (by decide)
  have s20' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 80) cvitProg 20 (.LI .x12 (11 : Word))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s20
  have hla21 := la_materialize_within .x13 old13 (D + 84) Ts (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 84) cvitProg 21 (.AUIPC .x13 (EvmAsm.Rv64.laHi (D + 84) Ts)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 88) cvitProg 22 (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (D + 84) Ts)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  runBlock s18' s19' s20' hla21

#print axioms cvitHdr0Setup

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

    Composes `cvitSpill` (spill `{child, i, prev}`) with `cvitArgSetup` (load the
    K34 call args) into one block from `D+128` to `D+192`. -/

set_option maxRecDepth 8000 in
theorem cvitSetup (hbi lenBase iW prevVal : Word) (Li : Nat)
    (old5 old10 old11 old12 old13 old28 : Word) :
    cpsTripleWithin 16 (D + 128) (D + 192) cvitCode
      ((.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x21 ↦ᵣ prevVal) **
        (.x9 ↦ᵣ lenBase) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        (.x13 ↦ᵣ old13) ** (.x28 ↦ᵣ old28) **
        memOwn IterChild ** memOwn IterI ** memOwn IterPrev **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x5 ↦ᵣ IterPrev) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x21 ↦ᵣ prevVal) **
        (.x9 ↦ᵣ lenBase) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
        (.x12 ↦ᵣ (11 : Word)) ** (.x13 ↦ᵣ Ts) ** (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  have hspillF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ lenBase) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
      (.x13 ↦ᵣ old13) ** (.x28 ↦ᵣ old28) ** ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
    (by pcfx) (cvitSpill hbi iW prevVal old5)
  have hargsF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ IterPrev) ** (.x21 ↦ᵣ prevVal) **
      (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal))
    (by pcfx) (cvitArgSetup hbi lenBase iW Li old10 old11 old12 old13 old28)
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hspillF hargsF)

#print axioms cvitSetup

/-! ## K34's whole-routine step count for field index 11. -/
abbrev nCall : Nat :=
  (7 + 4 + (1 + ((12 + ((85 + 93 * (11 + 2)) + 6)) + 9)))
    + ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5)

/-! ## Call block (instructions 32--48 + K34): setup ;; jal ;; rlp_field_to_u64

    From the loop-body entry (`D+128`) to the return site (`D+196`), producing
    K34's `flatPost` for header `hbi` (field 11).  `x18` holds the ORIGINAL
    `hdrBase` (K34's saved `s2`), `x21` the threaded `prev` (saved `s5`); the
    header base being decoded is `hbi` (moved into `x10`). -/

set_option maxRecDepth 8000 in
theorem cvitCall (spC hdrBase lenBase hbi iW validPtr firstBadPtr prevVal : Word) (Li : Nat)
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
        (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        bytesRegion hbi bytes ** savedFrame spC csaved)
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Ts, hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
          bytes Li 11 **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) := by
  set calleeNewSp : Word := spC + signExtend12 (-32 : BitVec 12) with hcalleeNewSp
  -- Setup block, lifted to fullCode, framed with the callee footprint.
  have hsetup := cpsTripleWithin_extend_code cvit_mono
    (cvitSetup hbi lenBase iW prevVal Li old5 o10 o11 o12 o13 o28)
  have hsetupF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
      (.x20 ↦ᵣ firstBadPtr) ** (.x14 ↦ᵣ old14) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x1 ↦ᵣ oldX1) ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hbi bytes ** savedFrame spC csaved)
    (by pcfx) hsetup
  -- [48] jal x1, rlp_field_to_u64
  have hjal := jal_link_spec_within
    (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64
      (GuestAddrs.chain_validate_increasing_timestamps + 192)) (D + 192) oldX1
  rw [show (D + 192) + signExtend21 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64
      (GuestAddrs.chain_validate_increasing_timestamps + 192))
      = EvmAsm.Codegen.RlpFieldToU64SAsm.B from by decide,
    show (D + 192 + 4 : Word) = LinkRA from by
      change (D + 192 + 4 : Word) = D + 196; bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code cvit_mono
    (cpsTripleWithin_extend_code (cr' := cvitCode)
      (CodeReq.ofProg_mem_at D (D + 192) cvitProg 48
        (.JAL .x1 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64
          (GuestAddrs.chain_validate_increasing_timestamps + 192))) (by bv_omega)
        (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) **
      (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
      (.x5 ↦ᵣ IterPrev) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
      (.x12 ↦ᵣ (11 : Word)) ** (.x13 ↦ᵣ Ts) ** (.x14 ↦ᵣ old14) **
      (.x28 ↦ᵣ (lenBase + (iW <<< 3))) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hbi bytes **
      (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal) **
      ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)
    (by pcfx) hjalC
  -- K34 flat callee, lifted to fullCode, framed with the spill/array/chain payload.
  have hcallee0 := EvmAsm.Codegen.RlpFieldToU64SAsm.rlpFieldToU64_flat_spec_within
    spC calleeNewSp hbi (BitVec.ofNat 64 Li) (11 : Word) Ts oldOut oldOff oldLen old14
    (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved) hdrBase validPtr firstBadPtr
    prevVal bytes Li 11
    hcalleeNewSp rfl (by decide) (by decide)
    hsalign hslack hover hvalid (by show LinkRA &&& ~~~(1 : Word) = LinkRA; decide)
  have hcalleeC := cpsTripleWithin_extend_code k34_mono hcallee0
  -- Present K34's entry footprint as explicit atoms, with x5/x6/x7/x28 shown owned.
  have hcallee : cpsTripleWithin nCall EvmAsm.Codegen.RlpFieldToU64SAsm.B LinkRA fullCode
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
          (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
          (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (11 : Word)) **
          (.x13 ↦ᵣ Ts) ** (.x14 ↦ᵣ old14) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
          stackFree calleeNewSp 8 ** bytesRegion hbi bytes **
          (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen)))
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC calleeNewSp hbi oldOff oldLen
          (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Ts, hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
          bytes Li 11) :=
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
        (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (11 : Word)) **
        (.x13 ↦ᵣ Ts) ** (.x14 ↦ᵣ old14) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
        stackFree calleeNewSp 8 ** bytesRegion hbi bytes **
        (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)) h := by
    xperm_hyp hp
  have hp'' := sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x)))) h hp'
  xperm_hyp hp''

#print axioms cvitCall

/-! ## Call block with the consumed scratch registers owned

    `cvitCall` with `x1/x5/x10/x11/x12/x13/x14/x28` presented as `regOwn`,
    matching how they sit in `LoopInv`/`scratchRegs`. -/

set_option maxRecDepth 8000 in
theorem cvitCallOwned (spC hdrBase lenBase hbi iW validPtr firstBadPtr prevVal : Word) (Li : Nat)
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
          (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
          bytesRegion hbi bytes ** savedFrame spC csaved) **
        regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28) ** regOwn .x1)
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Ts, hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
          bytes Li 11 **
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
          (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
          bytesRegion hbi bytes ** savedFrame spC csaved) ** (.x1 ↦ᵣ v1)) **
        regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28)
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Ts, hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
          bytes Li 11 **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) from ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_of_forall_regIs_to_regOwn7
    (fun v5 v10 v11 v12 v13 v14 v28 => ?_)
  exact cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => by xperm_hyp h)
    (cvitCall spC hdrBase lenBase hbi iW validPtr firstBadPtr prevVal Li nN oldOut oldOff oldLen
      v14 v1 v5 v10 v11 v12 v13 v28 bytes csaved hsalign hslack hover hvalid)

#print axioms cvitCallOwned

/-! ## Normalizing K34's `flatPost` into a single Result-carrying assertion

    `dispNorm status value` is the common owned shape both `flatPost` arms weaken
    to; it exposes `x10 = status` (for the `bne`) and `Ts ↦ value` (for the
    reload) while owning the callee-perturbed remainder.  The restored saved regs
    are `x18 = hdrBase` (`s2`), `x19 = validPtr` (`s3`), `x20 = firstBadPtr`
    (`s4`), `x21 = prev` (`s5`). -/
def dispNorm (spC calleeNewSp hbi hdrBase validPtr firstBadPtr nN lenBase prevVal
    value status : Word) (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
  (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
  (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (Ts ↦ₘ value) **
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
      (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, Ts, hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
      bytes Li 11) h →
    (∃ status value,
      (dispNorm spC (spC + signExtend12 (-32 : BitVec 12)) hbi hdrBase validPtr firstBadPtr nN
          lenBase prevVal value status bytes **
        ⌜EvmAsm.Codegen.RlpFieldToU64SAsm.Result bytes hbi Li 11 status value⌝) h) := by
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
          (.x10 ↦ᵣ wrapperStatus) ** (.x0 ↦ᵣ (0 : Word)) ** (Ts ↦ₘ outputValue) **
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
          (.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (Ts ↦ₘ (0 : Word)) **
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

end EvmAsm.Codegen.ChainValidateIncreasingTimestampsSpec
