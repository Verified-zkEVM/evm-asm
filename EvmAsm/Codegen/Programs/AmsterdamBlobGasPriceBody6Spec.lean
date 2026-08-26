/-
# exitDiv core for `amsterdam_blob_gas_price_u256` (#12851)

`exitdiv_core` covers instrs 201..224 @ `PriceK+804 .. PriceK+896`: the
5-instr prologue (divisor `D` from `x9`, `r := 0`, `t5 := sumPtr+40`,
limb counter 6) followed by the 6-limb restoring division
(`exitdiv_limbfold`, mirrored in Body5Spec), falling through to
`PriceK+900`. Registers `x19`/`x20` stay symbolic (`v19`/`v20`): the
swapDiv window swaps them every outer iteration, so their values at the
exit-tail are parity-dependent. No overflow exit — single fall exit.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody5Spec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody6Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody2Spec EvmAsm.Codegen.AmsterdamBlobGasPriceBody5Spec

set_option maxRecDepth 8000

/-- The 5-instr exitDiv prologue over a small core frame; `FR` absorbs the
rest of the routine state. -/
private theorem exitdiv_preamble_core (dv sumb : Word) (v5 v6 v30 v31 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 5 (PriceK + 804) (PriceK + 824) priceCode
      (((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ v5)) ** ((.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x22 ↦ᵣ sumb) ** FR))
      (((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ (sumb + signExtend12 (40 : BitVec 12))) ** (.x31 ↦ᵣ (6 : Word)) ** (.x22 ↦ᵣ sumb) ** FR)) := by
  have h1 := mv_spec_gen_within .x5 .x9 dv v5 (PriceK + 804) (by decide)
  have h1F : cpsTripleWithin 1 (PriceK + 804) (PriceK + 808) priceCode
      (((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ v5)) ** ((.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x22 ↦ᵣ sumb) ** FR))
      (((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv)) ** ((.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x22 ↦ᵣ sumb) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h1)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[201]'(by decide) = .MV .x5 .x9 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 804) amsterdamBlobGasPriceU256_prog
      201 (.MV .x5 .x9) (by decide) (by decide) hins (by decide) a i hi
  have h2 := mv_spec_gen_within .x6 .x0 (0 : Word) v6 (PriceK + 808) (by decide)
  have h2F : cpsTripleWithin 1 (PriceK + 808) (PriceK + 812) priceCode
      (((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6)) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x22 ↦ᵣ sumb) ** FR))
      (((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word))) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x22 ↦ᵣ sumb) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h2)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[202]'(by decide) = .MV .x6 .x0 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 808) amsterdamBlobGasPriceU256_prog
      202 (.MV .x6 .x0) (by decide) (by decide) hins (by decide) a i hi
  have h2F' : cpsTripleWithin 1 (PriceK + 808) (PriceK + 812) priceCode
      (((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv)) ** ((.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x22 ↦ᵣ sumb) ** FR))
      (((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv)) ** ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x22 ↦ᵣ sumb) ** FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (by intro h hx; xperm_hyp hx) h2F
  have hs1 := cpsTripleWithin_seq_same_cr h1F h2F'
  have h3 := mv_spec_gen_within .x30 .x22 sumb v30 (PriceK + 812) (by decide)
  have h3F : cpsTripleWithin 1 (PriceK + 812) (PriceK + 816) priceCode
      (((.x22 ↦ᵣ sumb) ** (.x30 ↦ᵣ v30)) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ v31) ** FR))
      (((.x22 ↦ᵣ sumb) ** (.x30 ↦ᵣ sumb)) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ v31) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h3)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[203]'(by decide) = .MV .x30 .x22 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 812) amsterdamBlobGasPriceU256_prog
      203 (.MV .x30 .x22) (by decide) (by decide) hins (by decide) a i hi
  have h3F' : cpsTripleWithin 1 (PriceK + 812) (PriceK + 816) priceCode
      (((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv)) ** ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x22 ↦ᵣ sumb) ** FR))
      (((.x22 ↦ᵣ sumb) ** (.x30 ↦ᵣ sumb)) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ v31) ** FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) h3F
  have hs2 := cpsTripleWithin_seq_same_cr hs1 h3F'
  have h4 := addi_spec_gen_same_within .x30 sumb (40 : BitVec 12) (PriceK + 816) (by decide)
  have h4F : cpsTripleWithin 1 (PriceK + 816) (PriceK + 820) priceCode
      ((.x30 ↦ᵣ sumb) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x22 ↦ᵣ sumb) ** (.x31 ↦ᵣ v31) ** FR))
      ((.x30 ↦ᵣ (sumb + signExtend12 (40 : BitVec 12))) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x22 ↦ᵣ sumb) ** (.x31 ↦ᵣ v31) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h4)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[204]'(by decide) = .ADDI .x30 .x30 (40 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 816) amsterdamBlobGasPriceU256_prog
      204 (.ADDI .x30 .x30 (40 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi
  have h4F' : cpsTripleWithin 1 (PriceK + 816) (PriceK + 820) priceCode
      (((.x22 ↦ᵣ sumb) ** (.x30 ↦ᵣ sumb)) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ v31) ** FR))
      (((.x22 ↦ᵣ sumb) ** (.x30 ↦ᵣ (sumb + signExtend12 (40 : BitVec 12)))) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ v31) ** FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (by intro h hx; xperm_hyp hx) h4F
  have hs3 := cpsTripleWithin_seq_same_cr hs2 h4F'
  have h5 := li_spec_gen_within .x31 v31 (6 : Word) (PriceK + 820) (by decide)
  have h5F : cpsTripleWithin 1 (PriceK + 820) (PriceK + 824) priceCode
      ((.x31 ↦ᵣ v31) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x22 ↦ᵣ sumb) ** (.x30 ↦ᵣ (sumb + signExtend12 (40 : BitVec 12))) ** FR))
      ((.x31 ↦ᵣ (6 : Word)) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x22 ↦ᵣ sumb) ** (.x30 ↦ᵣ (sumb + signExtend12 (40 : BitVec 12))) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h5)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[205]'(by decide) = .LI .x31 (6 : Word) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 820) amsterdamBlobGasPriceU256_prog
      205 (.LI .x31 (6 : Word)) (by decide) (by decide) hins (by decide) a i hi
  have h5F' : cpsTripleWithin 1 (PriceK + 820) (PriceK + 824) priceCode
      (((.x22 ↦ᵣ sumb) ** (.x30 ↦ᵣ (sumb + signExtend12 (40 : BitVec 12)))) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ v31) ** FR))
      (((.x22 ↦ᵣ sumb) ** (.x30 ↦ᵣ (sumb + signExtend12 (40 : BitVec 12))) ** (.x31 ↦ᵣ (6 : Word))) ** ((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (by intro h hx; xperm_hyp hx) h5F
  have hs4 := cpsTripleWithin_seq_same_cr hs3 h5F'
  refine cpsTripleWithin_weaken (fun _ hx => hx) (by intro h hx; xperm_hyp hx) hs4

/-- Same 5-instr prologue at the full routine state (`REST` absorbs every
atom the core does not mention). -/
theorem exitdiv_preamble (dv sumb : Word) (v5 v6 v30 v31 : Word)
    (REST : Assertion) (hREST : REST.pcFree) :
    cpsTripleWithin 5 (PriceK + 804) (PriceK + 824) priceCode
      (((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x22 ↦ᵣ sumb) ** REST))
      (((.x9 ↦ᵣ dv) ** (.x5 ↦ᵣ dv) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ (sumb + signExtend12 (40 : BitVec 12))) ** (.x31 ↦ᵣ (6 : Word)) ** (.x22 ↦ᵣ sumb) ** REST)) := by
  refine cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
    (by intro h hx; xperm_hyp hx)
    (exitdiv_preamble_core dv sumb v5 v6 v30 v31 REST hREST)

/-- exitDiv window: prologue + the 6-limb restoring division of the sum
buffer by `D`, as one triple `PriceK+804 -> PriceK+900` (3887 = 5 + 3882).
The postcondition pins the quotient limbs over the sum cells (top-down),
the final remainder/divstate projections, and leaves the acc/prod cells
untouched. `x19`/`x20` stay symbolic (parity-dependent at the exit tail). -/
theorem exitdiv_core (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v19 v20 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 3887 (PriceK + 804) (PriceK + 900) priceCode
      ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) **
        (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)
      ((((.x6 ↦ᵣ (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (0 : Word) s5 (0 : Word) 64).1 s4 (0 : Word) 64).1 s3 (0 : Word) 64).1 s2 (0 : Word) 64).1 s1 (0 : Word) 64).1 s0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (0 : Word) s5 (0 : Word) 64).1 s4 (0 : Word) 64).1 s3 (0 : Word) 64).1 s2 (0 : Word) 64).1 s1 (0 : Word) 64).1 s0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (0 : Word) s5 (0 : Word) 64).1 s4 (0 : Word) 64).1 s3 (0 : Word) 64).1 s2 (0 : Word) 64).1 s1 (0 : Word) 64).1 s0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ taylorDW)) ** (.x30 ↦ᵣ (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (0 : Word) s5 (0 : Word) 64).1 s4 (0 : Word) 64).1 s3 (0 : Word) 64).1 s2 (0 : Word) 64).1 s1 (0 : Word) 64).1 s0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst taylorDW (0 : Word) s5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst taylorDW (divst taylorDW (0 : Word) s5 (0 : Word) 64).1 s4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst taylorDW (divst taylorDW (divst taylorDW (0 : Word) s5 (0 : Word) 64).1 s4 (0 : Word) 64).1 s3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (0 : Word) s5 (0 : Word) 64).1 s4 (0 : Word) 64).1 s3 (0 : Word) 64).1 s2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (divst taylorDW (0 : Word) s5 (0 : Word) 64).1 s4 (0 : Word) 64).1 s3 (0 : Word) 64).1 s2 (0 : Word) 64).1 s1 (0 : Word) 64).2.2) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        FR))) := by
  have hP5 := exitdiv_preamble taylorDW (newSp + signExtend12 (160 : BitVec 12))
    v5 v6 v30 v31 ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) **
        (.x21 ↦ᵣ outPtr) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR) (by pcFree; exact hFR)
  have hP5lf : cpsTripleWithin 5 (PriceK + 804) (PriceK + 824) priceCode
      ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) **
        (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)
      ((((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x5 ↦ᵣ taylorDW)) ** (.x30 ↦ᵣ ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12))) ** (.x31 ↦ᵣ (6 : Word)) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
      (by intro h hx; xperm_hyp hx) hP5
  have hP5lcnt : cpsTripleWithin 5 (PriceK + 804) (PriceK + 824) priceCode
      ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) **
        (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)
      ((((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x5 ↦ᵣ taylorDW)) ** (.x30 ↦ᵣ ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        FR))) := by
    rw [show lcnt 0 = (6 : Word) from rfl]
    exact hP5lf
  exact cpsTripleWithin_seq_same_cr hP5lcnt
    (exitdiv_limbfold taylorDW (newSp + signExtend12 (160 : BitVec 12))
      s5 s4 s3 s2 s1 s0 v7 v28 v29 ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        FR) (by pcFree; exact hFR))

#print axioms exitdiv_core
