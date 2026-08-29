/-
Tail window (instrs 225..241, PriceK+900..964) of `amsterdam_blob_gas_price_u256`
(#12851): high-limb check (quotient limbs 4,5 must be zero), then the 32-iteration
byte copy `out[k] = sumByte[31-k]` (big-endian), then status + jump to the
epilogue at PriceK+968, or status 1 on the overflow arm. Copy-loop cells use
ofNat addressing; the entry converts the two check-phase se12 cells once.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody5Spec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody6Spec
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody5Spec
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

end EvmAsm.Codegen.AmsterdamBlobGasPriceBody6Spec

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody5Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody6Spec

set_option maxRecDepth 8000

/-- Out cell j after b+1 byte-writes of lanes 7-b..7 of source limb sv. -/
def pfill (sv o : Word) : Nat → Word
  | 0 => o
  | b + 1 => replaceByte (pfill sv o b) b (((extractByte sv (7 - b)).zeroExtend 64).truncate 8)

theorem pure_drop_mid {L1 L2 : Assertion} {P : Prop} {R : Assertion} :
    ∀ h, ((L1 ** (L2 ** ⌜P⌝)) ** R) h → ((L1 ** L2) ** R) h := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hl1, hr⟩ := hx
  obtain ⟨g1, g2, gd, gu, hg1, hg2⟩ := hl1
  rw [sepConj_comm'] at hg2
  obtain ⟨e, g2', ed, eu, he, hL2⟩ := hg2
  obtain ⟨heE, -⟩ := he
  have hg2eq : g2 = g2' := by rw [← eu, heE]; exact PartialState.union_empty_left
  rw [hg2eq] at gd gu
  exact ⟨h1, h2, hd, hu, ⟨g1, g2', gd, gu, hg1, hL2⟩, hr⟩

/-- Sequence a triple onto the taken exit of a branch (same CodeReq). Dual of
`cpsBranchWithin_seq_cpsTripleWithin_same_cr`. Bounds add. -/
theorem branch_seqTaken_same_cr {nSteps1 nSteps2 : Nat}
    {entry mid target exit_f : Word} {cr : CodeReq}
    {P Q_t1 Q_f1 Q_t2 : Assertion}
    (h1 : cpsBranchWithin nSteps1 entry cr P mid Q_t1 exit_f Q_f1)
    (h2 : cpsTripleWithin nSteps2 mid target cr Q_t1 Q_t2) :
    cpsBranchWithin (nSteps1 + nSteps2) entry cr P target Q_t2 exit_f Q_f1 := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hbranch1⟩ := h1 R hR s hcr hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hQ_t2R⟩ := h2 R hR s1 hcr' hQ_t1R hpc_t1
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
      Or.inl ⟨hpc2, hQ_t2R⟩⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right nSteps1 nSteps2), s1, hstep1,
      Or.inr ⟨hpc_f1, hQ_f1R⟩⟩

/-- Frame carried through copy-loop rounds 0..7 (out cell 0 is owned by the active round). -/
@[reducible] def tailFR0 (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 _q3 q4 q5 _o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (v18 v19 v20 v31 : Word) (FR : Assertion) : Assertion :=
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
     (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
     (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
     (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
     (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
     (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
     frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
     ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) ** ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) **
     ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR)

/-- Frame carried through copy-loop rounds 8..15 (out cell 1 is owned by the active round). -/
@[reducible] def tailFR1 (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 _q2 q3 q4 q5 o0 _o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (v18 v19 v20 v31 : Word) (FR : Assertion) : Assertion :=
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
     (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
     (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
     (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
     (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
     (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
     frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
     ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) **
     ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR)

/-- Frame carried through copy-loop rounds 16..23 (out cell 2 is owned by the active round). -/
@[reducible] def tailFR2 (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 _q1 q2 q3 q4 q5 o0 o1 _o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (v18 v19 v20 v31 : Word) (FR : Assertion) : Assertion :=
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
     (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
     (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
     (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
     (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
     (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
     frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
     ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
     ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR)

/-- Frame carried through copy-loop rounds 24..31 (out cell 3 is owned by the active round). -/
@[reducible] def tailFR3 (newSp excess outPtr : Word) (vals : Reg → Word)
    (_q0 q1 q2 q3 q4 q5 o0 o1 o2 _o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (v18 v19 v20 v31 : Word) (FR : Assertion) : Assertion :=
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
     (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
     (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
     (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
     (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
     (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
     frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
     ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
     ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR)

theorem tailFR0_eq (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (v18 v19 v20 v31 : Word) (FR : Assertion) :
    tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR =
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
     (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
     (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
     (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
     (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
     (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
     frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
     ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) ** ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) **
     ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR) := rfl

theorem tailFR1_eq (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (v18 v19 v20 v31 : Word) (FR : Assertion) :
    tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR =
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
     (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
     (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
     (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
     (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
     (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
     frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
     ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) **
     ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR) := rfl

theorem tailFR2_eq (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (v18 v19 v20 v31 : Word) (FR : Assertion) :
    tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR =
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
     (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
     (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
     (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
     (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
     (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
     frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
     ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
     ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR) := rfl

theorem tailFR3_eq (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (v18 v19 v20 v31 : Word) (FR : Assertion) :
    tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR =
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
     (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
     (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
     (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
     (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
     (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
     frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
     (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
     (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
     (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
     ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
     ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR) := rfl

/-- Copy-loop round precondition: 7 pins + read/write cells + frame.
`rdOff`/`wrOff` are the read/write dword byte-offsets (multiples of 8). -/
def preS (sumb outPtr v7x v28x w29x sv o : Word) (rdOff wrOff k : Nat)
    (F : Assertion) : Assertion :=
  (((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) ** (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7x) **
    (.x28 ↦ᵣ v28x) ** (.x29 ↦ᵣ w29x) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
    ((sumb + BitVec.ofNat 64 rdOff) ↦ₘ sv) **
    ((outPtr + BitVec.ofNat 64 wrOff) ↦ₘ o)) ** F)

theorem preS_eq (sumb outPtr v7x v28x w29x sv o : Word) (rdOff wrOff k : Nat)
    (F : Assertion) :
    preS sumb outPtr v7x v28x w29x sv o rdOff wrOff k F =
  (((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) ** (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7x) **
    (.x28 ↦ᵣ v28x) ** (.x29 ↦ᵣ w29x) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
    ((sumb + BitVec.ofNat 64 rdOff) ↦ₘ sv) **
    ((outPtr + BitVec.ofNat 64 wrOff) ↦ₘ o)) ** F) := rfl

/-- One byte-round of the copy loop (instrs 230..238, PriceK+920..952).
Symbolic in k; `m`/`wj` are the read/write dword byte-offsets (multiples of 8). -/
theorem tail_byteround (sumb outPtr : Word)
    (hsumAlign : sumb.toNat % 8 = 0) (houtAlign : outPtr.toNat % 8 = 0)
    (hsumRange : sumb.toNat + 40 < 2 ^ 64) (houtRange : outPtr.toNat + 32 < 2 ^ 64)
    (hsumValid : ∀ i < 32, isValidByteAccess (sumb + BitVec.ofNat 64 i) = true)
    (houtValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (k m wj : Nat) (hk : k < 32) (hm : 8 * ((31 - k) / 8) = m) (hwj : 8 * (k / 8) = wj)
    (sv o v7 v28 w29 : Word)
    (hRdSub : (31 : Word) - BitVec.ofNat 64 k = BitVec.ofNat 64 (31 - k))
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsBranchWithin 9 (PriceK + 920) priceCode
      (      ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ w29) **
       (.x30 ↦ᵣ BitVec.ofNat 64 k) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o)) **
      FR)
      (PriceK + 920)
      (((.x30 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))) ** (.x29 ↦ᵣ (32 : Word)) ** ⌜BitVec.ult (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12)) (32 : Word)⌝) **
       (      ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)))) ** FR))
      (PriceK + 956)
      (((.x30 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))) ** (.x29 ↦ᵣ (32 : Word)) ** ⌜¬ BitVec.ult (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12)) (32 : Word)⌝) **
       (      ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)))) ** FR)) := by
  have hs0 : ∀ x : Word, x + signExtend12 (0 : BitVec 12) = x := by
    intro x
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    exact BitVec.add_zero x
  have hrSum : sumb.toNat + (31 - k) < 2 ^ 64 := by omega
  have hrOut : outPtr.toNat + k < 2 ^ 64 := by omega
  have halignR : alignToDword ((sumb + ((31 : Word) - BitVec.ofNat 64 k)) + signExtend12 (0 : BitVec 12)) = (sumb + BitVec.ofNat 64 m) := by
    rw [hs0]
    rw [hRdSub]
    have hA := alignToDword_add_ofNat_of_aligned hsumAlign hrSum
    rw [hm] at hA
    exact hA
  have hvalidR : isValidByteAccess ((sumb + ((31 : Word) - BitVec.ofNat 64 k)) + signExtend12 (0 : BitVec 12)) = true := by
    rw [hs0]
    rw [hRdSub]
    exact hsumValid (31 - k) (by omega)
  have halignW : alignToDword ((outPtr + BitVec.ofNat 64 k) + signExtend12 (0 : BitVec 12)) = (outPtr + BitVec.ofNat 64 wj) := by
    rw [hs0]
    have hA := alignToDword_add_ofNat_of_aligned houtAlign hrOut
    rw [hwj] at hA
    exact hA
  have hvalidW : isValidByteAccess ((outPtr + BitVec.ofNat 64 k) + signExtend12 (0 : BitVec 12)) = true := by
    rw [hs0]
    exact houtValid k hk
  have hboR : byteOffset ((sumb + ((31 : Word) - BitVec.ofNat 64 k)) + signExtend12 (0 : BitVec 12)) = (31 - k) % 8 := by
    rw [hs0]
    rw [hRdSub]
    exact byteOffset_add_ofNat_of_aligned hsumAlign hrSum
  have hboW : byteOffset ((outPtr + BitVec.ofNat 64 k) + signExtend12 (0 : BitVec 12)) = k % 8 := by
    rw [hs0]
    exact byteOffset_add_ofNat_of_aligned houtAlign hrOut
  have h1 := li_spec_gen_within .x29 w29 (31 : Word) (PriceK + 920) (by decide)
  have h1F : cpsTripleWithin 1 (PriceK + 920) (PriceK + 924) priceCode
      ((.x29 ↦ᵣ w29) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) **
       FR)) (((.x29 ↦ᵣ (31 : Word)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) **
       FR))) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h1)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[230]'(by decide) = .LI .x29 (31 : Word) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 920) amsterdamBlobGasPriceU256_prog
      230 (.LI .x29 (31 : Word)) (by decide) (by decide) hins (by decide) a i hi
  have h2 := sub_spec_gen_rd_eq_rs1_within .x29 .x30 (31 : Word) (BitVec.ofNat 64 k)
    (PriceK + 924) (by decide)
  have h2F : cpsTripleWithin 1 (PriceK + 924) (PriceK + 928) priceCode
      (((.x29 ↦ᵣ (31 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) ** FR)) ((((.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) ** FR))) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h2)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[231]'(by decide) = .SUB .x29 .x29 .x30 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 924) amsterdamBlobGasPriceU256_prog
      231 (.SUB .x29 .x29 .x30) (by decide) (by decide) hins (by decide) a i hi
  have h3 := add_spec_gen_within .x28 .x22 .x29 sumb ((31 : Word) - BitVec.ofNat 64 k) v28
    (PriceK + 928) (by decide)
  have h3F : cpsTripleWithin 1 (PriceK + 928) (PriceK + 932) priceCode
      (((.x22 ↦ᵣ sumb) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) ** (.x28 ↦ᵣ v28)) **
              ((.x21 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ v7) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) **
       FR)) ((((.x22 ↦ᵣ sumb) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
        (.x28 ↦ᵣ (sumb + ((31 : Word) - BitVec.ofNat 64 k)))) **
              ((.x21 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ v7) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) **
       FR))) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h3)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[232]'(by decide) = .ADD .x28 .x22 .x29 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 928) amsterdamBlobGasPriceU256_prog
      232 (.ADD .x28 .x22 .x29) (by decide) (by decide) hins (by decide) a i hi
  have h4 := lbu_spec_gen_within .x7 .x28 (sumb + ((31 : Word) - BitVec.ofNat 64 k)) v7
    (0 : BitVec 12) (PriceK + 932) (sumb + BitVec.ofNat 64 m) sv (by decide) halignR hvalidR
  have h4F : cpsTripleWithin 1 (PriceK + 932) (PriceK + 936) priceCode
      (((.x28 ↦ᵣ (sumb + ((31 : Word) - BitVec.ofNat 64 k))) ** (.x7 ↦ᵣ v7) **
        ((sumb + BitVec.ofNat 64 m) ↦ₘ sv)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
       FR)) ((((.x28 ↦ᵣ (sumb + ((31 : Word) - BitVec.ofNat 64 k))) ** (.x7 ↦ᵣ ((extractByte sv (byteOffset ((sumb + ((31 : Word) - BitVec.ofNat 64 k)) + signExtend12 (0 : BitVec 12)))).zeroExtend 64)) **
        ((sumb + BitVec.ofNat 64 m) ↦ₘ sv)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
       FR))) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h4)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[233]'(by decide) = .LBU .x7 .x28 (0 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 932) amsterdamBlobGasPriceU256_prog
      233 (.LBU .x7 .x28 (0 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi
  have h5 := add_spec_gen_within .x28 .x21 .x30 outPtr (BitVec.ofNat 64 k)
    (sumb + ((31 : Word) - BitVec.ofNat 64 k)) (PriceK + 936) (by decide)
  have h5F : cpsTripleWithin 1 (PriceK + 936) (PriceK + 940) priceCode
      (((.x21 ↦ᵣ outPtr) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
        (.x28 ↦ᵣ (sumb + ((31 : Word) - BitVec.ofNat 64 k)))) **
              ((.x22 ↦ᵣ sumb) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) **
       (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       FR)) ((((.x21 ↦ᵣ outPtr) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
        (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k))) **
              ((.x22 ↦ᵣ sumb) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) **
       (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       FR))) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h5)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[234]'(by decide) = .ADD .x28 .x21 .x30 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 936) amsterdamBlobGasPriceU256_prog
      234 (.ADD .x28 .x21 .x30) (by decide) (by decide) hins (by decide) a i hi
  have h6 := sb_spec_gen_within .x28 .x7 (outPtr + BitVec.ofNat 64 k) ((extractByte sv ((31 - k) % 8)).zeroExtend 64)
    (0 : BitVec 12) (PriceK + 940) (outPtr + BitVec.ofNat 64 wj) o halignW hvalidW
  have h6F : cpsTripleWithin 1 (PriceK + 940) (PriceK + 944) priceCode
      (((.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
        ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
       FR)) ((((.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
        ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (byteOffset ((outPtr + BitVec.ofNat 64 k) + signExtend12 (0 : BitVec 12))) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)))) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
       FR))) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h6)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[235]'(by decide) = .SB .x28 .x7 (0 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 940) amsterdamBlobGasPriceU256_prog
      235 (.SB .x28 .x7 (0 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi
  have h7 := addi_spec_gen_same_within .x30 (BitVec.ofNat 64 k) (1 : BitVec 12)
    (PriceK + 944) (by decide)
  have h7F : cpsTripleWithin 1 (PriceK + 944) (PriceK + 948) priceCode
      ((.x30 ↦ᵣ BitVec.ofNat 64 k) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8))) **
       FR)) (((.x30 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8))) **
       FR))) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h7)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[236]'(by decide) = .ADDI .x30 .x30 (1 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 944) amsterdamBlobGasPriceU256_prog
      236 (.ADDI .x30 .x30 (1 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi
  have h8 := li_spec_gen_within .x29 ((31 : Word) - BitVec.ofNat 64 k) (32 : Word)
    (PriceK + 948) (by decide)
  have h8F : cpsTripleWithin 1 (PriceK + 948) (PriceK + 952) priceCode
      ((.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) ** (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8))) ** (.x30 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))) **
       FR)) (((.x29 ↦ᵣ (32 : Word)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) ** (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8))) ** (.x30 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))) **
       FR))) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h8)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[237]'(by decide) = .LI .x29 (32 : Word) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 948) amsterdamBlobGasPriceU256_prog
      237 (.LI .x29 (32 : Word)) (by decide) (by decide) hins (by decide) a i hi
  -- value-congruence weakens: byteOffset-mess -> simplified forms
  have hv7 : ((extractByte sv (byteOffset ((sumb + ((31 : Word) - BitVec.ofNat 64 k)) + signExtend12 (0 : BitVec 12)))).zeroExtend 64) = ((extractByte sv ((31 - k) % 8)).zeroExtend 64) := by rw [hboR]
  have hvW : (replaceByte o (byteOffset ((outPtr + BitVec.ofNat 64 k) + signExtend12 (0 : BitVec 12))) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)) = (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)) := by
    rw [hboW]
  have h4v : cpsTripleWithin 1 (PriceK + 932) (PriceK + 936) priceCode
      (((.x28 ↦ᵣ (sumb + ((31 : Word) - BitVec.ofNat 64 k))) ** (.x7 ↦ᵣ v7) **
        ((sumb + BitVec.ofNat 64 m) ↦ₘ sv)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
       FR)) ((((.x28 ↦ᵣ (sumb + ((31 : Word) - BitVec.ofNat 64 k))) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
        ((sumb + BitVec.ofNat 64 m) ↦ₘ sv)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
       FR))) := by
    refine cpsTripleWithin_weaken (fun _ hx => hx) ?_ h4F
    intro h hx
    obtain ⟨h1, h2, hd, hu, hlead, hfr⟩ := hx
    obtain ⟨g28, g7c, hd2, gu2, hg28, hg7c⟩ := hlead
    obtain ⟨g7, gc, hd3, gu3, hg7, hgc⟩ := hg7c
    rw [hv7] at hg7
    exact ⟨h1, h2, hd, hu,
      ⟨g28, g7c, hd2, gu2, hg28,
        ⟨g7, gc, hd3, gu3, hg7, hgc⟩⟩, hfr⟩
  have h6v : cpsTripleWithin 1 (PriceK + 940) (PriceK + 944) priceCode
      (((.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
        ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
       FR)) ((((.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
        ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)))) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
       FR))) := by
    refine cpsTripleWithin_weaken (fun _ hx => hx) ?_ h6F
    intro h hx
    obtain ⟨h1, h2, hd, hu, hlead, hfr⟩ := hx
    obtain ⟨g28, g7c, hd2, gu2, hg28, hg7c⟩ := hlead
    obtain ⟨g7, gc, hd3, gu3, hg7, hgc⟩ := hg7c
    obtain ⟨he, hvalid⟩ := hgc
    rw [hvW] at he
    exact ⟨h1, h2, hd, hu,
      ⟨g28, g7c, hd2, gu2, hg28,
        ⟨g7, gc, hd3, gu3, hg7, ⟨he, hvalid⟩⟩⟩, hfr⟩
  -- junction weakens (pre = previous post verbatim)
  have h1F' : cpsTripleWithin 1 (PriceK + 920) (PriceK + 924) priceCode
      (      ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ w29) **
       (.x30 ↦ᵣ BitVec.ofNat 64 k) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o)) **
      FR) (((.x29 ↦ᵣ (31 : Word)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) **
       FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) h1F
  have h2F' : cpsTripleWithin 1 (PriceK + 924) (PriceK + 928) priceCode
      (((.x29 ↦ᵣ (31 : Word)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) **
       FR))) ((((.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) h2F
  have h3F' : cpsTripleWithin 1 (PriceK + 928) (PriceK + 932) priceCode
      ((((.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) ** FR))) ((((.x22 ↦ᵣ sumb) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
        (.x28 ↦ᵣ (sumb + ((31 : Word) - BitVec.ofNat 64 k)))) **
              ((.x21 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ v7) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) **
       FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) h3F
  have h4F' : cpsTripleWithin 1 (PriceK + 932) (PriceK + 936) priceCode
      ((((.x22 ↦ᵣ sumb) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
        (.x28 ↦ᵣ (sumb + ((31 : Word) - BitVec.ofNat 64 k)))) **
              ((.x21 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ v7) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) **
       FR))) ((((.x28 ↦ᵣ (sumb + ((31 : Word) - BitVec.ofNat 64 k))) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
        ((sumb + BitVec.ofNat 64 m) ↦ₘ sv)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
       FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) h4v
  have h5F' : cpsTripleWithin 1 (PriceK + 936) (PriceK + 940) priceCode
      ((((.x28 ↦ᵣ (sumb + ((31 : Word) - BitVec.ofNat 64 k))) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
        ((sumb + BitVec.ofNat 64 m) ↦ₘ sv)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
       FR))) ((((.x21 ↦ᵣ outPtr) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
        (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k))) **
              ((.x22 ↦ᵣ sumb) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) **
       (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) h5F
  have h6F' : cpsTripleWithin 1 (PriceK + 940) (PriceK + 944) priceCode
      ((((.x21 ↦ᵣ outPtr) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
        (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k))) **
              ((.x22 ↦ᵣ sumb) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o) **
       (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       FR))) ((((.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
        ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)))) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
       FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) h6v
  have h7F' : cpsTripleWithin 1 (PriceK + 944) (PriceK + 948) priceCode
      ((((.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
        ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)))) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ BitVec.ofNat 64 k) **
       ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) ** (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) **
       FR))) (((.x30 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8))) **
       FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) h7F
  have h8F' : cpsTripleWithin 1 (PriceK + 948) (PriceK + 952) priceCode
      (((.x30 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       (.x29 ↦ᵣ ((31 : Word) - BitVec.ofNat 64 k)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8))) **
       FR))) (((.x29 ↦ᵣ (32 : Word)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) ** (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8))) ** (.x30 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))) **
       FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) h8F
  have hs1 := cpsTripleWithin_seq_same_cr h1F' h2F'
  have hs2 := cpsTripleWithin_seq_same_cr hs1 h3F'
  have hs3 := cpsTripleWithin_seq_same_cr hs2 h4F'
  have hs4 := cpsTripleWithin_seq_same_cr hs3 h5F'
  have hs5 := cpsTripleWithin_seq_same_cr hs4 h6F'
  have hs6 := cpsTripleWithin_seq_same_cr hs5 h7F'
  have hs7 := cpsTripleWithin_seq_same_cr hs6 h8F'
  have hrun : cpsTripleWithin 8 (PriceK + 920) (PriceK + 952) priceCode
      (      ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ w29) **
       (.x30 ↦ᵣ BitVec.ofNat 64 k) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ o)) **
      FR) (((.x30 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))) ** (.x29 ↦ᵣ (32 : Word))) ** (      ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)))) ** FR)) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by intro h hx; xperm_hyp hx) hs7
  have hb := bltu_spec_gen_within .x30 .x29 (-32 : BitVec 13)
    (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12)) (32 : Word) (PriceK + 952)
  rw [show (PriceK + 952 : Word) + signExtend13 (-32 : BitVec 13) = PriceK + 920 from by
      rw [show signExtend13 (-32 : BitVec 13) = (-32 : Word) from by decide]
      decide,
    show (PriceK + 952 : Word) + 4 = PriceK + 956 from by decide] at hb
  have hbF := cpsBranchWithin_frameR (      ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)))) ** FR) (by pcFree; exact hFR) hb
  have hbE : cpsBranchWithin 1 (PriceK + 952) priceCode
      (((.x30 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))) ** (.x29 ↦ᵣ (32 : Word))) ** (      ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)))) ** FR))
      (PriceK + 920)
      (((.x30 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))) ** (.x29 ↦ᵣ (32 : Word)) ** ⌜BitVec.ult (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12)) (32 : Word)⌝) ** (      ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)))) ** FR))
      (PriceK + 956)
      (((.x30 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))) ** (.x29 ↦ᵣ (32 : Word)) ** ⌜¬ BitVec.ult (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12)) (32 : Word)⌝) ** (      ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ sumb) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte sv ((31 - k) % 8)).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 k)) ** ((sumb + BitVec.ofNat 64 m) ↦ₘ sv) **
       ((outPtr + BitVec.ofNat 64 wj) ↦ₘ (replaceByte o (k % 8) (((extractByte sv ((31 - k) % 8)).zeroExtend 64).truncate 8)))) ** FR)) := by
    refine cpsBranchWithin_extend_code ?_ hbF
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[238]'(by decide) = .BLTU .x30 .x29 (-32 : BitVec 13) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 952) amsterdamBlobGasPriceU256_prog
      238 (.BLTU .x30 .x29 (-32 : BitVec 13)) (by decide) (by decide) hins (by decide) a i hi
  exact cpsTripleWithin_seq_cpsBranchWithin_same_cr hrun hbE

/-- Drop the loop-back pure and re-point the x30 pin of a byte-round exit post. -/
theorem link_fix {v v' : Word} {P : Prop} (hvv : v = v') {F : Assertion} :
    ∀ h, (((.x30 ↦ᵣ v) ** (.x29 ↦ᵣ (32 : Word)) ** ⌜P⌝) ** F) h →
      (((.x30 ↦ᵣ v') ** (.x29 ↦ᵣ (32 : Word))) ** F) h := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hlead, hF⟩ := hx
  obtain ⟨g30, g29p, gd30, gu30, hg30, h29p⟩ := hlead
  obtain ⟨g29, gP, _gd29, gu29, hg29, hgP⟩ := h29p
  obtain ⟨heq, -⟩ := hgP
  have gu' : g29 = g29p := by
    rw [heq, PartialState.union_empty_right] at gu29
    exact gu29
  rw [hvv] at hg30
  exact ⟨h1, h2, hd, hu,
    ⟨g30, g29, by rw [gu']; exact gd30, by rw [gu']; exact gu30, hg30, hg29⟩, hF⟩

