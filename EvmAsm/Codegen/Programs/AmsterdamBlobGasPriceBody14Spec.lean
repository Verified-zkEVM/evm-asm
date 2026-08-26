/-
Outer-loop ROUND for `amsterdam_blob_gas_price_u256` (#12851): one full taylor
iteration at PriceK+144 as a 12-exit cpsNBranchWithin (exit PriceK+804 on
acc = 0, PriceK+964 on the nine overflow paths, back-edge PriceK+144). AB/PB
parametric — both loop parities are instances. Consumes the parametric windows
or_chainP2 / add6P_core / mul6P_core / swapdivP_core and the branch leaves.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBodySpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody10Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody11Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody13Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody7Spec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec EvmAsm.Codegen.AmsterdamBlobGasPriceBody10Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec EvmAsm.Codegen.AmsterdamBlobGasPriceBody13Spec

set_option maxRecDepth 8000

/-- Sequence an N-branch onto the LAST exit of another (same CodeReq):
    runs that continue at the final station replace it; earlier exits pass
    through unchanged. -/
private theorem nb_snoc {n1 n2 : Nat} {entry m : Word} {cr : CodeReq}
    {P Qm : Assertion} {pre : List (Word × Assertion)} {exits2 : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n1 entry cr P (pre ++ [(m, Qm)]))
    (h2 : cpsNBranchWithin n2 m cr Qm exits2) :
    cpsNBranchWithin (n1 + n2) entry cr P (pre ++ exits2) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQ1⟩ := h1 R hR s hcr hPR hpc
  simp only [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | hlast
  · refine ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1, hstep1, ex, ?_, hpc1, hQ1⟩
    exact List.mem_append.mpr (Or.inl hmem)
  · subst hlast
    have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, ex2, hmem2, hpc2, hQ2⟩ := h2 R hR s1 hcr' hQ1 hpc1
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, ex2,
      List.mem_append.mpr (Or.inr hmem2), hpc2, hQ2⟩

/-- Pre-weakening for N-branches (same exits, stronger precondition). -/
private theorem nb_prew {n : Nat} {entry : Word} {cr : CodeReq}
    {P P' : Assertion} {exits : List (Word × Assertion)}
    (hpre : ∀ h, P' h → P h) (h : cpsNBranchWithin n entry cr P exits) :
    cpsNBranchWithin n entry cr P' exits := by
  intro R hR s hcr hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  exact h R hR s hcr hPR hpc

/-- Drop a pure riding as the second conjunct's tail: `(L1 ** (L2 ** ⌜P⌝)) h`
    implies `(L1 ** L2) h`. -/
private theorem pure_drop1 {L1 L2 : Assertion} {P : Prop} :
    ∀ h, (L1 ** (L2 ** ⌜P⌝)) h → (L1 ** L2) h := by
  intro h hx
  obtain ⟨g1, g2p, gd, gu, hL1, hL2p⟩ := hx
  obtain ⟨g2, gP, gd2, gu2, hL2, hP⟩ := hL2p
  obtain ⟨heq, -⟩ := hP
  have gu' : g2p = g2 := by
    rw [heq, PartialState.union_empty_right] at gu2
    exact gu2.symm
  rw [gu'] at gd gu
  exact ⟨g1, g2, gd, gu, hL1, hL2⟩

private theorem or2p_li (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v5 v6 v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 144) (PriceK + 148) priceCode
      (((.x5 ↦ᵣ v5) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         frameSlotsSaved priceFrame newSp vals ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) (((.x5 ↦ᵣ (0 : Word)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         frameSlotsSaved priceFrame newSp vals ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hli := li_spec_gen_within .x5 v5 (0 : Word) (PriceK + 144) (by decide)
  have hliF : cpsTripleWithin 1 (PriceK + 144) (PriceK + 148) priceCode
      ((.x5 ↦ᵣ v5) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         frameSlotsSaved priceFrame newSp vals ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) ((.x5 ↦ᵣ (0 : Word)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         frameSlotsSaved priceFrame newSp vals ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hli)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[36]'(by decide) = .LI .x5 (0 : Word) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 144) amsterdamBlobGasPriceU256_prog
      36 (.LI .x5 (0 : Word)) (by decide) (by decide) hins (by decide) a i hi

  exact hliF
private theorem or2p_ld0 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v6 v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 148) (PriceK + 152) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ v6) ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a0) ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hld0 := ld_spec_gen_within .x6 .x19 (AB) v6 a0 (0 : BitVec 12)
    (PriceK + 148) (by decide)
  have hld0F : cpsTripleWithin 1 (PriceK + 148) (PriceK + 152) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ v6) ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a0) ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld0)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[37]'(by decide) = .LD .x6 .x19 (0 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 148) amsterdamBlobGasPriceU256_prog
      37 (.LD .x6 .x19 (0 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi

  exact hld0F
private theorem or2p_or0 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 152) (PriceK + 156) priceCode
      ((((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x5 ↦ᵣ ((0 : Word) ||| a0)) ** (.x6 ↦ᵣ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) := by
  have hor0 := or_spec_gen_rd_eq_rs1_within .x5 .x6 (0 : Word) a0 (PriceK + 152) (by decide)
  have hor0F : cpsTripleWithin 1 (PriceK + 152) (PriceK + 156) priceCode
      (((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) (((.x5 ↦ᵣ ((0 : Word) ||| a0)) ** (.x6 ↦ᵣ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor0)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[38]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 152) amsterdamBlobGasPriceU256_prog
      38 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi

  exact hor0F
private theorem or2p_ld1 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 156) (PriceK + 160) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((0 : Word) ||| a0)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a1) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((0 : Word) ||| a0)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hld1 := ld_spec_gen_within .x6 .x19 (AB) a0 a1 (8 : BitVec 12)
    (PriceK + 156) (by decide)
  have hld1F : cpsTripleWithin 1 (PriceK + 156) (PriceK + 160) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((0 : Word) ||| a0)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a1) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((0 : Word) ||| a0)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld1)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[39]'(by decide) = .LD .x6 .x19 (8 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 156) amsterdamBlobGasPriceU256_prog
      39 (.LD .x6 .x19 (8 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi

  exact hld1F
private theorem or2p_or1 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 160) (PriceK + 164) priceCode
      ((((.x5 ↦ᵣ ((0 : Word) ||| a0)) ** (.x6 ↦ᵣ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) ** (.x6 ↦ᵣ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) := by
  have hor1 := or_spec_gen_rd_eq_rs1_within .x5 .x6 ((0 : Word) ||| a0) a1 (PriceK + 160) (by decide)
  have hor1F : cpsTripleWithin 1 (PriceK + 160) (PriceK + 164) priceCode
      (((.x5 ↦ᵣ ((0 : Word) ||| a0)) ** (.x6 ↦ᵣ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) (((.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) ** (.x6 ↦ᵣ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor1)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[40]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 160) amsterdamBlobGasPriceU256_prog
      40 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi

  exact hor1F
private theorem or2p_ld2 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 164) (PriceK + 168) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a2) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hld2 := ld_spec_gen_within .x6 .x19 (AB) a1 a2 (16 : BitVec 12)
    (PriceK + 164) (by decide)
  have hld2F : cpsTripleWithin 1 (PriceK + 164) (PriceK + 168) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a2) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld2)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[41]'(by decide) = .LD .x6 .x19 (16 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 164) amsterdamBlobGasPriceU256_prog
      41 (.LD .x6 .x19 (16 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi

  exact hld2F
private theorem or2p_or2 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 168) (PriceK + 172) priceCode
      ((((.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) ** (.x6 ↦ᵣ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) ** (.x6 ↦ᵣ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) := by
  have hor2 := or_spec_gen_rd_eq_rs1_within .x5 .x6 (((0 : Word) ||| a0) ||| a1) a2 (PriceK + 168) (by decide)
  have hor2F : cpsTripleWithin 1 (PriceK + 168) (PriceK + 172) priceCode
      (((.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) ** (.x6 ↦ᵣ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) (((.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) ** (.x6 ↦ᵣ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor2)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[42]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 168) amsterdamBlobGasPriceU256_prog
      42 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi

  exact hor2F
private theorem or2p_ld3 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 172) (PriceK + 176) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a3) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hld3 := ld_spec_gen_within .x6 .x19 (AB) a2 a3 (24 : BitVec 12)
    (PriceK + 172) (by decide)
  have hld3F : cpsTripleWithin 1 (PriceK + 172) (PriceK + 176) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a3) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld3)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[43]'(by decide) = .LD .x6 .x19 (24 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 172) amsterdamBlobGasPriceU256_prog
      43 (.LD .x6 .x19 (24 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi

  exact hld3F
private theorem or2p_or3 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 176) (PriceK + 180) priceCode
      ((((.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) ** (.x6 ↦ᵣ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) ** (.x6 ↦ᵣ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) := by
  have hor3 := or_spec_gen_rd_eq_rs1_within .x5 .x6 ((((0 : Word) ||| a0) ||| a1) ||| a2) a3 (PriceK + 176) (by decide)
  have hor3F : cpsTripleWithin 1 (PriceK + 176) (PriceK + 180) priceCode
      (((.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) ** (.x6 ↦ᵣ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) (((.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) ** (.x6 ↦ᵣ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor3)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[44]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 176) amsterdamBlobGasPriceU256_prog
      44 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi

  exact hor3F
private theorem or2p_ld4 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 180) (PriceK + 184) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a4) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hld4 := ld_spec_gen_within .x6 .x19 (AB) a3 a4 (32 : BitVec 12)
    (PriceK + 180) (by decide)
  have hld4F : cpsTripleWithin 1 (PriceK + 180) (PriceK + 184) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a4) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld4)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[45]'(by decide) = .LD .x6 .x19 (32 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 180) amsterdamBlobGasPriceU256_prog
      45 (.LD .x6 .x19 (32 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi

  exact hld4F
private theorem or2p_or4 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 184) (PriceK + 188) priceCode
      ((((.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) ** (.x6 ↦ᵣ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) ** (.x6 ↦ᵣ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) := by
  have hor4 := or_spec_gen_rd_eq_rs1_within .x5 .x6 (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) a4 (PriceK + 184) (by decide)
  have hor4F : cpsTripleWithin 1 (PriceK + 184) (PriceK + 188) priceCode
      (((.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) ** (.x6 ↦ᵣ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) (((.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) ** (.x6 ↦ᵣ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor4)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[46]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 184) amsterdamBlobGasPriceU256_prog
      46 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi

  exact hor4F
private theorem or2p_ld5 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 188) (PriceK + 192) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a5) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hld5 := ld_spec_gen_within .x6 .x19 (AB) a4 a5 (40 : BitVec 12)
    (PriceK + 188) (by decide)
  have hld5F : cpsTripleWithin 1 (PriceK + 188) (PriceK + 192) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a5) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld5)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[47]'(by decide) = .LD .x6 .x19 (40 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 188) amsterdamBlobGasPriceU256_prog
      47 (.LD .x6 .x19 (40 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi

  exact hld5F
private theorem or2p_or5 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 192) (PriceK + 196) priceCode
      ((((.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) ** (.x6 ↦ᵣ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x6 ↦ᵣ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) := by
  have hor5 := or_spec_gen_rd_eq_rs1_within .x5 .x6 ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) a5 (PriceK + 192) (by decide)
  have hor5F : cpsTripleWithin 1 (PriceK + 192) (PriceK + 196) priceCode
      (((.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) ** (.x6 ↦ᵣ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x6 ↦ᵣ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor5)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[48]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 192) amsterdamBlobGasPriceU256_prog
      48 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi

  exact hor5F
/-- Parametric or-chain window (13 instrs, PriceK+144..196): x5 := OR of the six
acc limbs; PB-parametric cells (safe for both parities). -/
theorem or_chainP2 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 13 (PriceK + 144) (PriceK + 196) priceCode
      (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))
      (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) := by
  have hli := or2p_li newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 FR hFR
  have hld0 := or2p_ld0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v6 v7 v28 v29 v30 v31 FR hFR
  have hld0F' : cpsTripleWithin 1 (PriceK + 148) (PriceK + 152) priceCode
      (((.x5 ↦ᵣ (0 : Word)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         frameSlotsSaved priceFrame newSp vals ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a0) ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld0
  have hor0 := or2p_or0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hor0F' : cpsTripleWithin 1 (PriceK + 152) (PriceK + 156) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a0) ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x5 ↦ᵣ ((0 : Word) ||| a0)) ** (.x6 ↦ᵣ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hor0
  have hld1 := or2p_ld1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hld1F' : cpsTripleWithin 1 (PriceK + 156) (PriceK + 160) priceCode
      ((((.x5 ↦ᵣ ((0 : Word) ||| a0)) ** (.x6 ↦ᵣ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a1) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((0 : Word) ||| a0)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld1
  have hor1 := or2p_or1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hor1F' : cpsTripleWithin 1 (PriceK + 160) (PriceK + 164) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a1) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((0 : Word) ||| a0)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) ** (.x6 ↦ᵣ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hor1
  have hld2 := or2p_ld2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hld2F' : cpsTripleWithin 1 (PriceK + 164) (PriceK + 168) priceCode
      ((((.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) ** (.x6 ↦ᵣ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a2) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld2
  have hor2 := or2p_or2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hor2F' : cpsTripleWithin 1 (PriceK + 168) (PriceK + 172) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a2) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) ** (.x6 ↦ᵣ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hor2
  have hld3 := or2p_ld3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hld3F' : cpsTripleWithin 1 (PriceK + 172) (PriceK + 176) priceCode
      ((((.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) ** (.x6 ↦ᵣ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a3) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld3
  have hor3 := or2p_or3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hor3F' : cpsTripleWithin 1 (PriceK + 176) (PriceK + 180) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a3) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) ** (.x6 ↦ᵣ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hor3
  have hld4 := or2p_ld4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hld4F' : cpsTripleWithin 1 (PriceK + 180) (PriceK + 184) priceCode
      ((((.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) ** (.x6 ↦ᵣ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a4) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld4
  have hor4 := or2p_or4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hor4F' : cpsTripleWithin 1 (PriceK + 184) (PriceK + 188) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a4) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) ** (.x6 ↦ᵣ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hor4
  have hld5 := or2p_ld5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hld5F' : cpsTripleWithin 1 (PriceK + 188) (PriceK + 192) priceCode
      ((((.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) ** (.x6 ↦ᵣ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a5) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld5
  have hor5 := or2p_or5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hor5F' : cpsTripleWithin 1 (PriceK + 192) (PriceK + 196) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a5) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x6 ↦ᵣ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hor5
  have hs1 := cpsTripleWithin_seq_same_cr hli hld0F'
  have hs2 := cpsTripleWithin_seq_same_cr hs1 hor0F'
  have hs3 := cpsTripleWithin_seq_same_cr hs2 hld1F'
  have hs4 := cpsTripleWithin_seq_same_cr hs3 hor1F'
  have hs5 := cpsTripleWithin_seq_same_cr hs4 hld2F'
  have hs6 := cpsTripleWithin_seq_same_cr hs5 hor2F'
  have hs7 := cpsTripleWithin_seq_same_cr hs6 hld3F'
  have hs8 := cpsTripleWithin_seq_same_cr hs7 hor3F'
  have hs9 := cpsTripleWithin_seq_same_cr hs8 hld4F'
  have hs10 := cpsTripleWithin_seq_same_cr hs9 hor4F'
  have hs11 := cpsTripleWithin_seq_same_cr hs10 hld5F'
  have hs12 := cpsTripleWithin_seq_same_cr hs11 hor5F'
  exact cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (by intro h hx; xperm_hyp hx) hs12

/-- One full outer-loop round of the taylor recurrence, PriceK+144..: the
or-chain zero test (exit PriceK+804 on acc = 0), the i < 496 cap (overflow
exit PriceK+964), the 6-limb ripple add (carry overflow), the 6-limb multiply
by excess (seven overflow exits), and the divisor/division window jumping back
to PriceK+144. Both loop parities are instances (AB/PB swap). -/
theorem taylor_round (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsNBranchWithin 4028 (PriceK + 144) priceCode
      (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))
      [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))),
    (PriceK + 964, (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))),
    (PriceK + 964, (((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR))),
    (PriceK + 964, mul6PQOVF0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVFF newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 680, mul6PQFALL newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, QOVFDIVP newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 * excess) + (0 : Word)) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) v7 v28 v29 v30 v31 FR),
    (PriceK + 144, QBACKP newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 * excess) + (0 : Word)) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) v7 v28 v29 v30 v31 FR)] := by
  have hOr2 := or_chainP2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5
    p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 FR hFR
  have hA : cpsTripleWithin 13 (PriceK + 144) (PriceK + 196) priceCode
      (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word))) **
              ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by intro h hx; xperm_hyp hx) hOr2
  have hBe := AmsterdamBlobGasPriceBodySpec.loop_test_beqz_branch ((((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5))
  have hBeF := cpsBranchWithin_frameR (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) (by pcFree; exact hFR) hBe
  have nbBeqz := cpsNBranchWithin_of_branch hBeF
  have nb0 := cpsTripleWithin_seq_cpsNBranchWithin_same_cr hA nbBeqz
  -- li t0, 496 (PriceK+200)
  have hLi := li_spec_gen_within .x5 ((((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) (496 : Word) (PriceK + 200) (by decide)
  have hLiF : cpsTripleWithin 1 (PriceK + 200) (PriceK + 204) priceCode
      ((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) **
              ((.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝ **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) ((.x5 ↦ᵣ (496 : Word)) **
              ((.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝ **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hLi)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[50]'(by decide) = .LI .x5 (496 : Word) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 200) amsterdamBlobGasPriceU256_prog
      50 (.LI .x5 (496 : Word)) (by decide) (by decide) hins (by decide) a i hi
  have hLiF' : cpsTripleWithin 1 (PriceK + 200) (PriceK + 204) priceCode
      ((((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) ((((.x5 ↦ᵣ (496 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (by intro h hx; xperm_hyp hx) hLiF
  have nbLi : cpsNBranchWithin 1 (PriceK + 200) priceCode
      ((((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) [(PriceK + 204, (((.x5 ↦ᵣ (496 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))] :=
    cpsNBranchWithin_of_triple (by simp) hLiF'
  have nb1 := nb_snoc (pre := [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))]) nb0 nbLi
  -- bgeu s2, t0 (PriceK+204)
  have hBg := AmsterdamBlobGasPriceBodySpec.loop_test_bgeu_branch iVal (496 : Word)
  have hBgF := cpsBranchWithin_frameR (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) (by pcFree; exact hFR) hBg
  have hBgF' : cpsBranchWithin 1 (PriceK + 204) priceCode
      ((((.x5 ↦ᵣ (496 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))
      (PriceK + 964)
      ((((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))
      (PriceK + 208)
      ((((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) := by
    refine cpsBranchWithin_weaken ?_ (fun _ hx => hx) (fun _ hx => hx) hBgF
    intro h hx
    obtain ⟨h1, h2, hd, hu, hlead, hfr⟩ := hx
    have hlead' := pure_drop1 _ hlead
    have hx' : (((.x5 ↦ᵣ (496 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) h :=
      ⟨h1, h2, hd, hu, hlead', hfr⟩
    xperm_hyp hx'
  have nbBg := cpsNBranchWithin_of_branch hBgF'
  have nb2 := nb_snoc (pre := [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))]) nb1 nbBg
  -- add6 (PriceK+208..428)
  have hAddInst := add6P_core newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 (496 : Word) a5 v7 v28 v29 v30 v31
  have hAddF := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word)) ** FR)
      (pcFree_sepConj pcFree_regIs hFR) hAddInst
  have hAdd' : cpsTripleWithin 55 (PriceK + 208) (PriceK + 428) priceCode
      ((((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ s5) **
       (.x28 ↦ᵣ (a5 + s5)) ** (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))))) **
        FR) := by
    refine cpsTripleWithin_weaken ?_ (by intro h hx; xperm_hyp hx) hAddF
    intro h hx
    obtain ⟨h1, h2, hd, hu, hlead, hfbg⟩ := hx
    have hlead' := pure_drop1 _ hlead
    have hx' : (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word))) ** (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) h :=
      ⟨h1, h2, hd, hu, hlead', hfbg⟩
    xperm_hyp hx'
  have nbAdd : cpsNBranchWithin 55 (PriceK + 208) priceCode
      ((((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) [(PriceK + 428,       ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ s5) **
       (.x28 ↦ᵣ (a5 + s5)) ** (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))))) ** FR)] :=
    cpsNBranchWithin_of_triple (by simp) hAdd'
  have nb3 := nb_snoc (pre := [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))), (PriceK + 964, (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))]) nb2 nbAdd
  -- carry branch (PriceK+428)
  have hCr := AmsterdamBlobGasPriceBodySpec.add6_carry_branch ((rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))))
  have hCrF := cpsBranchWithin_frameR (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR)) (by pcFree; exact hFR) hCr
  have hCrF' : cpsBranchWithin 1 (PriceK + 428) priceCode
      ((      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ s5) **
       (.x28 ↦ᵣ (a5 + s5)) ** (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))))) ** FR))
      (PriceK + 964)
      ((((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR)))
      (PriceK + 432)
      ((((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR))) := by
    refine cpsBranchWithin_weaken ?_ (fun _ hx => hx) (fun _ hx => hx) hCrF
    intro h hx
    xperm_hyp hx
  have nbCr := cpsNBranchWithin_of_branch hCrF'
  have nb4 := nb_snoc (pre := [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))), (PriceK + 964, (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))]) nb3 nbCr
  -- mul6 (PriceK+432..680)
  have hMulF : cpsNBranchWithin 62 (PriceK + 432) priceCode
      (((mul6PPRE newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) a5 s5 (a5 + s5) (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** FR))
      [(PriceK + 964, mul6PQOVF0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVFF newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 680, mul6PQFALL newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR)] :=
    cpsNBranchWithin_frameR hFR (mul6P_core newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) a5 s5 (a5 + s5) (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word)))
  have hMul' : cpsNBranchWithin 62 (PriceK + 432) priceCode
      ((((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR)))
      [(PriceK + 964, mul6PQOVF0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVFF newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 680, mul6PQFALL newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR)] := by
    refine nb_prew ?_ hMulF
    intro h hx
    obtain ⟨h1, h2, hd, hu, hlead, hfcr⟩ := hx
    have hlead' := pure_drop1 _ hlead
    have hx' : (((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word))) ** (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR))) h :=
      ⟨h1, h2, hd, hu, hlead', hfcr⟩
    xperm_hyp hx'
  have nb5 := nb_snoc (pre := [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))),
    (PriceK + 964, (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))),
    (PriceK + 964, (((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR)))]) nb4 hMul'
  -- swapdiv (PriceK+680..: back to PriceK+144)
  have hSd' : cpsNBranchWithin 3894 (PriceK + 680) priceCode
      ((mul6PQFALL newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 ** FR))
      [(PriceK + 964, QOVFDIVP newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 * excess) + (0 : Word)) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) v7 v28 v29 v30 v31 FR),
       (PriceK + 144, QBACKP newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 * excess) + (0 : Word)) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) v7 v28 v29 v30 v31 FR)] := by
    refine nb_prew ?_ (swapdivP_core newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 * excess) + (0 : Word)) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) a5 (a5 * excess) (rv64_mulhu a5 excess) ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word))) (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word))) (rv64_mulhu a5 excess) then (1 : Word) else (0 : Word)) ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word))) ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word))) FR hFR)
    intro h hx
    obtain ⟨h1, h2, hd, hu, hqf, hfrw⟩ := hx
    have hx2 : ((((.x31 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word)))) ** (.x0 ↦ᵣ (0 : Word)))) **
              ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ a5) **
       (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
       (.x28 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word))) (rv64_mulhu a5 excess) then (1 : Word) else (0 : Word))) **
       (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word)))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word))))) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word))))) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word))))) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word))))) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word))))) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))))) h1 :=
      pure_drop_mid _ hqf
    have hx3 : (((((.x31 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word)))) ** (.x0 ↦ᵣ (0 : Word)))) **
              ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ a5) **
       (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
       (.x28 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word))) (rv64_mulhu a5 excess) then (1 : Word) else (0 : Word))) **
       (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word)))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word))))) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word))))) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word))))) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word))))) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word))))) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))))) ** FR) h :=
      ⟨h1, h2, hd, hu, hx2, hfrw⟩
    xperm_hyp hx3
  have nb6 := nb_snoc (pre := [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))),
    (PriceK + 964, (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))),
    (PriceK + 964, (((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR))),
    (PriceK + 964, mul6PQOVF0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVFF newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 ** FR)]) nb5 hSd'
  exact nb6

#print axioms taylor_round
