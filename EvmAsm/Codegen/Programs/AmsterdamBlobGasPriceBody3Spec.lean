/-
# swapDiv window for `amsterdam_blob_gas_price_u256` (#12851, body discharge)

Window: instrs 170..200 @ `PriceK+680 .. PriceK+800` — pointer swap (acc↔prod),
divisor formation `D·i` with high-half overflow dispatch, then the 6-limb ×
64-bit MSB-first restoring division writing quotient limbs over the (swapped)
acc buffer, `i++`, and the unconditional back-edge `j` to the outer loop head
`PriceK+144`.

Structure: a parametric one-round bit lemma folded 64× by `countdown_loop_triple`
(the final round's taken-post `⌜(0 : Word) ≠ 0⌝` is absurd), a limb-round lemma
folded 6×, then the straight-line prologue merged with the ovf dispatch and the
back-edge jump (`jal_x0_spec_gen_within`). Values stay symbolic; the division
recurrence (`r⁺ = 2r + msb`, conditional subtract) is carried as `ite` terms in
the postcondition pins.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody2Spec
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody3Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody2Spec

set_option maxRecDepth 8000

/-- Countdown loop fold: N interior self-target rounds (taken → header with the
next invariant, fall → `exitB`) plus a final round whose taken-post is
unsatisfiable, collapsing to a single triple to `exitB`. -/
private theorem countdown_loop_triple {N m : Nat} {cr : CodeReq} {hdr exitB : Word}
    (inv : Nat → Assertion) (QB : Assertion)
    (hiter : ∀ j, j < N →
      cpsBranchWithin m hdr cr (inv j) hdr (inv (j + 1)) exitB QB)
    (hlast : cpsBranchWithin m hdr cr (inv N) hdr
      (fun h => (inv (N + 1) ** ⌜(0 : Word) ≠ (0 : Word)⌝) h) exitB QB) :
    cpsTripleWithin (N * m + m) hdr exitB cr (inv 0) QB := by
  suffices h : ∀ (M j : Nat), j + M = N →
      cpsBranchWithin (M * m + m) hdr cr (inv j) hdr
        (fun h => (inv (j + M + 1) ** ⌜(0 : Word) ≠ (0 : Word)⌝) h) exitB QB from
    cpsBranchWithin_ntakenPath (h N 0 (by omega))
      (fun h hx => by
        obtain ⟨_, _, _, _, _, _, hq⟩ := hx
        exact absurd rfl hq)
  intro M
  induction M with
  | zero =>
      intro j hj
      rw [show j = N from by omega]
      simpa using hlast
  | succ n ih =>
      intro j hj
      have hstayB : cpsBranchWithin (n * m + m) exitB cr QB hdr
          (fun h => (inv (j + 1 + n + 1) ** ⌜(0 : Word) ≠ (0 : Word)⌝) h) exitB QB := by
        intro R hR s hcr hQR hpc
        exact ⟨0, Nat.zero_le _, s, rfl, Or.inr ⟨hpc, hQR⟩⟩
      have hmerge := cpsBranchWithin_merge_branch_same_cr
        (hiter j (by omega)) (ih (j + 1) (by omega)) hstayB
      rw [show (n + 1) * m + m = m + (n * m + m) from by
        rw [Nat.succ_mul]; omega]
      rw [show j + 1 + n + 1 = j + (n + 1) + 1 from by omega] at hmerge
      exact hmerge

/-! ## swapDiv Stage A: helpers + bit-round (B+732..B+780) -/

private theorem regIs_val_congr {r : Reg} {v v' : Word} (hvv : v = v') :
    ∀ h, (r ↦ᵣ v) h → (r ↦ᵣ v') h := by
  intro h hx
  rw [← hvv]
  exact hx

private theorem pure_drop_mid {L1 L2 : Assertion} {P : Prop} {R : Assertion} :
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

/-- bltz fall arm: `slli t2; j B+756` (B+740→B+756), t1 keeps `rv<<<1`. -/
private theorem bit_fall_arm (rv tv : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 2 (PriceK + 740) (PriceK + 756) priceCode
      (((.x7 ↦ᵣ tv) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR))
      (((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) **
        (.x0 ↦ᵣ (0 : Word))) ** FR) := by
  have hs := slli_spec_gen_same_within .x7 tv (1 : BitVec 6) (PriceK + 740) (by decide)
  have hj := jal_x0_spec_gen_within (12 : BitVec 21) (PriceK + 744)
  rw [show (PriceK + 744 : Word) + signExtend21 (12 : BitVec 21) = PriceK + 756 from by
      rw [show signExtend21 (12 : BitVec 21) = (12 : Word) from by decide]; decide] at hj
  have hsF : cpsTripleWithin 1 (PriceK + 740) (PriceK + 744) priceCode
      ((.x7 ↦ᵣ tv) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR))
      ((.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
        ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hFR)) hs)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[185]'(by decide) = .SLLI .x7 .x7 1 := by decide
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 740)
      amsterdamBlobGasPriceU256_prog 185 (.SLLI .x7 .x7 1) (by decide) (by decide) hins
      (by decide) a i hi
  have hjF : cpsTripleWithin 1 (PriceK + 744) (PriceK + 756) priceCode
      (empAssertion ** ((.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
        ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR)))
      (empAssertion ** ((.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
        ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR))) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs hFR))) hj)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[186]'(by decide) = .JAL .x0 (12 : BitVec 21) := by
      decide
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 744)
      amsterdamBlobGasPriceU256_prog 186 (.JAL .x0 (12 : BitVec 21)) (by decide) (by decide)
      hins (by decide) a i hi
  have hjF' := cpsTripleWithin_weaken
    (by intro h hx; rw [sepConj_emp_left']; exact hx) (fun _ hx => hx) hjF
  have hseq := cpsTripleWithin_seq_same_cr hsF hjF'
  refine cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
    (by intro h hx; rw [sepConj_emp_left'] at hx; xperm_hyp hx) hseq

/-- bltz taken arm: `slli t2; addi t1,1` (B+748→B+756), t1 becomes `rv<<<1 + 1`. -/
private theorem bit_taken_arm (rv tv : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 2 (PriceK + 748) (PriceK + 756) priceCode
      (((.x7 ↦ᵣ tv) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR))
      (((.x6 ↦ᵣ ((rv <<< (1 : BitVec 6).toNat) + signExtend12 (1 : BitVec 12))) **
        (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word))) ** FR) := by
  have hs := slli_spec_gen_same_within .x7 tv (1 : BitVec 6) (PriceK + 748) (by decide)
  have ha := addi_spec_gen_same_within .x6 (rv <<< (1 : BitVec 6).toNat) (1 : BitVec 12)
    (PriceK + 752) (by decide)
  have hsF : cpsTripleWithin 1 (PriceK + 748) (PriceK + 752) priceCode
      ((.x7 ↦ᵣ tv) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR))
      ((.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
        ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hFR)) hs)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[187]'(by decide) = .SLLI .x7 .x7 1 := by decide
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 748)
      amsterdamBlobGasPriceU256_prog 187 (.SLLI .x7 .x7 1) (by decide) (by decide) hins
      (by decide) a i hi
  have haF : cpsTripleWithin 1 (PriceK + 752) (PriceK + 756) priceCode
      ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
        ((.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** FR))
      ((.x6 ↦ᵣ ((rv <<< (1 : BitVec 6).toNat) + signExtend12 (1 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) ** ((.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hFR)) ha)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[188]'(by decide) = .ADDI .x6 .x6 1 := by decide
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 752)
      amsterdamBlobGasPriceU256_prog 188 (.ADDI .x6 .x6 1) (by decide) (by decide) hins
      (by decide) a i hi
  have haF' : cpsTripleWithin 1 (PriceK + 752) (PriceK + 756) priceCode
      ((.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
        ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR))
      ((.x6 ↦ᵣ ((rv <<< (1 : BitVec 6).toNat) + signExtend12 (1 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) ** ((.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) haF
  have hseq := cpsTripleWithin_seq_same_cr hsF haF'
  refine cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
    (by intro h hx; xperm_hyp hx) hseq

/-- bltz taken arm, pure-carrying: the branch leaf's `⌜slt⌝` rides through the frame
(`bit_taken_arm` invoked with `FR := ⌜slt⌝ ** FR`) so the post can be stated in
if-form — consumed at the diamond merge. -/
private theorem bit_taken_arm_p (rv tv : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 2 (PriceK + 748) (PriceK + 756) priceCode
      (((.x7 ↦ᵣ tv) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜BitVec.slt tv (0 : Word)⌝) **
        ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR))
      (((.x6 ↦ᵣ ((rv <<< (1 : BitVec 6).toNat) +
          (if BitVec.slt tv (0 : Word) then 1 else 0))) **
        (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word))) ** FR) := by
  have hcore := bit_taken_arm rv tv (⌜BitVec.slt tv (0 : Word)⌝ ** FR)
    (pcFree_sepConj pcFree_pure hFR)
  refine cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) ?_ hcore
  intro h hx
  obtain ⟨h1, h2, hd, hu, h1h, h2h⟩ := hx
  obtain ⟨h3, h4, hd2, hu2, h3h, h4h⟩ := h2h
  obtain ⟨heE, hslt⟩ := h3h
  have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hv : ((rv <<< (1 : BitVec 6).toNat) + signExtend12 (1 : BitVec 12)) =
      ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) := by
    rw [hse, if_pos hslt]
  rw [hv] at h1h
  have h24 : h2 = h4 := by rw [← hu2, heE]; exact PartialState.union_empty_left
  exact ⟨h1, h2, hd, hu, h1h, by rw [h24]; exact h4h⟩

/-- bltz fall arm, pure-carrying (mirror of `bit_taken_arm_p`). -/
private theorem bit_fall_arm_p (rv tv : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 2 (PriceK + 740) (PriceK + 756) priceCode
      (((.x7 ↦ᵣ tv) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜¬BitVec.slt tv (0 : Word)⌝) **
        ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR))
      (((.x6 ↦ᵣ ((rv <<< (1 : BitVec 6).toNat) +
          (if BitVec.slt tv (0 : Word) then 1 else 0))) **
        (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word))) ** FR) := by
  have hcore := bit_fall_arm rv tv (⌜¬BitVec.slt tv (0 : Word)⌝ ** FR)
    (pcFree_sepConj pcFree_pure hFR)
  refine cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) ?_ hcore
  intro h hx
  obtain ⟨h1, h2, hd, hu, h1h, h2h⟩ := hx
  obtain ⟨h3, h4, hd2, hu2, h3h, h4h⟩ := h2h
  obtain ⟨heE, hns⟩ := h3h
  have hv : (rv <<< (1 : BitVec 6).toNat) =
      ((rv <<< (1 : BitVec 6).toNat) +
        (if BitVec.slt tv (0 : Word) then 1 else 0)) := by
    rw [if_neg hns]; simp
  rw [hv] at h1h
  have h24 : h2 = h4 := by rw [← hu2, heE]; exact PartialState.union_empty_left
  exact ⟨h1, h2, hd, hu, h1h, by rw [h24]; exact h4h⟩

/-- bltu fall arm (subtract path): `sub t1,t1,t0; addi t3,t3,1`. -/
private theorem bltu_fall_arm (rp dv qs : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 2 (PriceK + 764) (PriceK + 772) priceCode
      (((.x6 ↦ᵣ rp) ** (.x5 ↦ᵣ dv)) ** ((.x28 ↦ᵣ qs) ** FR))
      (((.x6 ↦ᵣ (rp - dv)) ** (.x5 ↦ᵣ dv) ** (.x28 ↦ᵣ (qs + signExtend12 (1 : BitVec 12)))) **
        FR) := by
  have hsub := sub_spec_gen_rd_eq_rs1_within .x6 .x5 rp dv (PriceK + 764) (by decide)
  have hadd := addi_spec_gen_same_within .x28 qs (1 : BitVec 12) (PriceK + 768) (by decide)
  have hsubF : cpsTripleWithin 1 (PriceK + 764) (PriceK + 768) priceCode
      (((.x6 ↦ᵣ rp) ** (.x5 ↦ᵣ dv)) ** ((.x28 ↦ᵣ qs) ** FR))
      (((.x6 ↦ᵣ (rp - dv)) ** (.x5 ↦ᵣ dv)) ** ((.x28 ↦ᵣ qs) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _
      (pcFree_sepConj pcFree_regIs hFR) hsub)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[191]'(by decide) = .SUB .x6 .x6 .x5 := by decide
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 764)
      amsterdamBlobGasPriceU256_prog 191 (.SUB .x6 .x6 .x5) (by decide) (by decide) hins
      (by decide) a i hi
  have haddF : cpsTripleWithin 1 (PriceK + 768) (PriceK + 772) priceCode
      ((.x28 ↦ᵣ qs) ** ((.x6 ↦ᵣ (rp - dv)) ** (.x5 ↦ᵣ dv) ** FR))
      ((.x28 ↦ᵣ (qs + signExtend12 (1 : BitVec 12))) ** ((.x6 ↦ᵣ (rp - dv)) ** (.x5 ↦ᵣ dv) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hFR)) hadd)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[192]'(by decide) = .ADDI .x28 .x28 1 := by decide
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 768)
      amsterdamBlobGasPriceU256_prog 192 (.ADDI .x28 .x28 1) (by decide) (by decide) hins
      (by decide) a i hi
  have haddF' : cpsTripleWithin 1 (PriceK + 768) (PriceK + 772) priceCode
      (((.x6 ↦ᵣ (rp - dv)) ** (.x5 ↦ᵣ dv)) ** ((.x28 ↦ᵣ qs) ** FR))
      ((.x28 ↦ᵣ (qs + signExtend12 (1 : BitVec 12))) ** ((.x6 ↦ᵣ (rp - dv)) ** (.x5 ↦ᵣ dv) ** FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) haddF
  have hseq := cpsTripleWithin_seq_same_cr hsubF haddF'
  refine cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
    (by intro h hx; xperm_hyp hx) hseq

/-- bltu fall arm, pure-carrying (⌜¬ult⌝ rides the frame; if-form post). -/
private theorem bltu_fall_arm_p (rp dv qs : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 2 (PriceK + 764) (PriceK + 772) priceCode
      (((.x6 ↦ᵣ rp) ** (.x5 ↦ᵣ dv) ** ⌜¬BitVec.ult rp dv⌝) ** ((.x28 ↦ᵣ qs) ** FR))
      (((.x6 ↦ᵣ (if BitVec.ult rp dv then rp else rp - dv)) ** (.x5 ↦ᵣ dv) **
          (.x28 ↦ᵣ (qs + (if BitVec.ult rp dv then 0 else 1)))) ** FR) := by
  have hcore := bltu_fall_arm rp dv qs (⌜¬BitVec.ult rp dv⌝ ** FR)
    (pcFree_sepConj pcFree_pure hFR)
  refine cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) ?_ hcore
  intro h hx
  obtain ⟨h1, h2, hd, hu, h1h, h2h⟩ := hx
  obtain ⟨h3, h4, hd2, hu2, h3h, h4h⟩ := h2h
  obtain ⟨heE, hnult⟩ := h3h
  have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hv1 : (rp - dv) = (if BitVec.ult rp dv then rp else rp - dv) := by rw [if_neg hnult]
  have hv2 : (qs + signExtend12 (1 : BitVec 12)) =
      (qs + (if BitVec.ult rp dv then 0 else 1)) := by rw [hse, if_neg hnult]
  rw [hv1, hv2] at h1h
  have h24 : h2 = h4 := by rw [← hu2, heE]; exact PartialState.union_empty_left
  exact ⟨h1, h2, hd, hu, h1h, by rw [h24]; exact h4h⟩

/-- bltu skip arm (taken side, 0 instructions): values unchanged, pure consumed
into the if-forms. -/
private theorem bltu_skip_arm (rp dv qs : Word) (FR : Assertion) (_hFR : FR.pcFree) :
    cpsTripleWithin 2 (PriceK + 772) (PriceK + 772) priceCode
      (((.x6 ↦ᵣ rp) ** (.x5 ↦ᵣ dv) ** (.x28 ↦ᵣ qs) ** ⌜BitVec.ult rp dv⌝) ** FR)
      (((.x6 ↦ᵣ (if BitVec.ult rp dv then rp else rp - dv)) ** (.x5 ↦ᵣ dv) **
          (.x28 ↦ᵣ (qs + (if BitVec.ult rp dv then 0 else 1)))) ** FR) := by
  have hrefl : cpsTripleWithin 0 (PriceK + 772) (PriceK + 772) CodeReq.empty
      (((.x6 ↦ᵣ rp) ** (.x5 ↦ᵣ dv) ** (.x28 ↦ᵣ qs) ** ⌜BitVec.ult rp dv⌝) ** FR)
      (((.x6 ↦ᵣ (if BitVec.ult rp dv then rp else rp - dv)) ** (.x5 ↦ᵣ dv) **
          (.x28 ↦ᵣ (qs + (if BitVec.ult rp dv then 0 else 1)))) ** FR) :=
    cpsTripleWithin_refl (by
      intro h hx
      obtain ⟨h1, h2, hd, hu, h1h, h2h⟩ := hx
      obtain ⟨g1, g234, gd1, gu1, g1h, g234h⟩ := h1h
      obtain ⟨g2, g34, gd2, gu2, g2h, g34h⟩ := g234h
      obtain ⟨g3, g4, gd3, gu3, g3h, g4h⟩ := g34h
      obtain ⟨geE, hult⟩ := g4h
      have hg34 : g34 = g3 := by rw [← gu3, geE]; exact PartialState.union_empty_right
      have hg234 : g234 = g2.union g3 := by rw [← gu2, hg34]
      have g1h' : (.x6 ↦ᵣ (if BitVec.ult rp dv then rp else rp - dv)) g1 := by
        rw [if_pos hult]; exact g1h
      have g3h' : (.x28 ↦ᵣ (qs + (if BitVec.ult rp dv then 0 else 1))) g3 := by
        rw [if_pos hult]; simpa using g3h
      have hd1' : g1.Disjoint (g2.union g3) := by rw [hg234] at gd1; exact gd1
      have gd2' : g2.Disjoint g3 := by rw [hg34] at gd2; exact gd2
      refine ⟨g1.union (g2.union g3), h2, ?_, ?_, ⟨g1, g2.union g3, hd1', rfl, g1h',
        ⟨g2, g3, gd2', rfl, g2h, g3h'⟩⟩, h2h⟩
      · rw [← gu1, hg234] at hd; exact hd
      · rw [← hu, ← gu1, hg234])
  have hex := cpsTripleWithin_extend_code (fun a i hi => by
    show priceCode a = some i
    rw [show (CodeReq.empty a : Option Instr) = none from rfl] at hi
    exact absurd hi (by simp)) hrefl
  exact cpsTripleWithin_mono_nSteps (Nat.zero_le 2) hex

/-- The bltz diamond at `PriceK+736`: branch, then both arms converge at `PriceK+756`
with the common if-form remainder value. -/
private theorem merged_bltz (rv tv : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 3 (PriceK + 736) (PriceK + 756) priceCode
    (((.x7 ↦ᵣ tv) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR))
    (((.x6 ↦ᵣ ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0))) **
      (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word))) ** FR) := by
  have hleaf := blt_spec_gen_within .x7 .x0 (12 : BitVec 13) tv (0 : Word) (PriceK + 736)
  rw [show (PriceK + 736 : Word) + signExtend13 (12 : BitVec 13) = PriceK + 748 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; decide,
    show (PriceK + 736 : Word) + 4 = PriceK + 740 from by decide] at hleaf
  have hleafF := cpsBranchWithin_frameR ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) ** FR)
    (pcFree_sepConj pcFree_regIs hFR) hleaf
  have hmono : ∀ a i,
      (CodeReq.singleton (PriceK + 736) (.BLT .x7 .x0 (12 : BitVec 13))) a = some i →
      priceCode a = some i := by
    intro a i hi
    show priceCode a = some i
    have hins : amsterdamBlobGasPriceU256_prog[184]'(by decide) =
        .BLT .x7 .x0 (12 : BitVec 13) := by decide
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 736) amsterdamBlobGasPriceU256_prog 184
      (.BLT .x7 .x0 (12 : BitVec 13)) (by decide) (by decide) hins (by decide) a i hi
  have hleafE := cpsBranchWithin_extend_code hmono hleafF
  exact cpsBranchWithin_merge_same_cr hleafE (bit_taken_arm_p rv tv FR hFR)
    (bit_fall_arm_p rv tv FR hFR)

/-- The bltu diamond at `PriceK+760`: taken (no underflow) skips to `PriceK+772`,
fall subtracts; both converge with the common if-form remainder/quotient values. -/
private theorem merged_bltu (rp dv qs : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 3 (PriceK + 760) (PriceK + 772) priceCode
    (((.x6 ↦ᵣ rp) ** (.x5 ↦ᵣ dv)) ** ((.x28 ↦ᵣ qs) ** FR))
    (((.x6 ↦ᵣ (if BitVec.ult rp dv then rp else rp - dv)) ** (.x5 ↦ᵣ dv) **
        (.x28 ↦ᵣ (qs + (if BitVec.ult rp dv then 0 else 1)))) ** FR) := by
  have hleaf := bltu_spec_gen_within .x6 .x5 (12 : BitVec 13) rp dv (PriceK + 760)
  rw [show (PriceK + 760 : Word) + signExtend13 (12 : BitVec 13) = PriceK + 772 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; decide,
    show (PriceK + 760 : Word) + 4 = PriceK + 764 from by decide] at hleaf
  have hleafF := cpsBranchWithin_frameR ((.x28 ↦ᵣ qs) ** FR)
    (pcFree_sepConj pcFree_regIs hFR) hleaf
  have hmono : ∀ a i,
      (CodeReq.singleton (PriceK + 760) (.BLTU .x6 .x5 (12 : BitVec 13))) a = some i →
      priceCode a = some i := by
    intro a i hi
    show priceCode a = some i
    have hins : amsterdamBlobGasPriceU256_prog[190]'(by decide) =
        .BLTU .x6 .x5 (12 : BitVec 13) := by decide
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 760) amsterdamBlobGasPriceU256_prog 190
      (.BLTU .x6 .x5 (12 : BitVec 13)) (by decide) (by decide) hins (by decide) a i hi
  have hleafE := cpsBranchWithin_extend_code hmono hleafF
  have h_t : cpsTripleWithin 2 (PriceK + 772) (PriceK + 772) priceCode
      (((.x6 ↦ᵣ rp) ** (.x5 ↦ᵣ dv) ** ⌜BitVec.ult rp dv⌝) ** ((.x28 ↦ᵣ qs) ** FR))
      (((.x6 ↦ᵣ (if BitVec.ult rp dv then rp else rp - dv)) ** (.x5 ↦ᵣ dv) **
          (.x28 ↦ᵣ (qs + (if BitVec.ult rp dv then 0 else 1)))) ** FR) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx)
      (bltu_skip_arm rp dv qs FR hFR)
  exact cpsBranchWithin_merge_same_cr hleafE h_t (bltu_fall_arm_p rp dv qs FR hFR)

/-- Bit-round part 1 (`PriceK+732 → PriceK+756`): `slli t1,t1,1` then the bltz diamond. -/
private theorem bitround_part1 (rv tv qv cv dv : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 4 (PriceK + 732) (PriceK + 756) priceCode
    (((.x6 ↦ᵣ rv) ** (.x7 ↦ᵣ tv) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ qv) ** (.x29 ↦ᵣ cv) **
      (.x5 ↦ᵣ dv)) ** FR)
    (((.x6 ↦ᵣ ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0))) **
      (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word))) **
      ((.x28 ↦ᵣ qv) ** (.x29 ↦ᵣ cv) ** (.x5 ↦ᵣ dv) ** FR)) := by
  have hs := slli_spec_gen_same_within .x6 rv (1 : BitVec 6) (PriceK + 732) (by decide)
  have hsF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ tv) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ qv) ** (.x29 ↦ᵣ cv) ** (.x5 ↦ᵣ dv) ** FR)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hFR))))) hs
  have hmono : ∀ a i,
      (CodeReq.singleton (PriceK + 732) (.SLLI .x6 .x6 (1 : BitVec 6))) a = some i →
      priceCode a = some i := by
    intro a i hi
    show priceCode a = some i
    have hins : amsterdamBlobGasPriceU256_prog[183]'(by decide) =
        .SLLI .x6 .x6 (1 : BitVec 6) := by decide
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 732) amsterdamBlobGasPriceU256_prog 183
      (.SLLI .x6 .x6 (1 : BitVec 6)) (by decide) (by decide) hins (by decide) a i hi
  have hsE := cpsTripleWithin_extend_code hmono hsF
  have hmz' : cpsTripleWithin 3 (PriceK + 736) (PriceK + 756) priceCode
      ((.x6 ↦ᵣ (rv <<< (1 : BitVec 6).toNat)) **
        ((.x7 ↦ᵣ tv) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ qv) ** (.x29 ↦ᵣ cv) ** (.x5 ↦ᵣ dv) **
          FR))
      (((.x6 ↦ᵣ ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0))) **
        (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x28 ↦ᵣ qv) ** (.x29 ↦ᵣ cv) ** (.x5 ↦ᵣ dv) ** FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx)
      (merged_bltz rv tv ((.x28 ↦ᵣ qv) ** (.x29 ↦ᵣ cv) ** (.x5 ↦ᵣ dv) ** FR)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs hFR))))
  refine cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
    (by intro h hx; xperm_hyp hx) (cpsTripleWithin_seq_same_cr hsE hmz')

/-- Bit-round part 2 (`PriceK+756 → PriceK+776`): `slli t3` then the bltu diamond then
`addi t4,t4,-1`. -/
private theorem bitround_part2 (rv tv qv cv dv : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 5 (PriceK + 756) (PriceK + 776) priceCode
    (((.x6 ↦ᵣ ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0))) **
      (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word))) **
      ((.x28 ↦ᵣ qv) ** (.x29 ↦ᵣ cv) ** (.x5 ↦ᵣ dv) ** FR))
    ((.x29 ↦ᵣ (cv + signExtend12 (-1 : BitVec 12))) **
      ((.x6 ↦ᵣ (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) +
          (if BitVec.slt tv (0 : Word) then 1 else 0)) dv
          then (rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)
          else (rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0) - dv)) **
        (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ ((qv <<< (1 : BitVec 6).toNat) +
          (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) +
            (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then 0 else 1))) **
        (.x5 ↦ᵣ dv) ** FR)) := by
  have hs2 := slli_spec_gen_same_within .x28 qv (1 : BitVec 6) (PriceK + 756) (by decide)
  have hs2F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0))) **
      (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ cv) **
      (.x5 ↦ᵣ dv) ** FR)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hFR))))) hs2
  have hmono2 : ∀ a i,
      (CodeReq.singleton (PriceK + 756) (.SLLI .x28 .x28 (1 : BitVec 6))) a = some i →
      priceCode a = some i := by
    intro a i hi
    show priceCode a = some i
    have hins : amsterdamBlobGasPriceU256_prog[189]'(by decide) =
        .SLLI .x28 .x28 (1 : BitVec 6) := by decide
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 756) amsterdamBlobGasPriceU256_prog 189
      (.SLLI .x28 .x28 (1 : BitVec 6)) (by decide) (by decide) hins (by decide) a i hi
  have hs2E := cpsTripleWithin_extend_code hmono2 hs2F
  have hmu' : cpsTripleWithin 3 (PriceK + 760) (PriceK + 772) priceCode
      ((.x28 ↦ᵣ (qv <<< (1 : BitVec 6).toNat)) **
        ((.x6 ↦ᵣ ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0))) **
          (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ cv) **
          (.x5 ↦ᵣ dv) ** FR))
      (((.x6 ↦ᵣ (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) +
          (if BitVec.slt tv (0 : Word) then 1 else 0)) dv
          then (rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)
          else (rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0) - dv)) **
        (.x5 ↦ᵣ dv) **
        (.x28 ↦ᵣ ((qv <<< (1 : BitVec 6).toNat) +
          (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) +
            (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then 0 else 1)))) **
        ((.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ cv) ** FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx)
      (merged_bltu ((rv <<< (1 : BitVec 6).toNat) +
          (if BitVec.slt tv (0 : Word) then 1 else 0)) dv (qv <<< (1 : BitVec 6).toNat)
        ((.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ cv) ** FR)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs hFR))))
  have hseq5 := cpsTripleWithin_seq_same_cr hs2E hmu'
  have ha := addi_spec_gen_same_within .x29 cv (-1 : BitVec 12) (PriceK + 772) (by decide)
  have haF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) +
          (if BitVec.slt tv (0 : Word) then 1 else 0)) dv
          then (rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)
          else (rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0) - dv)) **
      (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x28 ↦ᵣ ((qv <<< (1 : BitVec 6).toNat) +
        (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) +
          (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then 0 else 1))) **
      (.x5 ↦ᵣ dv) ** FR)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hFR))))) ha
  have hmono3 : ∀ a i,
      (CodeReq.singleton (PriceK + 772) (.ADDI .x29 .x29 (-1 : BitVec 12))) a = some i →
      priceCode a = some i := by
    intro a i hi
    show priceCode a = some i
    have hins : amsterdamBlobGasPriceU256_prog[193]'(by decide) =
        .ADDI .x29 .x29 (-1 : BitVec 12) := by decide
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 772) amsterdamBlobGasPriceU256_prog 193
      (.ADDI .x29 .x29 (-1 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi
  have haFE := cpsTripleWithin_extend_code hmono3 haF
  have haF' : cpsTripleWithin 1 (PriceK + 772) (PriceK + 776) priceCode
      (((.x6 ↦ᵣ (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) +
            (if BitVec.slt tv (0 : Word) then 1 else 0)) dv
            then (rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)
            else (rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0) - dv)) **
          (.x5 ↦ᵣ dv) **
          (.x28 ↦ᵣ ((qv <<< (1 : BitVec 6).toNat) +
            (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) +
              (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then 0 else 1)))) **
        ((.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ cv) ** FR))
      ((.x29 ↦ᵣ (cv + signExtend12 (-1 : BitVec 12))) **
        ((.x6 ↦ᵣ (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) +
            (if BitVec.slt tv (0 : Word) then 1 else 0)) dv
            then (rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)
            else (rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0) - dv)) **
          (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x28 ↦ᵣ ((qv <<< (1 : BitVec 6).toNat) +
            (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) +
              (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then 0 else 1))) **
          (.x5 ↦ᵣ dv) ** FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) haFE
  refine cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
    (by intro h hx; xperm_hyp hx) (cpsTripleWithin_seq_same_cr hseq5 haF')
/-- One full bit round: `slli t1; bltz-diamond; slli t3; bltu-diamond; addi t4,-1;
bnez t4` — back-edge to `PriceK+732` while the bit counter is nonzero. -/
theorem swapdiv_bitround (rv tv qv cv dv : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsBranchWithin 10 (PriceK + 732) priceCode
      (((.x6 ↦ᵣ rv) ** (.x7 ↦ᵣ tv) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ qv) **
        (.x29 ↦ᵣ cv) ** (.x5 ↦ᵣ dv)) ** FR)
      (PriceK + 732)
      (((.x6 ↦ᵣ (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) else ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) - dv)) ** (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ ((qv <<< (1 : BitVec 6).toNat) + (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then 0 else 1))) ** (.x29 ↦ᵣ (cv + signExtend12 (-1 : BitVec 12))) ** (.x5 ↦ᵣ dv) ** ⌜(cv + signExtend12 (-1 : BitVec 12)) ≠ (0 : Word)⌝) ** FR)
      (PriceK + 780)
      (((.x29 ↦ᵣ (cv + signExtend12 (-1 : BitVec 12))) ** (.x6 ↦ᵣ (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) else ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) - dv)) ** (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ ((qv <<< (1 : BitVec 6).toNat) + (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then 0 else 1))) ** (.x5 ↦ᵣ dv) ** ⌜(cv + signExtend12 (-1 : BitVec 12)) = (0 : Word)⌝) ** FR) := by
  have hb := bne_spec_gen_within .x29 .x0 (-44 : BitVec 13)
    (cv + signExtend12 (-1 : BitVec 12)) (0 : Word) (PriceK + 776)
  rw [show (PriceK + 776 : Word) + signExtend13 (-44 : BitVec 13) = PriceK + 732 from by
      rw [show signExtend13 (-44 : BitVec 13) = (-44 : Word) from by decide]; decide,
    show (PriceK + 776 : Word) + 4 = PriceK + 780 from by decide] at hb
  have hbF := cpsBranchWithin_frameR
    ((.x6 ↦ᵣ (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) else ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) - dv)) ** (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x28 ↦ᵣ ((qv <<< (1 : BitVec 6).toNat) + (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then 0 else 1))) ** (.x5 ↦ᵣ dv) ** FR)
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hFR))))
    hb
  have hins : amsterdamBlobGasPriceU256_prog[194]'(by decide) =
      .BNE .x29 .x0 (-44 : BitVec 13) := by decide
  have hmono : ∀ a i,
      (CodeReq.singleton (PriceK + 776) (.BNE .x29 .x0 (-44 : BitVec 13))) a = some i →
      priceCode a = some i := by
    intro a i hi
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 776)
      amsterdamBlobGasPriceU256_prog 194 (.BNE .x29 .x0 (-44 : BitVec 13))
      (by decide) (by decide) hins (by decide) a i hi
  have hbE := cpsBranchWithin_extend_code hmono hbF
  have hb' : cpsBranchWithin 1 (PriceK + 776) priceCode
      (((.x29 ↦ᵣ (cv + signExtend12 (-1 : BitVec 12))) ** (.x6 ↦ᵣ (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) else ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) - dv)) ** (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ ((qv <<< (1 : BitVec 6).toNat) + (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then 0 else 1))) ** (.x5 ↦ᵣ dv) ** FR))
      (PriceK + 732)
      (((.x6 ↦ᵣ (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) else ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) - dv)) ** (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ ((qv <<< (1 : BitVec 6).toNat) + (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then 0 else 1))) ** (.x29 ↦ᵣ (cv + signExtend12 (-1 : BitVec 12))) ** (.x5 ↦ᵣ dv) ** ⌜(cv + signExtend12 (-1 : BitVec 12)) ≠ (0 : Word)⌝) ** FR)
      (PriceK + 780)
      (((.x29 ↦ᵣ (cv + signExtend12 (-1 : BitVec 12))) ** (.x6 ↦ᵣ (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) else ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) - dv)) ** (.x7 ↦ᵣ (tv <<< (1 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ ((qv <<< (1 : BitVec 6).toNat) + (if BitVec.ult ((rv <<< (1 : BitVec 6).toNat) + (if BitVec.slt tv (0 : Word) then 1 else 0)) dv then 0 else 1))) ** (.x5 ↦ᵣ dv) ** ⌜(cv + signExtend12 (-1 : BitVec 12)) = (0 : Word)⌝) ** FR) :=
    cpsBranchWithin_weaken (by intro h hx; xperm_hyp hx) (by intro h hx; xperm_hyp hx)
      (by intro h hx; xperm_hyp hx) hbE
  have h12 := cpsTripleWithin_seq_same_cr (bitround_part1 rv tv qv cv dv FR hFR)
    (bitround_part2 rv tv qv cv dv FR hFR)
  exact cpsTripleWithin_seq_cpsBranchWithin_same_cr h12 hb'

/-! ## swapDiv: the 64-fold bit loop (B+732..B+780 folded 63+1 times) -/

/-- The bit-loop countdown register value after `j` rounds (starts at 64). -/
private def cnt : Nat → Word
  | 0 => (64 : Word)
  | j + 1 => cnt j + signExtend12 (-1 : BitVec 12)

private theorem cnt_zero : cnt 64 = (0 : Word) := by decide

/-- Restoring-division bit state after `j` bit rounds: remainder, shifted
limb, quotient.  The step is spelled exactly as the bit-round post values so
the one-round congruence is definitional. -/
def divst (dv r0 t0 q0 : Word) : Nat → Word × Word × Word
  | 0 => (r0, t0, q0)
  | j + 1 =>
    ((if BitVec.ult ((divst dv r0 t0 q0 j).1 <<< (1 : BitVec 6).toNat
          + (if BitVec.slt (divst dv r0 t0 q0 j).2.1 (0 : Word) then 1 else 0)) dv
        then (divst dv r0 t0 q0 j).1 <<< (1 : BitVec 6).toNat
          + (if BitVec.slt (divst dv r0 t0 q0 j).2.1 (0 : Word) then 1 else 0)
        else (divst dv r0 t0 q0 j).1 <<< (1 : BitVec 6).toNat
          + (if BitVec.slt (divst dv r0 t0 q0 j).2.1 (0 : Word) then 1 else 0) - dv),
     (divst dv r0 t0 q0 j).2.1 <<< (1 : BitVec 6).toNat,
     (divst dv r0 t0 q0 j).2.2 <<< (1 : BitVec 6).toNat
       + (if BitVec.ult ((divst dv r0 t0 q0 j).1 <<< (1 : BitVec 6).toNat
            + (if BitVec.slt (divst dv r0 t0 q0 j).2.1 (0 : Word) then 1 else 0)) dv
          then 0 else 1))

/-- Loop invariant for the 64-fold: the six pinned temps of the bit round. -/
private def sdinv (dv r0 t0 q0 : Word) (FR : Assertion) : Nat → Assertion :=
  fun j => (((.x6 ↦ᵣ (divst dv r0 t0 q0 j).1) **
    (.x7 ↦ᵣ (divst dv r0 t0 q0 j).2.1) **
    (.x0 ↦ᵣ (0 : Word)) **
    (.x28 ↦ᵣ (divst dv r0 t0 q0 j).2.2) **
    (.x29 ↦ᵣ (cnt j)) **
    (.x5 ↦ᵣ dv)) ** FR)

/-- Exit postcondition: the fall-exit state with values existentially packed
(the exit pure `CV1 = 0` is retained on the packed counter). -/
private def sdqb (dv : Word) (FR : Assertion) : Assertion :=
  fun h => ∃ r t q c, (((.x29 ↦ᵣ c) ** (.x6 ↦ᵣ r) ** (.x7 ↦ᵣ t) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x28 ↦ᵣ q) ** (.x5 ↦ᵣ dv) ** ⌜c = (0 : Word)⌝) ** FR) h

/-- Drop a trailing pure from a six-atom right-nested lead group. -/
private theorem pure_drop_6 {a1 a2 a3 a4 a5 a6 : Assertion} {P : Prop} {FR : Assertion} :
    ∀ h, ((a1 ** (a2 ** (a3 ** (a4 ** (a5 ** (a6 ** ⌜P⌝)))))) ** FR) h →
      ((a1 ** (a2 ** (a3 ** (a4 ** (a5 ** a6))))) ** FR) h := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hG, hFR⟩ := hx
  obtain ⟨g1, r1, d1, u1, ha1, hR1⟩ := hG
  obtain ⟨g2, r2, d2, u2, ha2, hR2⟩ := hR1
  obtain ⟨g3, r3, d3, u3, ha3, hR3⟩ := hR2
  obtain ⟨g4, r4, d4, u4, ha4, hR4⟩ := hR3
  obtain ⟨g5, r5, d5, u5, ha5, hR5⟩ := hR4
  obtain ⟨g6, gP, d6, u6, ha6, hP⟩ := hR5
  have hPe : gP = PartialState.empty := hP.1
  have hr5 : r5 = g6 := by
    rw [← u6, hPe]
    exact PartialState.union_empty_right
  rw [hr5] at u5 d5
  have hr4 : r4 = g5.union g6 := by rw [← u5]
  have hr3 : r3 = g4.union (g5.union g6) := by rw [← u4, ← u5]
  have hr2 : r2 = g3.union (g4.union (g5.union g6)) := by rw [← u3, ← u4, ← u5]
  have hr1 : r1 = g2.union (g3.union (g4.union (g5.union g6))) := by
    rw [← u2, ← u3, ← u4, ← u5]
  rw [hr1] at d1
  rw [hr2] at d2
  rw [hr3] at d3
  rw [hr4] at d4
  have h1eq : h1 = g1.union (g2.union (g3.union (g4.union (g5.union g6)))) := by
    rw [← u1, ← hr1]
  refine ⟨g1.union (g2.union (g3.union (g4.union (g5.union g6)))), h2, ?_, ?_,
    ⟨g1, g2.union (g3.union (g4.union (g5.union g6))), d1, rfl, ha1,
      ⟨g2, g3.union (g4.union (g5.union g6)), d2, rfl, ha2,
        ⟨g3, g4.union (g5.union g6), d3, rfl, ha3,
          ⟨g4, g5.union g6, d4, rfl, ha4,
            ⟨g5, g6, d5, rfl, ha5, ha6⟩⟩⟩⟩⟩, hFR⟩
  · rw [← h1eq]
    exact hd
  · rw [← h1eq]
    exact hu

/-- `cnt j = 64 - j` (as Words): the countdown relation. -/
private theorem cnt_add : ∀ j, j ≤ 64 → cnt j + BitVec.ofNat 64 j = (64 : Word) := by
  intro j
  induction j with
  | zero => simp [cnt]
  | succ n ih =>
    intro _
    have h1 : BitVec.ofNat 64 (n+1) = BitVec.ofNat 64 n + (1:Word) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat]
    have h2 := ih (by omega)
    have hse : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
    have hn1 : (-1 : Word) + (1 : Word) = (0 : Word) := by decide
    rw [cnt, hse, h1]
    rw [BitVec.add_comm (BitVec.ofNat 64 n) (1 : Word),
      ← BitVec.add_assoc (cnt n + (-1 : Word)) (1 : Word) (BitVec.ofNat 64 n),
      BitVec.add_assoc (cnt n) (-1 : Word) (1 : Word), hn1]
    have hz : cnt n + (0 : Word) = cnt n := by simp
    rw [hz]
    exact h2

/-- The bit counter is nonzero before round 64, so interior falls are vacuous. -/
private theorem cnt_ne_zero : ∀ j, j < 64 → cnt j ≠ (0 : Word) := by
  intro j h h0
  have hadd : cnt j + BitVec.ofNat 64 j = (64 : Word) := cnt_add j (by omega)
  rw [h0] at hadd
  have hlt : BitVec.ofNat 64 j < (64 : Word) := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat]
    rw [show BitVec.toNat (64:Word) = 64 from rfl]
    omega
  rw [show ((0:Word) + BitVec.ofNat 64 j) = BitVec.ofNat 64 j from by simp] at hadd
  rw [← hadd] at hlt
  exact absurd hlt (by simp)

/-- Concrete-exit form of the bit fold: the 64-bit loop's fall exit pins the final
divstate values directly (remainder, shifted-out limb, quotient, zero counter) so the
limb-level round can consume them without existentials.  Interior falls are vacuous:
the counter is nonzero before round 64 (`cnt_ne_zero`). -/
private def sdqc (dv r0 t0 q0 : Word) (FR : Assertion) : Assertion :=
  fun h => (((.x29 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (divst dv r0 t0 q0 64).1) **
    (.x7 ↦ᵣ (divst dv r0 t0 q0 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x28 ↦ᵣ (divst dv r0 t0 q0 64).2.2) ** (.x5 ↦ᵣ dv)) ** FR) h

private theorem swapdiv_hiter_q (dv r0 t0 q0 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    ∀ j < 63, cpsBranchWithin 10 (PriceK + 732) priceCode (sdinv dv r0 t0 q0 FR j)
      (PriceK + 732) (sdinv dv r0 t0 q0 FR (j + 1)) (PriceK + 780) (sdqc dv r0 t0 q0 FR) := by
  intro j _
  exact cpsBranchWithin_weaken (fun _ hx => hx)
    (by intro h hx; exact pure_drop_6 _ hx)
    (by intro h hx
        obtain ⟨h1, h2, hd, hu, hG, hFR⟩ := hx
        obtain ⟨_, r2, _, _, _, h2h⟩ := hG
        obtain ⟨_, r3, _, _, _, h3h⟩ := h2h
        obtain ⟨_, r4, _, _, _, h4h⟩ := h3h
        obtain ⟨_, r5, _, _, _, h5h⟩ := h4h
        obtain ⟨_, r6, _, _, _, h6h⟩ := h5h
        obtain ⟨_, _, _, _, _, hP⟩ := h6h
        obtain ⟨_, hPp⟩ := hP
        exact absurd hPp (cnt_ne_zero (j + 1) (by omega)))
    (swapdiv_bitround (divst dv r0 t0 q0 j).1 (divst dv r0 t0 q0 j).2.1
      (divst dv r0 t0 q0 j).2.2 (cnt j) dv FR hFR)

private theorem swapdiv_hiter (dv r0 t0 q0 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    ∀ j, j < 63 →
      cpsBranchWithin 10 (PriceK + 732) priceCode
        (sdinv dv r0 t0 q0 FR j) (PriceK + 732) (sdinv dv r0 t0 q0 FR (j + 1))
        (PriceK + 780) (sdqb dv FR) := by
  intro j _
  have hr := swapdiv_bitround (divst dv r0 t0 q0 j).1 (divst dv r0 t0 q0 j).2.1
    (divst dv r0 t0 q0 j).2.2 (cnt j) dv FR hFR
  refine cpsBranchWithin_weaken (fun _ hx => hx) ?_ ?_ hr
  · intro h hx
    exact pure_drop_6 _ hx
  · intro h hx
    exact ⟨_, _, _, _, hx⟩

private theorem swapdiv_hlast (dv r0 t0 q0 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsBranchWithin 10 (PriceK + 732) priceCode (sdinv dv r0 t0 q0 FR 63)
      (PriceK + 732) (fun h => (sdinv dv r0 t0 q0 FR 64 ** ⌜(0 : Word) ≠ (0 : Word)⌝) h)
      (PriceK + 780) (sdqb dv FR) := by
  have hr := swapdiv_bitround (divst dv r0 t0 q0 63).1 (divst dv r0 t0 q0 63).2.1
    (divst dv r0 t0 q0 63).2.2 (cnt 63) dv FR hFR
  refine cpsBranchWithin_weaken (fun _ hx => hx) ?_ ?_ hr
  · intro h hx
    obtain ⟨h1, h2, _, _, hG, _⟩ := hx
    obtain ⟨_, _, _, _, _, hR1⟩ := hG
    obtain ⟨_, _, _, _, _, hR2⟩ := hR1
    obtain ⟨_, _, _, _, _, hR3⟩ := hR2
    obtain ⟨_, _, _, _, _, hR4⟩ := hR3
    obtain ⟨_, _, _, _, _, hR5⟩ := hR4
    obtain ⟨_, _, _, _, _, hP⟩ := hR5
    obtain ⟨_, hPp⟩ := hP
    exact (hPp cnt_zero).elim
  · intro h hx
    exact ⟨_, _, _, _, hx⟩

/-- The 64-round bit loop as one triple: 63 iterating rounds plus the final
round whose taken (back-edge) branch is refuted by `cnt_zero`. -/
theorem swapdiv_bitfold (dv r0 t0 q0 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 640 (PriceK + 732) (PriceK + 780) priceCode
      (sdinv dv r0 t0 q0 FR 0) (sdqb dv FR) :=
  countdown_loop_triple (N := 63) (m := 10) (sdinv dv r0 t0 q0 FR) (sdqb dv FR)
    (swapdiv_hiter dv r0 t0 q0 FR hFR) (swapdiv_hlast dv r0 t0 q0 FR hFR)

#print axioms swapdiv_bitfold

private theorem swapdiv_hlast_q (dv r0 t0 q0 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsBranchWithin 10 (PriceK + 732) priceCode (sdinv dv r0 t0 q0 FR 63)
      (PriceK + 732) (fun h => (sdinv dv r0 t0 q0 FR 64 ** ⌜(0 : Word) ≠ (0 : Word)⌝) h)
      (PriceK + 780) (sdqc dv r0 t0 q0 FR) := by
  have hr := swapdiv_bitround (divst dv r0 t0 q0 63).1 (divst dv r0 t0 q0 63).2.1
    (divst dv r0 t0 q0 63).2.2 (cnt 63) dv FR hFR
  refine cpsBranchWithin_weaken (fun _ hx => hx) ?_ ?_ hr
  · intro h hx
    obtain ⟨h1, h2, _, _, hG, _⟩ := hx
    obtain ⟨_, _, _, _, _, hR1⟩ := hG
    obtain ⟨_, _, _, _, _, hR2⟩ := hR1
    obtain ⟨_, _, _, _, _, hR3⟩ := hR2
    obtain ⟨_, _, _, _, _, hR4⟩ := hR3
    obtain ⟨_, _, _, _, _, hR5⟩ := hR4
    obtain ⟨_, _, _, _, _, hP⟩ := hR5
    obtain ⟨_, hPp⟩ := hP
    exact (hPp cnt_zero).elim
  · intro h hx
    obtain ⟨h1, h2, hd, hu, hG, hFR⟩ := hx
    obtain ⟨g29, r2, d29, u29, hg29, hR2⟩ := hG
    obtain ⟨g6, r3, d6, u6, hg6, hR3⟩ := hR2
    obtain ⟨g7, r4, d7, u4, hg7, hR4⟩ := hR3
    obtain ⟨g0, r5, d0, u5, hg0, hR5⟩ := hR4
    obtain ⟨g28, r6, d28, u28, hg28, hR6⟩ := hR5
    obtain ⟨g5, gP, d5, u5p, hg5, hPe, _hPp⟩ := hR6
    -- x29 pin: counter value is cnt 64 = 0
    have hc0 : (cnt 63 + signExtend12 (-1 : BitVec 12)) = (0 : Word) := by
      rw [show (cnt 63 + signExtend12 (-1 : BitVec 12)) = cnt 64 from rfl, cnt_zero]
    -- the pure heap is empty, so the x5 subheap is the whole r6
    have hr6 : g5 = r6 := by
      rw [hPe] at u5p
      rw [PartialState.union_empty_right] at u5p
      exact u5p
    rw [← hr6] at d28 u28
    exact ⟨h1, h2, hd, hu,
      ⟨g29, r2, d29, u29, by rw [hc0] at hg29; exact hg29,
        ⟨g6, r3, d6, u6, hg6,
          ⟨g7, r4, d7, u4, hg7,
            ⟨g0, r5, d0, u5, hg0,
              ⟨g28, g5, d28, u28, hg28, hg5⟩⟩⟩⟩⟩,
      hFR⟩

/-- The 64-round bit loop with a CONCRETE fall exit: pins the final remainder,
shifted limb, quotient, and zero counter for the limb-level consumer. -/
theorem swapdiv_bitfold_q (dv r0 t0 q0 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 640 (PriceK + 732) (PriceK + 780) priceCode
      (sdinv dv r0 t0 q0 FR 0) (sdqc dv r0 t0 q0 FR) :=
  countdown_loop_triple (N := 63) (m := 10) (sdinv dv r0 t0 q0 FR) (sdqc dv r0 t0 q0 FR)
    (swapdiv_hiter_q dv r0 t0 q0 FR hFR) (swapdiv_hlast_q dv r0 t0 q0 FR hFR)

#print axioms swapdiv_bitfold_q

/-- One limb round of the restoring division: load limb, zero quotient temp,
set bit counter to 64, run the 64-bit loop (concrete exit), store the quotient
limb, advance the limb pointer, decrement the limb counter, and take the
back-edge branch.  The remainder register `t1` carries the division state
across limbs. -/
theorem swapdiv_limbround (dv rk pk v7 v28 v29 ptrk t6v : Word) (FR : Assertion)
    (hFR : FR.pcFree) :
    cpsBranchWithin 647 (PriceK + 720) priceCode
      (((.x6 ↦ᵣ rk) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ ptrk) ** (.x31 ↦ᵣ t6v) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) ** FR)
      (PriceK + 720)
      (((.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) **
        (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** ⌜(t6v + signExtend12 (-1 : BitVec 12)) ≠ (0 : Word)⌝) **
        ((.x30 ↦ᵣ (ptrk + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (t6v + signExtend12 (-1 : BitVec 12))) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) ** FR))
      (PriceK + 796)
      (((.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) **
        (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** ⌜(t6v + signExtend12 (-1 : BitVec 12)) = (0 : Word)⌝) **
        ((.x30 ↦ᵣ (ptrk + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (t6v + signExtend12 (-1 : BitVec 12))) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) ** FR)) := by
  have hld := ld_spec_gen_within .x7 .x30 ptrk v7 pk (0 : BitVec 12) (PriceK + 720)
    (by decide)
  have hli28 := li_spec_gen_within .x28 v28 (0 : Word) (PriceK + 724) (by decide)
  have hli29 := li_spec_gen_within .x29 v29 (64 : Word) (PriceK + 728) (by decide)
  have hpream : cpsTripleWithin 3 (PriceK + 720) (PriceK + 732) priceCode
      (((.x6 ↦ᵣ rk) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ ptrk) ** (.x31 ↦ᵣ t6v) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) ** FR) (((.x6 ↦ᵣ rk) ** (.x7 ↦ᵣ pk) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
        (.x29 ↦ᵣ (64 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ ptrk) ** (.x31 ↦ᵣ t6v) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) ** FR) := by
    have hldF : cpsTripleWithin 1 (PriceK + 720) (PriceK + 724) priceCode
        (((.x30 ↦ᵣ ptrk) ** (.x7 ↦ᵣ v7) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk)) **
          ((.x6 ↦ᵣ rk) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
            (.x5 ↦ᵣ dv) ** (.x31 ↦ᵣ t6v) ** FR))
      (((.x30 ↦ᵣ ptrk) ** (.x7 ↦ᵣ pk) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk)) **
          ((.x6 ↦ᵣ rk) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
            (.x5 ↦ᵣ dv) ** (.x31 ↦ᵣ t6v) ** FR)) :=
      cpsTripleWithin_extend_code
        (by intro a i hi
            have hins : amsterdamBlobGasPriceU256_prog[180]'(by decide) =
                .LD .x7 .x30 (0 : BitVec 12) := by decide
            show priceCode a = some i
            exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 720)
              amsterdamBlobGasPriceU256_prog 180 (.LD .x7 .x30 (0 : BitVec 12))
              (by decide) (by decide) hins (by decide) a i hi)
        (cpsTripleWithin_frameR _
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs hFR))))))
          hld)
    have hli28F : cpsTripleWithin 1 (PriceK + 724) (PriceK + 728) priceCode
        ((.x28 ↦ᵣ v28) ** ((.x30 ↦ᵣ ptrk) ** (.x7 ↦ᵣ pk) **
          ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) **
          (.x6 ↦ᵣ rk) ** (.x0 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ v29) **
            (.x5 ↦ᵣ dv) ** (.x31 ↦ᵣ t6v) ** FR))
      ((.x28 ↦ᵣ (0 : Word)) ** ((.x30 ↦ᵣ ptrk) ** (.x7 ↦ᵣ pk) **
          ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) **
          (.x6 ↦ᵣ rk) ** (.x0 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ v29) **
            (.x5 ↦ᵣ dv) ** (.x31 ↦ᵣ t6v) ** FR)) :=
      cpsTripleWithin_extend_code
        (by intro a i hi
            have hins : amsterdamBlobGasPriceU256_prog[181]'(by decide) =
                .LI .x28 (0 : Word) := by decide
            show priceCode a = some i
            exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 724)
              amsterdamBlobGasPriceU256_prog 181 (.LI .x28 (0 : Word))
              (by decide) (by decide) hins (by decide) a i hi)
        (cpsTripleWithin_frameR _
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_memIs (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs hFR))))))))
          hli28)
    have hli29F : cpsTripleWithin 1 (PriceK + 728) (PriceK + 732) priceCode
        ((.x29 ↦ᵣ v29) ** ((.x28 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ ptrk) ** (.x7 ↦ᵣ pk) **
          ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) **
          (.x6 ↦ᵣ rk) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x31 ↦ᵣ t6v) ** FR))
      ((.x29 ↦ᵣ (64 : Word)) ** ((.x28 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ ptrk) ** (.x7 ↦ᵣ pk) **
          ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) **
          (.x6 ↦ᵣ rk) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x31 ↦ᵣ t6v) ** FR)) :=
      cpsTripleWithin_extend_code
        (by intro a i hi
            have hins : amsterdamBlobGasPriceU256_prog[182]'(by decide) =
                .LI .x29 (64 : Word) := by decide
            show priceCode a = some i
            exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 728)
              amsterdamBlobGasPriceU256_prog 182 (.LI .x29 (64 : Word))
              (by decide) (by decide) hins (by decide) a i hi)
        (cpsTripleWithin_frameR _
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_memIs
              (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs hFR))))))))
          hli29)
    have hseq1 := cpsTripleWithin_seq_same_cr hldF (cpsTripleWithin_weaken
      (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hli28F)
    have hseq2 := cpsTripleWithin_seq_same_cr hseq1 (cpsTripleWithin_weaken
      (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hli29F)
    exact cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
      (by intro h hx; xperm_hyp hx) hseq2
  have hpream' : cpsTripleWithin 3 (PriceK + 720) (PriceK + 732) priceCode
      (((.x6 ↦ᵣ rk) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ ptrk) ** (.x31 ↦ᵣ t6v) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) ** FR) (sdinv dv rk pk (0 : Word) ((.x30 ↦ᵣ ptrk) ** (.x31 ↦ᵣ t6v) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) ** FR) 0) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (fun _ hx => hx) hpream
  have hfr' : (((.x30 ↦ᵣ ptrk) ** (.x31 ↦ᵣ t6v) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) ** FR)).pcFree :=
    pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_memIs hFR))
  have hfold : cpsTripleWithin 640 (PriceK + 732) (PriceK + 780) priceCode
      (sdinv dv rk pk (0 : Word) ((.x30 ↦ᵣ ptrk) ** (.x31 ↦ᵣ t6v) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) ** FR) 0) (sdqc dv rk pk (0 : Word) ((.x30 ↦ᵣ ptrk) ** (.x31 ↦ᵣ t6v) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) ** FR)) :=
    swapdiv_bitfold_q dv rk pk (0 : Word) ((.x30 ↦ᵣ ptrk) ** (.x31 ↦ᵣ t6v) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) ** FR) hfr'
  have hfold' : cpsTripleWithin 640 (PriceK + 732) (PriceK + 780) priceCode
      (sdinv dv rk pk (0 : Word) ((.x30 ↦ᵣ ptrk) ** (.x31 ↦ᵣ t6v) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk) ** FR) 0) (((.x30 ↦ᵣ ptrk) ** (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk)) ** ((.x31 ↦ᵣ t6v) ** (.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x29 ↦ᵣ (0 : Word)) ** FR)) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by intro h hx; simp only [sdqc] at hx; xperm_hyp hx) hfold
  have hsd := sd_spec_gen_within .x30 .x28 ptrk (divst dv rk pk (0 : Word) 64).2.2 pk (0 : BitVec 12) (PriceK + 780)
  have hsdF : cpsTripleWithin 1 (PriceK + 780) (PriceK + 784) priceCode (((.x30 ↦ᵣ ptrk) ** (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk)) ** ((.x31 ↦ᵣ t6v) ** (.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x29 ↦ᵣ (0 : Word)) ** FR))
      (((.x30 ↦ᵣ ptrk) ** (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) **
        ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2)) **
        ((.x31 ↦ᵣ t6v) ** (.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) **
          (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x29 ↦ᵣ (0 : Word)) ** FR)) :=
    cpsTripleWithin_extend_code
      (by intro a i hi
          have hins : amsterdamBlobGasPriceU256_prog[195]'(by decide) =
              .SD .x30 .x28 (0 : BitVec 12) := by decide
          show priceCode a = some i
          exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 780)
            amsterdamBlobGasPriceU256_prog 195 (.SD .x30 .x28 (0 : BitVec 12))
            (by decide) (by decide) hins (by decide) a i hi)
      (cpsTripleWithin_frameR _
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hFR))))))
        hsd)
  have hmid := cpsTripleWithin_seq_same_cr hpream' hfold'
  have hsdF2 : cpsTripleWithin 1 (PriceK + 780) (PriceK + 784) priceCode
      (((.x30 ↦ᵣ ptrk) ** (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) **
        ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ pk)) **
        ((.x31 ↦ᵣ t6v) ** (.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) **
          (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x29 ↦ᵣ (0 : Word)) ** FR))
      ((.x30 ↦ᵣ ptrk) ** ((.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) **
        ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) **
        (.x31 ↦ᵣ t6v) ** (.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) **
          (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x29 ↦ᵣ (0 : Word)) ** FR)) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by intro h hx; xperm_hyp hx) hsdF
  have hbody1 := cpsTripleWithin_seq_same_cr hmid hsdF2
  have ha30 := addi_spec_gen_same_within .x30 ptrk (-8 : BitVec 12) (PriceK + 784)
    (by decide)
  have ha30F : cpsTripleWithin 1 (PriceK + 784) (PriceK + 788) priceCode ((.x30 ↦ᵣ ptrk) ** ((.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) ** (.x31 ↦ᵣ t6v) ** (.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x29 ↦ᵣ (0 : Word)) ** FR))
      ((.x30 ↦ᵣ (ptrk + signExtend12 (-8 : BitVec 12))) ** ((.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) **
        ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) **
        (.x31 ↦ᵣ t6v) ** (.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) **
          (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x29 ↦ᵣ (0 : Word)) ** FR)) :=
    cpsTripleWithin_extend_code
      (by intro a i hi
          have hins : amsterdamBlobGasPriceU256_prog[196]'(by decide) =
              .ADDI .x30 .x30 (-8 : BitVec 12) := by decide
          show priceCode a = some i
          exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 784)
            amsterdamBlobGasPriceU256_prog 196 (.ADDI .x30 .x30 (-8 : BitVec 12))
            (by decide) (by decide) hins (by decide) a i hi)
      (cpsTripleWithin_frameR _
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_memIs
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hFR))))))))
        ha30)
  have ha30F2 : cpsTripleWithin 1 (PriceK + 784) (PriceK + 788) priceCode
      ((.x30 ↦ᵣ ptrk) ** ((.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) **
        ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) **
        (.x31 ↦ᵣ t6v) ** (.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) **
          (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x29 ↦ᵣ (0 : Word)) ** FR))
      ((.x31 ↦ᵣ t6v) ** ((.x30 ↦ᵣ (ptrk + signExtend12 (-8 : BitVec 12))) **
        (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) **
        ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) **
        (.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) **
          (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x29 ↦ᵣ (0 : Word)) ** FR)) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by intro h hx; xperm_hyp hx) ha30F
  have hbody2 := cpsTripleWithin_seq_same_cr hbody1 ha30F2
  have ha31 := addi_spec_gen_same_within .x31 t6v (-1 : BitVec 12) (PriceK + 788)
    (by decide)
  have ha31F : cpsTripleWithin 1 (PriceK + 788) (PriceK + 792) priceCode ((.x31 ↦ᵣ t6v) ** ((.x30 ↦ᵣ (ptrk + signExtend12 (-8 : BitVec 12))) ** (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) ** (.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x29 ↦ᵣ (0 : Word)) ** FR))
      ((.x31 ↦ᵣ (t6v + signExtend12 (-1 : BitVec 12))) ** ((.x30 ↦ᵣ (ptrk + signExtend12 (-8 : BitVec 12))) **
        (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) **
        ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) **
        (.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) **
          (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x29 ↦ᵣ (0 : Word)) ** FR)) :=
    cpsTripleWithin_extend_code
      (by intro a i hi
          have hins : amsterdamBlobGasPriceU256_prog[197]'(by decide) =
              .ADDI .x31 .x31 (-1 : BitVec 12) := by decide
          show priceCode a = some i
          exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 788)
            amsterdamBlobGasPriceU256_prog 197 (.ADDI .x31 .x31 (-1 : BitVec 12))
            (by decide) (by decide) hins (by decide) a i hi)
      (cpsTripleWithin_frameR _
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_memIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs hFR))))))))
        ha31)
  have hbody3 := cpsTripleWithin_seq_same_cr hbody2 ha31F
  have hb := bne_spec_gen_within .x31 .x0 (-72 : BitVec 13) (t6v + signExtend12 (-1 : BitVec 12))
    (0 : Word) (PriceK + 792)
  rw [show (PriceK + 792 : Word) + signExtend13 (-72 : BitVec 13) = PriceK + 720 from by
      rw [show signExtend13 (-72 : BitVec 13) = (-72 : Word) from by decide]; decide,
    show (PriceK + 792 : Word) + 4 = PriceK + 796 from by decide] at hb
  have hbF := cpsBranchWithin_frameR ((.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) ** (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x30 ↦ᵣ (ptrk + signExtend12 (-8 : BitVec 12))) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) ** FR)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_memIs hFR)))))))
    hb
  have hbE := cpsBranchWithin_extend_code
    (by intro a i hi
        have hins : amsterdamBlobGasPriceU256_prog[198]'(by decide) =
            .BNE .x31 .x0 (-72 : BitVec 13) := by decide
        show priceCode a = some i
        exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 792)
          amsterdamBlobGasPriceU256_prog 198 (.BNE .x31 .x0 (-72 : BitVec 13))
          (by decide) (by decide) hins (by decide) a i hi)
    hbF
  have hb' : cpsBranchWithin 1 (PriceK + 792) priceCode ((.x31 ↦ᵣ (t6v + signExtend12 (-1 : BitVec 12))) ** ((.x30 ↦ᵣ (ptrk + signExtend12 (-8 : BitVec 12))) ** (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) ** (.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x29 ↦ᵣ (0 : Word)) ** FR))
      (PriceK + 720) (((.x31 ↦ᵣ (t6v + signExtend12 (-1 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(t6v + signExtend12 (-1 : BitVec 12)) ≠ (0 : Word)⌝) **
        ((.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) ** (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x30 ↦ᵣ (ptrk + signExtend12 (-8 : BitVec 12))) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) ** FR)) (PriceK + 796) (((.x31 ↦ᵣ (t6v + signExtend12 (-1 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(t6v + signExtend12 (-1 : BitVec 12)) = (0 : Word)⌝) **
        ((.x6 ↦ᵣ (divst dv rk pk (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.1) ** (.x28 ↦ᵣ (divst dv rk pk (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv) ** (.x30 ↦ᵣ (ptrk + signExtend12 (-8 : BitVec 12))) ** ((ptrk + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv rk pk (0 : Word) 64).2.2) ** FR)) :=
    cpsBranchWithin_weaken (by intro h hx; xperm_hyp hx)
      (by intro h hx; xperm_hyp hx) (by intro h hx; xperm_hyp hx) hbE
  have hfin := cpsTripleWithin_seq_cpsBranchWithin_same_cr hbody3 hb'
  exact cpsBranchWithin_weaken (by intro h hx; xperm_hyp hx)
    (by intro h hx; xperm_hyp hx) (by intro h hx; xperm_hyp hx) hfin

#print axioms swapdiv_limbround


/-! ## Limb-counter lemmas and the 6-limb chain fold -/

def lcnt : Nat → Word
  | 0 => (6 : Word)
  | k + 1 => lcnt k + signExtend12 (-1 : BitVec 12)

private theorem lcnt_zero : lcnt 6 = (0 : Word) := by decide

private theorem lcnt_add : ∀ k ≤ 6, lcnt k + BitVec.ofNat 64 k = (6 : Word) := by
  intro k hk
  induction k with
  | zero => simp [lcnt]
  | succ n ih =>
    have hn : n < 6 := by omega
    have h1 : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + (1 : Word) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat]
    have hse : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
    have hn1 : (-1 : Word) + (1 : Word) = (0 : Word) := by decide
    rw [lcnt, hse, h1]
    rw [BitVec.add_comm (BitVec.ofNat 64 n) (1 : Word),
      ← BitVec.add_assoc (lcnt n + (-1 : Word)) (1 : Word) (BitVec.ofNat 64 n),
      BitVec.add_assoc (lcnt n) (-1 : Word) (1 : Word), hn1]
    have hz : lcnt n + (0 : Word) = lcnt n := by simp
    rw [hz]
    exact ih (by omega)

private theorem lcnt_ne_zero : ∀ j < 6, lcnt j ≠ (0 : Word) := by
  intro j hj h0
  have hadd : lcnt j + BitVec.ofNat 64 j = (6 : Word) := lcnt_add j (by omega)
  have hlt : BitVec.ofNat 64 j < (6 : Word) := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat]
    rw [show BitVec.toNat (6 : Word) = 6 from rfl]
    omega
  rw [h0] at hadd
  have hz : (0 : Word) + BitVec.ofNat 64 j = BitVec.ofNat 64 j := by simp
  rw [hz] at hadd
  rw [← hadd] at hlt
  exact absurd hlt (by simp)



private theorem swapdiv_limbstep_0 (dv base : Word) (p5 p4 p3 p2 p1 p0 : Word) (v7 v28 v29 : Word) (FR : Assertion)
    (hFR : FR.pcFree) :
    cpsTripleWithin 647 (PriceK + 720) (PriceK + 720) priceCode
      (((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ (base + signExtend12 (40 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 0) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR)
      (((.x6 ↦ᵣ (divst dv (0 : Word) p5 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv (0 : Word) p5 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ (base + signExtend12 (32 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 1) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR) := by
  have hL := swapdiv_limbround dv (0 : Word) p5 v7 v28 v29
      (base + signExtend12 (40 : BitVec 12)) (lcnt 0) (((base + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR) (by pcFree; exact hFR)
  have htp := cpsBranchWithin_takenPath hL (by
    intro hp hx
    obtain ⟨h1, h2, hd, hu, hG, _⟩ := hx
    obtain ⟨_, _, _, _, _, hR1⟩ := hG
    obtain ⟨_, _, _, _, _, hR2⟩ := hR1
    obtain ⟨_, _, _, _, _, hR3⟩ := hR2
    obtain ⟨_, _, _, _, _, hR4⟩ := hR3
    obtain ⟨_, _, _, _, _, hR5⟩ := hR4
    obtain ⟨_, _, _, _, _, _, hPp⟩ := hR5
    exact absurd hPp (lcnt_ne_zero 1 (by omega)))
  refine cpsTripleWithin_weaken ?_ ?_ htp
  · intro h hx
    rw [show ((base + signExtend12 (40 : BitVec 12)) + signExtend12 (0 : BitVec 12)) =
        (base + signExtend12 (40 : BitVec 12)) from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp]
    xperm_hyp hx
  · intro h hx
    have hx2 := pure_drop_6 _ hx
    rw [show ((base + signExtend12 (40 : BitVec 12)) + signExtend12 (-8 : BitVec 12)) =
        (base + signExtend12 (32 : BitVec 12)) from by
      rw [BitVec.add_assoc]; congr 1; try decide] at hx2
    rw [show (lcnt 0 + signExtend12 (-1 : BitVec 12)) = lcnt 1 from rfl] at hx2
    rw [show ((base + signExtend12 (40 : BitVec 12)) + signExtend12 (0 : BitVec 12)) =
        (base + signExtend12 (40 : BitVec 12)) from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp] at hx2
    xperm_hyp hx2

private theorem swapdiv_limbstep_1 (dv base : Word) (p5 p4 p3 p2 p1 p0 : Word) (FR : Assertion)
    (hFR : FR.pcFree) :
    cpsTripleWithin 647 (PriceK + 720) (PriceK + 720) priceCode
      (((.x6 ↦ᵣ (divst dv (0 : Word) p5 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv (0 : Word) p5 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ (base + signExtend12 (32 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 1) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR)
      (((.x6 ↦ᵣ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ (base + signExtend12 (24 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 2) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR) := by
  have hL := swapdiv_limbround dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (divst dv (0 : Word) p5 (0 : Word) 64).2.1 (divst dv (0 : Word) p5 (0 : Word) 64).2.2 (0 : Word)
      (base + signExtend12 (32 : BitVec 12)) (lcnt 1) (((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR) (by pcFree; exact hFR)
  have htp := cpsBranchWithin_takenPath hL (by
    intro hp hx
    obtain ⟨h1, h2, hd, hu, hG, _⟩ := hx
    obtain ⟨_, _, _, _, _, hR1⟩ := hG
    obtain ⟨_, _, _, _, _, hR2⟩ := hR1
    obtain ⟨_, _, _, _, _, hR3⟩ := hR2
    obtain ⟨_, _, _, _, _, hR4⟩ := hR3
    obtain ⟨_, _, _, _, _, hR5⟩ := hR4
    obtain ⟨_, _, _, _, _, _, hPp⟩ := hR5
    exact absurd hPp (lcnt_ne_zero 2 (by omega)))
  refine cpsTripleWithin_weaken ?_ ?_ htp
  · intro h hx
    rw [show ((base + signExtend12 (32 : BitVec 12)) + signExtend12 (0 : BitVec 12)) =
        (base + signExtend12 (32 : BitVec 12)) from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp]
    xperm_hyp hx
  · intro h hx
    have hx2 := pure_drop_6 _ hx
    rw [show ((base + signExtend12 (32 : BitVec 12)) + signExtend12 (-8 : BitVec 12)) =
        (base + signExtend12 (24 : BitVec 12)) from by
      rw [BitVec.add_assoc]; congr 1; try decide] at hx2
    rw [show (lcnt 1 + signExtend12 (-1 : BitVec 12)) = lcnt 2 from rfl] at hx2
    rw [show ((base + signExtend12 (32 : BitVec 12)) + signExtend12 (0 : BitVec 12)) =
        (base + signExtend12 (32 : BitVec 12)) from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp] at hx2
    xperm_hyp hx2

private theorem swapdiv_limbstep_2 (dv base : Word) (p5 p4 p3 p2 p1 p0 : Word) (FR : Assertion)
    (hFR : FR.pcFree) :
    cpsTripleWithin 647 (PriceK + 720) (PriceK + 720) priceCode
      (((.x6 ↦ᵣ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ (base + signExtend12 (24 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 2) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR)
      (((.x6 ↦ᵣ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ (base + signExtend12 (16 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 3) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR) := by
  have hL := swapdiv_limbround dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.1 (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2 (0 : Word)
      (base + signExtend12 (24 : BitVec 12)) (lcnt 2) (((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR) (by pcFree; exact hFR)
  have htp := cpsBranchWithin_takenPath hL (by
    intro hp hx
    obtain ⟨h1, h2, hd, hu, hG, _⟩ := hx
    obtain ⟨_, _, _, _, _, hR1⟩ := hG
    obtain ⟨_, _, _, _, _, hR2⟩ := hR1
    obtain ⟨_, _, _, _, _, hR3⟩ := hR2
    obtain ⟨_, _, _, _, _, hR4⟩ := hR3
    obtain ⟨_, _, _, _, _, hR5⟩ := hR4
    obtain ⟨_, _, _, _, _, _, hPp⟩ := hR5
    exact absurd hPp (lcnt_ne_zero 3 (by omega)))
  refine cpsTripleWithin_weaken ?_ ?_ htp
  · intro h hx
    rw [show ((base + signExtend12 (24 : BitVec 12)) + signExtend12 (0 : BitVec 12)) =
        (base + signExtend12 (24 : BitVec 12)) from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp]
    xperm_hyp hx
  · intro h hx
    have hx2 := pure_drop_6 _ hx
    rw [show ((base + signExtend12 (24 : BitVec 12)) + signExtend12 (-8 : BitVec 12)) =
        (base + signExtend12 (16 : BitVec 12)) from by
      rw [BitVec.add_assoc]; congr 1; try decide] at hx2
    rw [show (lcnt 2 + signExtend12 (-1 : BitVec 12)) = lcnt 3 from rfl] at hx2
    rw [show ((base + signExtend12 (24 : BitVec 12)) + signExtend12 (0 : BitVec 12)) =
        (base + signExtend12 (24 : BitVec 12)) from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp] at hx2
    xperm_hyp hx2

private theorem swapdiv_limbstep_3 (dv base : Word) (p5 p4 p3 p2 p1 p0 : Word) (FR : Assertion)
    (hFR : FR.pcFree) :
    cpsTripleWithin 647 (PriceK + 720) (PriceK + 720) priceCode
      (((.x6 ↦ᵣ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ (base + signExtend12 (16 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 3) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR)
      (((.x6 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ (base + signExtend12 (8 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 4) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR) := by
  have hL := swapdiv_limbround dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.1 (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2 (0 : Word)
      (base + signExtend12 (16 : BitVec 12)) (lcnt 3) (((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR) (by pcFree; exact hFR)
  have htp := cpsBranchWithin_takenPath hL (by
    intro hp hx
    obtain ⟨h1, h2, hd, hu, hG, _⟩ := hx
    obtain ⟨_, _, _, _, _, hR1⟩ := hG
    obtain ⟨_, _, _, _, _, hR2⟩ := hR1
    obtain ⟨_, _, _, _, _, hR3⟩ := hR2
    obtain ⟨_, _, _, _, _, hR4⟩ := hR3
    obtain ⟨_, _, _, _, _, hR5⟩ := hR4
    obtain ⟨_, _, _, _, _, _, hPp⟩ := hR5
    exact absurd hPp (lcnt_ne_zero 4 (by omega)))
  refine cpsTripleWithin_weaken ?_ ?_ htp
  · intro h hx
    rw [show ((base + signExtend12 (16 : BitVec 12)) + signExtend12 (0 : BitVec 12)) =
        (base + signExtend12 (16 : BitVec 12)) from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp]
    xperm_hyp hx
  · intro h hx
    have hx2 := pure_drop_6 _ hx
    rw [show ((base + signExtend12 (16 : BitVec 12)) + signExtend12 (-8 : BitVec 12)) =
        (base + signExtend12 (8 : BitVec 12)) from by
      rw [BitVec.add_assoc]; congr 1; try decide] at hx2
    rw [show (lcnt 3 + signExtend12 (-1 : BitVec 12)) = lcnt 4 from rfl] at hx2
    rw [show ((base + signExtend12 (16 : BitVec 12)) + signExtend12 (0 : BitVec 12)) =
        (base + signExtend12 (16 : BitVec 12)) from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp] at hx2
    xperm_hyp hx2

private theorem swapdiv_limbstep_4 (dv base : Word) (p5 p4 p3 p2 p1 p0 : Word) (FR : Assertion)
    (hFR : FR.pcFree) :
    cpsTripleWithin 647 (PriceK + 720) (PriceK + 720) priceCode
      (((.x6 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ (base + signExtend12 (8 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 4) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR)
      (((.x6 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ (base + signExtend12 (0 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 5) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR) := by
  have hL := swapdiv_limbround dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.1 (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2 (0 : Word)
      (base + signExtend12 (8 : BitVec 12)) (lcnt 4) (((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR) (by pcFree; exact hFR)
  have htp := cpsBranchWithin_takenPath hL (by
    intro hp hx
    obtain ⟨h1, h2, hd, hu, hG, _⟩ := hx
    obtain ⟨_, _, _, _, _, hR1⟩ := hG
    obtain ⟨_, _, _, _, _, hR2⟩ := hR1
    obtain ⟨_, _, _, _, _, hR3⟩ := hR2
    obtain ⟨_, _, _, _, _, hR4⟩ := hR3
    obtain ⟨_, _, _, _, _, hR5⟩ := hR4
    obtain ⟨_, _, _, _, _, _, hPp⟩ := hR5
    exact absurd hPp (lcnt_ne_zero 5 (by omega)))
  refine cpsTripleWithin_weaken ?_ ?_ htp
  · intro h hx
    rw [show ((base + signExtend12 (8 : BitVec 12)) + signExtend12 (0 : BitVec 12)) =
        (base + signExtend12 (8 : BitVec 12)) from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp]
    xperm_hyp hx
  · intro h hx
    have hx2 := pure_drop_6 _ hx
    rw [show ((base + signExtend12 (8 : BitVec 12)) + signExtend12 (-8 : BitVec 12)) =
        (base + signExtend12 (0 : BitVec 12)) from by
      rw [BitVec.add_assoc]; congr 1; try decide] at hx2
    rw [show (lcnt 4 + signExtend12 (-1 : BitVec 12)) = lcnt 5 from rfl] at hx2
    rw [show ((base + signExtend12 (8 : BitVec 12)) + signExtend12 (0 : BitVec 12)) =
        (base + signExtend12 (8 : BitVec 12)) from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp] at hx2
    xperm_hyp hx2

private theorem swapdiv_limbexit (dv base : Word) (p5 p4 p3 p2 p1 p0 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 647 (PriceK + 720) (PriceK + 796) priceCode
      (((.x6 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ (base + signExtend12 (0 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 5) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR)
      (((.x6 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ ((base + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2) ** FR) := by
  have hL := swapdiv_limbround dv (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.1 (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2 (0 : Word)
      (base + signExtend12 (0 : BitVec 12)) (lcnt 5) (((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2) ** FR) (by pcFree; exact hFR)
  have htp := cpsBranchWithin_ntakenPath hL (by
    intro hp hx
    obtain ⟨h1, h2, hd, hu, hG, _⟩ := hx
    obtain ⟨_, _, _, _, _, hR1⟩ := hG
    obtain ⟨_, _, _, _, _, hR2⟩ := hR1
    obtain ⟨_, _, _, _, _, hR3⟩ := hR2
    obtain ⟨_, _, _, _, _, hR4⟩ := hR3
    obtain ⟨_, _, _, _, _, hR5⟩ := hR4
    obtain ⟨_, _, _, _, _, _, hPp⟩ := hR5
    exact (hPp lcnt_zero).elim)
  refine cpsTripleWithin_weaken ?_ ?_ htp
  · intro h hx
    rw [show ((base + signExtend12 (0 : BitVec 12)) + signExtend12 (0 : BitVec 12)) =
        (base + signExtend12 (0 : BitVec 12)) from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp]
    xperm_hyp hx
  · intro h hx
    have hx2 := pure_drop_6 _ hx
    rw [show ((base + signExtend12 (0 : BitVec 12)) + signExtend12 (0 : BitVec 12)) =
        (base + signExtend12 (0 : BitVec 12)) from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp] at hx2
    exact hx2

/-- The 6-limb division loop as one triple: 3882 = 6 × 647. -/
theorem swapdiv_limbfold (dv base : Word) (p5 p4 p3 p2 p1 p0 : Word)
    (v7 v28 v29 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 3882 (PriceK + 720) (PriceK + 796) priceCode
      (((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ (base + signExtend12 (40 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 0) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** FR)
      (((.x6 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst dv (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ dv)) ** (.x30 ↦ᵣ ((base + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** ((base + signExtend12 (0 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** ((base + signExtend12 (40 : BitVec 12)) ↦ₘ (divst dv (0 : Word) p5 (0 : Word) 64).2.2) ** ((base + signExtend12 (32 : BitVec 12)) ↦ₘ (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** ((base + signExtend12 (24 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** ((base + signExtend12 (16 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** ((base + signExtend12 (8 : BitVec 12)) ↦ₘ (divst dv (divst dv (divst dv (divst dv (divst dv (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2) ** FR) := by
  have h1 := cpsTripleWithin_seq_same_cr
      (swapdiv_limbstep_0 dv base p5 p4 p3 p2 p1 p0 v7 v28 v29 FR hFR)
      (swapdiv_limbstep_1 dv base p5 p4 p3 p2 p1 p0 FR hFR)
  have h2 := cpsTripleWithin_seq_same_cr h1
      (swapdiv_limbstep_2 dv base p5 p4 p3 p2 p1 p0 FR hFR)
  have h3 := cpsTripleWithin_seq_same_cr h2
      (swapdiv_limbstep_3 dv base p5 p4 p3 p2 p1 p0 FR hFR)
  have h4 := cpsTripleWithin_seq_same_cr h3
      (swapdiv_limbstep_4 dv base p5 p4 p3 p2 p1 p0 FR hFR)
  exact cpsTripleWithin_seq_same_cr h4
      (swapdiv_limbexit dv base p5 p4 p3 p2 p1 p0 FR hFR)

#print axioms swapdiv_limbfold
