/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128CapV5

  CPS spec for the **v5 Phase-1a cap block** of the `divK_div128_v5`
  trial-division subroutine (instrs [13]-[20]).

  Unlike v4's clamp (which decrements `q1` by one when `q1 ≥ 2^32`),
  v5 *caps* the trial quotient at `0xFFFFFFFF` and recomputes the
  partial remainder from scratch:

    * [13] `SRLI .x5 .x10 32`   — x5 = hi1 = q1 >> 32
    * [14] `BEQ  .x5 .x0 28`    — skip cap when hi1 = 0 → exit at base+32
    * [15] `ADDI .x5 .x0 4095`  — x5 = signExtend12 4095 = allOnes
    * [16] `SRLI .x5 .x5 32`    — x5 = 0xFFFFFFFF (q1cCap)
    * [17] `SUB  .x9 .x10 .x5`  — x9 = q1 - q1cCap
    * [18] `MUL  .x9 .x9 .x6`   — x9 = (q1 - q1cCap) * dHi
    * [19] `ADD  .x7 .x7 .x9`   — x7 = rhat + (q1 - q1cCap) * dHi = rhatc
    * [20] `ADDI .x10 .x5 0`    — x10 = q1cCap (MV via ADDI 0)

  Both BEQ paths merge at base+32. The output `q1c`/`rhatc` match the
  Phase-1a portion of the Lean abstraction `div128Quot_v5`
  (`LoopDefs/IterV5.lean`): `q1c := if hi1 = 0 then q1 else q1cCap` and
  `rhatc := if hi1 = 0 then rhat else rhat + (q1 - q1cCap) * dHi`
  (algebraically `uHi - q1c * dHi`).

  Mirror of `divK_div128_clamp_q1_merged_spec_within` (Div128Clamp.lean),
  the v2/v4 analog. Bead `evm-asm-wbc4i.6.1` (V5.6.1), part of the
  `div128_v5_spec` composition (bead `.6`).
-/

module

public import EvmAsm.Evm64.DivMod.Program
public import EvmAsm.Rv64.AddrNorm
public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.ControlFlow
public import EvmAsm.Rv64.Tactics.XSimp
public import EvmAsm.Rv64.Tactics.RunBlock

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Code requirement for the div128 v5 Phase-1a `q1` cap (instrs [13]-[20]). -/
def divKDiv128CapQ1V5Code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.SRLI .x5 .x10 32))
  (CodeReq.union (CodeReq.singleton (base + 4) (.BEQ .x5 .x0 28))
  (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x5 .x0 4095))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x5 .x5 32))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x9 .x10 .x5))
  (CodeReq.union (CodeReq.singleton (base + 20) (.MUL .x9 .x9 .x6))
  (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x7 .x7 .x9))
   (CodeReq.singleton (base + 28) (.ADDI .x10 .x5 0))))))))

/-- div128 v5 Phase-1a cap on `q1`: test `q1 ≥ 2^32`; when set, cap
    `q1c := 0xFFFFFFFF` and recompute `rhatc := rhat + (q1 - q1cCap) * dHi`.
    Instrs [13]-[20]. Both BEQ paths merge at base+32. -/
theorem divK_div128_cap_q1_v5_merged_spec_within
    (q1 rhat dHi v5Old v9Old : Word) (base : Word) :
    let hi := q1 >>> (32 : BitVec 6).toNat
    let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
    let q1c := if hi = 0 then q1 else q1cCap
    let rhatc := if hi = 0 then rhat else rhat + (q1 - q1cCap) * dHi
    let x5o := if hi = 0 then hi else q1cCap
    let x9o := if hi = 0 then v9Old else (q1 - q1cCap) * dHi
    cpsTripleWithin 8 base (base + 32) (divKDiv128CapQ1V5Code base)
      ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) **
       (.x5 ↦ᵣ v5Old) ** (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0))
      ((.x10 ↦ᵣ q1c) ** (.x7 ↦ᵣ rhatc) ** (.x6 ↦ᵣ dHi) **
       (.x5 ↦ᵣ x5o) ** (.x9 ↦ᵣ x9o) ** (.x0 ↦ᵣ 0)) := by
  intro hi q1cCap q1c rhatc x5o x9o
  -- Proof-local `cr` bound to the union literal (so `runBlock` can resolve
  -- instruction addresses); the statement uses `divKDiv128CapQ1V5Code`.
  let cr :=
    CodeReq.union (CodeReq.singleton base (.SRLI .x5 .x10 32))
    (CodeReq.union (CodeReq.singleton (base + 4) (.BEQ .x5 .x0 28))
    (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x5 .x0 4095))
    (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x5 .x5 32))
    (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x9 .x10 .x5))
    (CodeReq.union (CodeReq.singleton (base + 20) (.MUL .x9 .x9 .x6))
    (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x7 .x7 .x9))
     (CodeReq.singleton (base + 28) (.ADDI .x10 .x5 0))))))))
  show cpsTripleWithin 8 base (base + 32) cr _ _
  -- Block prefix: [13] SRLI → x5 = hi.
  have I0 := srli_spec_gen_within .x5 .x10 v5Old q1 32 base (by nofun)
  have hbody : cpsTripleWithin 1 base (base + 4) cr
      ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) **
       (.x5 ↦ᵣ v5Old) ** (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0))
      ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) **
       (.x5 ↦ᵣ hi) ** (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0)) := by
    runBlock I0
  -- BEQ [14]: taken (hi = 0) → base+32, fall-through (hi ≠ 0) → base+8.
  have hbeq_raw := beq_spec_gen_within .x5 .x0 (28 : BitVec 13) hi (0 : Word) (base + 4)
  have ha_t : (base + 4) + signExtend13 (28 : BitVec 13) = base + 32 := by rv64_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbeq_raw
  have hbeq_framed := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) ** (.x9 ↦ᵣ v9Old))
    (by pcFree) hbeq_raw
  have hbeq_ext : cpsBranchWithin 1 (base + 4) cr
      (((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) ** (.x9 ↦ᵣ v9Old)))
      (base + 32)
        (((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi = 0⌝) **
         ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) ** (.x9 ↦ᵣ v9Old)))
      (base + 8)
        (((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi ≠ 0⌝) **
         ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) ** (.x9 ↦ᵣ v9Old))) :=
    fun R hR s hcr hPR hpc =>
      hbeq_framed R hR s (CodeReq.singleton_satisfiedBy.mpr (hcr _ _ (by
        show cr (base + 4) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  have composed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeq_ext
  by_cases hcond : hi = 0
  · -- Taken: cap skipped; outputs unchanged.
    have hq : q1c = q1 := if_pos hcond
    have hr : rhatc = rhat := if_pos hcond
    have h5 : x5o = hi := if_pos hcond
    have h9 : x9o = v9Old := if_pos hcond
    rw [hq, hr, h5, h9]
    have taken := cpsBranchWithin_takenPath composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_x0p).2 hcond)
    exact cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          have hp' := sepConj_mono_left (sepConj_mono_right
            (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
          xperm_hyp hp') taken)
  · -- Fall-through: cap fires.
    have hq : q1c = q1cCap := if_neg hcond
    have hr : rhatc = rhat + (q1 - q1cCap) * dHi := if_neg hcond
    have h5 : x5o = q1cCap := if_neg hcond
    have h9 : x9o = (q1 - q1cCap) * dHi := if_neg hcond
    rw [hq, hr, h5, h9]
    have ntaken := cpsBranchWithin_ntakenPath composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact hcond ((sepConj_pure_right _).1 h_x0p).2)
    -- Correction body [15]-[20]: raw register expressions.
    have I1 := addi_spec_gen_within .x5 .x0 hi (0 : Word) 4095 (base + 8) (by nofun)
    have I2 := srli_spec_gen_same_within .x5 ((0 : Word) + signExtend12 4095) 32
      (base + 12) (by nofun)
    have I3 := sub_spec_gen_within .x9 .x10 .x5 q1
      (((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat) v9Old (base + 16) (by nofun)
    have I4 := mul_spec_gen_rd_eq_rs1_within .x9 .x6
      (q1 - ((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat) dHi (base + 20) (by nofun)
    have I5 := add_spec_gen_rd_eq_rs1_within .x7 .x9 rhat
      ((q1 - ((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat) * dHi)
      (base + 24) (by nofun)
    have I6 := addi_spec_gen_within .x10 .x5 q1
      (((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat) 0 (base + 28) (by nofun)
    have hcorr : cpsTripleWithin 6 (base + 8) (base + 32) cr
        ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) **
         (.x5 ↦ᵣ hi) ** (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0))
        ((.x10 ↦ᵣ (((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat + signExtend12 0)) **
         (.x7 ↦ᵣ (rhat + (q1 - ((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat) * dHi)) **
         (.x6 ↦ᵣ dHi) **
         (.x5 ↦ᵣ (((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat)) **
         (.x9 ↦ᵣ ((q1 - ((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat) * dHi)) **
         (.x0 ↦ᵣ 0)) := by
      runBlock I1 I2 I3 I4 I5 I6
    have full := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp') ntaken hcorr
    -- Reconcile raw constant `((0)+signExtend12 4095)>>>32` with `q1cCap`.
    have hCAP : ((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat = q1cCap := by
      show ((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat
        = (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
      decide
    have hMV : q1cCap + signExtend12 0 = q1cCap := by
      show (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat + signExtend12 0
        = (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
      decide
    rw [hCAP] at full
    rw [hMV] at full
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full

/-- Code requirement for the div128 v5 Phase-2a `q0` cap (instrs [47]-[54]). -/
def divKDiv128CapQ0V5Code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.SRLI .x9 .x5 32))
  (CodeReq.union (CodeReq.singleton (base + 4) (.BEQ .x9 .x0 28))
  (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x9 .x0 4095))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x9 .x9 32))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x7 .x5 .x9))
  (CodeReq.union (CodeReq.singleton (base + 20) (.MUL .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x7))
   (CodeReq.singleton (base + 28) (.ADDI .x5 .x9 0))))))))

/-- div128 v5 Phase-2a cap on `q0`: test `q0 ≥ 2^32`; when set, cap
    `q0c := 0xFFFFFFFF` and recompute `rhat2c := rhat2 + (q0 - q0cCap) * dHi`.
    Instrs [47]-[54]. Register-renamed mirror of
    `divK_div128_cap_q1_v5_merged_spec_within`: the trial quotient lives in
    `x5` (was `x10`), the remainder in `x11` (was `x7`), the cap scratch in
    `x9` (was `x5`), and the diff scratch in `x7` (was `x9`). Both BEQ paths
    merge at base+32. Outputs match the Phase-2a portion of `div128Quot_v5`. -/
theorem divK_div128_cap_q0_v5_merged_spec_within
    (q0 rhat2 dHi v9Old v7Old : Word) (base : Word) :
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0cCap
    let rhat2c := if hi = 0 then rhat2 else rhat2 + (q0 - q0cCap) * dHi
    let x9o := if hi = 0 then hi else q0cCap
    let x7o := if hi = 0 then v7Old else (q0 - q0cCap) * dHi
    cpsTripleWithin 8 base (base + 32) (divKDiv128CapQ0V5Code base)
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi) **
       (.x9 ↦ᵣ v9Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ 0))
      ((.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ rhat2c) ** (.x6 ↦ᵣ dHi) **
       (.x9 ↦ᵣ x9o) ** (.x7 ↦ᵣ x7o) ** (.x0 ↦ᵣ 0)) := by
  intro hi q0cCap q0c rhat2c x9o x7o
  -- Proof-local `cr` bound to the union literal (so `runBlock` can resolve
  -- instruction addresses); the statement uses `divKDiv128CapQ0V5Code`.
  let cr :=
    CodeReq.union (CodeReq.singleton base (.SRLI .x9 .x5 32))
    (CodeReq.union (CodeReq.singleton (base + 4) (.BEQ .x9 .x0 28))
    (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x9 .x0 4095))
    (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x9 .x9 32))
    (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x7 .x5 .x9))
    (CodeReq.union (CodeReq.singleton (base + 20) (.MUL .x7 .x7 .x6))
    (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x7))
     (CodeReq.singleton (base + 28) (.ADDI .x5 .x9 0))))))))
  show cpsTripleWithin 8 base (base + 32) cr _ _
  -- Block prefix: [47] SRLI → x9 = hi.
  have I0 := srli_spec_gen_within .x9 .x5 v9Old q0 32 base (by nofun)
  have hbody : cpsTripleWithin 1 base (base + 4) cr
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi) **
       (.x9 ↦ᵣ v9Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ 0))
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi) **
       (.x9 ↦ᵣ hi) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ 0)) := by
    runBlock I0
  -- BEQ [48]: taken (hi = 0) → base+32, fall-through (hi ≠ 0) → base+8.
  have hbeq_raw := beq_spec_gen_within .x9 .x0 (28 : BitVec 13) hi (0 : Word) (base + 4)
  have ha_t : (base + 4) + signExtend13 (28 : BitVec 13) = base + 32 := by rv64_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbeq_raw
  have hbeq_framed := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ v7Old))
    (by pcFree) hbeq_raw
  have hbeq_ext : cpsBranchWithin 1 (base + 4) cr
      (((.x9 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ v7Old)))
      (base + 32)
        (((.x9 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi = 0⌝) **
         ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ v7Old)))
      (base + 8)
        (((.x9 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi ≠ 0⌝) **
         ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ v7Old))) :=
    fun R hR s hcr hPR hpc =>
      hbeq_framed R hR s (CodeReq.singleton_satisfiedBy.mpr (hcr _ _ (by
        show cr (base + 4) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  have composed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeq_ext
  by_cases hcond : hi = 0
  · -- Taken: cap skipped; outputs unchanged.
    have hq : q0c = q0 := if_pos hcond
    have hr : rhat2c = rhat2 := if_pos hcond
    have h9 : x9o = hi := if_pos hcond
    have h7 : x7o = v7Old := if_pos hcond
    rw [hq, hr, h9, h7]
    have taken := cpsBranchWithin_takenPath composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_x0p).2 hcond)
    exact cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          have hp' := sepConj_mono_left (sepConj_mono_right
            (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
          xperm_hyp hp') taken)
  · -- Fall-through: cap fires.
    have hq : q0c = q0cCap := if_neg hcond
    have hr : rhat2c = rhat2 + (q0 - q0cCap) * dHi := if_neg hcond
    have h9 : x9o = q0cCap := if_neg hcond
    have h7 : x7o = (q0 - q0cCap) * dHi := if_neg hcond
    rw [hq, hr, h9, h7]
    have ntaken := cpsBranchWithin_ntakenPath composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact hcond ((sepConj_pure_right _).1 h_x0p).2)
    -- Correction body [49]-[54]: raw register expressions.
    have I1 := addi_spec_gen_within .x9 .x0 hi (0 : Word) 4095 (base + 8) (by nofun)
    have I2 := srli_spec_gen_same_within .x9 ((0 : Word) + signExtend12 4095) 32
      (base + 12) (by nofun)
    have I3 := sub_spec_gen_within .x7 .x5 .x9 q0
      (((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat) v7Old (base + 16) (by nofun)
    have I4 := mul_spec_gen_rd_eq_rs1_within .x7 .x6
      (q0 - ((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat) dHi (base + 20) (by nofun)
    have I5 := add_spec_gen_rd_eq_rs1_within .x11 .x7 rhat2
      ((q0 - ((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat) * dHi)
      (base + 24) (by nofun)
    have I6 := addi_spec_gen_within .x5 .x9 q0
      (((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat) 0 (base + 28) (by nofun)
    have hcorr : cpsTripleWithin 6 (base + 8) (base + 32) cr
        ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi) **
         (.x9 ↦ᵣ hi) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ 0))
        ((.x5 ↦ᵣ (((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat + signExtend12 0)) **
         (.x11 ↦ᵣ (rhat2 + (q0 - ((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat) * dHi)) **
         (.x6 ↦ᵣ dHi) **
         (.x9 ↦ᵣ (((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat)) **
         (.x7 ↦ᵣ ((q0 - ((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat) * dHi)) **
         (.x0 ↦ᵣ 0)) := by
      runBlock I1 I2 I3 I4 I5 I6
    have full := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp') ntaken hcorr
    have hCAP : ((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat = q0cCap := by
      show ((0 : Word) + signExtend12 4095) >>> (32 : BitVec 6).toNat
        = (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
      decide
    have hMV : q0cCap + signExtend12 0 = q0cCap := by
      show (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat + signExtend12 0
        = (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
      decide
    rw [hCAP] at full
    rw [hMV] at full
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full

end EvmAsm.Evm64
