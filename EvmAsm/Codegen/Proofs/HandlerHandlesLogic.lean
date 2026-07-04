/-
  EvmAsm.Codegen.Proofs.HandlerHandlesLogic

  Bead evm-asm-4ch8f.10.1 — the equality/bitwise clean-ret handler handles
  (EQ, AND, OR, XOR), packaged as snapshot-parameterized dispatch handles
  (`FnHandleS`, `docs/4ch8f-interp-strategy.md` §3).  Split off from
  `HandlerHandlesBinary.lean` to stay within the per-file line cap; same
  "binary, pop-one" shape and same reusable bridges from `HandlerHandles.lean`
  (`bytesRegion_eq_8cells`, `regFileIs_split_bin`, `evmBinRest`, `wsDword`,
  `wsDword_lo`/`_peel`/`_head`).  Each block mirrors the ADD template
  `evmAddHandle_sound` there.

  EQ peels four scratch registers (x7,x6,x5,x11); AND/OR/XOR peel only two
  (x7,x6) and frame x5/x11 across the call.
-/

import EvmAsm.Codegen.Proofs.HandlerHandles

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

-- ============================================================================
-- EQ (0x14)  —  equality (XOR-OR-accumulate → SLTIU)
-- ============================================================================

/-- Snapshot-parameterized guarantee of the EQ handler. -/
def evmEqPostS (sp : Word) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    let a0 := wsDword ws₀ 0
    let a1 := wsDword ws₀ 8
    let a2 := wsDword ws₀ 16
    let a3 := wsDword ws₀ 24
    let b0 := wsDword ws₀ 32
    let b1 := wsDword ws₀ 40
    let b2 := wsDword ws₀ 48
    let b3 := wsDword ws₀ 56
    let acc0 := a0 ^^^ b0
    let acc1 := acc0 ||| (a1 ^^^ b1)
    let acc2 := acc1 ||| (a2 ^^^ b2)
    let acc3 := acc2 ||| (a3 ^^^ b3)
    let eqResult := if BitVec.ult acc3 (1 : Word) then (1 : Word) else 0
    rf.get .x12 = sp + 32
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x7 = eqResult
    ∧ rf.get .x6 = (a3 ^^^ b3)
    ∧ rf.get .x5 = b3
    ∧ rf.get .x11 = rf₀.get .x11
    ∧ ws = ws₀.take 32 ++ dwordBytes eqResult ++ dwordBytes 0
        ++ dwordBytes 0 ++ dwordBytes 0
    ∧ A = A₀

attribute [irreducible] evmEqPostS

/-- The EQ handler satisfies the `FnHandleS` calling contract. -/
theorem evmEqHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 64 → A₀.pcFree → evmAddPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 23 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_eq 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (evmEqPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty ⟨sp, 64⟩ (Reach.exact rf₀ ws₀ A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  have h_spec := evmEqHandlerSpec sp base
    (wsDword ws 0) (wsDword ws 8) (wsDword ws 16) (wsDword ws 24)
    (wsDword ws 32) (wsDword ws 40) (wsDword ws 48) (wsDword ws 56)
    (rf.get .x7) (rf.get .x6) (rf.get .x5) (rf.get .x11) (rf.get .x10) ret
  rw [halign] at h_spec
  have h_framed := cpsTripleWithin_frameR (regFileOn evmBinRest rf ** A)
    (pcFree_sepConj (pcFree_regFileOn _ _) hApc) h_spec
  refine cpsTripleWithin_weaken ?_ ?_ h_framed
  · intro hp hh
    rw [show bytesRegion Region.empty.base Region.empty.bytes = empAssertion
          from rfl,
      sepConj_emp_left', bytesRegion_eq_8cells sp ws hlen,
      regFileIs_split_bin rf, hpre] at hh
    xperm_hyp hh
  · intro hp hh
    set a0 := wsDword ws 0 with ha0
    set a1 := wsDword ws 8 with ha1
    set a2 := wsDword ws 16 with ha2
    set a3 := wsDword ws 24 with ha3
    set b0 := wsDword ws 32 with hb0
    set b1 := wsDword ws 40 with hb1
    set b2 := wsDword ws 48 with hb2
    set b3 := wsDword ws 56 with hb3
    set acc0 := a0 ^^^ b0 with hacc0
    set acc1 := acc0 ||| (a1 ^^^ b1) with hacc1
    set acc2 := acc1 ||| (a2 ^^^ b2) with hacc2
    set acc3 := acc2 ||| (a3 ^^^ b3) with hacc3
    set eqResult := if BitVec.ult acc3 (1 : Word) then (1 : Word) else 0 with heqResult
    set rf' : RegFile := fun r =>
      if r = .x12 then sp + 32
      else if r = .x7 then eqResult
      else if r = .x6 then (a3 ^^^ b3)
      else if r = .x5 then b3
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    set ws' : List (BitVec 8) :=
      ws.take 32 ++ dwordBytes eqResult ++ dwordBytes 0
        ++ dwordBytes 0 ++ dwordBytes 0 with hws'
    have hws'len : ws'.length = 64 := by
      simp only [hws', List.length_append, length_dwordBytes, List.length_take]
      omega
    have g12 : rf'.get .x12 = sp + 32 := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = eqResult := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = (a3 ^^^ b3) := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = b3 := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = rf.get .x11 := by rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    have hR : ws' = ws.take 32 ++ (dwordBytes eqResult ++ (dwordBytes 0 ++
        (dwordBytes 0 ++ dwordBytes 0))) := by
      rw [hws']; simp only [List.append_assoc]
    have h8 : (dwordBytes eqResult).length = 8 := length_dwordBytes _
    have h8' : (dwordBytes (0 : Word)).length = 8 := length_dwordBytes _
    have h8'' : (dwordBytes (0 : Word)).length = 8 := length_dwordBytes _
    have ht : (List.take 32 ws).length = 32 := by rw [List.length_take]; omega
    have hw0 : wsDword ws' 0 = a0 := by
      rw [ha0, hR]; exact wsDword_lo ws _ 0 (by omega) (by omega)
    have hw8 : wsDword ws' 8 = a1 := by
      rw [ha1, hR]; exact wsDword_lo ws _ 8 (by omega) (by omega)
    have hw16 : wsDword ws' 16 = a2 := by
      rw [ha2, hR]; exact wsDword_lo ws _ 16 (by omega) (by omega)
    have hw24 : wsDword ws' 24 = a3 := by
      rw [ha3, hR]; exact wsDword_lo ws _ 24 (by omega) (by omega)
    have hw32 : wsDword ws' 32 = eqResult := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega)]
      exact wsDword_head _ _
    have hw40 : wsDword ws' 40 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes eqResult) _ _ 8 h8 (by omega)]
      exact wsDword_head _ _
    have hw48 : wsDword ws' 48 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes eqResult) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (0 : Word)) _ _ 8 h8' (by omega)]
      exact wsDword_head _ _
    have hw56 : wsDword ws' 56 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes eqResult) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (0 : Word)) _ _ 8 h8' (by omega),
        wsDword_peel (dwordBytes (0 : Word)) _ _ 8 h8'' (by omega),
        ← List.append_nil (dwordBytes (0 : Word))]
      exact wsDword_head _ _
    have hx : (((.x1 : Reg) ↦ᵣ ret) **
        ((regFileIs rf' ** bytesRegion sp ws') ** A)) hp := by
      rw [regFileIs_split_bin rf', bytesRegion_eq_8cells sp ws' hws'len,
        g12, g7, g6, g5, g11, g10, grest, hw0, hw8, hw16, hw24, hw32, hw40,
        hw48, hw56]
      xperm_hyp hh
    refine sepConj_mono_right (fun h2 hh2 => ?_) hp hx
    rw [show asrtM Region.empty ⟨sp, 64⟩ (evmEqPostS sp rf ws A)
          = asrtOf ⟨sp, 64⟩ (evmEqPostS sp rf ws A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', ws', A, hws'len, hApc, ?_, hh2⟩
    show evmEqPostS sp rf ws A rf' ws' A
    simp only [evmEqPostS, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2,
      ← hb3, ← hacc0, ← hacc1, ← hacc2, ← hacc3, ← heqResult]
    exact ⟨g12, g10, g7, g6, g5, g11, hws', trivial⟩

/-- The packaged EQ dispatch handle. -/
def evmEqHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_eq 1
  nSteps := 23
  region := Region.empty
  rw := ⟨sp, 64⟩
  pre := evmAddPre sp
  post := evmEqPostS sp
  sound := evmEqHandle_sound base sp

-- ============================================================================
-- AND (0x16)  —  bitwise, two scratch registers (x7, x6)
-- ============================================================================

/-- Snapshot-parameterized guarantee of the AND handler.  Only the two scratch
    registers `x7`/`x6` are touched (x5/x11 are framed, hence unconstrained). -/
def evmAndPostS (sp : Word) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    let a0 := wsDword ws₀ 0
    let a1 := wsDword ws₀ 8
    let a2 := wsDword ws₀ 16
    let a3 := wsDword ws₀ 24
    let b0 := wsDword ws₀ 32
    let b1 := wsDword ws₀ 40
    let b2 := wsDword ws₀ 48
    let b3 := wsDword ws₀ 56
    rf.get .x12 = sp + 32
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x7 = a3 &&& b3
    ∧ rf.get .x6 = b3
    ∧ ws = ws₀.take 32 ++ dwordBytes (a0 &&& b0) ++ dwordBytes (a1 &&& b1)
        ++ dwordBytes (a2 &&& b2) ++ dwordBytes (a3 &&& b3)
    ∧ A = A₀

attribute [irreducible] evmAndPostS

/-- The AND handler satisfies the `FnHandleS` calling contract. -/
theorem evmAndHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 64 → A₀.pcFree → evmAddPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 19 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_and 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (evmAndPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty ⟨sp, 64⟩ (Reach.exact rf₀ ws₀ A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  have h_spec := evmAndHandlerSpec sp base
    (wsDword ws 0) (wsDword ws 8) (wsDword ws 16) (wsDword ws 24)
    (wsDword ws 32) (wsDword ws 40) (wsDword ws 48) (wsDword ws 56)
    (rf.get .x7) (rf.get .x6) (rf.get .x10) ret
  rw [halign] at h_spec
  have h_framed := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ rf.get .x5) ** ((.x11 : Reg) ↦ᵣ rf.get .x11) **
      (regFileOn evmBinRest rf ** A))
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (pcFree_regFileOn _ _) hApc))) h_spec
  refine cpsTripleWithin_weaken ?_ ?_ h_framed
  · intro hp hh
    rw [show bytesRegion Region.empty.base Region.empty.bytes = empAssertion
          from rfl,
      sepConj_emp_left', bytesRegion_eq_8cells sp ws hlen,
      regFileIs_split_bin rf, hpre] at hh
    xperm_hyp hh
  · intro hp hh
    set a0 := wsDword ws 0 with ha0
    set a1 := wsDword ws 8 with ha1
    set a2 := wsDword ws 16 with ha2
    set a3 := wsDword ws 24 with ha3
    set b0 := wsDword ws 32 with hb0
    set b1 := wsDword ws 40 with hb1
    set b2 := wsDword ws 48 with hb2
    set b3 := wsDword ws 56 with hb3
    set rf' : RegFile := fun r =>
      if r = .x12 then sp + 32
      else if r = .x7 then a3 &&& b3
      else if r = .x6 then b3
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    set ws' : List (BitVec 8) :=
      ws.take 32 ++ dwordBytes (a0 &&& b0) ++ dwordBytes (a1 &&& b1)
        ++ dwordBytes (a2 &&& b2) ++ dwordBytes (a3 &&& b3) with hws'
    have hws'len : ws'.length = 64 := by
      simp only [hws', List.length_append, length_dwordBytes, List.length_take]
      omega
    have g12 : rf'.get .x12 = sp + 32 := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = a3 &&& b3 := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = b3 := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = rf.get .x5 := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = rf.get .x11 := by rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    have hR : ws' = ws.take 32 ++ (dwordBytes (a0 &&& b0) ++
        (dwordBytes (a1 &&& b1) ++ (dwordBytes (a2 &&& b2)
          ++ dwordBytes (a3 &&& b3)))) := by
      rw [hws']; simp only [List.append_assoc]
    have h8 : (dwordBytes (a0 &&& b0)).length = 8 := length_dwordBytes _
    have h8' : (dwordBytes (a1 &&& b1)).length = 8 := length_dwordBytes _
    have h8'' : (dwordBytes (a2 &&& b2)).length = 8 := length_dwordBytes _
    have ht : (List.take 32 ws).length = 32 := by rw [List.length_take]; omega
    have hw0 : wsDword ws' 0 = a0 := by
      rw [ha0, hR]; exact wsDword_lo ws _ 0 (by omega) (by omega)
    have hw8 : wsDword ws' 8 = a1 := by
      rw [ha1, hR]; exact wsDword_lo ws _ 8 (by omega) (by omega)
    have hw16 : wsDword ws' 16 = a2 := by
      rw [ha2, hR]; exact wsDword_lo ws _ 16 (by omega) (by omega)
    have hw24 : wsDword ws' 24 = a3 := by
      rw [ha3, hR]; exact wsDword_lo ws _ 24 (by omega) (by omega)
    have hw32 : wsDword ws' 32 = a0 &&& b0 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega)]
      exact wsDword_head _ _
    have hw40 : wsDword ws' 40 = a1 &&& b1 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes (a0 &&& b0)) _ _ 8 h8 (by omega)]
      exact wsDword_head _ _
    have hw48 : wsDword ws' 48 = a2 &&& b2 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes (a0 &&& b0)) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (a1 &&& b1)) _ _ 8 h8' (by omega)]
      exact wsDword_head _ _
    have hw56 : wsDword ws' 56 = a3 &&& b3 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes (a0 &&& b0)) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (a1 &&& b1)) _ _ 8 h8' (by omega),
        wsDword_peel (dwordBytes (a2 &&& b2)) _ _ 8 h8'' (by omega),
        ← List.append_nil (dwordBytes (a3 &&& b3))]
      exact wsDword_head _ _
    have hx : (((.x1 : Reg) ↦ᵣ ret) **
        ((regFileIs rf' ** bytesRegion sp ws') ** A)) hp := by
      rw [regFileIs_split_bin rf', bytesRegion_eq_8cells sp ws' hws'len,
        g12, g7, g6, g5, g11, g10, grest, hw0, hw8, hw16, hw24, hw32, hw40,
        hw48, hw56]
      xperm_hyp hh
    refine sepConj_mono_right (fun h2 hh2 => ?_) hp hx
    rw [show asrtM Region.empty ⟨sp, 64⟩ (evmAndPostS sp rf ws A)
          = asrtOf ⟨sp, 64⟩ (evmAndPostS sp rf ws A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', ws', A, hws'len, hApc, ?_, hh2⟩
    show evmAndPostS sp rf ws A rf' ws' A
    simp only [evmAndPostS, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2,
      ← hb3]
    exact ⟨g12, g10, g7, g6, hws', trivial⟩

/-- The packaged AND dispatch handle. -/
def evmAndHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_and 1
  nSteps := 19
  region := Region.empty
  rw := ⟨sp, 64⟩
  pre := evmAddPre sp
  post := evmAndPostS sp
  sound := evmAndHandle_sound base sp

-- ============================================================================
-- OR (0x17)  —  bitwise, two scratch registers (x7, x6)
-- ============================================================================

/-- Snapshot-parameterized guarantee of the OR handler. -/
def evmOrPostS (sp : Word) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    let a0 := wsDword ws₀ 0
    let a1 := wsDword ws₀ 8
    let a2 := wsDword ws₀ 16
    let a3 := wsDword ws₀ 24
    let b0 := wsDword ws₀ 32
    let b1 := wsDword ws₀ 40
    let b2 := wsDword ws₀ 48
    let b3 := wsDword ws₀ 56
    rf.get .x12 = sp + 32
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x7 = a3 ||| b3
    ∧ rf.get .x6 = b3
    ∧ ws = ws₀.take 32 ++ dwordBytes (a0 ||| b0) ++ dwordBytes (a1 ||| b1)
        ++ dwordBytes (a2 ||| b2) ++ dwordBytes (a3 ||| b3)
    ∧ A = A₀

attribute [irreducible] evmOrPostS

/-- The OR handler satisfies the `FnHandleS` calling contract. -/
theorem evmOrHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 64 → A₀.pcFree → evmAddPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 19 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_or 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (evmOrPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty ⟨sp, 64⟩ (Reach.exact rf₀ ws₀ A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  have h_spec := evmOrHandlerSpec sp base
    (wsDword ws 0) (wsDword ws 8) (wsDword ws 16) (wsDword ws 24)
    (wsDword ws 32) (wsDword ws 40) (wsDword ws 48) (wsDword ws 56)
    (rf.get .x7) (rf.get .x6) (rf.get .x10) ret
  rw [halign] at h_spec
  have h_framed := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ rf.get .x5) ** ((.x11 : Reg) ↦ᵣ rf.get .x11) **
      (regFileOn evmBinRest rf ** A))
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (pcFree_regFileOn _ _) hApc))) h_spec
  refine cpsTripleWithin_weaken ?_ ?_ h_framed
  · intro hp hh
    rw [show bytesRegion Region.empty.base Region.empty.bytes = empAssertion
          from rfl,
      sepConj_emp_left', bytesRegion_eq_8cells sp ws hlen,
      regFileIs_split_bin rf, hpre] at hh
    xperm_hyp hh
  · intro hp hh
    set a0 := wsDword ws 0 with ha0
    set a1 := wsDword ws 8 with ha1
    set a2 := wsDword ws 16 with ha2
    set a3 := wsDword ws 24 with ha3
    set b0 := wsDword ws 32 with hb0
    set b1 := wsDword ws 40 with hb1
    set b2 := wsDword ws 48 with hb2
    set b3 := wsDword ws 56 with hb3
    set rf' : RegFile := fun r =>
      if r = .x12 then sp + 32
      else if r = .x7 then a3 ||| b3
      else if r = .x6 then b3
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    set ws' : List (BitVec 8) :=
      ws.take 32 ++ dwordBytes (a0 ||| b0) ++ dwordBytes (a1 ||| b1)
        ++ dwordBytes (a2 ||| b2) ++ dwordBytes (a3 ||| b3) with hws'
    have hws'len : ws'.length = 64 := by
      simp only [hws', List.length_append, length_dwordBytes, List.length_take]
      omega
    have g12 : rf'.get .x12 = sp + 32 := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = a3 ||| b3 := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = b3 := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = rf.get .x5 := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = rf.get .x11 := by rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    have hR : ws' = ws.take 32 ++ (dwordBytes (a0 ||| b0) ++
        (dwordBytes (a1 ||| b1) ++ (dwordBytes (a2 ||| b2)
          ++ dwordBytes (a3 ||| b3)))) := by
      rw [hws']; simp only [List.append_assoc]
    have h8 : (dwordBytes (a0 ||| b0)).length = 8 := length_dwordBytes _
    have h8' : (dwordBytes (a1 ||| b1)).length = 8 := length_dwordBytes _
    have h8'' : (dwordBytes (a2 ||| b2)).length = 8 := length_dwordBytes _
    have ht : (List.take 32 ws).length = 32 := by rw [List.length_take]; omega
    have hw0 : wsDword ws' 0 = a0 := by
      rw [ha0, hR]; exact wsDword_lo ws _ 0 (by omega) (by omega)
    have hw8 : wsDword ws' 8 = a1 := by
      rw [ha1, hR]; exact wsDword_lo ws _ 8 (by omega) (by omega)
    have hw16 : wsDword ws' 16 = a2 := by
      rw [ha2, hR]; exact wsDword_lo ws _ 16 (by omega) (by omega)
    have hw24 : wsDword ws' 24 = a3 := by
      rw [ha3, hR]; exact wsDword_lo ws _ 24 (by omega) (by omega)
    have hw32 : wsDword ws' 32 = a0 ||| b0 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega)]
      exact wsDword_head _ _
    have hw40 : wsDword ws' 40 = a1 ||| b1 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes (a0 ||| b0)) _ _ 8 h8 (by omega)]
      exact wsDword_head _ _
    have hw48 : wsDword ws' 48 = a2 ||| b2 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes (a0 ||| b0)) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (a1 ||| b1)) _ _ 8 h8' (by omega)]
      exact wsDword_head _ _
    have hw56 : wsDword ws' 56 = a3 ||| b3 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes (a0 ||| b0)) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (a1 ||| b1)) _ _ 8 h8' (by omega),
        wsDword_peel (dwordBytes (a2 ||| b2)) _ _ 8 h8'' (by omega),
        ← List.append_nil (dwordBytes (a3 ||| b3))]
      exact wsDword_head _ _
    have hx : (((.x1 : Reg) ↦ᵣ ret) **
        ((regFileIs rf' ** bytesRegion sp ws') ** A)) hp := by
      rw [regFileIs_split_bin rf', bytesRegion_eq_8cells sp ws' hws'len,
        g12, g7, g6, g5, g11, g10, grest, hw0, hw8, hw16, hw24, hw32, hw40,
        hw48, hw56]
      xperm_hyp hh
    refine sepConj_mono_right (fun h2 hh2 => ?_) hp hx
    rw [show asrtM Region.empty ⟨sp, 64⟩ (evmOrPostS sp rf ws A)
          = asrtOf ⟨sp, 64⟩ (evmOrPostS sp rf ws A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', ws', A, hws'len, hApc, ?_, hh2⟩
    show evmOrPostS sp rf ws A rf' ws' A
    simp only [evmOrPostS, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2,
      ← hb3]
    exact ⟨g12, g10, g7, g6, hws', trivial⟩

/-- The packaged OR dispatch handle. -/
def evmOrHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_or 1
  nSteps := 19
  region := Region.empty
  rw := ⟨sp, 64⟩
  pre := evmAddPre sp
  post := evmOrPostS sp
  sound := evmOrHandle_sound base sp

-- ============================================================================
-- XOR (0x18)  —  bitwise, two scratch registers (x7, x6)
-- ============================================================================

/-- Snapshot-parameterized guarantee of the XOR handler. -/
def evmXorPostS (sp : Word) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    let a0 := wsDword ws₀ 0
    let a1 := wsDword ws₀ 8
    let a2 := wsDword ws₀ 16
    let a3 := wsDword ws₀ 24
    let b0 := wsDword ws₀ 32
    let b1 := wsDword ws₀ 40
    let b2 := wsDword ws₀ 48
    let b3 := wsDword ws₀ 56
    rf.get .x12 = sp + 32
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x7 = a3 ^^^ b3
    ∧ rf.get .x6 = b3
    ∧ ws = ws₀.take 32 ++ dwordBytes (a0 ^^^ b0) ++ dwordBytes (a1 ^^^ b1)
        ++ dwordBytes (a2 ^^^ b2) ++ dwordBytes (a3 ^^^ b3)
    ∧ A = A₀

attribute [irreducible] evmXorPostS

/-- The XOR handler satisfies the `FnHandleS` calling contract. -/
theorem evmXorHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 64 → A₀.pcFree → evmAddPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 19 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_xor 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (evmXorPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty ⟨sp, 64⟩ (Reach.exact rf₀ ws₀ A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  have h_spec := evmXorHandlerSpec sp base
    (wsDword ws 0) (wsDword ws 8) (wsDword ws 16) (wsDword ws 24)
    (wsDword ws 32) (wsDword ws 40) (wsDword ws 48) (wsDword ws 56)
    (rf.get .x7) (rf.get .x6) (rf.get .x10) ret
  rw [halign] at h_spec
  have h_framed := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ rf.get .x5) ** ((.x11 : Reg) ↦ᵣ rf.get .x11) **
      (regFileOn evmBinRest rf ** A))
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (pcFree_regFileOn _ _) hApc))) h_spec
  refine cpsTripleWithin_weaken ?_ ?_ h_framed
  · intro hp hh
    rw [show bytesRegion Region.empty.base Region.empty.bytes = empAssertion
          from rfl,
      sepConj_emp_left', bytesRegion_eq_8cells sp ws hlen,
      regFileIs_split_bin rf, hpre] at hh
    xperm_hyp hh
  · intro hp hh
    set a0 := wsDword ws 0 with ha0
    set a1 := wsDword ws 8 with ha1
    set a2 := wsDword ws 16 with ha2
    set a3 := wsDword ws 24 with ha3
    set b0 := wsDword ws 32 with hb0
    set b1 := wsDword ws 40 with hb1
    set b2 := wsDword ws 48 with hb2
    set b3 := wsDword ws 56 with hb3
    set rf' : RegFile := fun r =>
      if r = .x12 then sp + 32
      else if r = .x7 then a3 ^^^ b3
      else if r = .x6 then b3
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    set ws' : List (BitVec 8) :=
      ws.take 32 ++ dwordBytes (a0 ^^^ b0) ++ dwordBytes (a1 ^^^ b1)
        ++ dwordBytes (a2 ^^^ b2) ++ dwordBytes (a3 ^^^ b3) with hws'
    have hws'len : ws'.length = 64 := by
      simp only [hws', List.length_append, length_dwordBytes, List.length_take]
      omega
    have g12 : rf'.get .x12 = sp + 32 := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = a3 ^^^ b3 := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = b3 := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = rf.get .x5 := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = rf.get .x11 := by rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    have hR : ws' = ws.take 32 ++ (dwordBytes (a0 ^^^ b0) ++
        (dwordBytes (a1 ^^^ b1) ++ (dwordBytes (a2 ^^^ b2)
          ++ dwordBytes (a3 ^^^ b3)))) := by
      rw [hws']; simp only [List.append_assoc]
    have h8 : (dwordBytes (a0 ^^^ b0)).length = 8 := length_dwordBytes _
    have h8' : (dwordBytes (a1 ^^^ b1)).length = 8 := length_dwordBytes _
    have h8'' : (dwordBytes (a2 ^^^ b2)).length = 8 := length_dwordBytes _
    have ht : (List.take 32 ws).length = 32 := by rw [List.length_take]; omega
    have hw0 : wsDword ws' 0 = a0 := by
      rw [ha0, hR]; exact wsDword_lo ws _ 0 (by omega) (by omega)
    have hw8 : wsDword ws' 8 = a1 := by
      rw [ha1, hR]; exact wsDword_lo ws _ 8 (by omega) (by omega)
    have hw16 : wsDword ws' 16 = a2 := by
      rw [ha2, hR]; exact wsDword_lo ws _ 16 (by omega) (by omega)
    have hw24 : wsDword ws' 24 = a3 := by
      rw [ha3, hR]; exact wsDword_lo ws _ 24 (by omega) (by omega)
    have hw32 : wsDword ws' 32 = a0 ^^^ b0 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega)]
      exact wsDword_head _ _
    have hw40 : wsDword ws' 40 = a1 ^^^ b1 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes (a0 ^^^ b0)) _ _ 8 h8 (by omega)]
      exact wsDword_head _ _
    have hw48 : wsDword ws' 48 = a2 ^^^ b2 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes (a0 ^^^ b0)) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (a1 ^^^ b1)) _ _ 8 h8' (by omega)]
      exact wsDword_head _ _
    have hw56 : wsDword ws' 56 = a3 ^^^ b3 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes (a0 ^^^ b0)) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (a1 ^^^ b1)) _ _ 8 h8' (by omega),
        wsDword_peel (dwordBytes (a2 ^^^ b2)) _ _ 8 h8'' (by omega),
        ← List.append_nil (dwordBytes (a3 ^^^ b3))]
      exact wsDword_head _ _
    have hx : (((.x1 : Reg) ↦ᵣ ret) **
        ((regFileIs rf' ** bytesRegion sp ws') ** A)) hp := by
      rw [regFileIs_split_bin rf', bytesRegion_eq_8cells sp ws' hws'len,
        g12, g7, g6, g5, g11, g10, grest, hw0, hw8, hw16, hw24, hw32, hw40,
        hw48, hw56]
      xperm_hyp hh
    refine sepConj_mono_right (fun h2 hh2 => ?_) hp hx
    rw [show asrtM Region.empty ⟨sp, 64⟩ (evmXorPostS sp rf ws A)
          = asrtOf ⟨sp, 64⟩ (evmXorPostS sp rf ws A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', ws', A, hws'len, hApc, ?_, hh2⟩
    show evmXorPostS sp rf ws A rf' ws' A
    simp only [evmXorPostS, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2,
      ← hb3]
    exact ⟨g12, g10, g7, g6, hws', trivial⟩

/-- The packaged XOR dispatch handle. -/
def evmXorHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_xor 1
  nSteps := 19
  region := Region.empty
  rw := ⟨sp, 64⟩
  pre := evmAddPre sp
  post := evmXorPostS sp
  sound := evmXorHandle_sound base sp

end EvmAsm.Codegen.Proofs
