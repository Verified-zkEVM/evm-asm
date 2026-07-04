/-
  EvmAsm.Codegen.Proofs.HandlerHandlesUnary

  Bead evm-asm-4ch8f.10.1 — package the verified UNARY clean-ret handler
  specs (ISZERO, NOT) and POP as snapshot-parameterized dispatch handles
  (`FnHandleS`, `docs/4ch8f-interp-strategy.md` §3), consumed by the
  interpreter dispatch loop (`.callRegS`, bead `.49`).

  Companion to `HandlerHandles.lean` (the ADD worked template + the reusable
  bridges reused here: `wsDword`, `regFileIs_split_bin`/`evmBinRest`,
  `wsDword_head`, `wsDword_peel`).  The two structural differences from the
  binary family:

  * ISZERO/NOT read one 256-bit operand word: a MINIMAL 4-dword window
    `rw := ⟨sp, 32⟩`, bridged by `bytesRegion_eq_4cells` (added here), the
    value-stack pointer `x12` UNCHANGED (unary ops don't move the top).
  * POP touches no stack bytes — it only bumps `x12` by one word — so its
    window is empty (`rw := RwRegion.empty`).

  As in the binary family the proof reuses the existing HandlerSpecs
  `cpsTripleWithin` verbatim (the arithmetic is NOT re-derived); each
  `<op>PostS` is `[irreducible]` so its `let`-bundle stays folded during
  unification (no `maxHeartbeats` raise).
-/

import EvmAsm.Codegen.Proofs.HandlerHandles

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

-- ============================================================================
-- The 4-dword window split (unary operand word)
-- ============================================================================

/-- A 32-byte value-stack window is the separating conjunction of its four
    dword cells, valued by `wsDword` — the unary analogue of
    `bytesRegion_eq_8cells`. -/
theorem bytesRegion_eq_4cells (sp : Word) (ws : List (BitVec 8))
    (h : ws.length = 32) :
    bytesRegion sp ws
      = ((sp ↦ₘ wsDword ws 0) ** ((sp + 8) ↦ₘ wsDword ws 8) **
         ((sp + 16) ↦ₘ wsDword ws 16) ** ((sp + 24) ↦ₘ wsDword ws 24)) := by
  have hnn : ∀ k : Nat, k ≤ 24 → ws.drop k ≠ [] := by
    intro k hk hc
    have : (ws.drop k).length = 0 := by rw [hc]; rfl
    rw [List.length_drop, h] at this; omega
  rw [bytesRegion_eq_cons sp ws (by simpa using hnn 0 (by omega))]
  rw [bytesRegion_eq_cons (sp + 8) (ws.drop 8)
    (by simpa [List.drop_drop] using hnn 8 (by omega))]
  rw [bytesRegion_eq_cons (sp + 8 + 8) ((ws.drop 8).drop 8)
    (by simpa [List.drop_drop] using hnn 16 (by omega))]
  rw [bytesRegion_eq_cons (sp + 8 + 8 + 8) (((ws.drop 8).drop 8).drop 8)
    (by simpa [List.drop_drop] using hnn 24 (by omega))]
  rw [show ((((ws.drop 8).drop 8).drop 8).drop 8) = [] from by
      rw [List.drop_eq_nil_iff]; simp only [List.length_drop, h]; omega,
    bytesRegion_nil, sepConj_emp_right']
  simp only [List.drop_drop]
  rw [show sp + 8 + 8 = sp + 16 from by bv_omega,
    show sp + 16 + 8 = sp + 24 from by bv_omega]
  simp only [wsDword, Nat.reduceAdd, List.drop_zero]

-- ============================================================================
-- ISZERO (0x15)
-- ============================================================================

/-- Call-site obligation of the ISZERO handler (§3 uniform pre). -/
def evmIsZeroPre (sp : Word) : Reach :=
  fun rf _ _ => rf.get .x12 = sp

/-- Snapshot-parameterized guarantee of the ISZERO handler: the top word is
    replaced by its zero-test (a boolean in the low dword, the rest zeroed);
    the stack pointer is UNCHANGED (unary), the code pointer advances one byte. -/
def evmIsZeroPostS (sp : Word) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    let a0 := wsDword ws₀ 0
    let a1 := wsDword ws₀ 8
    let a2 := wsDword ws₀ 16
    let a3 := wsDword ws₀ 24
    let orAll := a0 ||| a1 ||| a2 ||| a3
    let result := if BitVec.ult orAll (1 : Word) then (1 : Word) else 0
    rf.get .x12 = sp
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x7 = result
    ∧ rf.get .x6 = a3
    ∧ ws = dwordBytes result ++ dwordBytes 0 ++ dwordBytes 0 ++ dwordBytes 0
    ∧ A = A₀

attribute [irreducible] evmIsZeroPostS

/-- The ISZERO handler satisfies the `FnHandleS` calling contract. -/
theorem evmIsZeroHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 32 → A₀.pcFree → evmIsZeroPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 14 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_iszero 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 32⟩
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 32⟩
          (evmIsZeroPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty ⟨sp, 32⟩ (Reach.exact rf₀ ws₀ A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  have h_spec := evmIsZeroHandlerSpec sp base
    (wsDword ws 0) (wsDword ws 8) (wsDword ws 16) (wsDword ws 24)
    (rf.get .x7) (rf.get .x6) (rf.get .x10) ret
  rw [halign] at h_spec
  -- frame the untouched registers (x5, x11 among the peeled six) + ambient A
  have h_framed := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ rf.get .x5) ** ((.x11 : Reg) ↦ᵣ rf.get .x11) **
      regFileOn evmBinRest rf ** A)
    (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (pcFree_regFileOn _ _) hApc))) h_spec
  refine cpsTripleWithin_weaken ?_ ?_ h_framed
  · intro hp hh
    rw [show bytesRegion Region.empty.base Region.empty.bytes = empAssertion
          from rfl,
      sepConj_emp_left', bytesRegion_eq_4cells sp ws hlen,
      regFileIs_split_bin rf, hpre] at hh
    xperm_hyp hh
  · intro hp hh
    set a0 := wsDword ws 0 with ha0
    set a1 := wsDword ws 8 with ha1
    set a2 := wsDword ws 16 with ha2
    set a3 := wsDword ws 24 with ha3
    set orAll := a0 ||| a1 ||| a2 ||| a3 with horAll
    set result := if BitVec.ult orAll (1 : Word) then (1 : Word) else 0 with hresult
    set rf' : RegFile := fun r =>
      if r = .x12 then sp
      else if r = .x7 then result
      else if r = .x6 then a3
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    set ws' : List (BitVec 8) :=
      dwordBytes result ++ dwordBytes 0 ++ dwordBytes 0 ++ dwordBytes 0 with hws'
    have hws'len : ws'.length = 32 := by
      simp only [hws', List.length_append, length_dwordBytes]
    have g12 : rf'.get .x12 = sp := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = result := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = a3 := by rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = rf.get .x5 := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = rf.get .x11 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    have hR : ws' = dwordBytes result ++ (dwordBytes 0 ++ (dwordBytes 0 ++
        dwordBytes (0 : Word))) := by
      rw [hws']; simp only [List.append_assoc]
    have h8 : (dwordBytes result).length = 8 := length_dwordBytes _
    have h8' : (dwordBytes (0 : Word)).length = 8 := length_dwordBytes _
    have hw0 : wsDword ws' 0 = result := by rw [hR]; exact wsDword_head _ _
    have hw8 : wsDword ws' 8 = 0 := by
      rw [hR, wsDword_peel (dwordBytes result) _ _ 8 h8 (by omega)]
      exact wsDword_head _ _
    have hw16 : wsDword ws' 16 = 0 := by
      rw [hR, wsDword_peel (dwordBytes result) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (0 : Word)) _ _ 8 h8' (by omega)]
      exact wsDword_head _ _
    have hw24 : wsDword ws' 24 = 0 := by
      rw [hR, wsDword_peel (dwordBytes result) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (0 : Word)) _ _ 8 h8' (by omega),
        wsDword_peel (dwordBytes (0 : Word)) _ _ 8 h8' (by omega),
        ← List.append_nil (dwordBytes (0 : Word))]
      exact wsDword_head _ _
    have hx : (((.x1 : Reg) ↦ᵣ ret) **
        ((regFileIs rf' ** bytesRegion sp ws') ** A)) hp := by
      rw [regFileIs_split_bin rf', bytesRegion_eq_4cells sp ws' hws'len,
        g12, g7, g6, g10, g5, g11, grest, hw0, hw8, hw16, hw24]
      xperm_hyp hh
    refine sepConj_mono_right (fun h2 hh2 => ?_) hp hx
    rw [show asrtM Region.empty ⟨sp, 32⟩ (evmIsZeroPostS sp rf ws A)
          = asrtOf ⟨sp, 32⟩ (evmIsZeroPostS sp rf ws A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', ws', A, hws'len, hApc, ?_, hh2⟩
    show evmIsZeroPostS sp rf ws A rf' ws' A
    simp only [evmIsZeroPostS, ← ha0, ← ha1, ← ha2, ← ha3, ← horAll, ← hresult]
    exact ⟨g12, g10, g7, g6, hws', trivial⟩

/-- The packaged ISZERO dispatch handle. -/
def evmIsZeroHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_iszero 1
  nSteps := 14
  region := Region.empty
  rw := ⟨sp, 32⟩
  pre := evmIsZeroPre sp
  post := evmIsZeroPostS sp
  sound := evmIsZeroHandle_sound base sp

-- ============================================================================
-- NOT (0x19)
-- ============================================================================

/-- Call-site obligation of the NOT handler (§3 uniform pre). -/
def evmNotPre (sp : Word) : Reach :=
  fun rf _ _ => rf.get .x12 = sp

/-- Snapshot-parameterized guarantee of the NOT handler: the top word is
    replaced by its bitwise complement (`^^^ (-1)` per limb); the stack
    pointer is UNCHANGED (unary), the code pointer advances one byte. -/
def evmNotPostS (sp : Word) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    let c := signExtend12 (-1 : BitVec 12)
    let a0 := wsDword ws₀ 0
    let a1 := wsDword ws₀ 8
    let a2 := wsDword ws₀ 16
    let a3 := wsDword ws₀ 24
    rf.get .x12 = sp
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x7 = a3 ^^^ c
    ∧ ws = dwordBytes (a0 ^^^ c) ++ dwordBytes (a1 ^^^ c)
        ++ dwordBytes (a2 ^^^ c) ++ dwordBytes (a3 ^^^ c)
    ∧ A = A₀

attribute [irreducible] evmNotPostS

/-- The NOT handler satisfies the `FnHandleS` calling contract. -/
theorem evmNotHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 32 → A₀.pcFree → evmNotPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 14 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_not 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 32⟩
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 32⟩
          (evmNotPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty ⟨sp, 32⟩ (Reach.exact rf₀ ws₀ A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  have h_spec := evmNotHandlerSpec sp base
    (wsDword ws 0) (wsDword ws 8) (wsDword ws 16) (wsDword ws 24)
    (rf.get .x7) (rf.get .x10) ret
  rw [halign] at h_spec
  -- frame the untouched registers (x6, x5, x11) + ambient A
  have h_framed := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ rf.get .x6) ** ((.x5 : Reg) ↦ᵣ rf.get .x5) **
      ((.x11 : Reg) ↦ᵣ rf.get .x11) ** regFileOn evmBinRest rf ** A)
    (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (by pcFree)
        (pcFree_sepConj (pcFree_regFileOn _ _) hApc)))) h_spec
  refine cpsTripleWithin_weaken ?_ ?_ h_framed
  · intro hp hh
    rw [show bytesRegion Region.empty.base Region.empty.bytes = empAssertion
          from rfl,
      sepConj_emp_left', bytesRegion_eq_4cells sp ws hlen,
      regFileIs_split_bin rf, hpre] at hh
    xperm_hyp hh
  · intro hp hh
    set c := signExtend12 (-1 : BitVec 12) with hc
    set a0 := wsDword ws 0 with ha0
    set a1 := wsDword ws 8 with ha1
    set a2 := wsDword ws 16 with ha2
    set a3 := wsDword ws 24 with ha3
    set rf' : RegFile := fun r =>
      if r = .x12 then sp
      else if r = .x7 then a3 ^^^ c
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    set ws' : List (BitVec 8) :=
      dwordBytes (a0 ^^^ c) ++ dwordBytes (a1 ^^^ c)
        ++ dwordBytes (a2 ^^^ c) ++ dwordBytes (a3 ^^^ c) with hws'
    have hws'len : ws'.length = 32 := by
      simp only [hws', List.length_append, length_dwordBytes]
    have g12 : rf'.get .x12 = sp := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = a3 ^^^ c := by rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = rf.get .x6 := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = rf.get .x5 := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = rf.get .x11 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    have hR : ws' = dwordBytes (a0 ^^^ c) ++ (dwordBytes (a1 ^^^ c) ++
        (dwordBytes (a2 ^^^ c) ++ dwordBytes (a3 ^^^ c))) := by
      rw [hws']; simp only [List.append_assoc]
    have h8 : (dwordBytes (a0 ^^^ c)).length = 8 := length_dwordBytes _
    have h8' : (dwordBytes (a1 ^^^ c)).length = 8 := length_dwordBytes _
    have h8'' : (dwordBytes (a2 ^^^ c)).length = 8 := length_dwordBytes _
    have hw0 : wsDword ws' 0 = a0 ^^^ c := by rw [hR]; exact wsDword_head _ _
    have hw8 : wsDword ws' 8 = a1 ^^^ c := by
      rw [hR, wsDword_peel (dwordBytes (a0 ^^^ c)) _ _ 8 h8 (by omega)]
      exact wsDword_head _ _
    have hw16 : wsDword ws' 16 = a2 ^^^ c := by
      rw [hR, wsDword_peel (dwordBytes (a0 ^^^ c)) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (a1 ^^^ c)) _ _ 8 h8' (by omega)]
      exact wsDword_head _ _
    have hw24 : wsDword ws' 24 = a3 ^^^ c := by
      rw [hR, wsDword_peel (dwordBytes (a0 ^^^ c)) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (a1 ^^^ c)) _ _ 8 h8' (by omega),
        wsDword_peel (dwordBytes (a2 ^^^ c)) _ _ 8 h8'' (by omega),
        ← List.append_nil (dwordBytes (a3 ^^^ c))]
      exact wsDword_head _ _
    have hx : (((.x1 : Reg) ↦ᵣ ret) **
        ((regFileIs rf' ** bytesRegion sp ws') ** A)) hp := by
      rw [regFileIs_split_bin rf', bytesRegion_eq_4cells sp ws' hws'len,
        g12, g7, g6, g10, g5, g11, grest, hw0, hw8, hw16, hw24]
      xperm_hyp hh
    refine sepConj_mono_right (fun h2 hh2 => ?_) hp hx
    rw [show asrtM Region.empty ⟨sp, 32⟩ (evmNotPostS sp rf ws A)
          = asrtOf ⟨sp, 32⟩ (evmNotPostS sp rf ws A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', ws', A, hws'len, hApc, ?_, hh2⟩
    show evmNotPostS sp rf ws A rf' ws' A
    simp only [evmNotPostS, ← hc, ← ha0, ← ha1, ← ha2, ← ha3]
    exact ⟨g12, g10, g7, hws', trivial⟩

/-- The packaged NOT dispatch handle. -/
def evmNotHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_not 1
  nSteps := 14
  region := Region.empty
  rw := ⟨sp, 32⟩
  pre := evmNotPre sp
  post := evmNotPostS sp
  sound := evmNotHandle_sound base sp

-- ============================================================================
-- POP (0x50)
-- ============================================================================

/-- Call-site obligation of the POP handler (§3 uniform pre). -/
def evmPopPre (sp : Word) : Reach :=
  fun rf _ _ => rf.get .x12 = sp

/-- Snapshot-parameterized guarantee of the POP handler: the stack pointer
    moves up one word (`+32`) and the code pointer advances one byte; no
    stack bytes are touched. -/
def evmPopPostS (sp : Word) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    rf.get .x12 = sp + 32
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ ws = ws₀
    ∧ A = A₀

attribute [irreducible] evmPopPostS

/-- The POP handler satisfies the `FnHandleS` calling contract. -/
theorem evmPopHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 0 → A₀.pcFree → evmPopPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 3 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_pop 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty RwRegion.empty
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty RwRegion.empty
          (evmPopPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  obtain rfl : ws₀ = [] := List.eq_nil_of_length_eq_zero hlen
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty RwRegion.empty (Reach.exact rf₀ [] A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  have h_spec := evmPopHandlerSpec sp base (rf.get .x10) ret
  rw [halign] at h_spec
  -- frame the untouched registers (x7, x6, x5, x11) + ambient A
  have h_framed := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ rf.get .x7) ** ((.x6 : Reg) ↦ᵣ rf.get .x6) **
      ((.x5 : Reg) ↦ᵣ rf.get .x5) ** ((.x11 : Reg) ↦ᵣ rf.get .x11) **
      regFileOn evmBinRest rf ** A)
    (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree)
        (pcFree_sepConj (pcFree_regFileOn _ _) hApc))))) h_spec
  refine cpsTripleWithin_weaken ?_ ?_ h_framed
  · intro hp hh
    rw [show bytesRegion Region.empty.base Region.empty.bytes = empAssertion
          from rfl,
      show bytesRegion RwRegion.empty.base [] = empAssertion from rfl,
      sepConj_emp_left', sepConj_emp_right', regFileIs_split_bin rf, hpre] at hh
    xperm_hyp hh
  · intro hp hh
    set rf' : RegFile := fun r =>
      if r = .x12 then sp + 32
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    have g12 : rf'.get .x12 = sp + 32 := by rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = rf.get .x7 := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = rf.get .x6 := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = rf.get .x5 := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = rf.get .x11 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    have hx : (((.x1 : Reg) ↦ᵣ ret) **
        ((regFileIs rf' ** bytesRegion RwRegion.empty.base []) ** A)) hp := by
      rw [show bytesRegion RwRegion.empty.base [] = empAssertion from rfl,
        sepConj_emp_right', regFileIs_split_bin rf',
        g12, g7, g6, g10, g5, g11, grest]
      xperm_hyp hh
    refine sepConj_mono_right (fun h2 hh2 => ?_) hp hx
    rw [show asrtM Region.empty RwRegion.empty (evmPopPostS sp rf [] A)
          = asrtOf RwRegion.empty (evmPopPostS sp rf [] A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', [], A, rfl, hApc, ?_, hh2⟩
    show evmPopPostS sp rf [] A rf' [] A
    simp only [evmPopPostS]
    exact ⟨g12, g10, trivial, trivial⟩

/-- The packaged POP dispatch handle. -/
def evmPopHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_pop 1
  nSteps := 3
  region := Region.empty
  rw := RwRegion.empty
  pre := evmPopPre sp
  post := evmPopPostS sp
  sound := evmPopHandle_sound base sp

end EvmAsm.Codegen.Proofs
