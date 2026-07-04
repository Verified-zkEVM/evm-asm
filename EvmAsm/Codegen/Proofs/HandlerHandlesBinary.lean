/-
  EvmAsm.Codegen.Proofs.HandlerHandlesBinary

  Bead evm-asm-4ch8f.10.1 — the binary clean-ret handler handles (SUB, LT,
  GT, SLT, SGT, EQ, AND, OR, XOR), packaged as snapshot-parameterized
  dispatch handles (`FnHandleS`, `docs/4ch8f-interp-strategy.md` §3).

  Every handler here is "binary, pop-one": an 8-dword value-stack window
  `rw := ⟨sp, 64⟩`, `x12 → sp + 32`, `x10 → +1`, the result 256-bit word
  written into dwords 4..7 (byte offsets 32..56) and the untouched a-word
  (dwords 0..3) left in place.  So the exit window is uniformly
  `ws₀.take 32 ++ dwordBytes r0 ++ dwordBytes r1 ++ dwordBytes r2 ++ dwordBytes r3`.

  The proof reuses the existing HandlerSpecs `cpsTripleWithin` verbatim (the
  arithmetic is NOT re-derived) and the reusable bridges from
  `HandlerHandles.lean` (`bytesRegion_eq_8cells`, `regFileIs_split_bin`,
  `evmBinRest`, `wsDword`, `wsDword_lo`/`_peel`/`_head`).  Each block mirrors
  the ADD template `evmAddHandle_sound` there.
-/

import EvmAsm.Codegen.Proofs.HandlerHandles

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

-- ============================================================================
-- SUB (0x03)
-- ============================================================================

/-- Snapshot-parameterized guarantee of the SUB handler. -/
def evmSubPostS (sp : Word) :
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
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let diff0 := a0 - b0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let result1 := temp1 - borrow0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let result2 := temp2 - borrow1
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let result3 := temp3 - borrow2
    let borrow3 := borrow3a ||| borrow3b
    rf.get .x12 = sp + 32
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x7 = result3
    ∧ rf.get .x6 = borrow3b
    ∧ rf.get .x5 = borrow3
    ∧ rf.get .x11 = borrow3a
    ∧ ws = ws₀.take 32 ++ dwordBytes diff0 ++ dwordBytes result1
        ++ dwordBytes result2 ++ dwordBytes result3
    ∧ A = A₀

attribute [irreducible] evmSubPostS

/-- The SUB handler satisfies the `FnHandleS` calling contract. -/
theorem evmSubHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 64 → A₀.pcFree → evmAddPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 32 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_sub 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (evmSubPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty ⟨sp, 64⟩ (Reach.exact rf₀ ws₀ A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  have h_spec := evmSubHandlerSpec sp base
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
    set borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0 with hborrow0
    set diff0 := a0 - b0 with hdiff0
    set borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0 with hborrow1a
    set temp1 := a1 - b1 with htemp1
    set borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0 with hborrow1b
    set result1 := temp1 - borrow0 with hresult1
    set borrow1 := borrow1a ||| borrow1b with hborrow1
    set borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0 with hborrow2a
    set temp2 := a2 - b2 with htemp2
    set borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0 with hborrow2b
    set result2 := temp2 - borrow1 with hresult2
    set borrow2 := borrow2a ||| borrow2b with hborrow2
    set borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0 with hborrow3a
    set temp3 := a3 - b3 with htemp3
    set borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0 with hborrow3b
    set result3 := temp3 - borrow2 with hresult3
    set borrow3 := borrow3a ||| borrow3b with hborrow3
    set rf' : RegFile := fun r =>
      if r = .x12 then sp + 32
      else if r = .x7 then result3
      else if r = .x6 then borrow3b
      else if r = .x5 then borrow3
      else if r = .x11 then borrow3a
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    set ws' : List (BitVec 8) :=
      ws.take 32 ++ dwordBytes diff0 ++ dwordBytes result1
        ++ dwordBytes result2 ++ dwordBytes result3 with hws'
    have hws'len : ws'.length = 64 := by
      simp only [hws', List.length_append, length_dwordBytes, List.length_take]
      omega
    have g12 : rf'.get .x12 = sp + 32 := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = result3 := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = borrow3b := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = borrow3 := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = borrow3a := by rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    have hR : ws' = ws.take 32 ++ (dwordBytes diff0 ++ (dwordBytes result1 ++
        (dwordBytes result2 ++ dwordBytes result3))) := by
      rw [hws']; simp only [List.append_assoc]
    have h8 : (dwordBytes diff0).length = 8 := length_dwordBytes _
    have h8' : (dwordBytes result1).length = 8 := length_dwordBytes _
    have h8'' : (dwordBytes result2).length = 8 := length_dwordBytes _
    have ht : (List.take 32 ws).length = 32 := by rw [List.length_take]; omega
    have hw0 : wsDword ws' 0 = a0 := by
      rw [ha0, hR]; exact wsDword_lo ws _ 0 (by omega) (by omega)
    have hw8 : wsDword ws' 8 = a1 := by
      rw [ha1, hR]; exact wsDword_lo ws _ 8 (by omega) (by omega)
    have hw16 : wsDword ws' 16 = a2 := by
      rw [ha2, hR]; exact wsDword_lo ws _ 16 (by omega) (by omega)
    have hw24 : wsDword ws' 24 = a3 := by
      rw [ha3, hR]; exact wsDword_lo ws _ 24 (by omega) (by omega)
    have hw32 : wsDword ws' 32 = diff0 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega)]
      exact wsDword_head _ _
    have hw40 : wsDword ws' 40 = result1 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes diff0) _ _ 8 h8 (by omega)]
      exact wsDword_head _ _
    have hw48 : wsDword ws' 48 = result2 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes diff0) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes result1) _ _ 8 h8' (by omega)]
      exact wsDword_head _ _
    have hw56 : wsDword ws' 56 = result3 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes diff0) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes result1) _ _ 8 h8' (by omega),
        wsDword_peel (dwordBytes result2) _ _ 8 h8'' (by omega),
        ← List.append_nil (dwordBytes result3)]
      exact wsDword_head _ _
    have hx : (((.x1 : Reg) ↦ᵣ ret) **
        ((regFileIs rf' ** bytesRegion sp ws') ** A)) hp := by
      rw [regFileIs_split_bin rf', bytesRegion_eq_8cells sp ws' hws'len,
        g12, g7, g6, g5, g11, g10, grest, hw0, hw8, hw16, hw24, hw32, hw40,
        hw48, hw56]
      xperm_hyp hh
    refine sepConj_mono_right (fun h2 hh2 => ?_) hp hx
    rw [show asrtM Region.empty ⟨sp, 64⟩ (evmSubPostS sp rf ws A)
          = asrtOf ⟨sp, 64⟩ (evmSubPostS sp rf ws A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', ws', A, hws'len, hApc, ?_, hh2⟩
    show evmSubPostS sp rf ws A rf' ws' A
    simp only [evmSubPostS, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2,
      ← hb3, ← hborrow0, ← hdiff0, ← hborrow1a, ← htemp1, ← hborrow1b,
      ← hresult1, ← hborrow1, ← hborrow2a, ← htemp2, ← hborrow2b, ← hresult2,
      ← hborrow2, ← hborrow3a, ← htemp3, ← hborrow3b, ← hresult3, ← hborrow3]
    exact ⟨g12, g10, g7, g6, g5, g11, hws', trivial⟩

/-- The packaged SUB dispatch handle. -/
def evmSubHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_sub 1
  nSteps := 32
  region := Region.empty
  rw := ⟨sp, 64⟩
  pre := evmAddPre sp
  post := evmSubPostS sp
  sound := evmSubHandle_sound base sp

-- ============================================================================
-- LT (0x10)
-- ============================================================================

/-- Snapshot-parameterized guarantee of the LT handler. -/
def evmLtPostS (sp : Word) :
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
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let borrow3 := borrow3a ||| borrow3b
    rf.get .x12 = sp + 32
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x7 = temp3
    ∧ rf.get .x6 = borrow3b
    ∧ rf.get .x5 = borrow3
    ∧ rf.get .x11 = borrow3a
    ∧ ws = ws₀.take 32 ++ dwordBytes borrow3 ++ dwordBytes 0
        ++ dwordBytes 0 ++ dwordBytes 0
    ∧ A = A₀

attribute [irreducible] evmLtPostS

/-- The LT handler satisfies the `FnHandleS` calling contract. -/
theorem evmLtHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 64 → A₀.pcFree → evmAddPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 28 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_lt 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (evmLtPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty ⟨sp, 64⟩ (Reach.exact rf₀ ws₀ A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  have h_spec := evmLtHandlerSpec sp base
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
    set borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0 with hborrow0
    set borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0 with hborrow1a
    set temp1 := a1 - b1 with htemp1
    set borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0 with hborrow1b
    set borrow1 := borrow1a ||| borrow1b with hborrow1
    set borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0 with hborrow2a
    set temp2 := a2 - b2 with htemp2
    set borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0 with hborrow2b
    set borrow2 := borrow2a ||| borrow2b with hborrow2
    set borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0 with hborrow3a
    set temp3 := a3 - b3 with htemp3
    set borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0 with hborrow3b
    set borrow3 := borrow3a ||| borrow3b with hborrow3
    set rf' : RegFile := fun r =>
      if r = .x12 then sp + 32
      else if r = .x7 then temp3
      else if r = .x6 then borrow3b
      else if r = .x5 then borrow3
      else if r = .x11 then borrow3a
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    set ws' : List (BitVec 8) :=
      ws.take 32 ++ dwordBytes borrow3 ++ dwordBytes 0
        ++ dwordBytes 0 ++ dwordBytes 0 with hws'
    have hws'len : ws'.length = 64 := by
      simp only [hws', List.length_append, length_dwordBytes, List.length_take]
      omega
    have g12 : rf'.get .x12 = sp + 32 := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = temp3 := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = borrow3b := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = borrow3 := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = borrow3a := by rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    have hR : ws' = ws.take 32 ++ (dwordBytes borrow3 ++ (dwordBytes 0 ++
        (dwordBytes 0 ++ dwordBytes 0))) := by
      rw [hws']; simp only [List.append_assoc]
    have h8 : (dwordBytes borrow3).length = 8 := length_dwordBytes _
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
    have hw32 : wsDword ws' 32 = borrow3 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega)]
      exact wsDword_head _ _
    have hw40 : wsDword ws' 40 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes borrow3) _ _ 8 h8 (by omega)]
      exact wsDword_head _ _
    have hw48 : wsDword ws' 48 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes borrow3) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (0 : Word)) _ _ 8 h8' (by omega)]
      exact wsDword_head _ _
    have hw56 : wsDword ws' 56 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes borrow3) _ _ 8 h8 (by omega),
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
    rw [show asrtM Region.empty ⟨sp, 64⟩ (evmLtPostS sp rf ws A)
          = asrtOf ⟨sp, 64⟩ (evmLtPostS sp rf ws A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', ws', A, hws'len, hApc, ?_, hh2⟩
    show evmLtPostS sp rf ws A rf' ws' A
    simp only [evmLtPostS, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2,
      ← hb3, ← hborrow0, ← hborrow1a, ← htemp1, ← hborrow1b, ← hborrow1,
      ← hborrow2a, ← htemp2, ← hborrow2b, ← hborrow2, ← hborrow3a, ← htemp3,
      ← hborrow3b, ← hborrow3]
    exact ⟨g12, g10, g7, g6, g5, g11, hws', trivial⟩

/-- The packaged LT dispatch handle. -/
def evmLtHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_lt 1
  nSteps := 28
  region := Region.empty
  rw := ⟨sp, 64⟩
  pre := evmAddPre sp
  post := evmLtPostS sp
  sound := evmLtHandle_sound base sp

-- ============================================================================
-- GT (0x11)  —  LT with operands swapped (b < a)
-- ============================================================================

/-- Snapshot-parameterized guarantee of the GT handler. -/
def evmGtPostS (sp : Word) :
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
    let borrow0 := if BitVec.ult b0 a0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult b1 a1 then (1 : Word) else 0
    let temp1 := b1 - a1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult b2 a2 then (1 : Word) else 0
    let temp2 := b2 - a2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult b3 a3 then (1 : Word) else 0
    let temp3 := b3 - a3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let borrow3 := borrow3a ||| borrow3b
    rf.get .x12 = sp + 32
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x7 = temp3
    ∧ rf.get .x6 = borrow3b
    ∧ rf.get .x5 = borrow3
    ∧ rf.get .x11 = borrow3a
    ∧ ws = ws₀.take 32 ++ dwordBytes borrow3 ++ dwordBytes 0
        ++ dwordBytes 0 ++ dwordBytes 0
    ∧ A = A₀

attribute [irreducible] evmGtPostS

/-- The GT handler satisfies the `FnHandleS` calling contract. -/
theorem evmGtHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 64 → A₀.pcFree → evmAddPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 28 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_gt 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (evmGtPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty ⟨sp, 64⟩ (Reach.exact rf₀ ws₀ A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  have h_spec := evmGtHandlerSpec sp base
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
    set borrow0 := if BitVec.ult b0 a0 then (1 : Word) else 0 with hborrow0
    set borrow1a := if BitVec.ult b1 a1 then (1 : Word) else 0 with hborrow1a
    set temp1 := b1 - a1 with htemp1
    set borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0 with hborrow1b
    set borrow1 := borrow1a ||| borrow1b with hborrow1
    set borrow2a := if BitVec.ult b2 a2 then (1 : Word) else 0 with hborrow2a
    set temp2 := b2 - a2 with htemp2
    set borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0 with hborrow2b
    set borrow2 := borrow2a ||| borrow2b with hborrow2
    set borrow3a := if BitVec.ult b3 a3 then (1 : Word) else 0 with hborrow3a
    set temp3 := b3 - a3 with htemp3
    set borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0 with hborrow3b
    set borrow3 := borrow3a ||| borrow3b with hborrow3
    set rf' : RegFile := fun r =>
      if r = .x12 then sp + 32
      else if r = .x7 then temp3
      else if r = .x6 then borrow3b
      else if r = .x5 then borrow3
      else if r = .x11 then borrow3a
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    set ws' : List (BitVec 8) :=
      ws.take 32 ++ dwordBytes borrow3 ++ dwordBytes 0
        ++ dwordBytes 0 ++ dwordBytes 0 with hws'
    have hws'len : ws'.length = 64 := by
      simp only [hws', List.length_append, length_dwordBytes, List.length_take]
      omega
    have g12 : rf'.get .x12 = sp + 32 := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = temp3 := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = borrow3b := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = borrow3 := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = borrow3a := by rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    have hR : ws' = ws.take 32 ++ (dwordBytes borrow3 ++ (dwordBytes 0 ++
        (dwordBytes 0 ++ dwordBytes 0))) := by
      rw [hws']; simp only [List.append_assoc]
    have h8 : (dwordBytes borrow3).length = 8 := length_dwordBytes _
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
    have hw32 : wsDword ws' 32 = borrow3 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega)]
      exact wsDword_head _ _
    have hw40 : wsDword ws' 40 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes borrow3) _ _ 8 h8 (by omega)]
      exact wsDword_head _ _
    have hw48 : wsDword ws' 48 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes borrow3) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (0 : Word)) _ _ 8 h8' (by omega)]
      exact wsDword_head _ _
    have hw56 : wsDword ws' 56 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes borrow3) _ _ 8 h8 (by omega),
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
    rw [show asrtM Region.empty ⟨sp, 64⟩ (evmGtPostS sp rf ws A)
          = asrtOf ⟨sp, 64⟩ (evmGtPostS sp rf ws A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', ws', A, hws'len, hApc, ?_, hh2⟩
    show evmGtPostS sp rf ws A rf' ws' A
    simp only [evmGtPostS, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2,
      ← hb3, ← hborrow0, ← hborrow1a, ← htemp1, ← hborrow1b, ← hborrow1,
      ← hborrow2a, ← htemp2, ← hborrow2b, ← hborrow2, ← hborrow3a, ← htemp3,
      ← hborrow3b, ← hborrow3]
    exact ⟨g12, g10, g7, g6, g5, g11, hws', trivial⟩

/-- The packaged GT dispatch handle. -/
def evmGtHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_gt 1
  nSteps := 28
  region := Region.empty
  rw := ⟨sp, 64⟩
  pre := evmAddPre sp
  post := evmGtPostS sp
  sound := evmGtHandle_sound base sp

-- ============================================================================
-- SLT (0x12)  —  signed less-than
-- ============================================================================

/-- Snapshot-parameterized guarantee of the SLT handler. -/
def evmSltPostS (sp : Word) :
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
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let sltMsb := if BitVec.slt a3 b3 then (1 : Word) else 0
    let result := if a3 = b3 then borrow2 else sltMsb
    rf.get .x12 = sp + 32
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x7 = (if a3 = b3 then temp2 else a3)
    ∧ rf.get .x6 = (if a3 = b3 then borrow2b else b3)
    ∧ rf.get .x5 = result
    ∧ rf.get .x11 = (if a3 = b3 then borrow2a else rf₀.get .x11)
    ∧ ws = ws₀.take 32 ++ dwordBytes result ++ dwordBytes 0
        ++ dwordBytes 0 ++ dwordBytes 0
    ∧ A = A₀

attribute [irreducible] evmSltPostS

/-- The SLT handler satisfies the `FnHandleS` calling contract. -/
theorem evmSltHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 64 → A₀.pcFree → evmAddPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 27 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_slt 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (evmSltPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty ⟨sp, 64⟩ (Reach.exact rf₀ ws₀ A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  have h_spec := evmSltHandlerSpec sp base
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
    set borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0 with hborrow0
    set borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0 with hborrow1a
    set temp1 := a1 - b1 with htemp1
    set borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0 with hborrow1b
    set borrow1 := borrow1a ||| borrow1b with hborrow1
    set borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0 with hborrow2a
    set temp2 := a2 - b2 with htemp2
    set borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0 with hborrow2b
    set borrow2 := borrow2a ||| borrow2b with hborrow2
    set sltMsb := if BitVec.slt a3 b3 then (1 : Word) else 0 with hsltMsb
    set result := if a3 = b3 then borrow2 else sltMsb with hresult
    set rf' : RegFile := fun r =>
      if r = .x12 then sp + 32
      else if r = .x7 then (if a3 = b3 then temp2 else a3)
      else if r = .x6 then (if a3 = b3 then borrow2b else b3)
      else if r = .x5 then result
      else if r = .x11 then (if a3 = b3 then borrow2a else rf.get .x11)
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    set ws' : List (BitVec 8) :=
      ws.take 32 ++ dwordBytes result ++ dwordBytes 0
        ++ dwordBytes 0 ++ dwordBytes 0 with hws'
    have hws'len : ws'.length = 64 := by
      simp only [hws', List.length_append, length_dwordBytes, List.length_take]
      omega
    have g12 : rf'.get .x12 = sp + 32 := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = (if a3 = b3 then temp2 else a3) := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = (if a3 = b3 then borrow2b else b3) := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = result := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = (if a3 = b3 then borrow2a else rf.get .x11) := by
      rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    have hR : ws' = ws.take 32 ++ (dwordBytes result ++ (dwordBytes 0 ++
        (dwordBytes 0 ++ dwordBytes 0))) := by
      rw [hws']; simp only [List.append_assoc]
    have h8 : (dwordBytes result).length = 8 := length_dwordBytes _
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
    have hw32 : wsDword ws' 32 = result := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega)]
      exact wsDword_head _ _
    have hw40 : wsDword ws' 40 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes result) _ _ 8 h8 (by omega)]
      exact wsDword_head _ _
    have hw48 : wsDword ws' 48 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes result) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (0 : Word)) _ _ 8 h8' (by omega)]
      exact wsDword_head _ _
    have hw56 : wsDword ws' 56 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes result) _ _ 8 h8 (by omega),
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
    rw [show asrtM Region.empty ⟨sp, 64⟩ (evmSltPostS sp rf ws A)
          = asrtOf ⟨sp, 64⟩ (evmSltPostS sp rf ws A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', ws', A, hws'len, hApc, ?_, hh2⟩
    show evmSltPostS sp rf ws A rf' ws' A
    simp only [evmSltPostS, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2,
      ← hb3, ← hborrow0, ← hborrow1a, ← htemp1, ← hborrow1b, ← hborrow1,
      ← hborrow2a, ← htemp2, ← hborrow2b, ← hborrow2, ← hsltMsb, ← hresult]
    exact ⟨g12, g10, g7, g6, g5, g11, hws', trivial⟩

/-- The packaged SLT dispatch handle. -/
def evmSltHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_slt 1
  nSteps := 27
  region := Region.empty
  rw := ⟨sp, 64⟩
  pre := evmAddPre sp
  post := evmSltPostS sp
  sound := evmSltHandle_sound base sp

-- ============================================================================
-- SGT (0x13)  —  signed greater-than (SLT with operands swapped)
-- ============================================================================

/-- Snapshot-parameterized guarantee of the SGT handler. -/
def evmSgtPostS (sp : Word) :
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
    let borrow0 := if BitVec.ult b0 a0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult b1 a1 then (1 : Word) else 0
    let temp1 := b1 - a1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult b2 a2 then (1 : Word) else 0
    let temp2 := b2 - a2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let sgtMsb := if BitVec.slt b3 a3 then (1 : Word) else 0
    let result := if b3 = a3 then borrow2 else sgtMsb
    rf.get .x12 = sp + 32
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x7 = (if b3 = a3 then temp2 else b3)
    ∧ rf.get .x6 = (if b3 = a3 then borrow2b else a3)
    ∧ rf.get .x5 = result
    ∧ rf.get .x11 = (if b3 = a3 then borrow2a else rf₀.get .x11)
    ∧ ws = ws₀.take 32 ++ dwordBytes result ++ dwordBytes 0
        ++ dwordBytes 0 ++ dwordBytes 0
    ∧ A = A₀

attribute [irreducible] evmSgtPostS

/-- The SGT handler satisfies the `FnHandleS` calling contract. -/
theorem evmSgtHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 64 → A₀.pcFree → evmAddPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 27 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_sgt 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (evmSgtPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty ⟨sp, 64⟩ (Reach.exact rf₀ ws₀ A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  have h_spec := evmSgtHandlerSpec sp base
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
    set borrow0 := if BitVec.ult b0 a0 then (1 : Word) else 0 with hborrow0
    set borrow1a := if BitVec.ult b1 a1 then (1 : Word) else 0 with hborrow1a
    set temp1 := b1 - a1 with htemp1
    set borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0 with hborrow1b
    set borrow1 := borrow1a ||| borrow1b with hborrow1
    set borrow2a := if BitVec.ult b2 a2 then (1 : Word) else 0 with hborrow2a
    set temp2 := b2 - a2 with htemp2
    set borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0 with hborrow2b
    set borrow2 := borrow2a ||| borrow2b with hborrow2
    set sgtMsb := if BitVec.slt b3 a3 then (1 : Word) else 0 with hsgtMsb
    set result := if b3 = a3 then borrow2 else sgtMsb with hresult
    set rf' : RegFile := fun r =>
      if r = .x12 then sp + 32
      else if r = .x7 then (if b3 = a3 then temp2 else b3)
      else if r = .x6 then (if b3 = a3 then borrow2b else a3)
      else if r = .x5 then result
      else if r = .x11 then (if b3 = a3 then borrow2a else rf.get .x11)
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    set ws' : List (BitVec 8) :=
      ws.take 32 ++ dwordBytes result ++ dwordBytes 0
        ++ dwordBytes 0 ++ dwordBytes 0 with hws'
    have hws'len : ws'.length = 64 := by
      simp only [hws', List.length_append, length_dwordBytes, List.length_take]
      omega
    have g12 : rf'.get .x12 = sp + 32 := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = (if b3 = a3 then temp2 else b3) := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = (if b3 = a3 then borrow2b else a3) := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = result := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = (if b3 = a3 then borrow2a else rf.get .x11) := by
      rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    have hR : ws' = ws.take 32 ++ (dwordBytes result ++ (dwordBytes 0 ++
        (dwordBytes 0 ++ dwordBytes 0))) := by
      rw [hws']; simp only [List.append_assoc]
    have h8 : (dwordBytes result).length = 8 := length_dwordBytes _
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
    have hw32 : wsDword ws' 32 = result := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega)]
      exact wsDword_head _ _
    have hw40 : wsDword ws' 40 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes result) _ _ 8 h8 (by omega)]
      exact wsDword_head _ _
    have hw48 : wsDword ws' 48 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes result) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes (0 : Word)) _ _ 8 h8' (by omega)]
      exact wsDword_head _ _
    have hw56 : wsDword ws' 56 = (0 : Word) := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes result) _ _ 8 h8 (by omega),
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
    rw [show asrtM Region.empty ⟨sp, 64⟩ (evmSgtPostS sp rf ws A)
          = asrtOf ⟨sp, 64⟩ (evmSgtPostS sp rf ws A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', ws', A, hws'len, hApc, ?_, hh2⟩
    show evmSgtPostS sp rf ws A rf' ws' A
    simp only [evmSgtPostS, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2,
      ← hb3, ← hborrow0, ← hborrow1a, ← htemp1, ← hborrow1b, ← hborrow1,
      ← hborrow2a, ← htemp2, ← hborrow2b, ← hborrow2, ← hsgtMsb, ← hresult]
    exact ⟨g12, g10, g7, g6, g5, g11, hws', trivial⟩

/-- The packaged SGT dispatch handle. -/
def evmSgtHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_sgt 1
  nSteps := 27
  region := Region.empty
  rw := ⟨sp, 64⟩
  pre := evmAddPre sp
  post := evmSgtPostS sp
  sound := evmSgtHandle_sound base sp

end EvmAsm.Codegen.Proofs
