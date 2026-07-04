/-
  EvmAsm.Codegen.Proofs.HandlerHandles

  Bead evm-asm-4ch8f.10.1 — package the verified clean-ret handler specs
  (`Codegen/Proofs/HandlerSpecs.lean`) as snapshot-parameterized dispatch
  handles (`FnHandleS`, `docs/4ch8f-interp-strategy.md` §3), consumed by the
  interpreter dispatch loop (`.callRegS`, bead `.49`).

  Design (see the strategy doc §3 and the pilot `Rv64/SAsm/InterpLoopDemo`):

  * Each handle is verified against a MINIMAL value-stack window
    `rw := ⟨sp, 64⟩` — exactly the two 256-bit operand words at fixed byte
    offsets `0..56`, no junk framing.  `sp` is a `def` parameter (fully
    base-parameterized: no `GuestAddrs` pins).  The dispatch-loop bead
    (`.49`/`.56a`) embeds this window into the full arena via the existing
    `FnHandle.widenRw` (`SAsm/HandleWiden.lean`).
  * The `pre` is the §3 uniform shape: the value-stack window pointer
    (`x12 = sp`); the operand-count guard is discharged by the 64-byte
    window itself.
  * The `postS rf₀ ws₀ A₀` pins the exit registers/window as FUNCTIONS of
    the entry snapshot (no ∃-state escapes) — the auxiliary-variable
    contract a monomorphic `FnHandle.post` cannot express (§0).

  The proof reuses the existing HandlerSpecs `cpsTripleWithin` verbatim (the
  arithmetic is NOT re-derived).  The adapter is the raw-triple → `FnHandleS`
  bridge: split the window `bytesRegion` into the handler's `↦ₘ` operand
  cells (`bytesRegion_eq_cons`), peel the touched registers off `regFileIs`
  (`regFileIs_eq_atoms`), frame the untouched remainder, apply the
  HandlerSpecs triple, and re-fold.  It mirrors the documented template
  `Rv64/SAsm/ExamplesVc.handAdd_sound`.
-/

import EvmAsm.Codegen.Proofs.HandlerSpecs
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.SAsm.HandleWiden
import EvmAsm.Rv64.SAsm.AssertionSpec
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

-- ============================================================================
-- Window reads and the 8-dword split (reusable across the binary family)
-- ============================================================================

/-- The window dword at byte offset `k` (what an in-window aligned `LD`
    reads); mirrors `InterpLoopDemo.wsDword`. -/
def wsDword (ws : List (BitVec 8)) (k : Nat) : Word :=
  packBytes ((ws.drop k).take 8)

/-- A 64-byte value-stack window is the separating conjunction of its eight
    dword cells, valued by `wsDword` — the bridge from the window
    `bytesRegion` to the handler specs' `↦ₘ` operand cells. -/
theorem bytesRegion_eq_8cells (sp : Word) (ws : List (BitVec 8))
    (h : ws.length = 64) :
    bytesRegion sp ws
      = ((sp ↦ₘ wsDword ws 0) ** ((sp + 8) ↦ₘ wsDword ws 8) **
         ((sp + 16) ↦ₘ wsDword ws 16) ** ((sp + 24) ↦ₘ wsDword ws 24) **
         ((sp + 32) ↦ₘ wsDword ws 32) ** ((sp + 40) ↦ₘ wsDword ws 40) **
         ((sp + 48) ↦ₘ wsDword ws 48) ** ((sp + 56) ↦ₘ wsDword ws 56)) := by
  have hnn : ∀ k : Nat, k ≤ 56 → ws.drop k ≠ [] := by
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
  rw [bytesRegion_eq_cons (sp + 8 + 8 + 8 + 8) ((((ws.drop 8).drop 8).drop 8).drop 8)
    (by simpa [List.drop_drop] using hnn 32 (by omega))]
  rw [bytesRegion_eq_cons (sp + 8 + 8 + 8 + 8 + 8)
    (((((ws.drop 8).drop 8).drop 8).drop 8).drop 8)
    (by simpa [List.drop_drop] using hnn 40 (by omega))]
  rw [bytesRegion_eq_cons (sp + 8 + 8 + 8 + 8 + 8 + 8)
    ((((((ws.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8)
    (by simpa [List.drop_drop] using hnn 48 (by omega))]
  rw [bytesRegion_eq_cons (sp + 8 + 8 + 8 + 8 + 8 + 8 + 8)
    (((((((ws.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8)
    (by simpa [List.drop_drop] using hnn 56 (by omega))]
  rw [show (((((((ws.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8
        = [] from by
      rw [List.drop_eq_nil_iff]; simp only [List.length_drop, h]; omega,
    bytesRegion_nil, sepConj_emp_right']
  simp only [List.drop_drop]
  rw [show sp + 8 + 8 = sp + 16 from by bv_omega,
    show sp + 16 + 8 = sp + 24 from by bv_omega,
    show sp + 24 + 8 = sp + 32 from by bv_omega,
    show sp + 32 + 8 = sp + 40 from by bv_omega,
    show sp + 40 + 8 = sp + 48 from by bv_omega,
    show sp + 48 + 8 = sp + 56 from by bv_omega]
  simp only [wsDword, Nat.reduceAdd, List.drop_zero]

/-- A window read of a low dword (offset `< 32`) of the popped exit window
    equals the same read of the entry window (the top word is untouched). -/
theorem wsDword_lo (ws suf : List (BitVec 8)) (k : Nat)
    (hk : k + 8 ≤ 32) (hws : 32 ≤ ws.length) :
    wsDword (ws.take 32 ++ suf) k = wsDword ws k := by
  simp only [wsDword]
  congr 1
  rw [List.drop_append_of_le_length (by rw [List.length_take]; omega),
    List.take_append_of_le_length (by rw [List.length_drop, List.length_take]; omega),
    List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- Peel a known-length prefix off a window read. -/
theorem wsDword_peel (pre X : List (BitVec 8)) (m n : Nat)
    (hn : pre.length = n) (hnm : n ≤ m) :
    wsDword (pre ++ X) m = wsDword X (m - n) := by
  subst hn
  simp only [wsDword]
  rw [List.drop_append, List.drop_eq_nil_of_le hnm, List.nil_append]

/-- A window read at the base of a spliced dword recovers that dword. -/
theorem wsDword_head (v : Word) (suf : List (BitVec 8)) :
    wsDword (dwordBytes v ++ suf) 0 = v := by
  simp only [wsDword, List.drop_zero]
  rw [List.take_append_of_le_length (le_of_eq (length_dwordBytes v).symm),
    List.take_of_length_le (le_of_eq (length_dwordBytes v)), packBytes_dwordBytes]

/-- The exposed registers the binary arithmetic/logic handlers do NOT touch
    (everything outside `x5,x6,x7,x10,x11,x12`); framed across the call. -/
def evmBinRest : List Reg :=
  [.x28, .x29, .x30, .x31, .x13, .x14, .x15, .x16, .x17]

/-- Peel the six registers a binary handler touches off the register-file
    atom, leaving the untouched remainder as one `regFileOn` atom. -/
theorem regFileIs_split_bin (rf : RegFile) :
    regFileIs rf
      = (((.x12 : Reg) ↦ᵣ rf.get .x12) ** ((.x7 : Reg) ↦ᵣ rf.get .x7) **
         ((.x6 : Reg) ↦ᵣ rf.get .x6) ** ((.x5 : Reg) ↦ᵣ rf.get .x5) **
         ((.x11 : Reg) ↦ᵣ rf.get .x11) ** ((.x10 : Reg) ↦ᵣ rf.get .x10) **
         regFileOn evmBinRest rf) := by
  rw [regFileIs_eq_regFileOn,
    regFileOn_perm exposedRegs
      (.x12 :: .x7 :: .x6 :: .x5 :: .x11 :: .x10 :: evmBinRest) rf
      (by intro r; cases r <;> simp [exposedRegs, evmBinRest]),
    regFileOn_cons _ _ _ (by decide), regFileOn_cons _ _ _ (by decide),
    regFileOn_cons _ _ _ (by decide), regFileOn_cons _ _ _ (by decide),
    regFileOn_cons _ _ _ (by decide), regFileOn_cons _ _ _ (by decide)]

-- ============================================================================
-- ADD (0x01)
-- ============================================================================

/-- Call-site obligation of the ADD handler (§3 uniform pre): the value-stack
    top pointer is the window base. -/
def evmAddPre (sp : Word) : Reach :=
  fun rf _ _ => rf.get .x12 = sp

/-- Snapshot-parameterized guarantee of the ADD handler: the exit registers
    and window as functions of the entry snapshot.  The top two 256-bit words
    are replaced by their sum, the stack pointer moves up one word (`+32`),
    and the EVM code pointer advances one byte. -/
def evmAddPostS (sp : Word) :
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
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    rf.get .x12 = sp + 32
    ∧ rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x7 = result3
    ∧ rf.get .x6 = carry3b
    ∧ rf.get .x5 = carry3
    ∧ rf.get .x11 = carry3a
    ∧ ws = ws₀.take 32 ++ dwordBytes sum0 ++ dwordBytes result1
        ++ dwordBytes result2 ++ dwordBytes result3
    ∧ A = A₀

/- Keep the 25-`let` carry chain from being unfolded during the big
   `isDefEq`/`xperm_hyp` steps of the soundness proof (it rides along as a
   subterm of the pre/post `asrtM`); it is unfolded explicitly only where the
   proof needs it (`simp only [evmAddPostS, …]` via the equation lemma). -/
attribute [irreducible] evmAddPostS

/-- The ADD handler satisfies the `FnHandleS` calling contract at any code
    base `base` and window base `sp`. -/
theorem evmAddHandle_sound (base sp : Word) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = 64 → A₀.pcFree → evmAddPre sp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 32 base ret
        (cleanRetHandlerCode base EvmAsm.Evm64.evm_add 1)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty ⟨sp, 64⟩
          (evmAddPostS sp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret)
    (asrtM Region.empty ⟨sp, 64⟩ (Reach.exact rf₀ ws₀ A₀))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen' hApc' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := hpre'
  -- The existing HandlerSpecs triple, instantiated at the window's operand
  -- dwords and the snapshot's scratch registers.
  have h_spec := evmAddHandlerSpec sp base
    (wsDword ws 0) (wsDword ws 8) (wsDword ws 16) (wsDword ws 24)
    (wsDword ws 32) (wsDword ws 40) (wsDword ws 48) (wsDword ws 56)
    (rf.get .x7) (rf.get .x6) (rf.get .x5) (rf.get .x11) (rf.get .x10) ret
  rw [halign] at h_spec
  -- Frame the untouched registers and the ambient assertion.
  have h_framed := cpsTripleWithin_frameR (regFileOn evmBinRest rf ** A)
    (pcFree_sepConj (pcFree_regFileOn _ _) hApc) h_spec
  refine cpsTripleWithin_weaken ?_ ?_ h_framed
  · -- pre: the concrete window/register pre entails the handler-spec pre
    intro hp hh
    rw [show bytesRegion Region.empty.base Region.empty.bytes = empAssertion
          from rfl,
      sepConj_emp_left', bytesRegion_eq_8cells sp ws hlen,
      regFileIs_split_bin rf, hpre] at hh
    xperm_hyp hh
  · -- post: the handler-spec exit atoms package into the snapshot post
    intro hp hh
    -- name the ADD carry chain so `hh`'s expressions become tractable
    set a0 := wsDword ws 0 with ha0
    set a1 := wsDword ws 8 with ha1
    set a2 := wsDword ws 16 with ha2
    set a3 := wsDword ws 24 with ha3
    set b0 := wsDword ws 32 with hb0
    set b1 := wsDword ws 40 with hb1
    set b2 := wsDword ws 48 with hb2
    set b3 := wsDword ws 56 with hb3
    set sum0 := a0 + b0 with hsum0
    set carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0 with hcarry0
    set psum1 := a1 + b1 with hpsum1
    set carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0 with hcarry1a
    set result1 := psum1 + carry0 with hresult1
    set carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0 with hcarry1b
    set carry1 := carry1a ||| carry1b with hcarry1
    set psum2 := a2 + b2 with hpsum2
    set carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0 with hcarry2a
    set result2 := psum2 + carry1 with hresult2
    set carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0 with hcarry2b
    set carry2 := carry2a ||| carry2b with hcarry2
    set psum3 := a3 + b3 with hpsum3
    set carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0 with hcarry3a
    set result3 := psum3 + carry2 with hresult3
    set carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0 with hcarry3b
    set carry3 := carry3a ||| carry3b with hcarry3
    -- the exit register file and window (functions of the snapshot)
    set rf' : RegFile := fun r =>
      if r = .x12 then sp + 32
      else if r = .x7 then result3
      else if r = .x6 then carry3b
      else if r = .x5 then carry3
      else if r = .x11 then carry3a
      else if r = .x10 then rf.get .x10 + 1
      else rf r with hrf'
    set ws' : List (BitVec 8) :=
      ws.take 32 ++ dwordBytes sum0 ++ dwordBytes result1
        ++ dwordBytes result2 ++ dwordBytes result3 with hws'
    have hws'len : ws'.length = 64 := by
      simp only [hws', List.length_append, length_dwordBytes, List.length_take]
      omega
    have g12 : rf'.get .x12 = sp + 32 := by rw [hrf']; rfl
    have g7 : rf'.get .x7 = result3 := by rw [hrf']; rfl
    have g6 : rf'.get .x6 = carry3b := by rw [hrf']; rfl
    have g5 : rf'.get .x5 = carry3 := by rw [hrf']; rfl
    have g11 : rf'.get .x11 = carry3a := by rw [hrf']; rfl
    have g10 : rf'.get .x10 = rf.get .x10 + 1 := by rw [hrf']; rfl
    have grest : regFileOn evmBinRest rf' = regFileOn evmBinRest rf :=
      regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> (rw [hrf']; rfl))
    -- window reads of the exit window, right-nested for prefix peeling
    have hR : ws' = ws.take 32 ++ (dwordBytes sum0 ++ (dwordBytes result1 ++
        (dwordBytes result2 ++ dwordBytes result3))) := by
      rw [hws']; simp only [List.append_assoc]
    have h8 : (dwordBytes sum0).length = 8 := length_dwordBytes _
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
    have hw32 : wsDword ws' 32 = sum0 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega)]
      exact wsDword_head _ _
    have hw40 : wsDword ws' 40 = result1 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes sum0) _ _ 8 h8 (by omega)]
      exact wsDword_head _ _
    have hw48 : wsDword ws' 48 = result2 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes sum0) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes result1) _ _ 8 h8' (by omega)]
      exact wsDword_head _ _
    have hw56 : wsDword ws' 56 = result3 := by
      rw [hR, wsDword_peel (ws.take 32) _ _ 32 ht (by omega),
        wsDword_peel (dwordBytes sum0) _ _ 8 h8 (by omega),
        wsDword_peel (dwordBytes result1) _ _ 8 h8' (by omega),
        wsDword_peel (dwordBytes result2) _ _ 8 h8'' (by omega),
        ← List.append_nil (dwordBytes result3)]
      exact wsDword_head _ _
    -- the exit heap, in all-atoms form, matches `hh` by permutation
    have hx : (((.x1 : Reg) ↦ᵣ ret) **
        ((regFileIs rf' ** bytesRegion sp ws') ** A)) hp := by
      rw [regFileIs_split_bin rf', bytesRegion_eq_8cells sp ws' hws'len,
        g12, g7, g6, g5, g11, g10, grest, hw0, hw8, hw16, hw24, hw32, hw40,
        hw48, hw56]
      xperm_hyp hh
    -- package into `asrtM`/`asrtOf` with the snapshot post
    refine sepConj_mono_right (fun h2 hh2 => ?_) hp hx
    rw [show asrtM Region.empty ⟨sp, 64⟩ (evmAddPostS sp rf ws A)
          = asrtOf ⟨sp, 64⟩ (evmAddPostS sp rf ws A) from by
        rw [asrtM, show bytesRegion Region.empty.base Region.empty.bytes
          = empAssertion from rfl, sepConj_emp_right']]
    refine ⟨rf', ws', A, hws'len, hApc, ?_, hh2⟩
    show evmAddPostS sp rf ws A rf' ws' A
    simp only [evmAddPostS, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2,
      ← hb3, ← hsum0, ← hcarry0, ← hpsum1, ← hcarry1a, ← hresult1, ← hcarry1b,
      ← hcarry1, ← hpsum2, ← hcarry2a, ← hresult2, ← hcarry2b, ← hcarry2,
      ← hpsum3, ← hcarry3a, ← hresult3, ← hcarry3b, ← hcarry3]
    exact ⟨g12, g10, g7, g6, g5, g11, hws', trivial⟩

/-- The packaged ADD dispatch handle. -/
def evmAddHandle (base sp : Word) : FnHandleS where
  entry := base
  code := cleanRetHandlerCode base EvmAsm.Evm64.evm_add 1
  nSteps := 32
  region := Region.empty
  rw := ⟨sp, 64⟩
  pre := evmAddPre sp
  post := evmAddPostS sp
  sound := evmAddHandle_sound base sp

end EvmAsm.Codegen.Proofs
