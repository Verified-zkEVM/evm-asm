/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledBody

  #12183 — body compose enable=1 empty-miss (partial).

  Composes the enable path from body entry through nested indexed call
  entry (wlhB+36 → wlhB+164). Call→epi and abiFrame wrap follow.

  Nested stack: ambient carries `stackFree newSp 8` below parent frame.
  Walk residual entry needs `stackFree sp0 16` (SAY SO).
-/

import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledEmpty
import EvmAsm.Codegen.Programs.WitnessLookupByHashSpec
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedEmpty
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Codegen.WitnessLookupByHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec (WidxCountLoc indexedFrame)
open EvmAsm.Codegen.WitnessLookupByHashIndexedEmpty (IndexedSaved indexedSavedVals)

set_option maxRecDepth 8000

/-- Shared cells through the enable-empty body (not nested stack). -/
def wlhEnCells (secPtr : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) : Assertion :=
  (CallsLoc ↦ₘ nCalls) ** (WidxEnLoc ↦ₘ (1 : Word)) **
  (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ (0 : Word)) **
  (WidxCountLoc ↦ₘ (0 : Word)) **
  (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
  (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss)

theorem wlhEnCells_pcFree (secPtr : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) :
    (wlhEnCells secPtr nCalls nIdx nMiss nLin nLast nMax nLinMiss).pcFree := by
  unfold wlhEnCells; pcf

/-- Arg moves under enableFullCode. -/
theorem wlhEnArgMoves_spec (secPtr hashPtr outOff outLen
    a8 a9 a18 a19 a20 : Word) :
    cpsTripleWithin 5 (wlhB + 36) (wlhB + 56) enableFullCode
      (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
        ((.x14 : Reg) ↦ᵣ outLen) **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x18 : Reg) ↦ᵣ a18) ** ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20))
      (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
        ((.x14 : Reg) ↦ᵣ outLen) **
        ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
        ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOff) **
        ((.x20 : Reg) ↦ᵣ outLen)) :=
  cpsTripleWithin_extend_code wlh_in_enableFull
    (wlhArgMoves_spec secPtr (0 : Word) hashPtr outOff outLen a8 a9 a18 a19 a20)

/-- Lookup-calls bump under enableFullCode. -/
theorem wlhEnLookupBump_spec (v5 v6 nCalls : Word) :
    cpsTripleWithin 5 (wlhB + 56) (wlhB + 76) enableFullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** (CallsLoc ↦ₘ nCalls))
      (((.x5 : Reg) ↦ᵣ CallsLoc) ** ((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
        (CallsLoc ↦ₘ (nCalls + 1))) := by
  have hbase := wlhCounterBump_spec (wlhB + 56) CallsLoc v5 v6 nCalls (by decide)
    (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
    (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
    (by unfold wlhCr; code_mem)
  rw [show (wlhB + 56 : Word) + 20 = wlhB + 76 from by bv_omega] at hbase
  exact cpsTripleWithin_extend_code wlh_in_enableFull hbase

/-- Parent s-regs after arg moves (enable-empty domain). -/
def wlhEnSregs (secPtr hashPtr outOff outLen : Word) : Assertion :=
  ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
  ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOff) **
  ((.x20 : Reg) ↦ᵣ outLen)

/-- ABI a-regs after arg moves / restore. -/
def wlhEnAregs (secPtr hashPtr outOff outLen : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
  ((.x14 : Reg) ↦ᵣ outLen)

/-- +36 → +76: arg moves + lookup_calls bump. Fuel 10. -/
theorem wlhEn_setup_to_enable
    (v5 v6 a8 a9 a18 a19 a20 : Word)
    (secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 10 (wlhB + 36) (wlhB + 76) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        wlhEnAregs secPtr hashPtr outOff outLen **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x18 : Reg) ↦ᵣ a18) ** ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20) **
        wlhEnCells secPtr nCalls nIdx nMiss nLin nLast nMax nLinMiss ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ CallsLoc) ** ((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
        wlhEnAregs secPtr hashPtr outOff outLen **
        wlhEnSregs secPtr hashPtr outOff outLen **
        wlhEnCells secPtr (nCalls + 1) nIdx nMiss nLin nLast nMax nLinMiss ** F) := by
  have h1 := wlhEnArgMoves_spec secPtr hashPtr outOff outLen a8 a9 a18 a19 a20
  have f1 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      wlhEnCells secPtr nCalls nIdx nMiss nLin nLast nMax nLinMiss ** F)
    (by pcf; exact hF) h1
  have h2 := wlhEnLookupBump_spec v5 v6 nCalls
  have f2 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      wlhEnAregs secPtr hashPtr outOff outLen **
      wlhEnSregs secPtr hashPtr outOff outLen **
      (WidxEnLoc ↦ₘ (1 : Word)) ** (SecPtrLoc ↦ₘ secPtr) **
      (SecLenLoc ↦ₘ (0 : Word)) ** (WidxCountLoc ↦ₘ (0 : Word)) **
      (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF) h2
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [wlhEnAregs, wlhEnSregs, wlhEnCells] at hp ⊢
    xperm_chunked hp) f1 f2
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken
      (fun _ hp => by simp only [wlhEnAregs, wlhEnCells] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [wlhEnAregs, wlhEnSregs, wlhEnCells] at hq ⊢; xperm_chunked hq)
      c)

/-- +76 → +144: enable fallthrough + sec match + ABI restore. Fuel 17. -/
theorem wlhEn_enable_to_abi
    (secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 17 (wlhB + 76) (wlhB + 144) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ CallsLoc) ** ((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
        wlhEnAregs secPtr hashPtr outOff outLen **
        wlhEnSregs secPtr hashPtr outOff outLen **
        wlhEnCells secPtr (nCalls + 1) nIdx nMiss nLin nLast nMax nLinMiss ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
        wlhEnAregs secPtr hashPtr outOff outLen **
        wlhEnSregs secPtr hashPtr outOff outLen **
        wlhEnCells secPtr (nCalls + 1) nIdx nMiss nLin nLast nMax nLinMiss ** F) := by
  -- enable fallthrough: x5 := 1
  have h1 := wlhEnableFallthrough_spec CallsLoc
  have f1 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
      wlhEnAregs secPtr hashPtr outOff outLen **
      wlhEnSregs secPtr hashPtr outOff outLen **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (SecPtrLoc ↦ₘ secPtr) **
      (SecLenLoc ↦ₘ (0 : Word)) ** (WidxCountLoc ↦ₘ (0 : Word)) **
      (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF) h1
  -- sec ptr: x5 := secPtr
  have h2 := wlhSecPtrMatch_spec (1 : Word) secPtr
  have f2 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
      wlhEnAregs secPtr hashPtr outOff outLen **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOff) **
      ((.x20 : Reg) ↦ᵣ outLen) **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
      (SecLenLoc ↦ₘ (0 : Word)) ** (WidxCountLoc ↦ₘ (0 : Word)) **
      (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF) h2
  -- sec len: x5 := 0
  have h3 := wlhSecLenMatch_spec secPtr
  have f3 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
      wlhEnAregs secPtr hashPtr outOff outLen **
      ((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOff) **
      ((.x20 : Reg) ↦ᵣ outLen) **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
      (SecPtrLoc ↦ₘ secPtr) ** (WidxCountLoc ↦ₘ (0 : Word)) **
      (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF) h3
  -- ABI restore (already correct values — identity MVs)
  have h4 := wlhIdxAbiMoves_spec secPtr hashPtr outOff outLen
    secPtr (0 : Word) hashPtr outOff outLen
  have f4 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
      (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ (0 : Word)) **
      (WidxCountLoc ↦ₘ (0 : Word)) **
      (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF) h4
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [wlhEnAregs, wlhEnSregs] at hp ⊢; xperm_chunked hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [wlhEnAregs] at hp ⊢; xperm_chunked hp) c1 f3
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [wlhEnAregs] at hp ⊢; xperm_chunked hp) c2 f4
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken
      (fun _ hp => by simp only [wlhEnAregs, wlhEnSregs, wlhEnCells] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [wlhEnAregs, wlhEnSregs, wlhEnCells] at hq ⊢; xperm_chunked hq)
      c3)

/-- +144 → +164: idx_calls bump. Fuel 5. -/
theorem wlhEn_idx_calls_bump
    (secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 5 (wlhB + 144) (wlhB + 164) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
        wlhEnAregs secPtr hashPtr outOff outLen **
        wlhEnSregs secPtr hashPtr outOff outLen **
        wlhEnCells secPtr (nCalls + 1) nIdx nMiss nLin nLast nMax nLinMiss ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ IdxCallsLoc) ** ((.x6 : Reg) ↦ᵣ (nIdx + 1)) **
        wlhEnAregs secPtr hashPtr outOff outLen **
        wlhEnSregs secPtr hashPtr outOff outLen **
        wlhEnCells secPtr (nCalls + 1) (nIdx + 1) nMiss nLin nLast nMax nLinMiss ** F) := by
  have h := wlhIdxCallsBump_spec (0 : Word) (nCalls + 1) nIdx
  have f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      wlhEnAregs secPtr hashPtr outOff outLen **
      wlhEnSregs secPtr hashPtr outOff outLen **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
      (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ (0 : Word)) **
      (WidxCountLoc ↦ₘ (0 : Word)) **
      (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF) h
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken
      (fun _ hp => by simp only [wlhEnAregs, wlhEnSregs, wlhEnCells] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [wlhEnAregs, wlhEnSregs, wlhEnCells] at hq ⊢; xperm_chunked hq)
      f)

/-- +36 → +164: full setup to nested call entry. Fuel 32. -/
theorem wlhEn_body_to_call
    (v5 v6 a8 a9 a18 a19 a20 : Word)
    (secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 32 (wlhB + 36) (wlhB + 164) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        wlhEnAregs secPtr hashPtr outOff outLen **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x18 : Reg) ↦ᵣ a18) ** ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20) **
        wlhEnCells secPtr nCalls nIdx nMiss nLin nLast nMax nLinMiss ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ IdxCallsLoc) ** ((.x6 : Reg) ↦ᵣ (nIdx + 1)) **
        wlhEnAregs secPtr hashPtr outOff outLen **
        wlhEnSregs secPtr hashPtr outOff outLen **
        wlhEnCells secPtr (nCalls + 1) (nIdx + 1) nMiss nLin nLast nMax nLinMiss ** F) := by
  have h1 := wlhEn_setup_to_enable v5 v6 a8 a9 a18 a19 a20
    secPtr hashPtr outOff outLen nCalls nIdx nMiss nLin nLast nMax nLinMiss F hF
  -- enable_to_abi / idx_calls_bump take original nCalls so (nCalls+1) matches setup post
  have h2 := wlhEn_enable_to_abi secPtr hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss F hF
  have h3 := wlhEn_idx_calls_bump secPtr hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss F hF
  have c1 := cpsTripleWithin_seq_same_cr h1 h2
  have c2 := cpsTripleWithin_seq_same_cr c1 h3
  exact cpsTripleWithin_mono_nSteps (by omega) c2

/-- IndexedSaved from enable-empty parent s-regs. -/
def wlhEnIdxSaved (ra secPtr hashPtr outOff outLen s5 s6 : Word) : IndexedSaved where
  ra := ra
  s0 := secPtr
  s1 := (0 : Word)
  s2 := hashPtr
  s3 := outOff
  s4 := outLen
  s5 := s5
  s6 := s6

/-- Ambient through nested call that is NOT in wlhIdxCallP/Q. -/
def wlhEnCallExtra (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (secPtr : Word) (F : Assertion) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ (nIdx + 1)) **
  ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
  (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ (0 : Word)) **
  (IdxCallsLoc ↦ₘ (nIdx + 1)) ** (IdxMissLoc ↦ₘ nMiss) **
  (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F

/-- +164 → +168: nested indexed empty-miss callWithin. Fuel 29.
    Pre needs `stackFree spC 8` (or frameSlotsOwn) under F via CallP reshape. -/
theorem wlhEn_call_empty
    (spC vOld : Word) (s5 s6 : Word)
    (secPtr hashPtr outOff outLen v5 v10 : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    let s := wlhEnIdxSaved vOld secPtr hashPtr outOff outLen s5 s6
    cpsTripleWithin 29 (wlhB + 164) (wlhB + 168) enableFullCode
      ((.x1 ↦ᵣ vOld) **
        wlhIdxCallP spC s hashPtr outOff outLen v5 v10 **
        wlhEnCallExtra nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F)
      ((.x1 ↦ᵣ ((wlhB + 164 : Word) + 4)) **
        wlhIdxCallQ spC ((wlhB + 164 : Word) + 4) s hashPtr outOff outLen **
        wlhEnCallExtra nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F) := by
  intro s
  have hExtra : (wlhEnCallExtra nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F).pcFree := by
    unfold wlhEnCallExtra; pcf; exact hF
  exact wlhIndexedEmptyCall_spec spC vOld s hashPtr outOff outLen v5 v10
    (wlhEnCallExtra nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F) hExtra

/-- +168 → +196: BNE miss taken (a0=1). Fuel 1. -/
theorem wlhEn_miss_branch (v0 : Word) (hne : v0 ≠ 0)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (wlhB + 168) (wlhB + 196) enableFullCode
      (((.x10 : Reg) ↦ᵣ v0) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** F)
      (((.x10 : Reg) ↦ᵣ v0) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** F) := by
  have h := wlhIndexedMissBranch_spec v0 hne
  have hf := cpsTripleWithin_frameR F hF h
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hf

/-- +196 → +216: idx_miss bump. Fuel 5. -/
theorem wlhEn_miss_bump (v5 v6 nMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 5 (wlhB + 196) (wlhB + 216) enableFullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** (IdxMissLoc ↦ₘ nMiss) ** F)
      (((.x5 : Reg) ↦ᵣ IdxMissLoc) ** ((.x6 : Reg) ↦ᵣ (nMiss + 1)) **
        (IdxMissLoc ↦ₘ (nMiss + 1)) ** F) := by
  have h := wlhIdxMissBump_spec v5 v6 nMiss
  have hf := cpsTripleWithin_frameR F hF h
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hf

/-- +216 → +580: JAL epi. Fuel 1. -/
theorem wlhEn_jal_epi (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (wlhB + 216) (wlhB + 580) enableFullCode F F := by
  have h := wlhJalEpi_spec
  have hf := cpsTripleWithin_frameR F hF h
  exact cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) hf

/-- Post-call ambient at +168 (a0=1 miss). -/
def wlhEnAfterCall (spC ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (secPtr : Word) (F : Assertion) : Assertion :=
  ((.x1 ↦ᵣ ret) **
    ((.x10 : Reg) ↦ᵣ (1 : Word)) ** (.x2 ↦ᵣ spC) **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    frameSlotsSaved indexedFrame (spC + signExtend12 (-64 : BitVec 12))
      (indexedSavedVals { s with ra := ret }) **
    ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen) **
    wlhEnCallExtra nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F)

theorem wlhEnAfterCall_pcFree (spC ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (secPtr : Word) (F : Assertion) (hF : F.pcFree) :
    (wlhEnAfterCall spC ret s hashPtr outOff outLen
      nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F).pcFree := by
  unfold wlhEnAfterCall wlhEnCallExtra; pcf; exact hF

/-- Reshape call Q+Extra into flat after-call ambient. -/
theorem wlhEn_callQ_eq_after
    (spC ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (secPtr : Word) (F : Assertion) (h : PartialState)
    (hp : ((.x1 ↦ᵣ ret) **
      wlhIdxCallQ spC ret s hashPtr outOff outLen **
      wlhEnCallExtra nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F) h) :
    (wlhEnAfterCall spC ret s hashPtr outOff outLen
      nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F) h := by
  dsimp [wlhEnAfterCall, wlhIdxCallQ, wlhEnCallExtra] at hp ⊢
  xperm_chunked hp

/-- +168 → +196 under after-call ambient. Fuel 1.
    Focus is x10+x0; rest of AfterCall (without those) is F. -/
theorem wlhEn_afterCall_miss_branch
    (spC ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (secPtr : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (wlhB + 168) (wlhB + 196) enableFullCode
      (wlhEnAfterCall spC ret s hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F)
      (wlhEnAfterCall spC ret s hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F) := by
  -- Extra already has x0; peel it out so focus is only x10+x0
  have hbr := wlhEn_miss_branch (1 : Word) (by decide)
    ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
      (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
      frameSlotsSaved indexedFrame (spC + signExtend12 (-64 : BitVec 12))
        (indexedSavedVals { s with ra := ret }) **
      ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
      ((.x14 : Reg) ↦ᵣ outLen) **
      ((.x6 : Reg) ↦ᵣ (nIdx + 1)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
      (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ (0 : Word)) **
      (IdxCallsLoc ↦ₘ (nIdx + 1)) ** (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF)
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [wlhEnAfterCall, wlhEnCallExtra] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by
      dsimp [wlhEnAfterCall, wlhEnCallExtra] at hq ⊢; xperm_chunked hq) hbr

/-- Body-exit ambient after miss bump + jal epi. -/
def wlhEnBodyExit (spC ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (secPtr : Word) (F : Assertion) : Assertion :=
  ((.x1 ↦ᵣ ret) **
    ((.x10 : Reg) ↦ᵣ (1 : Word)) ** (.x2 ↦ᵣ spC) **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    frameSlotsSaved indexedFrame (spC + signExtend12 (-64 : BitVec 12))
      (indexedSavedVals { s with ra := ret }) **
    ((.x5 : Reg) ↦ᵣ IdxMissLoc) ** ((.x6 : Reg) ↦ᵣ (nMiss + 1)) **
    (WidxCountLoc ↦ₘ (0 : Word)) **
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen) **
    (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
    (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ (0 : Word)) **
    (IdxCallsLoc ↦ₘ (nIdx + 1)) ** (IdxMissLoc ↦ₘ (nMiss + 1)) **
    (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
    (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) ** F)

/-- +196 → +216 under after-call ambient → body-exit cells. Fuel 5.
    Focus x5+x6+IdxMissLoc; rest without those. -/
theorem wlhEn_afterCall_miss_bump
    (spC ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (secPtr : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 5 (wlhB + 196) (wlhB + 216) enableFullCode
      (wlhEnAfterCall spC ret s hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F)
      (wlhEnBodyExit spC ret s hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F) := by
  have hb := wlhEn_miss_bump WidxCountLoc (nIdx + 1) nMiss
    ((.x1 ↦ᵣ ret) **
      ((.x10 : Reg) ↦ᵣ (1 : Word)) ** (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
      (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
      frameSlotsSaved indexedFrame (spC + signExtend12 (-64 : BitVec 12))
        (indexedSavedVals { s with ra := ret }) **
      (WidxCountLoc ↦ₘ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
      ((.x14 : Reg) ↦ᵣ outLen) **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
      (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ (0 : Word)) **
      (IdxCallsLoc ↦ₘ (nIdx + 1)) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF)
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      -- AfterCall has x5=WidxCountLoc, Extra has x6=nIdx+1 and IdxMissLoc
      dsimp [wlhEnAfterCall, wlhEnCallExtra] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by
      dsimp [wlhEnBodyExit] at hq ⊢; xperm_chunked hq) hb

/-- +216 → +580 under body-exit ambient. Fuel 1. -/
theorem wlhEn_bodyExit_jal_epi
    (spC ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (secPtr : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (wlhB + 216) (wlhB + 580) enableFullCode
      (wlhEnBodyExit spC ret s hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F)
      (wlhEnBodyExit spC ret s hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F) :=
  wlhEn_jal_epi _ (by
    unfold wlhEnBodyExit; pcf; exact hF)

/-- +164 → +580: nested call + miss path to body exit. Fuel 36. -/
theorem wlhEn_call_to_bodyExit
    (spC vOld : Word) (s5 s6 : Word)
    (secPtr hashPtr outOff outLen v5 v10 : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    let s := wlhEnIdxSaved vOld secPtr hashPtr outOff outLen s5 s6
    let ret : Word := (wlhB + 164 : Word) + 4
    cpsTripleWithin 36 (wlhB + 164) (wlhB + 580) enableFullCode
      ((.x1 ↦ᵣ vOld) **
        wlhIdxCallP spC s hashPtr outOff outLen v5 v10 **
        wlhEnCallExtra nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F)
      (wlhEnBodyExit spC ret s hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F) := by
  intro s ret
  have h1 := wlhEn_call_empty spC vOld s5 s6 secPtr hashPtr outOff outLen v5 v10
    nCalls nIdx nMiss nLin nLast nMax nLinMiss F hF
  -- reshape call post → afterCall
  have h1' : cpsTripleWithin 29 (wlhB + 164) (wlhB + 168) enableFullCode
      ((.x1 ↦ᵣ vOld) **
        wlhIdxCallP spC s hashPtr outOff outLen v5 v10 **
        wlhEnCallExtra nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F)
      (wlhEnAfterCall spC ret s hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) h1
    -- ret defeq (wlhB+164)+4
    have hq' : ((.x1 ↦ᵣ ((wlhB + 164 : Word) + 4)) **
        wlhIdxCallQ spC ((wlhB + 164 : Word) + 4) s hashPtr outOff outLen **
        wlhEnCallExtra nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F) h := hq
    simp only [ret] at hq' ⊢
    exact wlhEn_callQ_eq_after spC _ s hashPtr outOff outLen
      nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F h hq'
  have h2 := wlhEn_afterCall_miss_branch spC ret s hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F hF
  have h3 := wlhEn_afterCall_miss_bump spC ret s hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F hF
  have h4 := wlhEn_bodyExit_jal_epi spC ret s hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr F hF
  have c1 := cpsTripleWithin_seq_same_cr h1' h2
  have c2 := cpsTripleWithin_seq_same_cr c1 h3
  have c3 := cpsTripleWithin_seq_same_cr c2 h4
  -- 29+1+5+1 = 36
  exact cpsTripleWithin_mono_nSteps (by decide) c3

end EvmAsm.Codegen.WitnessLookupByHashSpec
