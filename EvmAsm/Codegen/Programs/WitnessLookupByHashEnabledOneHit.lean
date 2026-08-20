/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledOneHit

  #12036 — the **hit** arm of `witness_lookup_by_hash` under production
  ambient (`widx_enabled = 1`), composed over the one-hit indexed callee.

  ## Domain (SAY SO)

  * `widx_enabled = 1` (index armed — production walk ambient after build)
  * `widx_section_ptr = a0` and `widx_section_len = a1` (**match**, both free)
  * `widx_count = 1` and the sole `widx_records` record's hash equals the
    target (`coverHit`) — this is the `count = 1` hit domain of
    `witness_lookup_by_hash_indexed_spec_within_one_hit` (#12192), **not**
    the general binary-search hit path.
  * Post: `a0 = 0` (hit), out cells written with `(hitOffW, hitLenW)`
  * Telemetry: `lookup_calls +1`, `indexed_calls +1`, `indexed_hits +1`
    (linear cells and `indexed_misses` untouched)

  ## Callee

  `witness_lookup_by_hash_indexed_spec_within_one_hit` (fuel 343) via
  `callWithin` at `wlhB + 164`.

  ## What this is NOT

  * NOT the general hit path: `widx_count = 1` only. Arbitrary
    `widx_count` (real binary search) is still open — that is what
    `MptWalkResidualChain.wlCallWithinShapeHit` stands in for at the three
    walk sites.
  * The linear scan and `zkvm_keccak256` remain outside the claim (not
    reached on this domain: the `widx_enabled` test at idx 22 and the
    `BNE a0, x0` at idx 42 both jump away from them).
-/

import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledBody
import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledWrap
import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledEmpty
import EvmAsm.Codegen.Programs.WitnessLookupByHashSpec
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedEmpty
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedOneHit
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedOneHitStores
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Codegen.WitnessLookupByHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
  (IndexedB WidxCountLoc WidxRecordsBase indexedFrame)
open EvmAsm.Codegen.WitnessLookupByHashIndexedEmpty (IndexedSaved indexedSavedVals)
open EvmAsm.Codegen.WitnessLookupByHashIndexedOneHit
  (hitOffAddr hitLenAddr hitOffW hitLenW hitCells hitCmp32Extra hitHashBytes
    hitExposedZeros hitExposedValsG coverHitHash
    witness_lookup_by_hash_indexed_spec_within_one_hit
    witness_lookup_by_hash_indexed_spec_within_one_hit_gen)

set_option maxRecDepth 8000

/-! ## §1  Setup: `+36 → +164` on the hit domain

    Mirror of the enable-empty setup chain with `widx_section_len` free
    (matched, not zero) and `widx_count = 1`. -/

/-- Shared cells through the enable-hit body (not nested stack). -/
def wlhHitCells (secPtr secLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) : Assertion :=
  (CallsLoc ↦ₘ nCalls) ** (WidxEnLoc ↦ₘ (1 : Word)) **
  (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ secLen) **
  (WidxCountLoc ↦ₘ (1 : Word)) **
  (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
  (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss)

theorem wlhHitCells_pcFree (secPtr secLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) :
    (wlhHitCells secPtr secLen nCalls nIdx nMiss nLin nLast nMax nLinMiss).pcFree := by
  unfold wlhHitCells; pcf

/-- Arg moves under enableFullCode. -/
theorem wlhHitArgMoves_spec (secPtr secLen hashPtr outOff outLen
    a8 a9 a18 a19 a20 : Word) :
    cpsTripleWithin 5 (wlhB + 36) (wlhB + 56) enableFullCode
      (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ secLen) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
        ((.x14 : Reg) ↦ᵣ outLen) **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x18 : Reg) ↦ᵣ a18) ** ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20))
      (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ secLen) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
        ((.x14 : Reg) ↦ᵣ outLen) **
        ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ secLen) **
        ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOff) **
        ((.x20 : Reg) ↦ᵣ outLen)) :=
  cpsTripleWithin_extend_code wlh_in_enableFull
    (wlhArgMoves_spec secPtr secLen hashPtr outOff outLen a8 a9 a18 a19 a20)

/-- Lookup-calls bump under enableFullCode. -/
theorem wlhHitLookupBump_spec (v5 v6 nCalls : Word) :
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

/-- Parent s-regs after arg moves (enable-hit domain). -/
def wlhHitSregs (secPtr secLen hashPtr outOff outLen : Word) : Assertion :=
  ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ secLen) **
  ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOff) **
  ((.x20 : Reg) ↦ᵣ outLen)

/-- ABI a-regs after arg moves / restore. -/
def wlhHitAregs (secPtr secLen hashPtr outOff outLen : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ secLen) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
  ((.x14 : Reg) ↦ᵣ outLen)

/-- +36 → +76: arg moves + lookup_calls bump. Fuel 10. -/
theorem wlhHit_setup_to_enable
    (v5 v6 a8 a9 a18 a19 a20 : Word)
    (secPtr secLen hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 10 (wlhB + 36) (wlhB + 76) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        wlhHitAregs secPtr secLen hashPtr outOff outLen **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x18 : Reg) ↦ᵣ a18) ** ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20) **
        wlhHitCells secPtr secLen nCalls nIdx nMiss nLin nLast nMax nLinMiss ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ CallsLoc) ** ((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
        wlhHitAregs secPtr secLen hashPtr outOff outLen **
        wlhHitSregs secPtr secLen hashPtr outOff outLen **
        wlhHitCells secPtr secLen (nCalls + 1) nIdx nMiss nLin nLast nMax nLinMiss ** F) := by
  have h1 := wlhHitArgMoves_spec secPtr secLen hashPtr outOff outLen a8 a9 a18 a19 a20
  have f1 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      wlhHitCells secPtr secLen nCalls nIdx nMiss nLin nLast nMax nLinMiss ** F)
    (by pcf; exact hF) h1
  have h2 := wlhHitLookupBump_spec v5 v6 nCalls
  have f2 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      wlhHitAregs secPtr secLen hashPtr outOff outLen **
      wlhHitSregs secPtr secLen hashPtr outOff outLen **
      (WidxEnLoc ↦ₘ (1 : Word)) ** (SecPtrLoc ↦ₘ secPtr) **
      (SecLenLoc ↦ₘ secLen) ** (WidxCountLoc ↦ₘ (1 : Word)) **
      (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF) h2
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [wlhHitAregs, wlhHitSregs, wlhHitCells] at hp ⊢
    xperm_chunked hp) f1 f2
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken
      (fun _ hp => by simp only [wlhHitAregs, wlhHitCells] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [wlhHitAregs, wlhHitSregs, wlhHitCells] at hq ⊢; xperm_chunked hq)
      c)

/-- +76 → +144: enable fallthrough + sec match + ABI restore. Fuel 17. -/
theorem wlhHit_enable_to_abi
    (secPtr secLen hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 17 (wlhB + 76) (wlhB + 144) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ CallsLoc) ** ((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
        wlhHitAregs secPtr secLen hashPtr outOff outLen **
        wlhHitSregs secPtr secLen hashPtr outOff outLen **
        wlhHitCells secPtr secLen (nCalls + 1) nIdx nMiss nLin nLast nMax nLinMiss ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ secLen) ** ((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
        wlhHitAregs secPtr secLen hashPtr outOff outLen **
        wlhHitSregs secPtr secLen hashPtr outOff outLen **
        wlhHitCells secPtr secLen (nCalls + 1) nIdx nMiss nLin nLast nMax nLinMiss ** F) := by
  -- enable fallthrough: x5 := 1
  have h1 := wlhEnableFallthrough_spec CallsLoc
  have f1 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
      wlhHitAregs secPtr secLen hashPtr outOff outLen **
      wlhHitSregs secPtr secLen hashPtr outOff outLen **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (SecPtrLoc ↦ₘ secPtr) **
      (SecLenLoc ↦ₘ secLen) ** (WidxCountLoc ↦ₘ (1 : Word)) **
      (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF) h1
  -- sec ptr: x5 := secPtr
  have h2 := wlhSecPtrMatch_spec (1 : Word) secPtr
  have f2 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
      wlhHitAregs secPtr secLen hashPtr outOff outLen **
      ((.x9 : Reg) ↦ᵣ secLen) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOff) **
      ((.x20 : Reg) ↦ᵣ outLen) **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
      (SecLenLoc ↦ₘ secLen) ** (WidxCountLoc ↦ₘ (1 : Word)) **
      (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF) h2
  -- sec len: x5 := 0
  have h3 := wlhSecLenMatchG_spec secPtr secLen
  have f3 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
      wlhHitAregs secPtr secLen hashPtr outOff outLen **
      ((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOff) **
      ((.x20 : Reg) ↦ᵣ outLen) **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
      (SecPtrLoc ↦ₘ secPtr) ** (WidxCountLoc ↦ₘ (1 : Word)) **
      (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF) h3
  -- ABI restore (already correct values — identity MVs)
  have h4 := wlhIdxAbiMovesG_spec secPtr secLen hashPtr outOff outLen
    secPtr secLen hashPtr outOff outLen
  have f4 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ secLen) **
      ((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
      (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ secLen) **
      (WidxCountLoc ↦ₘ (1 : Word)) **
      (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF) h4
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [wlhHitAregs, wlhHitSregs] at hp ⊢; xperm_chunked hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [wlhHitAregs] at hp ⊢; xperm_chunked hp) c1 f3
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [wlhHitAregs] at hp ⊢; xperm_chunked hp) c2 f4
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken
      (fun _ hp => by simp only [wlhHitAregs, wlhHitSregs, wlhHitCells] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [wlhHitAregs, wlhHitSregs, wlhHitCells] at hq ⊢; xperm_chunked hq)
      c3)

/-- +144 → +164: idx_calls bump. Fuel 5. -/
theorem wlhHit_idx_calls_bump
    (secPtr secLen hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 5 (wlhB + 144) (wlhB + 164) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ secLen) ** ((.x6 : Reg) ↦ᵣ (nCalls + 1)) **
        wlhHitAregs secPtr secLen hashPtr outOff outLen **
        wlhHitSregs secPtr secLen hashPtr outOff outLen **
        wlhHitCells secPtr secLen (nCalls + 1) nIdx nMiss nLin nLast nMax nLinMiss ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ IdxCallsLoc) ** ((.x6 : Reg) ↦ᵣ (nIdx + 1)) **
        wlhHitAregs secPtr secLen hashPtr outOff outLen **
        wlhHitSregs secPtr secLen hashPtr outOff outLen **
        wlhHitCells secPtr secLen (nCalls + 1) (nIdx + 1) nMiss nLin nLast nMax nLinMiss ** F) := by
  have h := wlhIdxCallsBump_spec secLen (nCalls + 1) nIdx
  have f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      wlhHitAregs secPtr secLen hashPtr outOff outLen **
      wlhHitSregs secPtr secLen hashPtr outOff outLen **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
      (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ secLen) **
      (WidxCountLoc ↦ₘ (1 : Word)) **
      (IdxMissLoc ↦ₘ nMiss) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F)
    (by pcf; exact hF) h
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken
      (fun _ hp => by simp only [wlhHitAregs, wlhHitSregs, wlhHitCells] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [wlhHitAregs, wlhHitSregs, wlhHitCells] at hq ⊢; xperm_chunked hq)
      f)

/-- +36 → +164: full setup to nested call entry. Fuel 32. -/
theorem wlhHit_body_to_call
    (v5 v6 a8 a9 a18 a19 a20 : Word)
    (secPtr secLen hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 32 (wlhB + 36) (wlhB + 164) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        wlhHitAregs secPtr secLen hashPtr outOff outLen **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x18 : Reg) ↦ᵣ a18) ** ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20) **
        wlhHitCells secPtr secLen nCalls nIdx nMiss nLin nLast nMax nLinMiss ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ IdxCallsLoc) ** ((.x6 : Reg) ↦ᵣ (nIdx + 1)) **
        wlhHitAregs secPtr secLen hashPtr outOff outLen **
        wlhHitSregs secPtr secLen hashPtr outOff outLen **
        wlhHitCells secPtr secLen (nCalls + 1) (nIdx + 1) nMiss nLin nLast nMax nLinMiss ** F) := by
  have h1 := wlhHit_setup_to_enable v5 v6 a8 a9 a18 a19 a20
    secPtr secLen hashPtr outOff outLen nCalls nIdx nMiss nLin nLast nMax nLinMiss F hF
  -- enable_to_abi / idx_calls_bump take original nCalls so (nCalls+1) matches setup post
  have h2 := wlhHit_enable_to_abi secPtr secLen hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss F hF
  have h3 := wlhHit_idx_calls_bump secPtr secLen hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss F hF
  have c1 := cpsTripleWithin_seq_same_cr h1 h2
  have c2 := cpsTripleWithin_seq_same_cr c1 h3
  exact cpsTripleWithin_mono_nSteps (by omega) c2

/-! ## §2  The hit arm: `+168 → +580`

    Program shape (indices 42…48 of `witnessLookupByHash_prog`):

    * idx 42 `BNE a0, x0, +28` — **not** taken on a hit (`a0 = 0`)
    * idx 43…47 — the five-instruction `wlh_indexed_hits` bump
    * idx 48 `JAL x0, +580` — straight to the ABI epilogue

    So the hit arm is seven instructions and lands exactly on the frame
    boundary; no linear-scan code is executed. -/

private theorem hit_bne_same_absurd {r1 r2 : Reg} {v : Word} :
    ∀ hp, (((r1 : Reg) ↦ᵣ v) ** ((r2 : Reg) ↦ᵣ v) ** ⌜v ≠ v⌝) hp → False := by
  intro hp hq
  obtain ⟨_, _, _, _, _, hB⟩ := hq
  obtain ⟨_, _, _, _, _, hP⟩ := hB
  exact hP.2 rfl

/-- After the indexed callee returns `a0 = 0`, the `BNE a0, x0` at `+168`
    is NOT taken, so control falls through to the hit telemetry at `+172`. -/
theorem wlhIndexedHitBranch_spec :
    cpsTripleWithin 1 (wlhB + 168) (wlhB + 172) enableFullCode
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  have hbr := cpsBranchWithin_extend_code (cr' := enableFullCode)
    (by enable_parent_mem)
    (bne_spec_gen_within .x10 .x0 (28 : BitVec 13) (0 : Word) (0 : Word)
      (wlhB + 168))
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr hit_bne_same_absurd
  rw [show (wlhB + 168 : Word) + 4 = wlhB + 172 from by bv_omega] at hnt
  exact cpsTripleWithin_mono_nSteps (by omega) hnt

/-- Bump `wlh_indexed_hits` at body `+172` (5 insn). -/
theorem wlhIdxHitBump_spec (v5 v6 nHit : Word) :
    cpsTripleWithin 5 (wlhB + 172) (wlhB + 192) enableFullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** (IdxHitLoc ↦ₘ nHit))
      (((.x5 : Reg) ↦ᵣ IdxHitLoc) ** ((.x6 : Reg) ↦ᵣ (nHit + 1)) **
        (IdxHitLoc ↦ₘ (nHit + 1))) := by
  have hbase := wlhCounterBump_spec (wlhB + 172) IdxHitLoc v5 v6 nHit
    (by decide)
    (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
    (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
    (by unfold wlhCr; code_mem)
  exact cpsTripleWithin_extend_code wlh_in_enableFull hbase

private theorem hit_jal_epi_target :
    (wlhB + 192) + signExtend21
      (jalOff (GuestAddrs.witness_lookup_by_hash + 580)
        (GuestAddrs.witness_lookup_by_hash + 192)) =
      wlhB + 580 := by
  unfold wlhB; decide

/-- `JAL x0` to the epilogue at `+580` from `+192` (hit arm). -/
theorem wlhHitJalEpi_spec :
    cpsTripleWithin 1 (wlhB + 192) (wlhB + 580) enableFullCode
      empAssertion empAssertion := by
  have h := liftCode (cr' := enableFullCode)
    (jal_x0_spec_gen_within
      (jalOff (GuestAddrs.witness_lookup_by_hash + 580)
        (GuestAddrs.witness_lookup_by_hash + 192)) (wlhB + 192))
    (by enable_parent_mem)
  rw [hit_jal_epi_target] at h
  exact h

/-! ## §3  Nested one-hit call at `+164`

    The generalized callee (`witness_lookup_by_hash_indexed_spec_within_one_hit_gen`,
    #12036) is what makes this composable: the parent arrives with
    `x6 = wlh_indexed_calls + 1` and `x11 = a1`, so the zeros-pinned form
    could not be instantiated. -/

/-- `IndexedSaved` from the hit-domain parent s-regs (`s1` = section length). -/
def wlhHitIdxSaved (ra secPtr secLen hashPtr outOff outLen s5 s6 : Word) :
    IndexedSaved where
  ra := ra
  s0 := secPtr
  s1 := secLen
  s2 := hashPtr
  s3 := outOff
  s4 := outLen
  s5 := s5
  s6 := s6

/-- CallWithin `P` for the nested one-hit call (everything except caller `x1`). -/
def wlhIdxHitCallP (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen offOld lenOld v5 v10 : Word)
    (w6 w7 w11 w15 w16 w17 w28 w29 w30 w31 : Word) : Assertion :=
  ((.x2 ↦ᵣ spC) **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    (.x12 ↦ᵣ hashPtr) ** (.x13 ↦ᵣ outOff) ** (.x14 ↦ᵣ outLen) **
    (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
    frameSlotsOwn indexedFrame (spC + signExtend12 (-64 : BitVec 12)) **
    (WidxCountLoc ↦ₘ (1 : Word)) **
    hitExposedValsG w6 w7 w11 w15 w16 w17 w28 w29 w30 w31 **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    hitHashBytes hashPtr **
    hitCells outOff outLen offOld lenOld)

/-- CallWithin `Q`: `a0 = 0` and the out cells hold `(hitOffW, hitLenW)`. -/
def wlhIdxHitCallQ (spC ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) : Assertion :=
  (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    frameSlotsSaved indexedFrame (spC + signExtend12 (-64 : BitVec 12))
      (indexedSavedVals { s with ra := ret }) **
    (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
    (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
    ((.x5 : Reg) ↦ᵣ hitLenW) **
    hitCmp32Extra hashPtr)

private theorem wlhIdxHitCallP_pcFree (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen offOld lenOld v5 v10 : Word)
    (w6 w7 w11 w15 w16 w17 w28 w29 w30 w31 : Word) :
    (wlhIdxHitCallP spC s hashPtr outOff outLen offOld lenOld v5 v10
      w6 w7 w11 w15 w16 w17 w28 w29 w30 w31).pcFree := by
  dsimp [wlhIdxHitCallP, hitExposedValsG, hitHashBytes, hitCells]
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp

private abbrev WlhProgH : List Instr := witnessLookupByHash_prog

private theorem wlhProgH_length : WlhProgH.length = 155 := by decide

private abbrev idxHitJalOff : BitVec 21 :=
  jalOff GuestAddrs.witness_lookup_by_hash_indexed
    (GuestAddrs.witness_lookup_by_hash + 164)

private theorem idxHit_jal_target :
    (wlhB + 164 : Word) + signExtend21 idxHitJalOff = (IndexedB : Word) := by
  unfold wlhB IndexedB idxHitJalOff; decide

private theorem idxHit_call_ret_even :
    (((wlhB + 164 : Word) + 4) &&& ~~~(1 : Word)) = (wlhB + 164 : Word) + 4 := by
  decide

private theorem progH_jal_indexed :
    WlhProgH[41]'(by rw [wlhProgH_length]; decide) =
      Instr.JAL .x1 idxHitJalOff := by
  unfold WlhProgH witnessLookupByHash_prog idxHitJalOff; rfl

/-- `+164 → +168`: nested indexed **one-hit** callWithin. Fuel 344 = 1 + 343. -/
theorem wlhIndexedOneHitCall_spec
    (spC vOld : Word) (s : IndexedSaved)
    (hashPtr outOff outLen offOld lenOld v5 v10 : Word)
    (w6 w7 w11 w15 w16 w17 w28 w29 w30 w31 : Word)
    (F : Assertion) (hF : F.pcFree)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 344 (wlhB + 164) (wlhB + 168) enableFullCode
      ((.x1 ↦ᵣ vOld) **
        wlhIdxHitCallP spC s hashPtr outOff outLen offOld lenOld v5 v10
          w6 w7 w11 w15 w16 w17 w28 w29 w30 w31 ** F)
      ((.x1 ↦ᵣ ((wlhB + 164 : Word) + 4)) **
        wlhIdxHitCallQ spC ((wlhB + 164 : Word) + 4) s hashPtr outOff outLen ** F) := by
  set ret : Word := (wlhB + 164 : Word) + 4
  have hbase0 :=
    witness_lookup_by_hash_indexed_spec_within_one_hit_gen spC ret s
      hashPtr outOff outLen offOld lenOld v5 v10
      w6 w7 w11 w15 w16 w17 w28 w29 w30 w31
      idxHit_call_ret_even halignH hovH hvalidR hvalidH
  have hbase := cpsTripleWithin_extend_code idx_in_enableFull hbase0
  have hcallee0 : cpsTripleWithin 343 (IndexedB : Word) ret enableFullCode
      ((.x1 ↦ᵣ ret) **
        wlhIdxHitCallP spC s hashPtr outOff outLen offOld lenOld v5 v10
          w6 w7 w11 w15 w16 w17 w28 w29 w30 w31)
      ((.x1 ↦ᵣ ret) ** wlhIdxHitCallQ spC ret s hashPtr outOff outLen) := by
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hbase
    · rw [WitnessLookupByHashIndexedEmpty.regsAt_indexedFrame]
      dsimp [wlhIdxHitCallP, indexedSavedVals] at hp ⊢
      xperm_chunked hp
    · dsimp [wlhIdxHitCallQ, indexedSavedVals] at hq ⊢
      xperm_chunked hq
  have hP :
      (wlhIdxHitCallP spC s hashPtr outOff outLen offOld lenOld v5 v10
        w6 w7 w11 w15 w16 w17 w28 w29 w30 w31 ** F).pcFree :=
    pcFree_sepConj (wlhIdxHitCallP_pcFree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) hF
  have hcallee : cpsTripleWithin 343 (IndexedB : Word) ret enableFullCode
      ((.x1 ↦ᵣ ret) **
        (wlhIdxHitCallP spC s hashPtr outOff outLen offOld lenOld v5 v10
          w6 w7 w11 w15 w16 w17 w28 w29 w30 w31 ** F))
      ((.x1 ↦ᵣ ret) ** (wlhIdxHitCallQ spC ret s hashPtr outOff outLen ** F)) := by
    have hfr := cpsTripleWithin_frameR F hF hcallee0
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hfr
  have hmem : ∀ a i,
      CodeReq.singleton (wlhB + 164) (Instr.JAL .x1 idxHitJalOff) a = some i →
        enableFullCode a = some i := by
    intro a i hh
    apply wlh_in_enableFull
    exact CodeReq.ofProg_mem_at wlhB (wlhB + 164) WlhProgH 41
      (Instr.JAL .x1 idxHitJalOff)
      (by unfold wlhB; decide)
      (by rw [wlhProgH_length]; decide)
      progH_jal_indexed
      (by rw [wlhProgH_length]; decide)
      a i hh
  have hcall := callWithin_spec (wlhB + 164) (IndexedB : Word) vOld idxHitJalOff 343
    idxHit_jal_target hmem hP hcallee
  have hpc : ret = wlhB + 168 := by simp only [ret]; unfold wlhB; decide
  have hn : 1 + 343 = 344 := rfl
  have hcall' : cpsTripleWithin 344 (wlhB + 164) (wlhB + 168) enableFullCode
      ((.x1 ↦ᵣ vOld) **
        (wlhIdxHitCallP spC s hashPtr outOff outLen offOld lenOld v5 v10
          w6 w7 w11 w15 w16 w17 w28 w29 w30 w31 ** F))
      ((.x1 ↦ᵣ ret) ** (wlhIdxHitCallQ spC ret s hashPtr outOff outLen ** F)) := by
    rw [← hn, ← hpc]
    exact hcall
  exact hcall'

/-- `+192 → +580` under an arbitrary pcFree ambient. Fuel 1. -/
theorem wlhHit_jal_epi (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (wlhB + 192) (wlhB + 580) enableFullCode F F := by
  have h := cpsTripleWithin_frameR F hF wlhHitJalEpi_spec
  exact cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) h

/-! ## §4  Hit arm `+168 → +580` -/

/-- `+168 → +580` on the hit arm with `x6` at a named value. Fuel 7. -/
theorem wlhHit_arm_to_epi (v6 nHit : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (wlhB + 168) (wlhB + 580) enableFullCode
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ hitLenW) ** ((.x6 : Reg) ↦ᵣ v6) **
        (IdxHitLoc ↦ₘ nHit) ** F)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ IdxHitLoc) ** ((.x6 : Reg) ↦ᵣ (nHit + 1)) **
        (IdxHitLoc ↦ₘ (nHit + 1)) ** F) := by
  have h1 := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ hitLenW) ** ((.x6 : Reg) ↦ᵣ v6) **
      (IdxHitLoc ↦ₘ nHit) ** F)
    (by pcf; exact hF) wlhIndexedHitBranch_spec
  have h2 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) (wlhIdxHitBump_spec hitLenW v6 nHit)
  have h3 := wlhHit_jal_epi
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ IdxHitLoc) ** ((.x6 : Reg) ↦ᵣ (nHit + 1)) **
      (IdxHitLoc ↦ₘ (nHit + 1)) ** F)
    (by pcf; exact hF)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) h1 h2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 h3
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) c2)

/-- `+168 → +580` taking `x6` as an ownership (which is what the callee's post
    hands back). Fuel 7. -/
theorem wlhHit_arm_to_epi_own (nHit : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (wlhB + 168) (wlhB + 580) enableFullCode
      ((((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ hitLenW) ** (IdxHitLoc ↦ₘ nHit) ** F) ** regOwn .x6)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ IdxHitLoc) ** ((.x6 : Reg) ↦ᵣ (nHit + 1)) **
        (IdxHitLoc ↦ₘ (nHit + 1)) ** F) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v6
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
    (wlhHit_arm_to_epi v6 nHit F hF)

/-! ## §5  `+164 → +580`: nested call then hit arm -/

/-- Non-hit-counter cells + user ambient framed through the nested call. -/
def wlhHitPostCells (secPtr secLen cCalls cIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) : Assertion :=
  (CallsLoc ↦ₘ cCalls) ** (WidxEnLoc ↦ₘ (1 : Word)) **
  (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ secLen) **
  (IdxCallsLoc ↦ₘ cIdx) ** (IdxHitLoc ↦ₘ nHit) **
  (IdxMissLoc ↦ₘ nMiss) **
  (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F

theorem wlhHitPostCells_pcFree
    (secPtr secLen cCalls cIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    (wlhHitPostCells secPtr secLen cCalls cIdx nHit nMiss nLin nLast nMax
      nLinMiss F).pcFree := by
  unfold wlhHitPostCells; pcf; exact hF

/-- Everything the hit arm carries but does not touch (its `F`). -/
def wlhHitArmF (spC ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen secPtr secLen : Word)
    (cCalls cIdx nMiss nLin nLast nMax nLinMiss : Word) (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
  (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
  (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
  frameSlotsSaved indexedFrame (spC + signExtend12 (-64 : BitVec 12))
    (indexedSavedVals { s with ra := ret }) **
  (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
  (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
  regOwn .x7 ** regOwn .x11 **
  regOwns [.x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17] **
  bytesRegion WidxRecordsBase coverHitHash **
  bytesRegion hashPtr coverHitHash **
  (WidxCountLoc ↦ₘ (1 : Word)) **
  (CallsLoc ↦ₘ cCalls) ** (WidxEnLoc ↦ₘ (1 : Word)) **
  (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ secLen) **
  (IdxCallsLoc ↦ₘ cIdx) ** (IdxMissLoc ↦ₘ nMiss) **
  (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) ** F

theorem wlhHitArmF_pcFree (spC ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen secPtr secLen : Word)
    (cCalls cIdx nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree) :
    (wlhHitArmF spC ret s hashPtr outOff outLen secPtr secLen
      cCalls cIdx nMiss nLin nLast nMax nLinMiss F).pcFree := by
  unfold wlhHitArmF
  repeat' first
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_regOwn
    | exact pcFree_regOwns _
    | exact pcFree_frameSlotsSaved _ _ _
    | exact bytesRegion_pcFree _ _
    | exact hF
    | apply pcFree_sepConj

/-- Body exit at `+580` on the hit arm. -/
def wlhHitBodyExit (spC ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen secPtr secLen : Word)
    (cCalls cIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  ((.x5 : Reg) ↦ᵣ IdxHitLoc) ** ((.x6 : Reg) ↦ᵣ (nHit + 1)) **
  (IdxHitLoc ↦ₘ (nHit + 1)) **
  wlhHitArmF spC ret s hashPtr outOff outLen secPtr secLen
    cCalls cIdx nMiss nLin nLast nMax nLinMiss F

/-- `+164 → +580`: nested one-hit call then the hit arm. Fuel 351 = 344 + 7. -/
theorem wlhHit_call_to_bodyExit
    (spC vOld s5 s6 : Word)
    (secPtr secLen hashPtr outOff outLen offOld lenOld v5 v10 : Word)
    (w6 w7 w11 w15 w16 w17 w28 w29 w30 w31 : Word)
    (cCalls cIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (F : Assertion) (hF : F.pcFree)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    let s := wlhHitIdxSaved vOld secPtr secLen hashPtr outOff outLen s5 s6
    let ret : Word := (wlhB + 164 : Word) + 4
    cpsTripleWithin 351 (wlhB + 164) (wlhB + 580) enableFullCode
      ((.x1 ↦ᵣ vOld) **
        wlhIdxHitCallP spC s hashPtr outOff outLen offOld lenOld v5 v10
          w6 w7 w11 w15 w16 w17 w28 w29 w30 w31 **
        wlhHitPostCells secPtr secLen cCalls cIdx nHit nMiss nLin nLast nMax
          nLinMiss F)
      (wlhHitBodyExit spC ret s hashPtr outOff outLen secPtr secLen
        cCalls cIdx nHit nMiss nLin nLast nMax nLinMiss F) := by
  intro s ret
  have hExtra := wlhHitPostCells_pcFree secPtr secLen cCalls cIdx nHit nMiss
    nLin nLast nMax nLinMiss F hF
  have h1 := wlhIndexedOneHitCall_spec spC vOld s hashPtr outOff outLen
    offOld lenOld v5 v10 w6 w7 w11 w15 w16 w17 w28 w29 w30 w31
    (wlhHitPostCells secPtr secLen cCalls cIdx nHit nMiss nLin nLast nMax
      nLinMiss F) hExtra halignH hovH hvalidR hvalidH
  have hAF := wlhHitArmF_pcFree spC ret s hashPtr outOff outLen secPtr secLen
    cCalls cIdx nMiss nLin nLast nMax nLinMiss F hF
  -- Reshape the call post into the arm's pre (x6 as an own).
  have h1' : cpsTripleWithin 344 (wlhB + 164) (wlhB + 168) enableFullCode
      ((.x1 ↦ᵣ vOld) **
        wlhIdxHitCallP spC s hashPtr outOff outLen offOld lenOld v5 v10
          w6 w7 w11 w15 w16 w17 w28 w29 w30 w31 **
        wlhHitPostCells secPtr secLen cCalls cIdx nHit nMiss nLin nLast nMax
          nLinMiss F)
      ((((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ hitLenW) ** (IdxHitLoc ↦ₘ nHit) **
        wlhHitArmF spC ret s hashPtr outOff outLen secPtr secLen
          cCalls cIdx nMiss nLin nLast nMax nLinMiss F) ** regOwn .x6) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) h1
    dsimp [wlhIdxHitCallQ, wlhHitPostCells, wlhHitArmF, hitCmp32Extra, ret] at hq ⊢
    xperm_chunked hq
  have h2 := wlhHit_arm_to_epi_own nHit
    (wlhHitArmF spC ret s hashPtr outOff outLen secPtr secLen
      cCalls cIdx nMiss nLin nLast nMax nLinMiss F) hAF
  have c := cpsTripleWithin_seq_same_cr h1' h2
  have hn : 344 + 7 = 351 := rfl
  rw [hn] at c
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by dsimp [wlhHitBodyExit] at hq ⊢; xperm_chunked hq) c

/-! ## §6  `+36 → +580` body core -/

/-- Ambient framed through the whole hit body: parent frame, nested stack,
    the scratch temps handed to the callee, the index-hit counter, and the
    record/hash byte regions plus out cells. -/
def wlhHitBodyF (newSp : Word) (vals : Reg → Word)
    (hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 nHit : Word) : Assertion :=
  ((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x2 : Reg) ↦ᵣ newSp) **
  ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
  frameSlotsSaved wlhFrame newSp vals **
  wlhEnNestedStack newSp **
  ((.x7 : Reg) ↦ᵣ w7) ** ((.x15 : Reg) ↦ᵣ w15) **
  ((.x16 : Reg) ↦ᵣ w16) ** ((.x17 : Reg) ↦ᵣ w17) **
  ((.x28 : Reg) ↦ᵣ w28) ** ((.x29 : Reg) ↦ᵣ w29) **
  ((.x30 : Reg) ↦ᵣ w30) ** ((.x31 : Reg) ↦ᵣ w31) **
  (IdxHitLoc ↦ₘ nHit) **
  hitHashBytes hashPtr ** hitCells outOff outLen offOld lenOld

theorem wlhHitBodyF_pcFree (newSp : Word) (vals : Reg → Word)
    (hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 nHit : Word) :
    (wlhHitBodyF newSp vals hashPtr outOff outLen offOld lenOld
      w7 w15 w16 w17 w28 w29 w30 w31 nHit).pcFree := by
  unfold wlhHitBodyF wlhEnNestedStack hitHashBytes hitCells
  repeat' first
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_frameSlotsSaved _ _ _
    | exact bytesRegion_pcFree _ _
    | exact pcFree_emp
    | apply pcFree_sepConj

/-- `+36 → +580` on the hit domain. Fuel 383 = 32 (setup) + 351 (call+arm). -/
theorem wlhHit_body_core
    (newSp : Word) (vals : Reg → Word)
    (v5 v6 a8 a9 a18 a19 a20 : Word)
    (secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    let s := wlhHitIdxSaved (vals .x1) secPtr secLen hashPtr outOff outLen
      (vals .x21) (vals .x22)
    let retCall : Word := (wlhB + 164 : Word) + 4
    cpsTripleWithin 383 (wlhB + 36) (wlhB + 580) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        wlhHitAregs secPtr secLen hashPtr outOff outLen **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x18 : Reg) ↦ᵣ a18) ** ((.x19 : Reg) ↦ᵣ a19) **
        ((.x20 : Reg) ↦ᵣ a20) **
        wlhHitCells secPtr secLen nCalls nIdx nMiss nLin nLast nMax nLinMiss **
        wlhHitBodyF newSp vals hashPtr outOff outLen offOld lenOld
          w7 w15 w16 w17 w28 w29 w30 w31 nHit)
      (wlhHitBodyExit newSp retCall s hashPtr outOff outLen secPtr secLen
        (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss
        (frameSlotsSaved wlhFrame newSp vals)) := by
  intro s retCall
  have hF := wlhHitBodyF_pcFree newSp vals hashPtr outOff outLen offOld lenOld
    w7 w15 w16 w17 w28 w29 w30 w31 nHit
  have h1 := wlhHit_body_to_call v5 v6 a8 a9 a18 a19 a20
    secPtr secLen hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss
    (wlhHitBodyF newSp vals hashPtr outOff outLen offOld lenOld
      w7 w15 w16 w17 w28 w29 w30 w31 nHit) hF
  have h1' : cpsTripleWithin 32 (wlhB + 36) (wlhB + 164) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        wlhHitAregs secPtr secLen hashPtr outOff outLen **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x18 : Reg) ↦ᵣ a18) ** ((.x19 : Reg) ↦ᵣ a19) **
        ((.x20 : Reg) ↦ᵣ a20) **
        wlhHitCells secPtr secLen nCalls nIdx nMiss nLin nLast nMax nLinMiss **
        wlhHitBodyF newSp vals hashPtr outOff outLen offOld lenOld
          w7 w15 w16 w17 w28 w29 w30 w31 nHit)
      ((.x1 ↦ᵣ vals .x1) **
        wlhIdxHitCallP newSp s hashPtr outOff outLen offOld lenOld
          IdxCallsLoc secPtr (nIdx + 1) w7 secLen w15 w16 w17 w28 w29 w30 w31 **
        wlhHitPostCells secPtr secLen (nCalls + 1) (nIdx + 1) nHit nMiss
          nLin nLast nMax nLinMiss (frameSlotsSaved wlhFrame newSp vals)) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) h1
    dsimp [wlhHitAregs, wlhHitSregs, wlhHitCells, wlhHitBodyF, wlhEnNestedStack,
      wlhIdxHitCallP, wlhHitPostCells, wlhHitIdxSaved, hitExposedValsG, s] at hq ⊢
    xperm_chunked hq
  have h2 := wlhHit_call_to_bodyExit newSp (vals .x1) (vals .x21) (vals .x22)
    secPtr secLen hashPtr outOff outLen offOld lenOld IdxCallsLoc secPtr
    (nIdx + 1) w7 secLen w15 w16 w17 w28 w29 w30 w31
    (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss
    (frameSlotsSaved wlhFrame newSp vals) (by exact pcFree_frameSlotsSaved _ _ _)
    halignH hovH hvalidR hvalidH
  have c := cpsTripleWithin_seq_same_cr h1' h2
  exact cpsTripleWithin_mono_nSteps (by decide : 32 + 351 ≤ 383) c

/-! ## §7  Whole-routine wrap -/

/-- Caller ambient at entry (no frame regs). Nested Own below parent SP. -/
def wlhHitCallerPre (newSp : Word)
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
  wlhHitAregs secPtr secLen hashPtr outOff outLen **
  wlhHitCells secPtr secLen nCalls nIdx nMiss nLin nLast nMax nLinMiss **
  wlhEnNestedStack newSp **
  ((.x7 : Reg) ↦ᵣ w7) ** ((.x15 : Reg) ↦ᵣ w15) **
  ((.x16 : Reg) ↦ᵣ w16) ** ((.x17 : Reg) ↦ᵣ w17) **
  ((.x28 : Reg) ↦ᵣ w28) ** ((.x29 : Reg) ↦ᵣ w29) **
  ((.x30 : Reg) ↦ᵣ w30) ** ((.x31 : Reg) ↦ᵣ w31) **
  (IdxHitLoc ↦ₘ nHit) **
  hitHashBytes hashPtr ** hitCells outOff outLen offOld lenOld

theorem wlhHitCallerPre_pcFree (newSp : Word)
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word) :
    (wlhHitCallerPre newSp v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
      w7 w15 w16 w17 w28 w29 w30 w31
      nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss).pcFree := by
  unfold wlhHitCallerPre wlhHitAregs wlhHitCells wlhEnNestedStack
    hitHashBytes hitCells
  repeat' first
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact bytesRegion_pcFree _ _
    | exact pcFree_emp
    | apply pcFree_sepConj

/-- Caller ambient at exit: `a0 = 0`, out cells written, hit telemetry bumped. -/
def wlhHitCallerPost (newSp retCall : Word) (s : IndexedSaved)
    (hashPtr outOff outLen secPtr secLen : Word)
    (cCalls cIdx nHit nMiss nLin nLast nMax nLinMiss : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  ((.x5 : Reg) ↦ᵣ IdxHitLoc) ** ((.x6 : Reg) ↦ᵣ (nHit + 1)) **
  regOwn .x7 ** regOwn .x11 **
  regOwns [.x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17] **
  frameSlotsSaved indexedFrame (newSp + signExtend12 (-64 : BitVec 12))
    (indexedSavedVals { s with ra := retCall }) **
  (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
  (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
  bytesRegion WidxRecordsBase coverHitHash **
  bytesRegion hashPtr coverHitHash **
  (WidxCountLoc ↦ₘ (1 : Word)) **
  (CallsLoc ↦ₘ cCalls) ** (WidxEnLoc ↦ₘ (1 : Word)) **
  (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ secLen) **
  (IdxCallsLoc ↦ₘ cIdx) ** (IdxHitLoc ↦ₘ (nHit + 1)) **
  (IdxMissLoc ↦ₘ nMiss) **
  (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss)

theorem wlhHitCallerPost_pcFree (newSp retCall : Word) (s : IndexedSaved)
    (hashPtr outOff outLen secPtr secLen : Word)
    (cCalls cIdx nHit nMiss nLin nLast nMax nLinMiss : Word) :
    (wlhHitCallerPost newSp retCall s hashPtr outOff outLen secPtr secLen
      cCalls cIdx nHit nMiss nLin nLast nMax nLinMiss).pcFree := by
  unfold wlhHitCallerPost
  repeat' first
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_regOwn
    | exact pcFree_regOwns _
    | exact pcFree_frameSlotsSaved _ _ _
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj

private theorem regsAt_wlhFrame_hit (vals : Reg → Word) :
    regsAt wlhFrame vals =
      (((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x8 : Reg) ↦ᵣ vals .x8) **
        ((.x9 : Reg) ↦ᵣ vals .x9) ** ((.x18 : Reg) ↦ᵣ vals .x18) **
        ((.x19 : Reg) ↦ᵣ vals .x19) ** ((.x20 : Reg) ↦ᵣ vals .x20) **
        ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22)) := by
  simp [wlhFrame, regsAt, sepConj_emp_right']

private theorem regsOwnAt_wlhFrame_hit :
    regsOwnAt wlhFrame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
        regOwn .x20 ** regOwn .x21 ** regOwn .x22) := by
  simp [wlhFrame, regsOwnAt, sepConj_emp_right']

private theorem ent_own8_hit (r1 r2 r3 r4 r5 r6 r7 r8 : Reg)
    (w1 w2 w3 w4 w5 w6 w7 w8 : Word) (P : Assertion) (h : PartialState)
    (hp : ((r1 ↦ᵣ w1) ** (r2 ↦ᵣ w2) ** (r3 ↦ᵣ w3) ** (r4 ↦ᵣ w4) ** (r5 ↦ᵣ w5) **
      (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** (r8 ↦ᵣ w8) ** P) h) :
    (regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5 ** regOwn r6 **
      regOwn r7 ** regOwn r8 ** P) h :=
  sepConj_mono (regIs_to_regOwn r1 w1)
    (sepConj_mono (regIs_to_regOwn r2 w2)
      (sepConj_mono (regIs_to_regOwn r3 w3)
        (sepConj_mono (regIs_to_regOwn r4 w4)
          (sepConj_mono (regIs_to_regOwn r5 w5)
            (sepConj_mono (regIs_to_regOwn r6 w6)
              (sepConj_mono (regIs_to_regOwn r7 w7)
                (sepConj_mono (regIs_to_regOwn r8 w8) (fun _ hx => hx)))))))) h hp

/-- Hit body in `abiFrame` shape. Fuel 383. -/
theorem wlhHit_body_abi
    (newSp : Word) (vals : Reg → Word)
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    let s := wlhHitIdxSaved (vals .x1) secPtr secLen hashPtr outOff outLen
      (vals .x21) (vals .x22)
    let retCall : Word := (wlhB + 164 : Word) + 4
    cpsTripleWithin 383
      (wlhB + BitVec.ofNat 64 (4 * (1 + wlhFrame.length)))
      (wlhB + BitVec.ofNat 64 (4 * (1 + wlhFrame.length + wlhBody.length)))
      enableFullCode
      (((.x2 : Reg) ↦ᵣ newSp) ** regsAt wlhFrame vals **
        frameSlotsSaved wlhFrame newSp vals **
        wlhHitCallerPre newSp v5 v6 secPtr secLen hashPtr outOff outLen
          offOld lenOld w7 w15 w16 w17 w28 w29 w30 w31
          nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss)
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt wlhFrame **
        frameSlotsSaved wlhFrame newSp vals **
        wlhHitCallerPost newSp retCall s hashPtr outOff outLen secPtr secLen
          (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss) := by
  intro s retCall
  rw [wlhFrame_length, wlhBody_length]
  simp only [show 4 * (1 + 8) = 36 from rfl, show 4 * (1 + 8 + 136) = 580 from rfl]
  have core := wlhHit_body_core newSp vals v5 v6
    (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20)
    secPtr secLen hashPtr outOff outLen offOld lenOld
    w7 w15 w16 w17 w28 w29 w30 w31
    nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss
    halignH hovH hvalidR hvalidH
  refine cpsTripleWithin_weaken (fun h hp => ?pre) (fun h hq => ?post) core
  case pre =>
    rw [regsAt_wlhFrame_hit] at hp
    dsimp [wlhHitCallerPre, wlhHitBodyF, wlhEnNestedStack, wlhHitAregs,
      wlhHitCells, hitHashBytes, hitCells] at hp ⊢
    xperm_chunked hp
  case post =>
    rw [regsOwnAt_wlhFrame_hit]
    have hq1 : (wlhHitBodyExit newSp retCall s hashPtr outOff outLen secPtr secLen
        (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss
        (frameSlotsSaved wlhFrame newSp vals)) h := hq
    dsimp [wlhHitBodyExit, wlhHitArmF, wlhHitIdxSaved, indexedSavedVals, s,
      retCall] at hq1
    have hq2 : (((.x1 : Reg) ↦ᵣ retCall) **
        ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ secLen) **
        ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOff) **
        ((.x20 : Reg) ↦ᵣ outLen) ** ((.x21 : Reg) ↦ᵣ vals .x21) **
        ((.x22 : Reg) ↦ᵣ vals .x22) **
        (((.x2 : Reg) ↦ᵣ newSp) ** frameSlotsSaved wlhFrame newSp vals **
          wlhHitCallerPost newSp retCall s hashPtr outOff outLen secPtr secLen
            (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss)) h := by
      dsimp [wlhHitCallerPost, wlhHitIdxSaved, indexedSavedVals, s, retCall]
      xperm_chunked hq1
    have hq3 := ent_own8_hit .x1 .x8 .x9 .x18 .x19 .x20 .x21 .x22
      retCall secPtr secLen hashPtr outOff outLen (vals .x21) (vals .x22) _ h hq2
    dsimp [wlhHitCallerPost, wlhHitIdxSaved, indexedSavedVals, s, retCall] at hq3 ⊢
    xperm_chunked hq3

/-- **Whole-routine machine triple, `enable = 1` hit arm.** Fuel 402 =
    1 + 8 + 383 + 8 + 1 + 1.

    Domain (SAY SO): `widx_enabled = 1`, `widx_section_ptr = a0`,
    `widx_section_len = a1` (both free but matched), `widx_count = 1`, and the
    sole `widx_records` record's 32-byte hash equals the target
    (`coverHitHash`). Post: `a0 = 0`, the caller's out cells hold
    `(hitOffW, hitLenW) = (0, 32)`, `lookup_calls`/`indexed_calls`/
    `indexed_hits` each bumped by one, the linear counters and
    `indexed_misses` untouched, the callee-saved registers restored and the
    `sp` round-trip closed.

    NOT the general hit path: `widx_count = 1` only. -/
theorem witness_lookup_by_hash_spec_within_enabled_one_hit
    (sp0 ret : Word) (vals : Reg → Word)
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (hret : vals .x1 = ret)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    let newSp := sp0 + signExtend12 (-64 : BitVec 12)
    let s := wlhHitIdxSaved (vals .x1) secPtr secLen hashPtr outOff outLen
      (vals .x21) (vals .x22)
    let retCall : Word := (wlhB + 164 : Word) + 4
    cpsTripleWithin 402 wlhB ret enableFullCode
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wlhFrame vals **
        frameSlotsOwn wlhFrame newSp **
        wlhHitCallerPre newSp v5 v6 secPtr secLen hashPtr outOff outLen
          offOld lenOld w7 w15 w16 w17 w28 w29 w30 w31
          nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss)
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wlhFrame vals **
        frameSlotsSaved wlhFrame newSp vals **
        wlhHitCallerPost newSp retCall s hashPtr outOff outLen secPtr secLen
          (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss) := by
  intro newSp s retCall
  set spC : Word := sp0 + signExtend12 (-64 : BitVec 12)
  set sSaved := wlhHitIdxSaved (vals .x1) secPtr secLen hashPtr outOff outLen
    (vals .x21) (vals .x22)
  set rc : Word := (wlhB + 164 : Word) + 4
  have hbody := wlhHit_body_abi spC vals v5 v6 secPtr secLen hashPtr outOff outLen
    offOld lenOld w7 w15 w16 w17 w28 w29 w30 w31
    nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss
    halignH hovH hvalidR hvalidH
  have hpreF := wlhHitCallerPre_pcFree spC v5 v6 secPtr secLen hashPtr outOff outLen
    offOld lenOld w7 w15 w16 w17 w28 w29 w30 w31
    nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss
  have hpostF := wlhHitCallerPost_pcFree spC rc sSaved hashPtr outOff outLen
    secPtr secLen (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss
  have h := abiFrame_spec_own wlhB sp0 ret (-64 : BitVec 12) (64 : BitVec 12)
    wlhFrame (0 : BitVec 12)
    [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12)),
     (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)), (.x21, (48 : BitVec 12)),
     (.x22, (56 : BitVec 12))]
    vals wlhBody 383
    (wlhHitCallerPre spC v5 v6 secPtr secLen hashPtr outOff outLen
      offOld lenOld w7 w15 w16 w17 w28 w29 w30 w31
      nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss)
    (wlhHitCallerPost spC rc sSaved hashPtr outOff outLen secPtr secLen
      (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss)
    enableFullCode rfl (by decide) (by decide)
    (by rw [wlh_abiFrame_byte_tie]; decide)
    hret halign (sext_frameRestore _ _ _ (by decide))
    hpreF hpostF
    (by
      rw [wlh_abiFrame_byte_tie]
      intro a i hi
      exact wlh_in_enableFull a i (by simpa [wlhCr] using hi))
    hbody
  rw [wlhFrame_length] at h
  change cpsTripleWithin 402 wlhB ret enableFullCode
    (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wlhFrame vals **
      frameSlotsOwn wlhFrame spC **
      wlhHitCallerPre spC v5 v6 secPtr secLen hashPtr outOff outLen
        offOld lenOld w7 w15 w16 w17 w28 w29 w30 w31
        nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss)
    (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wlhFrame vals **
      frameSlotsSaved wlhFrame spC vals **
      wlhHitCallerPost spC rc sSaved hashPtr outOff outLen secPtr secLen
        (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss) at h
  simpa [newSp, s, retCall, spC, sSaved, rc] using h

/-! ## §8  Non-vacuity guard (partial)

    ⚠️ SAY SO: this PR does **not** exhibit a `MachineState` model of
    `wlhHitCallerPre` the way `WitnessLookupByHashIndexedOneHitSat` does for the
    callee's pre (#12193). What is checked here is the aliasing failure mode
    that would make the pre unsatisfiable for free: the one `.data` cell this
    arm adds to the parent's footprint (`wlh_indexed_hits`) is distinct from
    every other cell the pre owns, including the two `widx_records` dwords the
    callee writes. -/
theorem hit_cells_distinct :
    IdxHitLoc ≠ CallsLoc ∧ IdxHitLoc ≠ WidxEnLoc ∧ IdxHitLoc ≠ SecPtrLoc ∧
    IdxHitLoc ≠ SecLenLoc ∧ IdxHitLoc ≠ WidxCountLoc ∧
    IdxHitLoc ≠ IdxCallsLoc ∧ IdxHitLoc ≠ IdxMissLoc ∧
    IdxHitLoc ≠ LinCallsLoc ∧ IdxHitLoc ≠ LinLastLoc ∧
    IdxHitLoc ≠ LinMaxLoc ∧ IdxHitLoc ≠ LinMissLoc ∧
    IdxHitLoc ≠ hitOffAddr ∧ IdxHitLoc ≠ hitLenAddr := by
  unfold IdxHitLoc CallsLoc WidxEnLoc SecPtrLoc SecLenLoc IdxCallsLoc IdxMissLoc
    LinCallsLoc LinLastLoc LinMaxLoc LinMissLoc
  decide

end EvmAsm.Codegen.WitnessLookupByHashSpec
