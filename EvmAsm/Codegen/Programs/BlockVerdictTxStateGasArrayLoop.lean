/-
  Loop body + induction for `block_verdict_tx_state_gas_array` (a4gbr).

  Index invariant at `LoopGuard` (B+128): after `i` successful iterations the
  pure prefix `∀ j < i, out[j] = cell j` holds and regs match `LoopInv`.

  Loop-site `bgv_u32le` calls load at `txBase + 4*i`, which is only 8-aligned
  for even `i`. The proven `bgvFlat_spec` needs `Region.wf` (8-align base), so
  loop calls take a named `BgvOffsetAssumed` hyp (discharge: ambient
  `bytesRegion_lbu_within` composition; residual if not closed in PR-1).
  Intrinsic/teer stay under `ArrayCalleeAssumptions` (fable2 discharge).
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayHeader
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthSpec
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom)

local macro "bvt_pcf" : tactic => `(tactic|
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_regOwns _
    | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _
    | exact pcFree_wordArray _ _
    | exact pcFree_wordArrayFrom _ _ _
    | exact pcFree_emp
    | exact pcFree_pure
    | unfold payload; skip
    | unfold savedFrame; skip
    | unfold scratchRegs; skip)

/-! ## Offset-general bgv contract (loop sites)

    Header call uses proven `bgvFlat_spec` (aligned `txBase`). Loop sites pass
    `a0 = txBase + 4*i` which may be only 4-aligned; this hyp is the honest
    modular slot until an ambient-region LBU composition discharges it.
-/

/-- Assumed flat contract for `bgv_u32le` reading `leU32 bs off` from an
    ambient 8-aligned `bytesRegion regionBase bs` with `a0 = regionBase+off`. -/
structure BgvOffsetAssumed (cr : CodeReq) where
  success_flat :
    ∀ (ret loadPtr regionBase : Word) (bs : List (BitVec 8)) (off : Nat),
      (ret &&& ~~~(1 : Word)) = ret →
      loadPtr = regionBase + BitVec.ofNat 64 off →
      off + 4 ≤ bs.length →
      regionBase.toNat % 8 = 0 →
      regionBase.toNat + off + 3 < 2 ^ 64 →
      (∀ k, k < 4 →
        isValidByteAccess (regionBase + BitVec.ofNat 64 (off + k)) = true) →
      cpsTripleWithin nBgvSteps Bgv ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ loadPtr) ** regOwns bgvScratch **
          bytesRegion regionBase bs)
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ leU32 bs off) ** regOwns bgvScratch **
          bytesRegion regionBase bs)

/-! ## Pure prefix for the value-level loop invariant -/

def prefixOk (teer : TeerApplied) (txs : List (List (BitVec 8)))
    (balBytes : List (BitVec 8)) (chainId : Nat) (balEnabled : Bool)
    (outVals : List Nat) (i : Nat) : Prop :=
  ∀ j, j < i →
    j < outVals.length ∧ j < txs.length ∧
    outVals[j]! = txStateGasCell teer txs[j]! balBytes chainId (j + 1) balEnabled

theorem prefixOk_zero (teer : TeerApplied) (txs : List (List (BitVec 8)))
    (balBytes : List (BitVec 8)) (chainId : Nat) (balEnabled : Bool)
    (outVals : List Nat) :
    prefixOk teer txs balBytes chainId balEnabled outVals 0 := by
  intro j hj; exact False.elim (Nat.not_lt_zero j hj)

theorem prefixOk_succ (teer : TeerApplied) (txs : List (List (BitVec 8)))
    (balBytes : List (BitVec 8)) (chainId : Nat) (balEnabled : Bool)
    (outVals : List Nat) (i : Nat)
    (hpre : prefixOk teer txs balBytes chainId balEnabled outVals i)
    (hi : i < outVals.length) (htx : i < txs.length)
    (hcell : outVals[i]! =
      txStateGasCell teer txs[i]! balBytes chainId (i + 1) balEnabled) :
    prefixOk teer txs balBytes chainId balEnabled outVals (i + 1) := by
  intro j hj
  rcases (by omega : j < i ∨ j = i) with hlt | heq
  · exact hpre j hlt
  · subst heq; exact ⟨hi, htx, hcell⟩

/-! ## Loop step budget (over-approx; mono) -/

/-- One iteration: guard fall-through + 2×bgv + intrinsic + optional teer +
    store + i++ + back-edge. Fuel pad covers both bal branches. -/
def nIterSteps : Nat :=
  1 + (2 + (1 + nBgvSteps)) + (2 + (1 + nBgvSteps)) +
    (5 + (1 + nIntrinsicSteps)) + (1 + (7 + (1 + nTeerSteps)) + 6) + 2

def nLoopSteps : Nat → Nat
  | 0     => 1 + 15  -- guard taken + status0 + epilogue lower bound
  | r + 1 => nIterSteps + nLoopSteps r

/-! ## Guard taken: i = n → status-ok entry (LI a0,0 @ B+296) -/

abbrev StatusOk : Word := B + 296

set_option maxRecDepth 8000 in
/-- Loop guard taken when `i = n` (both regs hold `nW`): land at StatusOk,
    preserving the full `LoopInv` footprint. -/
theorem bvtGuardTaken (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n : Nat)
    (hnW : nW = BitVec.ofNat 64 n) :
    cpsTripleWithin 1 LoopGuard StatusOk bvtCode
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes balEnabled n)
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes balEnabled n) := by
  unfold LoopInv
  -- Reshape so BEQ focus sees x21 = nW = x20 (via hnW).
  rw [hnW]
  set nWord : Word := BitVec.ofNat 64 n
  have hbr := beq_spec_gen_within .x21 .x20 (168 : BitVec 13) nWord nWord LoopGuard
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B LoopGuard bvtProg 32
      (.BEQ .x21 .x20 (168 : BitVec 13))
      (by simp only [LoopGuard]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr
  have htk := cpsBranchWithin_takenStripPure2 hbrC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LoopGuard + signExtend13 (168 : BitVec 13) = StatusOk := by
    simp only [LoopGuard, StatusOk]
    rw [show signExtend13 (168 : BitVec 13) = (168 : Word) from by decide]
    bv_omega
  rw [hpc] at htk
  have hF :
      (((.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ nWord) ** (.x19 ↦ᵣ outBase) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) **
          regOwn .x1 ** regOwn .x22 ** regOwn .x23 ** regOwn .x27 **
          savedFrame spC csaved **
          payload txBase outBase balBase txBlob outVals balBytes balEnabled **
          scratchRegs) : Assertion).pcFree := by
    unfold payload savedFrame scratchRegs
    cases balEnabled <;> bvt_pcf
  have htkF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nWord) ** (.x19 ↦ᵣ outBase) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) **
      regOwn .x1 ** regOwn .x22 ** regOwn .x23 ** regOwn .x27 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      scratchRegs)
    hF htk
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) htkF

/-! ## Guard fall-through: i ≠ n → body entry at B+132 -/

abbrev LoopBody : Word := B + 132

set_option maxRecDepth 8000 in
/-- Loop guard not-taken when `i ≠ n`: fall through to body entry, preserving
    `LoopInv` (index still `i`). -/
theorem bvtGuardNtaken (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (i : Nat)
    (hiW : BitVec.ofNat 64 i ≠ nW) :
    cpsTripleWithin 1 LoopGuard LoopBody bvtCode
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes balEnabled i)
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes balEnabled i) := by
  unfold LoopInv
  set iWord : Word := BitVec.ofNat 64 i
  have hbr := beq_spec_gen_within .x21 .x20 (168 : BitVec 13) iWord nW LoopGuard
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B LoopGuard bvtProg 32
      (.BEQ .x21 .x20 (168 : BitVec 13))
      (by simp only [LoopGuard]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hrest).2 hiW)
  have hpc : LoopGuard + 4 = LoopBody := by
    simp only [LoopGuard, LoopBody]; bv_omega
  rw [hpc] at hnt
  have hF :
      (((.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) **
          regOwn .x1 ** regOwn .x22 ** regOwn .x23 ** regOwn .x27 **
          savedFrame spC csaved **
          payload txBase outBase balBase txBlob outVals balBytes balEnabled **
          scratchRegs) : Assertion).pcFree := by
    unfold payload savedFrame scratchRegs
    cases balEnabled <;> bvt_pcf
  have hntF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) **
      regOwn .x1 ** regOwn .x22 ** regOwn .x23 ** regOwn .x27 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      scratchRegs)
    hF hnt
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hntF

/-! ## Success-path iteration static facts

    One successful iteration under well-formed SSZ offset-table hyps. Fail
    branches (status 2/3) are not claimed here — the top theorem's success
    arm requires `IterOk` for every `i < n`.
-/

/-- Static facts for a successful body iteration at index `i`. -/
structure IterOk (txBlob : List (BitVec 8)) (n i : Nat) where
  hi : i < n
  hNBound : n < 2 ^ 62
  hLenBound : txBlob.length < 2 ^ 64
  /-- Start offset word = leU32 at byte offset `4*i`. -/
  startW : Word
  hStart : startW = leU32 txBlob (4 * i)
  /-- End offset: next table entry, or body length when last. -/
  endW : Word
  hEnd : endW =
    if i + 1 = n then BitVec.ofNat 64 txBlob.length
    else leU32 txBlob (4 * (i + 1))
  hStartOff : 4 * i + 4 ≤ txBlob.length
  hEndOff : i + 1 = n ∨ 4 * (i + 1) + 4 ≤ txBlob.length
  hStartGeTable : (n * 4 : Nat) ≤ startW.toNat
  hStartLeLen : startW.toNat ≤ txBlob.length
  hEndGeStart : startW.toNat ≤ endW.toNat
  hEndLeLen : endW.toNat ≤ txBlob.length
  /-- Region base stays in range for LBU loads at `txBase+4*i`. -/
  hNoWrap : ∀ (base : Word), base.toNat % 8 = 0 →
    base.toNat + 4 * i + 3 < 2 ^ 64
  hValid : ∀ (base : Word) (k : Nat), k < 4 →
    isValidByteAccess (base + BitVec.ofNat 64 (4 * i + k)) = true
  /-- Same for next table entry when not last. -/
  hNoWrapNext : i + 1 = n ∨ ∀ (base : Word), base.toNat % 8 = 0 →
    base.toNat + 4 * (i + 1) + 3 < 2 ^ 64
  hValidNext : i + 1 = n ∨ ∀ (base : Word) (k : Nat), k < 4 →
    isValidByteAccess (base + BitVec.ofNat 64 (4 * (i + 1) + k)) = true

abbrev LinkLoopBgv1 : Word := B + 144
abbrev LinkLoopBgv2 : Word := B + 180

abbrev loopBgv1JalOff : BitVec 21 :=
  jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_tx_state_gas_array + 140)

abbrev loopBgv2JalOff : BitVec 21 :=
  jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_tx_state_gas_array + 176)

/-- Pure: `ofNat i <<< 2 = ofNat (4*i)` when `i < 2^62`. -/
theorem slli2_ofNat (i : Nat) (hi : i < 2 ^ 62) :
    BitVec.ofNat 64 i <<< (2 : Nat) = BitVec.ofNat 64 (4 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hi' : i < 2 ^ 64 := by omega
  have h4i : 4 * i < 2 ^ 64 := by
    have : i * 4 < 2 ^ 62 * 4 := Nat.mul_lt_mul_of_pos_right hi (by decide)
    omega
  rw [Nat.mod_eq_of_lt hi', Nat.shiftLeft_eq, show 2 ^ (2 : Nat) = 4 from rfl,
    Nat.mod_eq_of_lt h4i]
  omega

/-- Caller-private frame across loop-site bgv (LoopInv s-regs + out/BAL;
    clobberable x22/x23/x27 ride as regOwn). -/
def loopBgvFrame (spC txBase outBase balBase chainIdW nW iW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  regOwn .x22 ** regOwn .x23 **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  savedFrame spC csaved **
  wordArray outBase outVals **
  (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
  (.x0 ↦ᵣ (0 : Word))

theorem loopBgvFrame_pcFree (spC txBase outBase balBase chainIdW nW iW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) :
    (loopBgvFrame spC txBase outBase balBase chainIdW nW iW csaved
      txBlob outVals balBytes balEnabled).pcFree := by
  unfold loopBgvFrame savedFrame
  cases balEnabled <;>
    repeat' first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_wordArray _ _
      | exact pcFree_emp

/-! ## Iteration start: SLLI/ADD + loop-site bgv + MV x22 (instr 33–36) -/

abbrev AfterStartBgv : Word := B + 148

/-- Pack owned t0–t2 + s-temps + a-temps into `regOwns bgvScratch`. -/
private theorem pack_loop_bgvScratch :
    ∀ h, ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17) h) →
      (regOwns bgvScratch) h := by
  intro h hp
  simp only [bgvScratch, regOwns_cons, regOwns_nil, sepConj_emp_right']
  exact hp

/-- Pack `regIs x5` + owned temps into `regOwns bgvScratch` (Header-style). -/
private theorem pack_loop_bgvScratch_is (v5 : Word) :
    ∀ h, (((.x5 ↦ᵣ v5) ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17) h) →
      (regOwns bgvScratch) h := by
  intro h hp
  exact pack_loop_bgvScratch h
    (sepConj_mono (regIs_to_regOwn .x5 v5) (fun _ hh => hh) h hp)

/-- `loopBgvFrame` after MV x22 (x22 pinned, not regOwn). -/
private def loopBgvFrameAfterMv (spC txBase outBase balBase chainIdW nW iW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (startW : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** regOwn .x23 **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  savedFrame spC csaved **
  wordArray outBase outVals **
  (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
  (.x0 ↦ᵣ (0 : Word))

/-- Ambient across SLLI/ADD: everything except focus x5/x8/x10/x21. -/
private def setupFrame (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (old1 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) **
  (.x1 ↦ᵣ old1) ** regOwn .x22 ** regOwn .x23 ** regOwn .x27 **
  savedFrame spC csaved **
  payload txBase outBase balBase txBlob outVals balBytes balEnabled **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

private theorem setupFrame_pcFree (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (old1 : Word) :
    (setupFrame spC txBase outBase balBase chainIdW nW csaved
      txBlob outVals balBytes balEnabled old1).pcFree := by
  unfold setupFrame savedFrame payload
  cases balEnabled <;>
    repeat' first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_wordArray _ _
      | exact pcFree_emp

/-- Local pcFree for framed loop atoms. -/
local macro "bvt_pcf" : tactic =>
  `(tactic| repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_regOwns _
    | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _
    | exact pcFree_wordArray _ _
    | exact pcFree_emp
    | exact pcFree_pure)

set_option maxRecDepth 8000 in
/-- Loop-site start: SLLI/ADD + bgv under `BgvOffsetAssumed` + MV x22
    (instr 33–36). Lands at AfterStartBgv with `x22 = x10 = leU32(4*i)`. -/
theorem bvtIterStartBgv (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (old1 old5 old10 : Word)
    (hbgv : BgvOffsetAssumed fullCode)
    (hok : IterOk txBlob n i)
    (htxAlign : txBase.toNat % 8 = 0) :
    let iW := BitVec.ofNat 64 i
    let startW := leU32 txBlob (4 * i)
    cpsTripleWithin (2 + (1 + nBgvSteps) + 1) LoopBody AfterStartBgv fullCode
      ((.x8 ↦ᵣ txBase) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ old10) **
        setupFrame spC txBase outBase balBase chainIdW nW csaved
          txBlob outVals balBytes balEnabled old1)
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x10 ↦ᵣ startW) **
        regOwns bgvScratch **
        bytesRegion txBase txBlob **
        loopBgvFrameAfterMv spC txBase outBase balBase chainIdW nW iW csaved
          txBlob outVals balBytes balEnabled startW) := by
  intro iW startW
  let loadPtr := txBase + BitVec.ofNat 64 (4 * i)
  have hiBound : i < 2 ^ 62 := Nat.lt_trans hok.hi hok.hNBound
  have hslli_pure := slli2_ofNat i hiBound
  -- [33] SLLI x5, x21, 2
  have e33 := slli_spec_gen_within .x5 .x21 old5 iW (2 : BitVec 6)
    LoopBody (by decide)
  rw [show (2 : BitVec 6).toNat = 2 from by decide, hslli_pure] at e33
  have e33C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B LoopBody bvtProg 33
      (.SLLI .x5 .x21 (2 : BitVec 6))
      (by simp only [LoopBody]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e33
  have e33F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x10 ↦ᵣ old10))
    (by apply pcFree_sepConj <;> exact pcFree_regIs) e33C
  -- [34] ADD x10, x8, x5
  have e34 := add_spec_gen_within .x10 .x8 .x5 txBase (BitVec.ofNat 64 (4 * i))
    old10 (B + 136) (by decide)
  have e34C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 136) bvtProg 34
      (.ADD .x10 .x8 .x5)
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e34
  have e34F := cpsTripleWithin_frameR ((.x21 ↦ᵣ iW)) pcFree_regIs e34C
  have hsetup0 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e33F e34F
  have hsetupF := cpsTripleWithin_frameR
    (setupFrame spC txBase outBase balBase chainIdW nW csaved
      txBlob outVals balBytes balEnabled old1)
    (setupFrame_pcFree _ _ _ _ _ _ _ _ _ _ _ _) hsetup0
  have hsetupC := cpsTripleWithin_extend_code bvt_mono hsetupF
  -- Reshape setup post → call pre (pack x5 + temps into bgvScratch)
  have hsetup' : cpsTripleWithin 2 LoopBody (B + 140) fullCode
      ((.x8 ↦ᵣ txBase) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ old10) **
        setupFrame spC txBase outBase balBase chainIdW nW csaved
          txBlob outVals balBytes balEnabled old1)
      ((.x1 ↦ᵣ old1) **
        (.x10 ↦ᵣ loadPtr) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        loopBgvFrame spC txBase outBase balBase chainIdW nW iW csaved
          txBlob outVals balBytes balEnabled) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_ hsetupC
    intro h hq
    have hq1 :
        (((.x5 ↦ᵣ BitVec.ofNat 64 (4 * i)) ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17) **
          ((.x1 ↦ᵣ old1) ** (.x10 ↦ᵣ loadPtr) ** bytesRegion txBase txBlob **
            loopBgvFrame spC txBase outBase balBase chainIdW nW iW csaved
              txBlob outVals balBytes balEnabled)) h := by
      unfold setupFrame payload at hq
      unfold loopBgvFrame
      xperm_hyp hq
    have hq2 :=
      sepConj_mono (pack_loop_bgvScratch_is (BitVec.ofNat 64 (4 * i)))
        (fun _ hh => hh) h hq1
    xperm_hyp hq2
  -- Bgv call under BgvOffsetAssumed
  have hflat := hbgv.success_flat LinkLoopBgv1 loadPtr txBase txBlob (4 * i)
    (by show LinkLoopBgv1 &&& ~~~(1 : Word) = LinkLoopBgv1; decide)
    rfl hok.hStartOff htxAlign (hok.hNoWrap txBase htxAlign)
    (fun k hk => hok.hValid txBase k hk)
  have hflatF := cpsTripleWithin_frameR
    (loopBgvFrame spC txBase outBase balBase chainIdW nW iW csaved
      txBlob outVals balBytes balEnabled)
    (loopBgvFrame_pcFree _ _ _ _ _ _ _ _ _ _ _ _) hflat
  have hcallee : cpsTripleWithin nBgvSteps Bgv LinkLoopBgv1 fullCode
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        ((.x10 ↦ᵣ loadPtr) ** regOwns bgvScratch **
          bytesRegion txBase txBlob **
          loopBgvFrame spC txBase outBase balBase chainIdW nW iW csaved
            txBlob outVals balBytes balEnabled))
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        ((.x10 ↦ᵣ startW) ** regOwns bgvScratch **
          bytesRegion txBase txBlob **
          loopBgvFrame spC txBase outBase balBase chainIdW nW iW csaved
            txBlob outVals balBytes balEnabled)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hflatF
  have hcall : cpsTripleWithin (1 + nBgvSteps) (B + 140) LinkLoopBgv1 fullCode
      ((.x1 ↦ᵣ old1) **
        (.x10 ↦ᵣ loadPtr) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        loopBgvFrame spC txBase outBase balBase chainIdW nW iW csaved
          txBlob outVals balBytes balEnabled)
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x10 ↦ᵣ startW) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        loopBgvFrame spC txBase outBase balBase chainIdW nW iW csaved
          txBlob outVals balBytes balEnabled) := by
    have h0 := callWithin_spec (B + 140) Bgv old1 loopBgv1JalOff nBgvSteps
      (by show (B + 140) + signExtend21 loopBgv1JalOff = Bgv; decide)
      (fun a off hi => bvt_mono a off
        (CodeReq.ofProg_mem_at B (B + 140) bvtProg 35
          (.JAL .x1 loopBgv1JalOff) (by bv_omega)
          (by rw [bvt_length]; decide) rfl
          (by rw [bvt_length]; decide) a off hi))
      (by
        apply pcFree_sepConj
        · exact pcFree_regIs
        · apply pcFree_sepConj
          · exact pcFree_regOwns _
          · apply pcFree_sepConj
            · exact bytesRegion_pcFree _ _
            · exact loopBgvFrame_pcFree _ _ _ _ _ _ _ _ _ _ _ _)
      hcallee
    rw [show (B + 140 + 4 : Word) = LinkLoopBgv1 from by
      simp only [LinkLoopBgv1]; bv_omega] at h0
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0
  -- [36] MV x22, x10  (peel regOwn x22 from loopBgvFrame)
  have e36Own : cpsTripleWithin 1 LinkLoopBgv1 AfterStartBgv fullCode
      (((.x1 ↦ᵣ LinkLoopBgv1) **
          (.x10 ↦ᵣ startW) ** regOwns bgvScratch **
          bytesRegion txBase txBlob **
          ((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            regOwn .x23 **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            wordArray outBase outVals **
            (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
            (.x0 ↦ᵣ (0 : Word)))) **
        regOwn .x22)
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x10 ↦ᵣ startW) **
        regOwns bgvScratch **
        bytesRegion txBase txBlob **
        loopBgvFrameAfterMv spC txBase outBase balBase chainIdW nW iW csaved
          txBlob outVals balBytes balEnabled startW) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x22) (fun o22 => ?_)
    have e36 := mv_spec_gen_within .x22 .x10 startW o22 LinkLoopBgv1 (by decide)
    have e36C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at B LinkLoopBgv1 bvtProg 36
        (.MV .x22 .x10)
        (by simp only [LinkLoopBgv1]; bv_omega)
        (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide)) e36
    have e36F := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word)))
      (by unfold savedFrame; cases balEnabled <;> bvt_pcf) e36C
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        unfold loopBgvFrameAfterMv
        xperm_hyp hq)
      (cpsTripleWithin_extend_code bvt_mono e36F)
  -- Compose setup' ;; call ;; mv
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsetup' hcall
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      unfold loopBgvFrame at hp
      xperm_hyp hp) c01 e36Own
  change cpsTripleWithin (2 + (1 + nBgvSteps) + 1) LoopBody AfterStartBgv fullCode
    _ _ at c02
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c02

/-! ## Span checks after start bgv (instr 37–39) -/

abbrev AfterSpanChecks : Word := B + 160

/-- Pure: `¬ ult startW tableW` when `n*4 ≤ startW.toNat` and `tableW = ofNat (4*n)`. -/
private theorem not_ult_start_table (startW tableW : Word) (n : Nat)
    (htab : tableW = BitVec.ofNat 64 (4 * n)) (hNBound : n < 2 ^ 62)
    (hGe : (n * 4 : Nat) ≤ startW.toNat) :
    ¬ (BitVec.ult startW tableW = true) := by
  simp only [BitVec.ult, decide_eq_true_eq, not_lt, htab, BitVec.toNat_ofNat]
  have hn4 : 4 * n < 2 ^ 64 := by
    have : n * 4 < 2 ^ 62 * 4 := Nat.mul_lt_mul_of_pos_right hNBound (by decide)
    omega
  rw [Nat.mod_eq_of_lt hn4]
  omega

/-- Pure: `¬ ult lenW startW` when `startW.toNat ≤ len`. -/
private theorem not_ult_len_start (txLenW startW : Word) (txLen : Nat)
    (htxLenW : txLenW = BitVec.ofNat 64 txLen)
    (hLe : startW.toNat ≤ txLen) (hLenBound : txLen < 2 ^ 64) :
    ¬ (BitVec.ult txLenW startW = true) := by
  simp only [BitVec.ult, decide_eq_true_eq, not_lt]
  rw [htxLenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLenBound]
  exact hLe

set_option maxRecDepth 8000 in
/-- Instr 37–39 under `IterOk`: SLLI 4n; BLTU start≥4n; BLTU start≤len.
    Lands at AfterSpanChecks (B+160) with x5=4n, x22=startW. -/
theorem bvtIterSpanChecks (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (startW : Word)
    (hok : IterOk txBlob n i)
    (hnW : nW = BitVec.ofNat 64 n)
    (hStart : startW = leU32 txBlob (4 * i)) :
    let iW := BitVec.ofNat 64 i
    let tableW := BitVec.ofNat 64 (4 * n)
    cpsTripleWithin 3 AfterStartBgv AfterSpanChecks bvtCode
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x10 ↦ᵣ startW) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x10 ↦ᵣ startW) **
        (.x5 ↦ᵣ tableW) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word))) := by
  intro iW tableW
  have hslli_n := slli2_ofNat n hok.hNBound
  have hnW_shift : nW <<< (2 : Nat) = tableW := by
    rw [hnW, hslli_n]
  -- [37] SLLI x5, x20, 2
  have e37 :
      cpsTripleWithin 1 AfterStartBgv (AfterStartBgv + 4) bvtCode
        ((.x20 ↦ᵣ nW) ** regOwn .x5)
        ((.x20 ↦ᵣ nW) ** (.x5 ↦ᵣ tableW)) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5) (fun o5 => ?_)
    have h0 := slli_spec_gen_within .x5 .x20 o5 nW (2 : BitVec 6)
      AfterStartBgv (by decide)
    rw [show (2 : BitVec 6).toNat = 2 from by decide, hnW_shift] at h0
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at B AfterStartBgv bvtProg 37
        (.SLLI .x5 .x20 (2 : BitVec 6))
        (by simp only [AfterStartBgv]; bv_omega)
        (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide)) h0
  have e37F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ startW) **
      regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e37
  -- [38] BLTU x22, x5 — ntaken (rs1 rs2 offset v1 v2 addr)
  have hbr38 := bltu_spec_gen_within .x22 .x5 (152 : BitVec 13) startW tableW
    (B + 152)
  have hbr38C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 152) bvtProg 38
      (.BLTU .x22 .x5 (152 : BitVec 13))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr38
  have hStartEq : hok.startW = startW := hok.hStart.trans hStart.symm
  have h_not_ult38 : ¬ (BitVec.ult startW tableW = true) := by
    have hge : (n * 4 : Nat) ≤ startW.toNat := by
      simpa [hStartEq] using hok.hStartGeTable
    exact not_ult_start_table startW tableW n rfl hok.hNBound hge
  have hnt38 : cpsTripleWithin 1 (B + 152) (B + 156) bvtCode
      ((.x22 ↦ᵣ startW) ** (.x5 ↦ᵣ tableW))
      ((.x22 ↦ᵣ startW) ** (.x5 ↦ᵣ tableW)) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr38C (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact h_not_ult38 ((sepConj_pure_right _).1 hQ).2)
    rw [show (B + 152 + 4 : Word) = B + 156 from by bv_omega] at hnt
    exact hnt
  have e38F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ startW) **
      regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) hnt38
  -- [39] BLTU x9, x22 — ntaken
  have hbr39 := bltu_spec_gen_within .x9 .x22 (148 : BitVec 13)
    (BitVec.ofNat 64 txBlob.length) startW (B + 156)
  have hbr39C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 156) bvtProg 39
      (.BLTU .x9 .x22 (148 : BitVec 13))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr39
  have h_not_ult39 : ¬ (BitVec.ult (BitVec.ofNat 64 txBlob.length) startW = true) := by
    have hle : startW.toNat ≤ txBlob.length := by
      simpa [hStartEq] using hok.hStartLeLen
    exact not_ult_len_start _ startW txBlob.length rfl hle hok.hLenBound
  have hnt39 : cpsTripleWithin 1 (B + 156) AfterSpanChecks bvtCode
      ((.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) ** (.x22 ↦ᵣ startW))
      ((.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) ** (.x22 ↦ᵣ startW)) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr39C (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact h_not_ult39 ((sepConj_pure_right _).1 hQ).2)
    rw [show (B + 156 + 4 : Word) = AfterSpanChecks from by
      simp only [AfterSpanChecks]; bv_omega] at hnt
    exact hnt
  have e39F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x5 ↦ᵣ tableW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ startW) **
      regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) hnt39
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e37F e38F
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c01 e39F
  change cpsTripleWithin (1 + 1 + 1) AfterStartBgv AfterSpanChecks bvtCode
    _ _ at c02
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c02

/-! ## End-offset path (instr 40–47): last tx vs next-table bgv -/

abbrev AfterEndOffset : Word := B + 192
abbrev LastEndMv : Word := B + 188

/-- Pure: `ofNat i + 1 = ofNat (i+1)` when no wrap. -/
private theorem ofNat_addi1 (i : Nat) :
    BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 (i + 1) := by
  have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  rw [hse, show (1 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]

set_option maxRecDepth 8000 in
/-- Last-tx end path: `i+1 = n`. ADDI; BEQ taken; MV x23,x9 → AfterEndOffset
    with `x23 = body_len`. -/
theorem bvtIterEndLast (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (startW tableW : Word)
    (_hok : IterOk txBlob n i)
    (hLast : i + 1 = n)
    (hnW : nW = BitVec.ofNat 64 n)
    (_hStart : startW = leU32 txBlob (4 * i))
    (_htab : tableW = BitVec.ofNat 64 (4 * n)) :
    let iW := BitVec.ofNat 64 i
    let ip1W := BitVec.ofNat 64 (i + 1)
    let lenW := BitVec.ofNat 64 txBlob.length
    cpsTripleWithin 3 AfterSpanChecks AfterEndOffset bvtCode
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x10 ↦ᵣ startW) **
        (.x5 ↦ᵣ tableW) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ lenW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x10 ↦ᵣ startW) **
        (.x5 ↦ᵣ ip1W) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word))) := by
  intro iW ip1W lenW
  have hip1_eq_nW : ip1W = nW := by
    simp only [ip1W, hnW, hLast]
  -- [40] ADDI x5, x21, 1  (overwrites tableW in x5)
  have e40 :
      cpsTripleWithin 1 AfterSpanChecks (AfterSpanChecks + 4) bvtCode
        ((.x21 ↦ᵣ iW) ** (.x5 ↦ᵣ tableW))
        ((.x21 ↦ᵣ iW) ** (.x5 ↦ᵣ ip1W)) := by
    have h0 := addi_spec_gen_within .x5 .x21 tableW iW (1 : BitVec 12)
      AfterSpanChecks (by decide)
    rw [ofNat_addi1 i] at h0
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at B AfterSpanChecks bvtProg 40
        (.ADDI .x5 .x21 (1 : BitVec 12))
        (by simp only [AfterSpanChecks]; bv_omega)
        (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide)) h0
  have e40F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ startW) **
      regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e40
  -- [41] BEQ x5, x20, +24 — taken (i+1 = n)
  have hbr41 := beq_spec_gen_within .x5 .x20 (24 : BitVec 13) ip1W nW
    (B + 164)
  have hbr41C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 164) bvtProg 41
      (.BEQ .x5 .x20 (24 : BitVec 13))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr41
  have htk41 : cpsTripleWithin 1 (B + 164) LastEndMv bvtCode
      ((.x5 ↦ᵣ ip1W) ** (.x20 ↦ᵣ nW))
      ((.x5 ↦ᵣ ip1W) ** (.x20 ↦ᵣ nW)) := by
    have htk := cpsBranchWithin_takenStripPure2 hbr41C (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hQf
      exact absurd hip1_eq_nW ((sepConj_pure_right _).1 hrest).2)
    have hpc : B + 164 + signExtend13 (24 : BitVec 13) = LastEndMv := by
      simp only [LastEndMv]
      rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]
      bv_omega
    rwa [hpc] at htk
  have e41F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ startW) **
      regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) htk41
  -- [47] MV x23, x9  (args: rd rs v_rs v_rd_old)
  have e47 :
      cpsTripleWithin 1 LastEndMv AfterEndOffset bvtCode
        ((.x9 ↦ᵣ lenW) ** regOwn .x23)
        ((.x9 ↦ᵣ lenW) ** (.x23 ↦ᵣ lenW)) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x23) (fun o23 => ?_)
    have h0 := mv_spec_gen_within .x23 .x9 lenW o23 LastEndMv (by decide)
    have hpc : LastEndMv + 4 = AfterEndOffset := by
      simp only [LastEndMv, AfterEndOffset]; bv_omega
    rw [← hpc]
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at B LastEndMv bvtProg 47
        (.MV .x23 .x9)
        (by simp only [LastEndMv]; bv_omega)
        (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide)) h0
  have e47F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ startW) **
      (.x5 ↦ᵣ ip1W) ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e47
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e40F e41F
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c01 e47F
  change cpsTripleWithin (1 + 1 + 1) AfterSpanChecks AfterEndOffset bvtCode
    _ _ at c02
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c02

set_option maxRecDepth 8000 in
/-- Non-last end path: `i+1 ≠ n`. ADDI; BEQ ntaken; SLLI/ADD; bgv@LinkLoopBgv2;
    MV x23; JAL skip → AfterEndOffset with `x23 = leU32(4*(i+1))`. -/
theorem bvtIterEndNext (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (startW tableW old6 old10 : Word)
    (hbgv : BgvOffsetAssumed fullCode)
    (hok : IterOk txBlob n i)
    (hNext : i + 1 ≠ n)
    (hnW : nW = BitVec.ofNat 64 n)
    (_hStart : startW = leU32 txBlob (4 * i))
    (_htab : tableW = BitVec.ofNat 64 (4 * n))
    (htxAlign : txBase.toNat % 8 = 0) :
    let iW := BitVec.ofNat 64 i
    let endW := leU32 txBlob (4 * (i + 1))
    let lenW := BitVec.ofNat 64 txBlob.length
    cpsTripleWithin (2 + 2 + (1 + nBgvSteps) + 2) AfterSpanChecks AfterEndOffset
      fullCode
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x10 ↦ᵣ old10) **
        (.x5 ↦ᵣ tableW) ** (.x6 ↦ᵣ old6) ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkLoopBgv2) **
        (.x10 ↦ᵣ endW) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word))) := by
  intro iW endW lenW
  let ip1W : Word := BitVec.ofNat 64 (i + 1)
  let loadPtr := txBase + BitVec.ofNat 64 (4 * (i + 1))
  have hip1_ne : ip1W ≠ nW := by
    intro heq
    apply hNext
    have hi1 : i + 1 < 2 ^ 64 := by
      have := hok.hi; have := hok.hNBound; omega
    have hn : n < 2 ^ 64 := by
      have := hok.hNBound; omega
    have hEqNat : (BitVec.ofNat 64 (i + 1)).toNat = (BitVec.ofNat 64 n).toNat := by
      have := congrArg BitVec.toNat heq
      simp only [ip1W, hnW] at this
      exact this
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi1,
      Nat.mod_eq_of_lt hn] at hEqNat
    exact hEqNat
  have hEndOff : 4 * (i + 1) + 4 ≤ txBlob.length := by
    rcases hok.hEndOff with h | h
    · exact False.elim (hNext h)
    · exact h
  have hNoWrapN : txBase.toNat + 4 * (i + 1) + 3 < 2 ^ 64 := by
    rcases hok.hNoWrapNext with h | h
    · exact False.elim (hNext h)
    · exact h txBase htxAlign
  have hValidN : ∀ k, k < 4 →
      isValidByteAccess (txBase + BitVec.ofNat 64 (4 * (i + 1) + k)) = true := by
    rcases hok.hValidNext with h | h
    · exact False.elim (hNext h)
    · exact fun k hk => h txBase k hk
  have hip1_lt : i + 1 < 2 ^ 62 := by
    have := hok.hi; have := hok.hNBound; omega
  -- [40] ADDI x5, x21, 1
  have e40 :
      cpsTripleWithin 1 AfterSpanChecks (AfterSpanChecks + 4) bvtCode
        ((.x21 ↦ᵣ iW) ** (.x5 ↦ᵣ tableW))
        ((.x21 ↦ᵣ iW) ** (.x5 ↦ᵣ ip1W)) := by
    have h0 := addi_spec_gen_within .x5 .x21 tableW iW (1 : BitVec 12)
      AfterSpanChecks (by decide)
    rw [ofNat_addi1 i] at h0
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at B AfterSpanChecks bvtProg 40
        (.ADDI .x5 .x21 (1 : BitVec 12))
        (by simp only [AfterSpanChecks]; bv_omega)
        (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide)) h0
  have e40F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ old10) **
      (.x6 ↦ᵣ old6) ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e40
  -- [41] BEQ ntaken
  have hbr41 := beq_spec_gen_within .x5 .x20 (24 : BitVec 13) ip1W nW (B + 164)
  have hbr41C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 164) bvtProg 41
      (.BEQ .x5 .x20 (24 : BitVec 13))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr41
  have hnt41 : cpsTripleWithin 1 (B + 164) (B + 168) bvtCode
      ((.x5 ↦ᵣ ip1W) ** (.x20 ↦ᵣ nW))
      ((.x5 ↦ᵣ ip1W) ** (.x20 ↦ᵣ nW)) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr41C (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hrest).2 hip1_ne)
    have hpc : B + 164 + 4 = B + 168 := by bv_omega
    rwa [hpc] at hnt
  have e41F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ old10) **
      (.x6 ↦ᵣ old6) ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) hnt41
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e40F e41F
  have c01C := cpsTripleWithin_extend_code bvt_mono c01
  -- [42] SLLI x6, x5, 2
  have hslli := slli2_ofNat (i + 1) hip1_lt
  have e42 := slli_spec_gen_within .x6 .x5 old6 ip1W (2 : BitVec 6)
    (B + 168) (by decide)
  rw [show (2 : BitVec 6).toNat = 2 from by decide, hslli] at e42
  have e42C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 168) bvtProg 42
      (.SLLI .x6 .x5 (2 : BitVec 6))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e42
  have e42F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ old10) **
      regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e42C
  -- [43] ADD x10, x8, x6
  have e43 := add_spec_gen_within .x10 .x8 .x6 txBase
    (BitVec.ofNat 64 (4 * (i + 1))) old10 (B + 172) (by decide)
  have e43C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 172) bvtProg 43
      (.ADD .x10 .x8 .x6)
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e43
  have e43F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x5 ↦ᵣ ip1W) **
      regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e43C
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e42F e43F
  have c02C := cpsTripleWithin_extend_code bvt_mono c02
  -- reshape setup post → call pre (pack scratch; peel payload)
  have hsetup' : cpsTripleWithin 2 (B + 168) (B + 176) fullCode
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x10 ↦ᵣ old10) **
        (.x5 ↦ᵣ ip1W) ** (.x6 ↦ᵣ old6) ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x10 ↦ᵣ loadPtr) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_ c02C
    intro h hq
    unfold payload at hq
    have hq1 :
        (((.x5 ↦ᵣ ip1W) ** (.x6 ↦ᵣ BitVec.ofNat 64 (4 * (i + 1))) ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17) **
          ((.x1 ↦ᵣ LinkLoopBgv1) ** (.x10 ↦ᵣ loadPtr) **
            bytesRegion txBase txBlob **
            (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** regOwn .x23 **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            wordArray outBase outVals **
            (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
            (.x0 ↦ᵣ (0 : Word)))) h := by
      xperm_hyp hq
    -- x5 ** (x6 ** restTemps) → x5 ** (regOwn x6 ** restTemps)
    have hq2 :
        (((.x5 ↦ᵣ ip1W) ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17) **
          ((.x1 ↦ᵣ LinkLoopBgv1) ** (.x10 ↦ᵣ loadPtr) **
            bytesRegion txBase txBlob **
            (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** regOwn .x23 **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            wordArray outBase outVals **
            (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
            (.x0 ↦ᵣ (0 : Word)))) h := by
      refine sepConj_mono ?_ (fun _ hh => hh) h hq1
      intro h0 hp0
      -- left is x5 ** (x6 ** restTemps); convert middle x6 to regOwn
      refine sepConj_mono (fun _ => id) ?_ h0 hp0
      intro h1 hp1
      exact sepConj_mono
        (regIs_to_regOwn .x6 (BitVec.ofNat 64 (4 * (i + 1))))
        (fun _ => id) h1 hp1
    have hq3 :=
      sepConj_mono (pack_loop_bgvScratch_is ip1W)
        (fun _ hh => hh) h hq2
    xperm_hyp hq3
  -- Bgv call
  have hflat := hbgv.success_flat LinkLoopBgv2 loadPtr txBase txBlob (4 * (i + 1))
    (by show LinkLoopBgv2 &&& ~~~(1 : Word) = LinkLoopBgv2; decide)
    rfl hEndOff htxAlign hNoWrapN hValidN
  have hframe :
      (((.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
          (.x22 ↦ᵣ startW) ** regOwn .x23 **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          savedFrame spC csaved **
          wordArray outBase outVals **
          (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
          (.x0 ↦ᵣ (0 : Word))) : Assertion).pcFree := by
    unfold savedFrame; cases balEnabled <;> bvt_pcf
  have hflatF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      wordArray outBase outVals **
      (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
      (.x0 ↦ᵣ (0 : Word)))
    hframe hflat
  have hcallee : cpsTripleWithin nBgvSteps Bgv LinkLoopBgv2 fullCode
      ((.x1 ↦ᵣ LinkLoopBgv2) **
        ((.x10 ↦ᵣ loadPtr) ** regOwns bgvScratch **
          bytesRegion txBase txBlob **
          ((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** regOwn .x23 **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            wordArray outBase outVals **
            (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
            (.x0 ↦ᵣ (0 : Word)))))
      ((.x1 ↦ᵣ LinkLoopBgv2) **
        ((.x10 ↦ᵣ endW) ** regOwns bgvScratch **
          bytesRegion txBase txBlob **
          ((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** regOwn .x23 **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            wordArray outBase outVals **
            (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
            (.x0 ↦ᵣ (0 : Word))))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hflatF
  have hcall : cpsTripleWithin (1 + nBgvSteps) (B + 176) LinkLoopBgv2 fullCode
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x10 ↦ᵣ loadPtr) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkLoopBgv2) **
        (.x10 ↦ᵣ endW) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word))) := by
    have h0 := callWithin_spec (B + 176) Bgv LinkLoopBgv1 loopBgv2JalOff nBgvSteps
      (by show (B + 176) + signExtend21 loopBgv2JalOff = Bgv; decide)
      (fun a off hi => bvt_mono a off
        (CodeReq.ofProg_mem_at B (B + 176) bvtProg 44
          (.JAL .x1 loopBgv2JalOff) (by bv_omega)
          (by rw [bvt_length]; decide) rfl
          (by rw [bvt_length]; decide) a off hi))
      (by
        apply pcFree_sepConj
        · exact pcFree_regIs
        · apply pcFree_sepConj
          · exact pcFree_regOwns _
          · apply pcFree_sepConj
            · exact bytesRegion_pcFree _ _
            · exact hframe)
      hcallee
    rw [show (B + 176 + 4 : Word) = LinkLoopBgv2 from by
      simp only [LinkLoopBgv2]; bv_omega] at h0
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0
  -- [45] MV x23, x10
  have e45Own : cpsTripleWithin 1 LinkLoopBgv2 (B + 184) fullCode
      (((.x1 ↦ᵣ LinkLoopBgv2) **
          (.x10 ↦ᵣ endW) ** regOwns bgvScratch **
          bytesRegion txBase txBlob **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
          (.x22 ↦ᵣ startW) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          savedFrame spC csaved **
          wordArray outBase outVals **
          (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
          (.x0 ↦ᵣ (0 : Word))) **
        regOwn .x23)
      ((.x1 ↦ᵣ LinkLoopBgv2) **
        (.x10 ↦ᵣ endW) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x23) (fun o23 => ?_)
    have e45 := mv_spec_gen_within .x23 .x10 endW o23 LinkLoopBgv2 (by decide)
    have e45C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at B LinkLoopBgv2 bvtProg 45
        (.MV .x23 .x10)
        (by simp only [LinkLoopBgv2]; bv_omega)
        (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide)) e45
    have e45F := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ LinkLoopBgv2) **
        regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word)))
      (by unfold savedFrame; cases balEnabled <;> bvt_pcf) e45C
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code bvt_mono e45F)
  -- [46] JAL x0, +8 → AfterEndOffset
  have e46 :
      cpsTripleWithin 1 (B + 184) AfterEndOffset fullCode
        empAssertion empAssertion := by
    have h0 := jal_x0_spec_gen_within (8 : BitVec 21) (B + 184)
    have hpc : B + 184 + signExtend21 (8 : BitVec 21) = AfterEndOffset := by
      simp only [AfterEndOffset]
      rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
      bv_omega
    rw [hpc] at h0
    have hmem := CodeReq.ofProg_mem_at B (B + 184) bvtProg 46
      (.JAL .x0 (8 : BitVec 21))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)
    exact cpsTripleWithin_extend_code
      (fun a off hi => bvt_mono a off (hmem a off hi)) h0
  let ambient : Assertion :=
    (.x1 ↦ᵣ LinkLoopBgv2) **
      (.x10 ↦ᵣ endW) ** regOwns bgvScratch **
      bytesRegion txBase txBlob **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      wordArray outBase outVals **
      (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
      (.x0 ↦ᵣ (0 : Word))
  have e46F : cpsTripleWithin 1 (B + 184) AfterEndOffset fullCode
      ambient ambient := by
    have h0 := cpsTripleWithin_frameR ambient
      (by unfold ambient savedFrame; cases balEnabled <;> bvt_pcf) e46
    -- frameR gives ambient ** emp; cancel emp via equality
    exact cpsTripleWithin_weaken
      (fun h hp => by
        -- ambient → emp ** ambient
        show (empAssertion ** ambient) h
        rwa [sepConj_emp_left' ambient])
      (fun h hq => by
        -- emp ** ambient → ambient
        have hq' : (empAssertion ** ambient) h := hq
        rwa [sepConj_emp_left' ambient] at hq')
      h0
  -- Compose: c01 ;; setup' ;; call ;; mv ;; jal
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c01C hsetup'
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c03 hcall
  have c05 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c04 e45Own
  have c06 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c05 e46F
  change cpsTripleWithin
    ((1 + 1) + (2 + ((1 + nBgvSteps) + (1 + 1)))) AfterSpanChecks AfterEndOffset
    fullCode _ _ at c06
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      unfold ambient at hq
      xperm_hyp hq) c06

/-! ## End-offset span checks + intrinsic ABI setup (instr 48–53) -/

abbrev AfterEndSpan : Word := B + 216

/-- Pure: `¬ ult endW startW` when `startW.toNat ≤ endW.toNat`. -/
private theorem not_ult_end_start (startW endW : Word)
    (hGe : startW.toNat ≤ endW.toNat) :
    ¬ (BitVec.ult endW startW = true) := by
  simp only [BitVec.ult, decide_eq_true_eq, not_lt]
  omega

/-- Pure: `¬ ult lenW endW` when `endW.toNat ≤ len` and `lenW = ofNat len`. -/
private theorem not_ult_len_end (endW lenW : Word) (len : Nat)
    (hlen : lenW = BitVec.ofNat 64 len) (hLenBound : len < 2 ^ 64)
    (hLe : endW.toNat ≤ len) :
    ¬ (BitVec.ult lenW endW = true) := by
  simp only [BitVec.ult, decide_eq_true_eq, not_lt, hlen, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hLenBound]
  omega

/-- Pure: `ofNat i <<< 3 = ofNat (8*i)` when `i < 2^61`. -/
theorem slli3_ofNat (i : Nat) (hi : i < 2 ^ 61) :
    BitVec.ofNat 64 i <<< (3 : Nat) = BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hi' : i < 2 ^ 64 := by omega
  have h8i : 8 * i < 2 ^ 64 := by
    have : i * 8 < 2 ^ 61 * 8 := Nat.mul_lt_mul_of_pos_right hi (by decide)
    omega
  rw [Nat.mod_eq_of_lt hi', Nat.shiftLeft_eq, show 2 ^ (3 : Nat) = 8 from rfl,
    Nat.mod_eq_of_lt h8i]
  omega

set_option maxRecDepth 8000 in
/-- End span checks + ABI setup for intrinsic (instr 48–53).
    Lands at AfterEndSpan with a0=txBase+start, a1=end-start, a2=outBase+8*i.
    Requires `i < 2^61` so `8*i` fits in a Word (stricter than IterOk `n < 2^62`). -/
theorem bvtIterEndSpanSetup (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (startW endW old5 old10 old11 old12 : Word)
    (hok : IterOk txBlob n i)
    (hStart : startW = hok.startW)
    (hEnd : endW = hok.endW)
    (hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let lenW := BitVec.ofNat 64 txBlob.length
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    cpsTripleWithin 6 AfterEndOffset AfterEndSpan bvtCode
      ((.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
        regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word))) := by
  intro iW lenW txPtr txLenW outPtr
  -- Align IterOk start/end with concrete regs
  have hGe' : startW.toNat ≤ endW.toNat := by
    simpa [hStart, hEnd] using hok.hEndGeStart
  have hLe' : endW.toNat ≤ txBlob.length := by
    simpa [hEnd] using hok.hEndLeLen
  have hnot1 := not_ult_end_start startW endW hGe'
  have hnot2 := not_ult_len_end endW lenW txBlob.length rfl hok.hLenBound hLe'
  have hslli3 := slli3_ofNat i hi61
  -- Ambient frame atoms shared by all steps (scratch focus peels per instr)
  let ambient : Assertion :=
    (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word))
  have hAmb : ambient.pcFree := by
    unfold ambient savedFrame payload; cases balEnabled <;> bvt_pcf
  -- [48] BLTU x23, x22 ntaken  (focus x23,x22 — exclude from frame)
  have hbr48 := bltu_spec_gen_within .x23 .x22 (112 : BitVec 13) endW startW
    AfterEndOffset
  have hbr48C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B AfterEndOffset bvtProg 48
      (.BLTU .x23 .x22 (112 : BitVec 13))
      (by simp only [AfterEndOffset]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr48
  have hnt48 : cpsTripleWithin 1 AfterEndOffset (B + 196) bvtCode
      ((.x23 ↦ᵣ endW) ** (.x22 ↦ᵣ startW))
      ((.x23 ↦ᵣ endW) ** (.x22 ↦ᵣ startW)) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr48C (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hrest).2 hnot1)
    have hpc : AfterEndOffset + 4 = B + 196 := by
      simp only [AfterEndOffset]; bv_omega
    rwa [hpc] at hnt
  have e48F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) hnt48
  -- [49] BLTU x9, x23 ntaken  (focus x9,x23)
  have hbr49 := bltu_spec_gen_within .x9 .x23 (108 : BitVec 13) lenW endW (B + 196)
  have hbr49C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 196) bvtProg 49
      (.BLTU .x9 .x23 (108 : BitVec 13))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr49
  have hnt49 : cpsTripleWithin 1 (B + 196) (B + 200) bvtCode
      ((.x9 ↦ᵣ lenW) ** (.x23 ↦ᵣ endW))
      ((.x9 ↦ᵣ lenW) ** (.x23 ↦ᵣ endW)) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr49C (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hrest).2 hnot2)
    have hpc : B + 196 + 4 = B + 200 := by bv_omega
    rwa [hpc] at hnt
  have e49F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) hnt49
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e48F e49F
  -- [50] ADD x10, x8, x22  (focus x10,x8,x22)
  have e50 := add_spec_gen_within .x10 .x8 .x22 txBase startW old10 (B + 200) (by decide)
  have e50C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 200) bvtProg 50
      (.ADD .x10 .x8 .x22)
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e50
  have e50F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x5 ↦ᵣ old5) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e50C
  -- [51] SUB x11, x23, x22  (focus x11,x23,x22)
  have e51 := sub_spec_gen_within .x11 .x23 .x22 endW startW old11 (B + 204) (by decide)
  have e51C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 204) bvtProg 51
      (.SUB .x11 .x23 .x22)
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e51
  have e51F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ (txBase + startW)) ** (.x12 ↦ᵣ old12) **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e51C
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e50F e51F
  -- [52] SLLI x5, x21, 3  (focus x5,x21)
  have e52 := slli_spec_gen_within .x5 .x21 old5 iW (3 : BitVec 6) (B + 208) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide, hslli3] at e52
  have e52C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 208) bvtProg 52
      (.SLLI .x5 .x21 (3 : BitVec 6))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e52
  have e52F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ (txBase + startW)) ** (.x11 ↦ᵣ (endW - startW)) ** (.x12 ↦ᵣ old12) **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e52C
  -- [53] ADD x12, x19, x5  (focus x12,x19,x5)
  have e53 := add_spec_gen_within .x12 .x19 .x5 outBase (BitVec.ofNat 64 (8 * i))
    old12 (B + 212) (by decide)
  have e53C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 212) bvtProg 53
      (.ADD .x12 .x19 .x5)
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e53
  have e53F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ (txBase + startW)) ** (.x11 ↦ᵣ (endW - startW)) **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e53C
  have c02' := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e50F e51F
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e52F e53F
  have c12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c01 c02'
  have c13 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c12 c03
  change cpsTripleWithin ((1 + 1) + ((1 + 1) + (1 + 1))) AfterEndOffset AfterEndSpan
    bvtCode _ _ at c13
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c13

/-! ## Intrinsic call (instr 54) under IntrinsicAssumed -/

abbrev intrinsicJalOff : BitVec 21 :=
  jalOff GuestAddrs.tx_intrinsic_state_gas
    (GuestAddrs.block_verdict_tx_state_gas_array + 216)

/-- Caller-private frame across intrinsic (s-regs + start/end + saved + bal;
    ambient tx region + out cell + ABI a-regs ride in the callee footprint). -/
def loopIntrinsicFrame (spC txBase outBase balBase chainIdW nW iW
    startW endW lenW : Word)
    (csaved : Saved) (balBytes : List (BitVec 8)) (balEnabled : Bool)
    : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  savedFrame spC csaved **
  (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
  (.x0 ↦ᵣ (0 : Word))

theorem loopIntrinsicFrame_pcFree (spC txBase outBase balBase chainIdW nW iW
    startW endW lenW : Word)
    (csaved : Saved) (balBytes : List (BitVec 8)) (balEnabled : Bool) :
    (loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
      startW endW lenW csaved balBytes balEnabled).pcFree := by
  unfold loopIntrinsicFrame savedFrame
  cases balEnabled <;> bvt_pcf

set_option maxRecDepth 8000 in
/-- Intrinsic success call (instr 54) under ambient-region `IntrinsicAssumed`.
    Pre: full `bytesRegion txBase txBlob` + peeled `outPtr ↦ₘ oldOut`.
    Post: a0=0, *out=pureIntrinsicStateGasSuccess (=0), ambient tx preserved. -/
theorem bvtIterIntrinsic
    (hintr : IntrinsicAssumed fullCode)
    (spC txBase outBase balBase chainIdW nW bodyLenW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (balBytes : List (BitVec 8))
    (balEnabled : Bool) (i off len : Nat)
    (startW endW oldOut old1 : Word)
    (hentry : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hret : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hstart : startW = BitVec.ofNat 64 off)
    (hlen : off + len ≤ txBlob.length)
    (htxLen : endW - startW = BitVec.ofNat 64 len) :
    let iW := BitVec.ofNat 64 i
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    cpsTripleWithin (1 + nIntrinsicSteps) AfterEndSpan LinkIntrinsic fullCode
      ((.x1 ↦ᵣ old1) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
        bytesRegion txBase txBlob **
        (outPtr ↦ₘ oldOut) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
          startW endW bodyLenW csaved balBytes balEnabled)
      ((.x1 ↦ᵣ LinkIntrinsic) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBlob **
        (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
          startW endW bodyLenW csaved balBytes balEnabled) := by
  intro iW txPtr txLenW outPtr
  have hload : txPtr = txBase + BitVec.ofNat 64 off := by
    simp only [txPtr, hstart]
  have hlenW : txLenW = BitVec.ofNat 64 len := by
    simp only [txLenW, htxLen]
  have hflat0 := hintr.success_flat LinkIntrinsic txBase txPtr outPtr oldOut
    txBlob off len hret hload hlen
  have hflatLen : cpsTripleWithin nIntrinsicSteps hintr.entry LinkIntrinsic fullCode
      ((.x1 ↦ᵣ LinkIntrinsic) ** (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
        (.x12 ↦ᵣ outPtr) ** bytesRegion txBase txBlob **
        (outPtr ↦ₘ oldOut) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkIntrinsic) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBlob **
        (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) := by
    simpa [hlenW] using hflat0
  have hflatF := cpsTripleWithin_frameR
    (loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
      startW endW bodyLenW csaved balBytes balEnabled)
    (loopIntrinsicFrame_pcFree _ _ _ _ _ _ _ _ _ _ _ _ _) hflatLen
  have hcallee : cpsTripleWithin nIntrinsicSteps hintr.entry LinkIntrinsic fullCode
      ((.x1 ↦ᵣ LinkIntrinsic) **
        ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
          bytesRegion txBase txBlob ** (outPtr ↦ₘ oldOut) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
            startW endW bodyLenW csaved balBytes balEnabled))
      ((.x1 ↦ᵣ LinkIntrinsic) **
        ((.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBlob **
          (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
            startW endW bodyLenW csaved balBytes balEnabled)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hflatF
  have hcall := callWithin_spec AfterEndSpan hintr.entry old1 intrinsicJalOff
    nIntrinsicSteps
    (by
      rw [hentry]
      show AfterEndSpan + signExtend21 intrinsicJalOff =
        (GuestAddrs.tx_intrinsic_state_gas : Word)
      simp only [AfterEndSpan, intrinsicJalOff, B]
      decide)
    (fun a off' hi => bvt_mono a off'
      (CodeReq.ofProg_mem_at B AfterEndSpan bvtProg 54
        (.JAL .x1 intrinsicJalOff)
        (by simp only [AfterEndSpan]; bv_omega)
        (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide) a off' hi))
    (by
      unfold loopIntrinsicFrame savedFrame
      cases balEnabled <;> bvt_pcf)
    hcallee
  have hlink : AfterEndSpan + 4 = LinkIntrinsic := by
    simp only [AfterEndSpan, LinkIntrinsic]; bv_omega
  rw [hlink] at hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hcall

/-! ## Post-intrinsic bal=0 success tail (instr 55–56 + 72–73)

    a0=0 → BNE ntaken; bal=0 → BEQ taken → LoopAdvance; ADDI i++; back-edge.
    Post keeps concrete temps (convert to regOwn at LoopInv glue).
-/

abbrev AfterIntrinsicBne : Word := B + 224
abbrev LoopAdvance : Word := B + 288

/-- Caller-private footprint for the bal=0 tail (no x0/x10/x24 focus regs). -/
def bal0Rest (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balLenW startW endW iW : Word) : Assertion :=
  (.x1 ↦ᵣ LinkIntrinsic) **
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
  (.x25 ↦ᵣ balLenW) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  savedFrame spC csaved **
  bytesRegion txBase txBlob **
  wordArray outBase outVals **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

theorem bal0Rest_pcFree (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balLenW startW endW iW : Word) :
    (bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
      balLenW startW endW iW).pcFree := by
  unfold bal0Rest savedFrame
  bvt_pcf

set_option maxRecDepth 8000 in
/-- Instr 55: BNE a0,x0 ntaken when a0=0 → AfterIntrinsicBne. -/
theorem bvtIterBneOk
    (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balLenW startW endW iW : Word) :
    cpsTripleWithin 1 LinkIntrinsic AfterIntrinsicBne bvtCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
          balLenW startW endW iW)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
          balLenW startW endW iW) := by
  have hbr := bne_spec_gen_within .x10 .x0 (100 : BitVec 13)
    (0 : Word) (0 : Word) LinkIntrinsic
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B LinkIntrinsic bvtProg 55
      (.BNE .x10 .x0 (100 : BitVec 13))
      (by simp only [LinkIntrinsic]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkIntrinsic + 4 = AfterIntrinsicBne := by
    simp only [LinkIntrinsic, AfterIntrinsicBne]; bv_omega
  rw [hpc] at hnt
  have hF :
      (((.x24 ↦ᵣ (0 : Word)) **
          bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
            balLenW startW endW iW) : Assertion).pcFree := by
    unfold bal0Rest savedFrame; bvt_pcf
  have hntF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ (0 : Word)) **
      bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
        balLenW startW endW iW) hF hnt
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hntF

set_option maxRecDepth 8000 in
/-- Instr 56: BEQ bal,x0 taken when bal=0 → LoopAdvance. -/
theorem bvtIterBal0Skip
    (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balLenW startW endW iW : Word) :
    cpsTripleWithin 1 AfterIntrinsicBne LoopAdvance bvtCode
      ((.x24 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) **
        bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
          balLenW startW endW iW)
      ((.x24 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) **
        bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
          balLenW startW endW iW) := by
  have hbr := beq_spec_gen_within .x24 .x0 (64 : BitVec 13)
    (0 : Word) (0 : Word) AfterIntrinsicBne
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B AfterIntrinsicBne bvtProg 56
      (.BEQ .x24 .x0 (64 : BitVec 13))
      (by simp only [AfterIntrinsicBne]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr
  have htk := cpsBranchWithin_takenStripPure2 hbrC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : AfterIntrinsicBne + signExtend13 (64 : BitVec 13) = LoopAdvance := by
    simp only [AfterIntrinsicBne, LoopAdvance]
    rw [show signExtend13 (64 : BitVec 13) = (64 : Word) from by decide]
    bv_omega
  rw [hpc] at htk
  have hF :
      (((.x10 ↦ᵣ (0 : Word)) **
          bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
            balLenW startW endW iW) : Assertion).pcFree := by
    unfold bal0Rest savedFrame; bvt_pcf
  have htkF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) **
      bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
        balLenW startW endW iW) hF htk
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) htkF

set_option maxRecDepth 8000 in
/-- Instr 72–73: ADDI i++ + JAL back → LoopGuard at i+1. -/
theorem bvtIterAdvanceBack
    (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balLenW startW endW : Word) (i : Nat) :
    let iW := BitVec.ofNat 64 i
    cpsTripleWithin 2 LoopAdvance LoopGuard bvtCode
      ((.x21 ↦ᵣ iW) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x25 ↦ᵣ balLenW) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x25 ↦ᵣ balLenW) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW
  -- ADDI same-reg
  have e72_0 := addi_spec_gen_same_within .x21 iW (1 : BitVec 12) LoopAdvance (by decide)
  have e72_1 : cpsTripleWithin 1 LoopAdvance (LoopAdvance + 4)
      (CodeReq.singleton LoopAdvance (.ADDI .x21 .x21 (1 : BitVec 12)))
      (.x21 ↦ᵣ iW) (.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) := by
    have h := e72_0; rw [ofNat_addi1 i] at h; exact h
  have e72C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B LoopAdvance bvtProg 72
      (.ADDI .x21 .x21 (1 : BitVec 12))
      (by simp only [LoopAdvance]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e72_1
  have hF72 :
      ((((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x24 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkIntrinsic) **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) **
          (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (.x25 ↦ᵣ balLenW) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          savedFrame spC csaved **
          bytesRegion txBase txBlob **
          wordArray outBase outVals **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) : Assertion).pcFree) := by
    unfold savedFrame; bvt_pcf
  have e72 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x24 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x25 ↦ᵣ balLenW) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    hF72 e72C
  have hpc72 : LoopAdvance + 4 = B + 292 := by simp only [LoopAdvance]; bv_omega
  rw [hpc72] at e72
  -- JAL back
  have e73_0 := jal_x0_spec_gen_within (-164 : BitVec 21) (B + 292)
  have e73C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 292) bvtProg 73
      (.JAL .x0 (-164 : BitVec 21))
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e73_0
  have hpc73 : (B + 292) + signExtend21 (-164 : BitVec 21) = LoopGuard := by
    -- Concrete guest base: avoid bv_omega recursion on large addrs.
    simp only [LoopGuard, B, GuestAddrs.block_verdict_tx_state_gas_array]
    rw [show signExtend21 (-164 : BitVec 21) = (-164 : Word) from by decide]
    decide
  rw [hpc73] at e73C
  -- Frame ambient across emp jal (EndNext pattern)
  let ambient : Assertion :=
    (.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x24 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x25 ↦ᵣ balLenW) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
  have e73 : cpsTripleWithin 1 (B + 292) LoopGuard bvtCode ambient ambient := by
    have h0 := cpsTripleWithin_frameR ambient
      (by unfold ambient savedFrame; bvt_pcf) e73C
    exact cpsTripleWithin_weaken
      (fun h hp => by
        show (empAssertion ** ambient) h
        rwa [sepConj_emp_left' ambient])
      (fun h hq => by
        have hq' : (empAssertion ** ambient) h := hq
        rwa [sepConj_emp_left' ambient] at hq')
      h0
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) e72 e73

set_option maxRecDepth 8000 in
/-- Composite bal=0 tail: LinkIntrinsic → LoopGuard at i+1. -/
theorem bvtIterBal0Tail
    (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (i : Nat)
    (startW endW : Word) :
    let iW := BitVec.ofNat 64 i
    let balLenW := BitVec.ofNat 64 balBytes.length
    cpsTripleWithin 4 LinkIntrinsic LoopGuard bvtCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
          balLenW startW endW iW)
      ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x25 ↦ᵣ balLenW) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW balLenW
  have e55 := bvtIterBneOk spC txBase outBase chainIdW nW csaved txBlob outVals
    balLenW startW endW iW
  have e56 := bvtIterBal0Skip spC txBase outBase chainIdW nW csaved txBlob outVals
    balLenW startW endW iW
  have e72 := bvtIterAdvanceBack spC txBase outBase chainIdW nW csaved txBlob outVals
    balLenW startW endW i
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) e55 e56
  have c12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by
      unfold bal0Rest at hq
      xperm_hyp hq) c01 e72
  exact c12

/-! ## Post-intrinsic bal≠0 teer + store tail (instr 55–69 + 72–73)

    a0=0 → BNE ntaken; bal≠0 → BEQ ntaken; setup teer ABI; call teer;
    LD/ADD/SD out[i] += teer; JAL to LoopAdvance; i++; back-edge.
-/

abbrev AfterBalCheck : Word := B + 228
abbrev AfterTeerSetup : Word := B + 252
abbrev AfterStore : Word := B + 276

abbrev teerJalOff : BitVec 21 :=
  jalOff GuestAddrs.tx_eip7702_existing_authority_refund
    (GuestAddrs.block_verdict_tx_state_gas_array + 252)

/-- Ambient for bal≠0 post-intrinsic path (balBase ≠ 0, bal region present).
    Excludes focus regs x0/x10/x24 for BNE/BEQ. -/
def teerRest (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW iW : Word) : Assertion :=
  (.x1 ↦ᵣ LinkIntrinsic) **
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
  (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  savedFrame spC csaved **
  bytesRegion txBase txBlob **
  wordArray outBase outVals **
  bytesRegion balBase balBytes **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

theorem teerRest_pcFree (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW iW : Word) :
    (teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
      balBytes startW endW iW).pcFree := by
  unfold teerRest savedFrame; bvt_pcf

set_option maxRecDepth 8000 in
/-- Instr 55: BNE a0,x0 ntaken when a0=0 (bal≠0 ambient). -/
theorem bvtIterBneOkBal
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW iW : Word) :
    cpsTripleWithin 1 LinkIntrinsic AfterIntrinsicBne bvtCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ balBase) **
        teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
          balBytes startW endW iW)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ balBase) **
        teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
          balBytes startW endW iW) := by
  have hbr := bne_spec_gen_within .x10 .x0 (100 : BitVec 13)
    (0 : Word) (0 : Word) LinkIntrinsic
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B LinkIntrinsic bvtProg 55
      (.BNE .x10 .x0 (100 : BitVec 13))
      (by simp only [LinkIntrinsic]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkIntrinsic + 4 = AfterIntrinsicBne := by
    simp only [LinkIntrinsic, AfterIntrinsicBne]; bv_omega
  rw [hpc] at hnt
  have hF :
      (((.x24 ↦ᵣ balBase) **
          teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
            balBytes startW endW iW) : Assertion).pcFree := by
    unfold teerRest savedFrame; bvt_pcf
  have hntF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ balBase) **
      teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes startW endW iW) hF hnt
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hntF

set_option maxRecDepth 8000 in
/-- Instr 56: BEQ bal,x0 ntaken when balBase ≠ 0 → AfterBalCheck. -/
theorem bvtIterBalNezFall
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW iW : Word)
    (hbal : balBase ≠ 0) :
    cpsTripleWithin 1 AfterIntrinsicBne AfterBalCheck bvtCode
      ((.x24 ↦ᵣ balBase) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) **
        teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
          balBytes startW endW iW)
      ((.x24 ↦ᵣ balBase) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) **
        teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
          balBytes startW endW iW) := by
  have hbr := beq_spec_gen_within .x24 .x0 (64 : BitVec 13)
    balBase (0 : Word) AfterIntrinsicBne
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B AfterIntrinsicBne bvtProg 56
      (.BEQ .x24 .x0 (64 : BitVec 13))
      (by simp only [AfterIntrinsicBne]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hrest).2 hbal)
  have hpc : AfterIntrinsicBne + 4 = AfterBalCheck := by
    simp only [AfterIntrinsicBne, AfterBalCheck]; bv_omega
  rw [hpc] at hnt
  have hF :
      (((.x10 ↦ᵣ (0 : Word)) **
          teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
            balBytes startW endW iW) : Assertion).pcFree := by
    unfold teerRest savedFrame; bvt_pcf
  have hntF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) **
      teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes startW endW iW) hF hnt
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hntF

set_option maxRecDepth 8000 in
/-- Instr 57–62: teer ABI setup → AfterTeerSetup with a0..a5 filled. -/
theorem bvtIterTeerSetup
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW : Word) (i : Nat)
    (old10 old11 old12 old13 old14 old15 : Word)
    (_hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let balLenW := BitVec.ofNat 64 balBytes.length
    let baiW := BitVec.ofNat 64 (i + 1)
    cpsTripleWithin 6 AfterBalCheck AfterTeerSetup bvtCode
      ((.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
        (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ iW) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ balBase) **
        (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ iW) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW txPtr txLenW balLenW baiW
  -- 57 ADD a0, s0, s6 (txBase + start)
  have e57_0 := add_spec_gen_within .x10 .x8 .x22 txBase startW old10
    AfterBalCheck (by decide)
  have e57C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B AfterBalCheck bvtProg 57
      (.ADD .x10 .x8 .x22)
      (by simp only [AfterBalCheck]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e57_0
  have e57F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
      (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
      (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x21 ↦ᵣ iW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e57C
  have hpc57 : AfterBalCheck + 4 = B + 232 := by
    simp only [AfterBalCheck]; bv_omega
  rw [hpc57] at e57F
  -- 58 SUB a1, s7, s6 (end - start); a1 starts as old11
  have e58_0 := sub_spec_gen_within .x11 .x23 .x22 endW startW old11
    (B + 232) (by decide)
  have e58C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 232) bvtProg 58
      (.SUB .x11 .x23 .x22)
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e58_0
  have e58F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ txPtr) ** (.x12 ↦ᵣ old12) **
      (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
      (.x8 ↦ᵣ txBase) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x21 ↦ᵣ iW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e58C
  have hpc58 : (B + 232) + 4 = B + 236 := by bv_omega
  rw [hpc58] at e58F
  -- 59 MV a2, s8 (bal)
  have e59_0 := mv_spec_gen_within .x12 .x24 balBase old12 (B + 236) (by decide)
  have e59C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 236) bvtProg 59
      (.MV .x12 .x24)
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e59_0
  have e59F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
      (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
      (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x21 ↦ᵣ iW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e59C
  have hpc59 : (B + 236) + 4 = B + 240 := by bv_omega
  rw [hpc59] at e59F
  -- 60 MV a3, s9 (bal_len)
  have e60_0 := mv_spec_gen_within .x13 .x25 balLenW old13 (B + 240) (by decide)
  have e60C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 240) bvtProg 60
      (.MV .x13 .x25)
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e60_0
  have e60F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ balBase) **
      (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
      (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x26 ↦ᵣ chainIdW) **
      (.x21 ↦ᵣ iW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e60C
  have hpc60 : (B + 240) + 4 = B + 244 := by bv_omega
  rw [hpc60] at e60F
  -- 61 MV a4, s10 (chain_id)
  have e61_0 := mv_spec_gen_within .x14 .x26 chainIdW old14 (B + 244) (by decide)
  have e61C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 244) bvtProg 61
      (.MV .x14 .x26)
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e61_0
  have e61F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ balBase) **
      (.x13 ↦ᵣ balLenW) ** (.x15 ↦ᵣ old15) **
      (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) **
      (.x21 ↦ᵣ iW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e61C
  have hpc61 : (B + 244) + 4 = B + 248 := by bv_omega
  rw [hpc61] at e61F
  -- 62 ADDI a5, s5, 1 (i+1); addi order is (rs1 ** rd)
  have e62_0 := addi_spec_gen_within .x15 .x21 old15 iW (1 : BitVec 12)
    (B + 248) (by decide)
  have e62_1 : cpsTripleWithin 1 (B + 248) ((B + 248) + 4)
      (CodeReq.singleton (B + 248) (.ADDI .x15 .x21 (1 : BitVec 12)))
      ((.x21 ↦ᵣ iW) ** (.x15 ↦ᵣ old15))
      ((.x21 ↦ᵣ iW) ** (.x15 ↦ᵣ baiW)) := by
    have h := e62_0
    have hbai : iW + signExtend12 (1 : BitVec 12) = baiW := by
      simp only [iW, baiW]
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      exact ofNat_addi1 i
    rw [hbai] at h
    exact h
  have e62C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 248) bvtProg 62
      (.ADDI .x15 .x21 (1 : BitVec 12))
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e62_1
  have e62F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ balBase) **
      (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW) **
      (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e62C
  have hpc62 : (B + 248) + 4 = AfterTeerSetup := by
    simp only [AfterTeerSetup]; bv_omega
  rw [hpc62] at e62F
  -- compose 57;;58;;59;;60;;61;;62
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) e57F e58F
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c01 e59F
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c02 e60F
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c03 e61F
  have c05 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c04 e62F
  change cpsTripleWithin
    ((((((1 + 1) + 1) + 1) + 1) + 1)) AfterBalCheck AfterTeerSetup
    bvtCode _ _ at c05
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c05

/-- Caller-private frame across teer. wordArray + s-regs; ambient tx/BAL
    ride in the callee footprint. -/
def loopTeerFrame (spC txBase outBase balBase chainIdW nW iW
    startW endW bodyLenW balLenW : Word)
    (csaved : Saved) (outVals : List Nat) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  savedFrame spC csaved **
  wordArray outBase outVals **
  regOwn .x17 **
  (.x0 ↦ᵣ (0 : Word))

theorem loopTeerFrame_pcFree (spC txBase outBase balBase chainIdW nW iW
    startW endW bodyLenW balLenW : Word)
    (csaved : Saved) (outVals : List Nat) :
    (loopTeerFrame spC txBase outBase balBase chainIdW nW iW
      startW endW bodyLenW balLenW csaved outVals).pcFree := by
  unfold loopTeerFrame savedFrame; bvt_pcf

set_option maxRecDepth 8000 in
/-- Teer success call (instr 63) under ambient-region `TeerAssumed`.
    Pre: full `bytesRegion txBase txBlob` + `bytesRegion balBase balBytes`.
    Post: a0 = teer APPLIED charge on slice `(txBlob.drop off).take len`. -/
theorem bvtIterTeerCall
    (teer : TeerApplied) (hteer : TeerAssumed fullCode teer)
    (spC txBase outBase balBase chainIdW nW bodyLenW : Word)
    (csaved : Saved) (txBlob balBytes : List (BitVec 8))
    (outVals : List Nat) (chainId i off len : Nat)
    (startW endW old1 : Word)
    (hentry : hteer.entry =
      (GuestAddrs.tx_eip7702_existing_authority_refund : Word))
    (hret : (LinkTeer &&& ~~~(1 : Word)) = LinkTeer)
    (hbal : balBase ≠ 0)
    (hstart : startW = BitVec.ofNat 64 off)
    (hlen : off + len ≤ txBlob.length)
    (htxLen : endW - startW = BitVec.ofNat 64 len)
    (hchain : chainIdW = BitVec.ofNat 64 chainId) :
    let iW := BitVec.ofNat 64 i
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let balLenW := BitVec.ofNat 64 balBytes.length
    let baiW := BitVec.ofNat 64 (i + 1)
    let chargeW := BitVec.ofNat 64
      (teer ((txBlob.drop off).take len) balBytes chainId (i + 1))
    cpsTripleWithin (1 + nTeerSteps) AfterTeerSetup LinkTeer fullCode
      ((.x1 ↦ᵣ old1) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
        (.x12 ↦ᵣ balBase) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion txBase txBlob **
        bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        loopTeerFrame spC txBase outBase balBase chainIdW nW iW
          startW endW bodyLenW balLenW csaved outVals)
      ((.x1 ↦ᵣ LinkTeer) **
        (.x10 ↦ᵣ chargeW) **
        regOwn .x11 **
        bytesRegion txBase txBlob **
        bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        loopTeerFrame spC txBase outBase balBase chainIdW nW iW
          startW endW bodyLenW balLenW csaved outVals) := by
  intro iW txPtr txLenW balLenW baiW chargeW
  have hload : txPtr = txBase + BitVec.ofNat 64 off := by
    simp only [txPtr, hstart]
  have hlenW : txLenW = BitVec.ofNat 64 len := by
    simp only [txLenW, htxLen]
  have hflat0 := hteer.applied_flat LinkTeer txBase txPtr balBase balLenW
    chainIdW baiW txBlob balBytes off len chainId (i + 1)
    hret hbal hload hlen rfl hchain rfl
  have hflatLen : cpsTripleWithin nTeerSteps hteer.entry LinkTeer fullCode
      ((.x1 ↦ᵣ LinkTeer) ** (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
        (.x12 ↦ᵣ balBase) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion txBase txBlob ** bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkTeer) **
        (.x10 ↦ᵣ chargeW) **
        regOwn .x11 **
        bytesRegion txBase txBlob ** bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) := by
    simpa [hlenW, chargeW] using hflat0
  have hflatF := cpsTripleWithin_frameR
    (loopTeerFrame spC txBase outBase balBase chainIdW nW iW
      startW endW bodyLenW balLenW csaved outVals)
    (loopTeerFrame_pcFree _ _ _ _ _ _ _ _ _ _ _ _ _) hflatLen
  have hcallee : cpsTripleWithin nTeerSteps hteer.entry LinkTeer fullCode
      ((.x1 ↦ᵣ LinkTeer) **
        ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
          (.x12 ↦ᵣ balBase) ** (.x13 ↦ᵣ balLenW) **
          (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
          bytesRegion txBase txBlob **
          bytesRegion balBase balBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          loopTeerFrame spC txBase outBase balBase chainIdW nW iW
            startW endW bodyLenW balLenW csaved outVals))
      ((.x1 ↦ᵣ LinkTeer) **
        ((.x10 ↦ᵣ chargeW) **
          regOwn .x11 **
          bytesRegion txBase txBlob **
          bytesRegion balBase balBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          loopTeerFrame spC txBase outBase balBase chainIdW nW iW
            startW endW bodyLenW balLenW csaved outVals)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hflatF
  have hcall := callWithin_spec AfterTeerSetup hteer.entry old1 teerJalOff
    nTeerSteps
    (by
      rw [hentry]
      show AfterTeerSetup + signExtend21 teerJalOff =
        (GuestAddrs.tx_eip7702_existing_authority_refund : Word)
      simp only [AfterTeerSetup, teerJalOff, B]
      decide)
    (fun a off' hi => bvt_mono a off'
      (CodeReq.ofProg_mem_at B AfterTeerSetup bvtProg 63
        (.JAL .x1 teerJalOff)
        (by simp only [AfterTeerSetup]; bv_omega)
        (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide) a off' hi))
    (by
      unfold loopTeerFrame savedFrame
      bvt_pcf)
    hcallee
  have hlink : AfterTeerSetup + 4 = LinkTeer := by
    simp only [AfterTeerSetup, LinkTeer]; bv_omega
  rw [hlink] at hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
/-- Instr 64–68: SLLI/ADD/LD/ADD/SD — out[i] += teer charge.
    Pre: peeled cell at pureIntrinsic; post: cell = pureIntrinsic + charge. -/
theorem bvtIterStoreAdd
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8))
    (outPrefix outSuffix : List Nat) (balBytes : List (BitVec 8))
    (startW endW chargeW old5 old6 old7 : Word) (i : Nat)
    (hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    let pureW := BitVec.ofNat 64 pureIntrinsicStateGasSuccess
    let sumW := pureW + chargeW
    cpsTripleWithin 5 LinkTeer AfterStore bvtCode
      ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        (outPtr ↦ₘ pureW) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArrayFrom outBase 0 outPrefix **
        wordArrayFrom outBase (i + 1) outSuffix **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
        (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) **
        (outPtr ↦ₘ sumW) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArrayFrom outBase 0 outPrefix **
        wordArrayFrom outBase (i + 1) outSuffix **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW outPtr pureW sumW
  -- 64 SLLI x5, x21, 3  (spec order: rs1 ** rd)
  have e64_0 := slli_spec_gen_within .x5 .x21 old5 iW (3 : BitVec 6)
    LinkTeer (by decide)
  have e64_1 : cpsTripleWithin 1 LinkTeer (LinkTeer + 4)
      (CodeReq.singleton LinkTeer (.SLLI .x5 .x21 (3 : BitVec 6)))
      ((.x21 ↦ᵣ iW) ** (.x5 ↦ᵣ old5))
      ((.x21 ↦ᵣ iW) ** (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i))) := by
    have h := e64_0
    have hs' : iW <<< (3 : BitVec 6).toNat = BitVec.ofNat 64 (8 * i) := by
      change iW <<< (3 : Nat) = BitVec.ofNat 64 (8 * i)
      simp only [iW]; exact slli3_ofNat i hi61
    rw [hs'] at h
    exact h
  have e64C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B LinkTeer bvtProg 64
      (.SLLI .x5 .x21 (3 : BitVec 6))
      (by simp only [LinkTeer]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e64_1
  -- Shared ambient across store (excludes focus regs of each step)
  let storeAmb : Assertion :=
    (.x10 ↦ᵣ chargeW) ** (.x19 ↦ᵣ outBase) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArrayFrom outBase 0 outPrefix **
      wordArrayFrom outBase (i + 1) outSuffix **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
  have hstoreAmb : storeAmb.pcFree := by
    unfold storeAmb savedFrame
    repeat' first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_wordArrayFrom outBase 0 outPrefix
      | exact pcFree_wordArrayFrom outBase (i + 1) outSuffix
  have e64F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) ** (outPtr ↦ₘ pureW) ** storeAmb)
    (by
      apply pcFree_sepConj pcFree_regIs
      apply pcFree_sepConj pcFree_regIs
      apply pcFree_sepConj pcFree_memIs
      exact hstoreAmb) e64C
  have hpc64 : LinkTeer + 4 = B + 260 := by
    simp only [LinkTeer]; bv_omega
  rw [hpc64] at e64F
  -- 65 ADD x6, x19, x5 → x6 = outPtr
  have e65_0 := add_spec_gen_within .x6 .x19 .x5 outBase
    (BitVec.ofNat 64 (8 * i)) old6 (B + 260) (by decide)
  have e65_1 : cpsTripleWithin 1 (B + 260) ((B + 260) + 4)
      (CodeReq.singleton (B + 260) (.ADD .x6 .x19 .x5))
      ((.x19 ↦ᵣ outBase) ** (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x6 ↦ᵣ old6))
      ((.x19 ↦ᵣ outBase) ** (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x6 ↦ᵣ outPtr)) := by
    have h := e65_0
    have heq : outBase + BitVec.ofNat 64 (8 * i) = outPtr := by
      simp only [outPtr]
    rw [heq] at h
    exact h
  have e65C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 260) bvtProg 65
      (.ADD .x6 .x19 .x5)
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e65_1
  have e65F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ iW) ** (.x7 ↦ᵣ old7) ** (outPtr ↦ₘ pureW) **
      (.x10 ↦ᵣ chargeW) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArrayFrom outBase 0 outPrefix **
      wordArrayFrom outBase (i + 1) outSuffix **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by
      unfold savedFrame
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | exact pcFree_wordArrayFrom outBase 0 outPrefix
        | exact pcFree_wordArrayFrom outBase (i + 1) outSuffix) e65C
  have hpc65 : (B + 260) + 4 = B + 264 := by bv_omega
  rw [hpc65] at e65F
  -- 66 LD x7, 0(x6)
  have e66_0 := ld_spec_gen_within .x7 .x6 outPtr old7 pureW
    (0 : BitVec 12) (B + 264) (by decide)
  have e66_1 : cpsTripleWithin 1 (B + 264) ((B + 264) + 4)
      (CodeReq.singleton (B + 264) (.LD .x7 .x6 (0 : BitVec 12)))
      ((.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ old7) ** (outPtr ↦ₘ pureW))
      ((.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ pureW) ** (outPtr ↦ₘ pureW)) := by
    have h := e66_0
    have hoff : outPtr + signExtend12 (0 : BitVec 12) = outPtr := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      simp
    rw [hoff] at h
    exact h
  have e66C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 264) bvtProg 66
      (.LD .x7 .x6 (0 : BitVec 12))
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e66_1
  have e66F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
      (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArrayFrom outBase 0 outPrefix **
      wordArrayFrom outBase (i + 1) outSuffix **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by
      unfold savedFrame
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | exact pcFree_wordArrayFrom outBase 0 outPrefix
        | exact pcFree_wordArrayFrom outBase (i + 1) outSuffix) e66C
  have hpc66 : (B + 264) + 4 = B + 268 := by bv_omega
  rw [hpc66] at e66F
  -- 67 ADD x7, x7, x10
  have e67_0 := add_spec_gen_rd_eq_rs1_within .x7 .x10 pureW chargeW
    (B + 268) (by decide)
  have e67_1 : cpsTripleWithin 1 (B + 268) ((B + 268) + 4)
      (CodeReq.singleton (B + 268) (.ADD .x7 .x7 .x10))
      ((.x7 ↦ᵣ pureW) ** (.x10 ↦ᵣ chargeW))
      ((.x7 ↦ᵣ sumW) ** (.x10 ↦ᵣ chargeW)) := by
    have h := e67_0
    change cpsTripleWithin 1 (B + 268) ((B + 268) + 4) _
      ((.x7 ↦ᵣ pureW) ** (.x10 ↦ᵣ chargeW))
      ((.x7 ↦ᵣ (pureW + chargeW)) ** (.x10 ↦ᵣ chargeW)) at h
    simpa only [sumW] using h
  have e67C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 268) bvtProg 67
      (.ADD .x7 .x7 .x10)
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e67_1
  have e67F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
      (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) ** (.x6 ↦ᵣ outPtr) **
      (outPtr ↦ₘ pureW) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArrayFrom outBase 0 outPrefix **
      wordArrayFrom outBase (i + 1) outSuffix **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by
      unfold savedFrame
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | exact pcFree_wordArrayFrom outBase 0 outPrefix
        | exact pcFree_wordArrayFrom outBase (i + 1) outSuffix) e67C
  have hpc67 : (B + 268) + 4 = B + 272 := by bv_omega
  rw [hpc67] at e67F
  -- 68 SD x6, x7, 0
  have e68_0 := sd_spec_gen_within .x6 .x7 outPtr sumW pureW
    (0 : BitVec 12) (B + 272)
  have e68_1 : cpsTripleWithin 1 (B + 272) ((B + 272) + 4)
      (CodeReq.singleton (B + 272) (.SD .x6 .x7 (0 : BitVec 12)))
      ((.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) ** (outPtr ↦ₘ pureW))
      ((.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) ** (outPtr ↦ₘ sumW)) := by
    have h := e68_0
    have hoff : outPtr + signExtend12 (0 : BitVec 12) = outPtr := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      simp
    rw [hoff] at h
    exact h
  have e68C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 272) bvtProg 68
      (.SD .x6 .x7 (0 : BitVec 12))
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e68_1
  have e68F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
      (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArrayFrom outBase 0 outPrefix **
      wordArrayFrom outBase (i + 1) outSuffix **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by
      unfold savedFrame
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | exact pcFree_wordArrayFrom outBase 0 outPrefix
        | exact pcFree_wordArrayFrom outBase (i + 1) outSuffix) e68C
  have hpc68 : (B + 272) + 4 = AfterStore := by
    simp only [AfterStore]; bv_omega
  rw [hpc68] at e68F
  -- Compose 64;;65;;66;;67;;68
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) e64F e65F
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c01 e66F
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c02 e67F
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c03 e68F
  change cpsTripleWithin ((((1 + 1) + 1) + 1) + 1) LinkTeer AfterStore
    bvtCode _ _ at c04
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c04

set_option maxRecDepth 8000 in
/-- Instr 69: JAL +12 → LoopAdvance (skip zero-store join). -/
theorem bvtIterAfterStoreJal
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW iW chargeW : Word)
    (v5 v6 v7 : Word) :
    cpsTripleWithin 1 AfterStore LoopAdvance bvtCode
      ((.x21 ↦ᵣ iW) **
        (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x21 ↦ᵣ iW) **
        (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  have e69_0 := jal_x0_spec_gen_within (12 : BitVec 21) AfterStore
  have e69C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B AfterStore bvtProg 69
      (.JAL .x0 (12 : BitVec 21))
      (by simp only [AfterStore]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e69_0
  have hpc : AfterStore + signExtend21 (12 : BitVec 21) = LoopAdvance := by
    simp only [AfterStore, LoopAdvance]
    rw [show signExtend21 (12 : BitVec 21) = (12 : Word) from by decide]
    bv_omega
  rw [hpc] at e69C
  let ambient : Assertion :=
    (.x21 ↦ᵣ iW) **
      (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
  have e69 : cpsTripleWithin 1 AfterStore LoopAdvance bvtCode ambient ambient := by
    have h0 := cpsTripleWithin_frameR ambient
      (by unfold ambient savedFrame; bvt_pcf) e69C
    exact cpsTripleWithin_weaken
      (fun h hp => by
        show (empAssertion ** ambient) h
        rwa [sepConj_emp_left' ambient])
      (fun h hq => by
        have hq' : (empAssertion ** ambient) h := hq
        rwa [sepConj_emp_left' ambient] at hq')
      h0
  exact e69

/-! ## wordArray peel helper for intrinsic + store glue -/

/-- Peel cell `i` when its value is already `v` (e.g. pureIntrinsic after write). -/
theorem wordArray_set_eq_of_get
    (base : Word) (outVals : List Nat) (i v : Nat)
    (hi : i < outVals.length) (hcell : outVals[i] = v) :
    wordArray base outVals =
      (wordArrayFrom base 0 (outVals.take i) **
        ((base + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 v) **
        wordArrayFrom base (i + 1) (outVals.drop (i + 1))) := by
  have h := wordArray_split base outVals i hi
  simpa [hcell] using h

/-! ## Composition notes (next slice)

    Ambient IntrinsicAssumed/TeerAssumed remove unaligned tx peels.
    Remaining glue for one-iter:

    1. `wordArray_set_eq_of_get` / `wordArray_split` peels `out[i]`.
    2. bal=0: `outVals[i] = pureIntrinsic` so intrinsic write folds via peel;
       then `bvtIterBal0Tail`.
    3. bal≠0: cell pure through teer; store pure→sum; fold final cell.
    4. Align `bvtIterAfterStoreJal` ambient with store peel form.
    5. Full iter + induction + top theorem under ArrayCalleeAssumptions.
-/

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
