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
    | exact pcFree_stackFree _ _
    | exact pcFree_tisScratchOwn
    | exact pcFree_teerScratchOwn
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_regOwns _
    | exact pcFree_memIs
    | exact pcFree_memOwn
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
          stackFree spC nCalleeStackDwords **
          tisScratchOwn **
          teerScratchOwn **
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
      stackFree spC nCalleeStackDwords **
      tisScratchOwn **
      teerScratchOwn **
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
          stackFree spC nCalleeStackDwords **
          tisScratchOwn **
          teerScratchOwn **
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
      stackFree spC nCalleeStackDwords **
      tisScratchOwn **
      teerScratchOwn **
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
  stackFree spC nCalleeStackDwords **
  tisScratchOwn **
  teerScratchOwn **
  wordArray outBase outVals **
  (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
  (.x0 ↦ᵣ (0 : Word))

theorem loopBgvFrame_pcFree (spC txBase outBase balBase chainIdW nW iW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) :
    (loopBgvFrame spC txBase outBase balBase chainIdW nW iW csaved
      txBlob outVals balBytes balEnabled).pcFree := by
  unfold loopBgvFrame savedFrame
  cases balEnabled <;> bvt_pcf

/-! ## Iteration start: SLLI/ADD + loop-site bgv + MV x22 (instr 33–36) -/

abbrev AfterStartBgv : Word := B + 148

/-- Pack owned t0–t2 + s-temps + a-temps into `regOwns bgvScratch`. -/
theorem pack_loop_bgvScratch :
    ∀ h, ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17) h) →
      (regOwns bgvScratch) h := by
  intro h hp
  simp only [bgvScratch, regOwns_cons, regOwns_nil, sepConj_emp_right']
  exact hp

/-- Pack `regIs x5` + owned temps into `regOwns bgvScratch` (Header-style). -/
theorem pack_loop_bgvScratch_is (v5 : Word) :
    ∀ h, (((.x5 ↦ᵣ v5) ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17) h) →
      (regOwns bgvScratch) h := by
  intro h hp
  exact pack_loop_bgvScratch h
    (sepConj_mono (regIs_to_regOwn .x5 v5) (fun _ hh => hh) h hp)

/-- `loopBgvFrame` after MV x22 (x22 pinned, not regOwn). -/
def loopBgvFrameAfterMv (spC txBase outBase balBase chainIdW nW iW : Word)
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
  stackFree spC nCalleeStackDwords **
  tisScratchOwn **
  teerScratchOwn **
  wordArray outBase outVals **
  (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
  (.x0 ↦ᵣ (0 : Word))

/-- Ambient across SLLI/ADD: everything except focus x5/x8/x10/x21. -/
def setupFrame (spC txBase outBase balBase chainIdW nW : Word)
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
  stackFree spC nCalleeStackDwords **
  tisScratchOwn **
  teerScratchOwn **
  payload txBase outBase balBase txBlob outVals balBytes balEnabled **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

theorem setupFrame_pcFree (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (old1 : Word) :
    (setupFrame spC txBase outBase balBase chainIdW nW csaved
      txBlob outVals balBytes balEnabled old1).pcFree := by
  unfold setupFrame savedFrame payload
  cases balEnabled <;> bvt_pcf

/-- Local pcFree for framed loop atoms. -/
local macro "bvt_pcf" : tactic =>
  `(tactic| repeat' first
    | exact pcFree_stackFree _ _
    | exact pcFree_tisScratchOwn
    | exact pcFree_teerScratchOwn
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_regOwns _
    | exact pcFree_memIs
    | exact pcFree_memOwn
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
            stackFree spC nCalleeStackDwords **
            tisScratchOwn **
            teerScratchOwn **
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
        stackFree spC nCalleeStackDwords **
        tisScratchOwn **
        teerScratchOwn **
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
        stackFree spC nCalleeStackDwords **
        tisScratchOwn **
        teerScratchOwn **
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
        stackFree spC nCalleeStackDwords **
        tisScratchOwn **
        teerScratchOwn **
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
      stackFree spC nCalleeStackDwords **
      tisScratchOwn **
      teerScratchOwn **
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
      stackFree spC nCalleeStackDwords **
      tisScratchOwn **
      teerScratchOwn **
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
      stackFree spC nCalleeStackDwords **
      tisScratchOwn **
      teerScratchOwn **
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
theorem ofNat_addi1 (i : Nat) :
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
        stackFree spC nCalleeStackDwords **
        tisScratchOwn **
        teerScratchOwn **
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
        stackFree spC nCalleeStackDwords **
        tisScratchOwn **
        teerScratchOwn **
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
      stackFree spC nCalleeStackDwords **
      tisScratchOwn **
      teerScratchOwn **
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
      stackFree spC nCalleeStackDwords **
      tisScratchOwn **
      teerScratchOwn **
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
      stackFree spC nCalleeStackDwords **
      tisScratchOwn **
      teerScratchOwn **
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

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
