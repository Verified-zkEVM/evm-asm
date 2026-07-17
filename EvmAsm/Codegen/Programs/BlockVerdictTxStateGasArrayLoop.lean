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

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArray_split pcFree_wordArray)

local macro "bvt_pcf" : tactic => `(tactic|
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_regOwns _
    | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _
    | exact pcFree_wordArray _ _
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

/-- Caller-private frame across loop-site bgv (keeps LoopInv s-regs + out/BAL). -/
def loopBgvFrame (spC txBase outBase balBase chainIdW nW iW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool)
    (o22 o23 o27 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ o22) ** (.x23 ↦ᵣ o23) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** (.x27 ↦ᵣ o27) **
  savedFrame spC csaved **
  wordArray outBase outVals **
  (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
  (.x0 ↦ᵣ (0 : Word))

theorem loopBgvFrame_pcFree (spC txBase outBase balBase chainIdW nW iW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool)
    (o22 o23 o27 : Word) :
    (loopBgvFrame spC txBase outBase balBase chainIdW nW iW csaved
      txBlob outVals balBytes balEnabled o22 o23 o27).pcFree := by
  unfold loopBgvFrame savedFrame
  cases balEnabled <;> bvt_pcf

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
