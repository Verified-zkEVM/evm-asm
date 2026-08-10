/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakOuterBody

  Discharge `hbody` of `keccakAbsorbOuterLoop_reload` from
  `keccakAbsorbBody_with_backedge` + window focus over the full input.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakOuter
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

/-- Countdown remaining after one rate block. -/
theorem keccakAbsorb_remaining_step (n rem : Nat) :
    keccakAbsorbStep * (n + 1) + rem - keccakAbsorbStep =
      keccakAbsorbStep * n + rem := by
  simp only [keccakAbsorbStep]; omega

/-- Absorbed-count after one hop. -/
theorem keccakAbsorb_absorbed_succ (N n : Nat) (hn : n < N) :
    N - (n + 1) + 1 = N - n := by omega

/-- Block window length under outer fit. -/
theorem keccakAbsorb_blk_length (input : List (BitVec 8)) (N n rem : Nat)
    (hn : n < N) (hfit : keccakAbsorbStep * N + rem ≤ input.length) :
    ((input.drop (keccakAbsorbStep * (N - (n + 1)))).take keccakAbsorbStep).length =
      keccakAbsorbStep := by
  simp only [keccakAbsorbStep] at hfit ⊢
  have hle : 136 * (N - (n + 1)) + 136 ≤ input.length := by
    have h1 : N - (n + 1) + 1 ≤ N := by omega
    have h2 : 136 * (N - (n + 1) + 1) ≤ 136 * N :=
      Nat.mul_le_mul_left _ h1
    have h3 : 136 * (N - (n + 1) + 1) = 136 * (N - (n + 1)) + 136 := by omega
    omega
  rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]

/-- Fit of one block under outer fit. -/
theorem keccakAbsorb_blk_fit (input : List (BitVec 8)) (N n rem : Nat)
    (hn : n < N) (hfit : keccakAbsorbStep * N + rem ≤ input.length) :
    keccakAbsorbStep * (N - (n + 1)) + keccakAbsorbStep ≤ input.length := by
  simp only [keccakAbsorbStep] at hfit ⊢
  have h1 : N - (n + 1) + 1 ≤ N := by omega
  have h2 : 136 * (N - (n + 1) + 1) ≤ 136 * N := Nat.mul_le_mul_left _ h1
  omega

/-- 136-aligned offset. -/
theorem keccakAbsorb_offset_mod8 (k : Nat) :
    (keccakAbsorbStep * k) % 8 = 0 := by
  simp only [keccakAbsorbStep]; omega

/-- Merge focused window back to full region (assertion equality). -/
theorem bytesRegion_window_unfocus (B : Word) (ws : List (BitVec 8)) (j n : Nat)
    (hfit : j + n ≤ ws.length) (h8j : j % 8 = 0) (h8n : n % 8 = 0) :
    (bytesRegion (B + BitVec.ofNat 64 j) ((ws.drop j).take n) **
        windowRest B ws j n) =
      bytesRegion B ws := by
  exact (bytesRegion_window_focus B ws j n hfit h8j h8n).symm

/-- of_forall3 matching MeasureLoop style (nested owns destructure).
    `P ** own1 ** own2 ** own3` = `P ** (own1 ** (own2 ** own3))`. -/
private theorem of_forall3 {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {r1 r2 r3 : Reg}
    (h : ∀ (v1 v2 v3 : Word),
      cpsTripleWithin nSteps entry exit_ cr
        (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** (regOwn r1) ** (regOwn r2) ** (regOwn r3)) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  -- hPP : (P ** (own1 ** (own2 ** own3))) on half
  obtain ⟨h3, h4, hd2, hu2, hP3, hOwn⟩ := hPP
  -- hOwn : own1 ** (own2 ** own3)
  obtain ⟨h5, h6, hd3, hu3, ⟨v1, hv1⟩, hOwn23⟩ := hOwn
  -- hOwn23 : own2 ** own3
  obtain ⟨h7, h8, hd4, hu4, ⟨v2, hv2⟩, ⟨v3, hv3⟩⟩ := hOwn23
  exact h v1 v2 v3 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨h3, h4, hd2, hu2, hP3,
        ⟨h5, h6, hd3, hu3, hv1,
          ⟨h7, h8, hd4, hu4, hv2, hv3⟩⟩⟩, hRb⟩ hpc

/-- Peel a single trailing `regOwn r`. -/
private theorem of_forall1 {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {r : Reg}
    (h : ∀ v, cpsTripleWithin nSteps entry exit_ cr (P ** (r ↦ᵣ v)) Q) :
    cpsTripleWithin nSteps entry exit_ cr (P ** regOwn r) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hMem, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hP0, hOwn, hd0, hu0, hp0, hpOwn⟩ := hpP
  obtain ⟨v, hv⟩ := hpOwn
  have hPR' :
      ((P ** (r ↦ᵣ v)) ** R).holdsFor s :=
    ⟨hMem, hcompat, h_P, h_R, hdisj, hunion,
      ⟨hP0, hOwn, hd0, hu0, hp0, hv⟩, hpR⟩
  exact h v R hR s hcr hPR' hpc

/-- Body step with window already focused (blk + rest ambient).
    Pre/post use outer-inv register shape with concrete lim. -/
theorem keccakAbsorbOuterBody_step_focused (cr : CodeReq) (liHdr : Word)
    (scratchBase inputCur : Word) (remaining : Nat)
    (st0 blk : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hst : st0.length = 200) (hblk : blk.length = 136)
    (hrem : 136 ≤ remaining) (hrem64 : remaining < 2 ^ 64)
    (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hpc_jal : (liHdr + 8) + 60 + signExtend21 (-68 : BitVec 21) = liHdr)
    (hmemMvS : ∀ a i, CodeReq.singleton (liHdr + 8) (.MV .x28 .x8) a = some i →
      cr a = some i)
    (hmemMvI : ∀ a i, CodeReq.singleton ((liHdr + 8) + 4) (.MV .x30 .x20) a = some i →
      cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton ((liHdr + 8) + 8) (.LI .x31 (17 : Word)) a = some i →
      cr a = some i)
    (hmemLdI : ∀ a i, CodeReq.singleton ((liHdr + 8) + 12) (.LD .x5 .x30 0) a = some i →
      cr a = some i)
    (hmemLdS : ∀ a i, CodeReq.singleton ((liHdr + 8) + 16) (.LD .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton ((liHdr + 8) + 20) (.XOR .x6 .x6 .x5) a = some i →
      cr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton ((liHdr + 8) + 24) (.SD .x28 .x6 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton ((liHdr + 8) + 28) (.ADDI .x28 .x28 8) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton ((liHdr + 8) + 32) (.ADDI .x30 .x30 8) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton ((liHdr + 8) + 36) (.ADDI .x31 .x31 (-1)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton ((liHdr + 8) + 40) (.BNE .x31 .x0 (-28)) a = some i →
      cr a = some i)
    (hmemMv10 : ∀ a i, CodeReq.singleton ((liHdr + 8) + 44) (.MV .x10 .x8) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton ((liHdr + 8) + 48) (.CSRS 0x800 .x10) a = some i →
      cr a = some i)
    (hmemA20 : ∀ a i, CodeReq.singleton ((liHdr + 8) + 52)
        (.ADDI .x20 .x20 (136 : BitVec 12)) a = some i → cr a = some i)
    (hmemA9 : ∀ a i, CodeReq.singleton ((liHdr + 8) + 56)
        (.ADDI .x9 .x9 (-136 : BitVec 12)) a = some i → cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton ((liHdr + 8) + 60)
        (.JAL .x0 (-68 : BitVec 21)) a = some i → cr a = some i) :
    cpsTripleWithin keccakAbsorbBodyFuel (liHdr + 8) liHdr cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
        (.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x10) **
        regOwns keccakAbsorbOuterTemps **
        bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A)
      ((.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
        (regOwn .x29) **
        (.x8 ↦ᵣ scratchBase) **
        (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x10) **
        regOwns keccakAbsorbOuterTemps **
        bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
        bytesRegion inputCur blk ** A) := by
  -- Concrete-value body (any v10; MV x10,x8 establishes CSRS pointer)
  have hbodyV : ∀ (v10 v28 v30 v31 : Word),
      cpsTripleWithin keccakAbsorbBodyFuel (liHdr + 8) liHdr cr
        ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
          (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ v10) ** (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30) **
          (.x31 ↦ᵣ v31) **
          regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
          bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A)
        ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
          (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
          bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
          bytesRegion inputCur blk ** A) := by
    intro v10 v28 v30 v31
    exact keccakAbsorbBody_with_backedge cr (liHdr + 8) liHdr
      scratchBase inputCur remaining st0 blk A hA
      hst hblk hrem hrem64 hb8 hvalid
      v10 v28 v30 v31 rfl hpc_jal
      hmemMvS hmemMvI hmemLi hmemLdI hmemLdS hmemXor hmemSd
      hmemAddS hmemAddI hmemAddC hmemBne hmemMv10 hmemCsrs hmemA20 hmemA9 hmemJal
  -- Peel x10 then x28/x30/x31
  have hbodyO : cpsTripleWithin keccakAbsorbBodyFuel (liHdr + 8) liHdr cr
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x10) **
        (regOwn .x28) ** (regOwn .x30) ** (regOwn .x31) **
        regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
        (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
        bytesRegion inputCur blk ** A) := by
    have h3 : ∀ v10, cpsTripleWithin keccakAbsorbBodyFuel (liHdr + 8) liHdr cr
        ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
          (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ v10) **
          (regOwn .x28) ** (regOwn .x30) ** (regOwn .x31) **
          regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
          bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A)
        ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
          (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
          bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
          bytesRegion inputCur blk ** A) := by
      intro v10
      have h := of_forall3
        (P :=
          (.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
            (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x10 ↦ᵣ v10) **
            regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
            bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A)
        (Q :=
          (.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
            (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
            bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
            bytesRegion inputCur blk ** A)
        (r1 := .x28) (r2 := .x30) (r3 := .x31)
        (fun v1 v2 v3 => by
          refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
            (fun _ hq => hq) (hbodyV v10 v1 v2 v3))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) h
    -- of_forall1 peels rightmost own x10
    have h := of_forall1
      (P :=
        (.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
          (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
          (regOwn .x28) ** (regOwn .x30) ** (regOwn .x31) **
          regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
          bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A)
      (Q :=
        (.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
          (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
          bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
          bytesRegion inputCur blk ** A)
      (r := .x10)
      (fun v => by
        refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h3 v))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  -- Bridge outer-shaped pre/post ↔ body owns form
  refine cpsTripleWithin_weaken
    (fun h hp => by
      have hp1 :=
        sepConj_mono (fun _ => id)
          (sepConj_mono (regIs_implies_regOwn (r := .x29))
            (fun _ => id)) h hp
      have hp2 : (
          (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
            ((regOwn .x29) ** regOwns keccakAbsorbOuterTemps) **
            (.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
            (regOwn .x10) **
            bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A) h := by
        xperm_hyp hp1
      have hp3 : (
          (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
            ((regOwn .x28) ** (regOwn .x30) ** (regOwn .x31) **
              regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6)) **
            (.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
            (regOwn .x10) **
            bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A) h := by
        refine sepConj_mono (fun _ => id)
          (sepConj_mono outerTemps_to_body_owns (fun _ => id)) h hp2
      xperm_hyp hp3)
    (fun h hq => by
      -- Drop x10 value → own; peel csrsRest → own x29 ** outerTemps
      have hq0 :=
        sepConj_mono (fun _ => id)
          (sepConj_mono (fun _ => id)
            (sepConj_mono (fun _ => id)
              (sepConj_mono (fun _ => id)
                (sepConj_mono (regIs_implies_regOwn (r := .x10))
                  (fun _ => id))))) h hq
      have hq1 : (
          (.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
            (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
            (regOwn .x10) **
            ((regOwn .x29) ** regOwns keccakAbsorbOuterTemps) **
            bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
            bytesRegion inputCur blk ** A) h := by
        refine sepConj_mono (fun _ => id)
          (sepConj_mono (fun _ => id)
            (sepConj_mono (fun _ => id)
              (sepConj_mono (fun _ => id)
                (sepConj_mono (fun _ => id)
                  (sepConj_mono regOwns_csrsRest_to_x29_outerTemps
                    (fun _ => id)))))) h hq0
      xperm_hyp hq1)
    hbodyO

/-- Full outer-inv body step: window-focus full input, run focused body, unfocus. -/
theorem keccakAbsorbOuterBody_step (cr : CodeReq) (liHdr : Word)
    (scratchBase inputBase : Word) (input : List (BitVec 8))
    (N rem n : Nat) (A : Assertion) (hA : A.pcFree)
    (hn : n < N)
    (hrem : rem < keccakAbsorbStep)
    (hfit : keccakAbsorbStep * N + rem ≤ input.length)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hpc_jal : (liHdr + 8) + 60 + signExtend21 (-68 : BitVec 21) = liHdr)
    (hmemMvS : ∀ a i, CodeReq.singleton (liHdr + 8) (.MV .x28 .x8) a = some i →
      cr a = some i)
    (hmemMvI : ∀ a i, CodeReq.singleton ((liHdr + 8) + 4) (.MV .x30 .x20) a = some i →
      cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton ((liHdr + 8) + 8) (.LI .x31 (17 : Word)) a = some i →
      cr a = some i)
    (hmemLdI : ∀ a i, CodeReq.singleton ((liHdr + 8) + 12) (.LD .x5 .x30 0) a = some i →
      cr a = some i)
    (hmemLdS : ∀ a i, CodeReq.singleton ((liHdr + 8) + 16) (.LD .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton ((liHdr + 8) + 20) (.XOR .x6 .x6 .x5) a = some i →
      cr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton ((liHdr + 8) + 24) (.SD .x28 .x6 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton ((liHdr + 8) + 28) (.ADDI .x28 .x28 8) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton ((liHdr + 8) + 32) (.ADDI .x30 .x30 8) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton ((liHdr + 8) + 36) (.ADDI .x31 .x31 (-1)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton ((liHdr + 8) + 40) (.BNE .x31 .x0 (-28)) a = some i →
      cr a = some i)
    (hmemMv10 : ∀ a i, CodeReq.singleton ((liHdr + 8) + 44) (.MV .x10 .x8) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton ((liHdr + 8) + 48) (.CSRS 0x800 .x10) a = some i →
      cr a = some i)
    (hmemA20 : ∀ a i, CodeReq.singleton ((liHdr + 8) + 52)
        (.ADDI .x20 .x20 (136 : BitVec 12)) a = some i → cr a = some i)
    (hmemA9 : ∀ a i, CodeReq.singleton ((liHdr + 8) + 56)
        (.ADDI .x9 .x9 (-136 : BitVec 12)) a = some i → cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton ((liHdr + 8) + 60)
        (.JAL .x0 (-68 : BitVec 21)) a = some i → cr a = some i) :
    cpsTripleWithin keccakAbsorbOuterBodyFuel (liHdr + 8) liHdr cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * (n + 1) + rem)) **
        (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
        keccakAbsorbOuterInv scratchBase inputBase input N (n + 1) A)
      ((.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * n + rem)) **
        (regOwn .x29) **
        keccakAbsorbOuterInv scratchBase inputBase input N n A) := by
  have hfit_blk := keccakAbsorb_blk_fit input N n rem hn hfit
  have hblk_len := keccakAbsorb_blk_length input N n rem hn hfit
  have hj8 := keccakAbsorb_offset_mod8 (N - (n + 1))
  have hstep8 : keccakAbsorbStep % 8 = 0 := by
    simp only [keccakAbsorbStep]
  have hk_abs := keccakAbsorb_absorbed_succ N n hn
  have hrem_arith := keccakAbsorb_remaining_step n rem
  -- residual rem is always < rate (domain of remainder path after outer loop)
  have := hrem
  let j := keccakAbsorbStep * (N - (n + 1))
  let blk := (input.drop j).take keccakAbsorbStep
  let st0 := keccakAbsorbedPrefix input (N - (n + 1))
  let inputCur := keccakAbsorbCursor inputBase (N - (n + 1))
  let remaining := keccakAbsorbStep * (n + 1) + rem
  have hst0_len : st0.length = 200 := keccakAbsorbedPrefix_length _ _
  have hrem_ge : 136 ≤ remaining := by
    simp only [remaining, keccakAbsorbStep]; omega
  have hrem64 : remaining < 2 ^ 64 := by
    simp only [remaining]
    have : keccakAbsorbStep * (n + 1) + rem ≤ keccakAbsorbStep * N + rem := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    omega
  have hwin := bytesRegion_window_focus inputBase input j keccakAbsorbStep
    (by simpa [j] using hfit_blk) hj8 hstep8
  have hunf := bytesRegion_window_unfocus inputBase input j keccakAbsorbStep
    (by simpa [j] using hfit_blk) hj8 hstep8
  let Abody : Assertion := windowRest inputBase input j keccakAbsorbStep ** A
  have hAbody : Abody.pcFree :=
    pcFree_sepConj (pcFree_windowRest _ _ _ _) hA
  have cF := keccakAbsorbOuterBody_step_focused cr liHdr
    scratchBase inputCur remaining st0 blk Abody hAbody
    hst0_len (by simpa [blk, j] using hblk_len)
    hrem_ge hrem64 hb8 hvalid hpc_jal
    hmemMvS hmemMvI hmemLi hmemLdI hmemLdS hmemXor hmemSd
    hmemAddS hmemAddI hmemAddC hmemBne hmemMv10 hmemCsrs hmemA20 hmemA9 hmemJal
  have hcur_succ :
      inputCur + BitVec.ofNat 64 136 = keccakAbsorbCursor inputBase (N - n) := by
    have hsc := keccakAbsorbCursor_succ inputBase (N - (n + 1)) (by
      simp only [keccakAbsorbStep] at hNbound ⊢
      have : 136 * (N - (n + 1) + 1) ≤ 136 * N + rem := by
        have : N - (n + 1) + 1 ≤ N := by omega
        calc 136 * (N - (n + 1) + 1) ≤ 136 * N := Nat.mul_le_mul_left _ (by omega)
          _ ≤ 136 * N + rem := by omega
      omega)
    simpa [inputCur, hk_abs, keccakAbsorbStep] using hsc.symm
  have hst_succ :
      keccakPermuteAbsorbed st0 blk = keccakAbsorbedPrefix input (N - n) := by
    have hs := keccakAbsorbedPrefix_succ input (N - (n + 1))
    simpa [st0, blk, j, hk_abs, keccakAbsorbStep] using hs.symm
  have hrem' : remaining - 136 = keccakAbsorbStep * n + rem := by
    simpa [remaining] using hrem_arith
  have hcur_def : inputCur = inputBase + BitVec.ofNat 64 j := rfl
  -- focused pre/post as named assertions for cleaner weaken
  let Pfocus : Assertion :=
    (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
      (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
      (.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
      (regOwn .x10) **
      regOwns keccakAbsorbOuterTemps **
      bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** Abody
  let Qfocus : Assertion :=
    (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
      (regOwn .x29) **
      (.x8 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
      (regOwn .x10) **
      regOwns keccakAbsorbOuterTemps **
      bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
      bytesRegion inputCur blk ** Abody
  have cF' : cpsTripleWithin keccakAbsorbBodyFuel (liHdr + 8) liHdr cr Pfocus Qfocus := by
    simpa [Pfocus, Qfocus] using cF
  refine cpsTripleWithin_weaken
    (fun h hp => by
      have hp1 : (
          (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
            (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
            (.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
            (regOwn .x10) **
            regOwns keccakAbsorbOuterTemps **
            bytesRegion scratchBase st0 ** bytesRegion inputBase input ** A) h := by
        simpa [keccakAbsorbOuterInv, keccakAbsorbOuterCore, remaining, inputCur, st0] using hp
      -- rewrite full input → window; reassoc to Abody
      have hp2 : (
          (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
            (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
            (.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
            (regOwn .x10) **
            regOwns keccakAbsorbOuterTemps **
            bytesRegion scratchBase st0 **
            bytesRegion inputCur blk **
            windowRest inputBase input j keccakAbsorbStep ** A) h := by
        have hp1' : (
            (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
              (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
              (.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
              (regOwn .x10) **
              regOwns keccakAbsorbOuterTemps **
              bytesRegion scratchBase st0 **
              (bytesRegion inputCur blk **
                windowRest inputBase input j keccakAbsorbStep) ** A) h := by
          -- hwin: full = (base+j)blk ** rest; hcur_def
          simpa [hwin, hcur_def, blk, j] using hp1
        -- reassoc (X ** Y) ** Z → X ** Y ** Z
        xperm_hyp hp1'
      simpa [Pfocus, Abody] using hp2)
    (fun h hq => by
      have hq0 : Qfocus h := by simpa [Qfocus] using hq
      -- Abody = rest ** A; reassoc blk ** rest → full input
      have hq1 : (
          (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
            (regOwn .x29) **
            (.x8 ↦ᵣ scratchBase) **
            (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
            (regOwn .x10) **
            regOwns keccakAbsorbOuterTemps **
            bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
            (bytesRegion inputCur blk **
              windowRest inputBase input j keccakAbsorbStep) ** A) h := by
        simp only [Qfocus, Abody] at hq0
        xperm_hyp hq0
      have hmerge :
          (bytesRegion inputCur blk **
            windowRest inputBase input j keccakAbsorbStep) =
            bytesRegion inputBase input := by
        simpa [hcur_def, blk] using hunf
      have hq2 : (
          (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
            (regOwn .x29) **
            (.x8 ↦ᵣ scratchBase) **
            (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
            (regOwn .x10) **
            regOwns keccakAbsorbOuterTemps **
            bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
            bytesRegion inputBase input ** A) h := by
        simpa [hmerge] using hq1
      have hq3 : (
          (.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * n + rem)) **
            (regOwn .x29) **
            (.x8 ↦ᵣ scratchBase) **
            (.x20 ↦ᵣ keccakAbsorbCursor inputBase (N - n)) **
            (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
            regOwns keccakAbsorbOuterTemps **
            bytesRegion scratchBase (keccakAbsorbedPrefix input (N - n)) **
            bytesRegion inputBase input ** A) h := by
        simpa [hrem', hcur_succ, hst_succ] using hq2
      -- fold into OuterInv
      simpa [keccakAbsorbOuterInv, keccakAbsorbOuterCore] using hq3)
    cF'

/-- Instantiate outer absorb loop with discharged body. -/
theorem keccakAbsorbOuterLoop_spec (cr : CodeReq) (liHdr exitAddr : Word)
    (scratchBase inputBase : Word) (input : List (BitVec 8))
    (N rem : Nat) (A : Assertion) (hA : A.pcFree)
    (hrem : rem < keccakAbsorbStep)
    (hfit : keccakAbsorbStep * N + rem ≤ input.length)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hexit : (liHdr + 4) + signExtend13 keccakAbsorbExitOff = exitAddr)
    (hpc_jal : (liHdr + 8) + 60 + signExtend21 (-68 : BitVec 21) = liHdr)
    (hliMem : ∀ a i,
      CodeReq.singleton liHdr (.LI .x29 (BitVec.ofNat 64 keccakAbsorbStep)) a = some i →
        cr a = some i)
    (hguardMem : ∀ a i,
      CodeReq.singleton (liHdr + 4) (.BLT .x9 .x29 keccakAbsorbExitOff) a = some i →
        cr a = some i)
    (hmemMvS : ∀ a i, CodeReq.singleton (liHdr + 8) (.MV .x28 .x8) a = some i →
      cr a = some i)
    (hmemMvI : ∀ a i, CodeReq.singleton ((liHdr + 8) + 4) (.MV .x30 .x20) a = some i →
      cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton ((liHdr + 8) + 8) (.LI .x31 (17 : Word)) a = some i →
      cr a = some i)
    (hmemLdI : ∀ a i, CodeReq.singleton ((liHdr + 8) + 12) (.LD .x5 .x30 0) a = some i →
      cr a = some i)
    (hmemLdS : ∀ a i, CodeReq.singleton ((liHdr + 8) + 16) (.LD .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton ((liHdr + 8) + 20) (.XOR .x6 .x6 .x5) a = some i →
      cr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton ((liHdr + 8) + 24) (.SD .x28 .x6 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton ((liHdr + 8) + 28) (.ADDI .x28 .x28 8) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton ((liHdr + 8) + 32) (.ADDI .x30 .x30 8) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton ((liHdr + 8) + 36) (.ADDI .x31 .x31 (-1)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton ((liHdr + 8) + 40) (.BNE .x31 .x0 (-28)) a = some i →
      cr a = some i)
    (hmemMv10 : ∀ a i, CodeReq.singleton ((liHdr + 8) + 44) (.MV .x10 .x8) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton ((liHdr + 8) + 48) (.CSRS 0x800 .x10) a = some i →
      cr a = some i)
    (hmemA20 : ∀ a i, CodeReq.singleton ((liHdr + 8) + 52)
        (.ADDI .x20 .x20 (136 : BitVec 12)) a = some i → cr a = some i)
    (hmemA9 : ∀ a i, CodeReq.singleton ((liHdr + 8) + 56)
        (.ADDI .x9 .x9 (-136 : BitVec 12)) a = some i → cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton ((liHdr + 8) + 60)
        (.JAL .x0 (-68 : BitVec 21)) a = some i → cr a = some i) :
    cpsTripleWithin (N * (keccakAbsorbOuterBodyFuel + 2) + 2) liHdr exitAddr cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * N + rem)) **
        (regOwn .x29) **
        keccakAbsorbOuterInv scratchBase inputBase input N N A)
      ((.x9 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
        keccakAbsorbOuterInv scratchBase inputBase input N 0 A) := by
  refine keccakAbsorbOuterLoop_reload cr liHdr exitAddr scratchBase inputBase input
    N rem A hA hrem hNbound hexit hliMem hguardMem
    (fun n => keccakAbsorbOuterInv_pcFree _ _ _ _ _ _ hA)
    (fun n hn =>
      keccakAbsorbOuterBody_step cr liHdr scratchBase inputBase input N rem n A hA
        hn hrem hfit hNbound hb8 hvalid hpc_jal
        hmemMvS hmemMvI hmemLi hmemLdI hmemLdS hmemXor hmemSd
        hmemAddS hmemAddI hmemAddC hmemBne hmemMv10 hmemCsrs hmemA20 hmemA9 hmemJal)

end EvmAsm.Codegen.Proofs
