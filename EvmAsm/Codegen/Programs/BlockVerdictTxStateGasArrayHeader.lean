/-
  Header-validate path (instr 21–32) for `block_verdict_tx_state_gas_array`.

  After prologue (PC = B+84):
    LI t0,4; BLTU len,4 → fail1; MV a0,txBase; jal bgv_u32le;
    ANDI t0,a0,3; BNE t0,0 → fail1; BLTU len,first → fail2;
    SRLI n,first,2; BNE n,count → fail2; BEQ n,0 → ok;
    MV i,0;  -- land at LoopGuard (B+128)

  This file proves:
    1. flat `bgv_u32le` contract via `Fn.retSpecFlat` (leaf already proven SAsm)
    2. success-path header setup (LI/BLTU-fallthrough/MV) under well-formed hyps
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayPrologue
import EvmAsm.Codegen.Programs.BalGasValidSAsm
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.BalGasValidSAsm
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)

/-- Exposed regs other than `a0` — bgv clobbers t0/t1; the rest ride as regOwn. -/
def bgvScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem x10_notin_bgvScratch : (.x10 : Reg) ∉ bgvScratch := by decide

private theorem bgvScratch_nodup : bgvScratch.Nodup := by decide

private theorem exposedRegs_split_bgv (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf bgvScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [bgvScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

/-- Step budget: 11 body instrs + ret. -/
def nBgvSteps : Nat := 12

theorem nBgvSteps_eq :
    nBgvSteps = (bgvU32leFn 0 []).body.steps + 1 := by
  simp only [nBgvSteps, bgvU32leFn, bgvU32leBody, bgvU32leInstrs, Stmt.steps]
  decide

/-- Flat whole-routine contract for `bgv_u32le` (derived from `bgvU32leFn_spec`).
    Requires `Region.wf` (8-aligned base) — header call uses txBase. -/
theorem bgvFlat_spec (ret p : Word) (bs : List (BitVec 8))
    (hLen : 4 ≤ bs.length)
    (hwf : (Region.mk p bs).wf)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin nBgvSteps Bgv ret bgvCode
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ p) ** regOwns bgvScratch **
        bytesRegion p bs)
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ leU32 bs 0) ** regOwns bgvScratch **
        bytesRegion p bs) := by
  rw [nBgvSteps_eq]
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns bgvScratch bgvScratch_nodup
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) ** bytesRegion p bs)
      (fun vf => ?_))
  have had := Fn.retSpecFlat (bgvU32leFn p bs) Bgv
    (bgvU32leFn_spec p bs hwf Bgv)
    (by show 4 * (11 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then p else vf r)
    ([] : List (BitVec 8))
    (by simp [bgvU32leFn, RwRegion.empty])
    (by
      refine And.intro ?_ (And.intro hLen rfl)
      show RegFile.get (fun r => if r = .x10 then p else vf r) .x10 = p
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl)
    (fun _ _ _ h => h.2)
    (Q := (.x10 ↦ᵣ leU32 bs 0) ** regOwns bgvScratch)
    (fun rf' ws' hlen' hpost hp hh => by
      obtain ⟨hx10', -⟩ := hpost
      have hx : rf' .x10 = leU32 bs 0 := by
        have : RegFile.get rf' .x10 = leU32 bs 0 := hx10'
        rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)] at this
        exact this
      have hws : ws' = ([] : List (BitVec 8)) := by
        have : ws'.length = 0 := by
          simpa [bgvU32leFn, RwRegion.empty] using hlen'
        exact List.eq_nil_of_length_eq_zero this
      subst hws
      -- Empty rw window: bytesRegion _ [] = emp (rfl); drop it once.
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_bgv, show rf' .x10 = leU32 bs 0 from hx,
        bytesRegion_nil, sepConj_emp_right'] at hh
      have hh2 : (((.x10 ↦ᵣ leU32 bs 0) ** regOwns bgvScratch) hp) :=
        sepConj_mono (fun _ h => h)
          (regAtomsOf_to_regOwns (fun r => rf' r) bgvScratch) hp hh
      xperm_hyp hh2)
  rw [show (bgvU32leFn p bs).programRet Bgv = bgvProg from by
    simp only [Fn.programRet, bgvU32leFn, bgvU32leBody, bgvU32leInstrs,
      bgvProg, bgvU32le_prog]
    rfl] at had
  have hadC := liftCode (cr' := bgvCode) had (by unfold bgvCode; intro a i h; exact h)
  -- Empty rw rides inside the regFileIs triple; drop it once (region is non-empty).
  rw [bytesRegion_nil (bgvU32leFn p bs).rw.base, sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_bgv,
    show (if (Reg.x10 : Reg) = .x10 then p else vf .x10) = p from if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then p else vf r) vf bgvScratch
      (fun r hr => by
        show (if r = .x10 then p else vf r) = vf r
        exact if_neg (fun hc => by subst hc; exact x10_notin_bgvScratch hr)),
    show (bgvU32leFn p bs).region.base = p from rfl,
    show (bgvU32leFn p bs).region.bytes = bs from rfl] at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

/-- Link address after the header bgv call (instr 24 → B+96+4). -/
abbrev LinkHeaderBgv : Word := B + 100

/-- Pure well-formedness of the SSZ offset-table header that the success path
    requires (static; known before run). -/
structure HeaderOk (txBlob : List (BitVec 8)) (count : Nat) where
  /-- At least the first u32 offset is present. -/
  hLen : 4 ≤ txBlob.length
  /-- First u32 is 4-byte aligned. -/
  hAlign : (leU32 txBlob 0).toNat % 4 = 0
  /-- First u32 ≤ body length. -/
  hSpan : (leU32 txBlob 0).toNat ≤ txBlob.length
  /-- Decoded count matches the ABI count argument. -/
  hCount : (leU32 txBlob 0).toNat / 4 = count
  /-- Non-empty: empty is a separate ok-exit before the loop. -/
  hNonEmpty : count ≠ 0
  /-- Length fits in a Word (static guest bound). -/
  hLenBound : txBlob.length < 2 ^ 64

set_option maxRecDepth 8000 in
/-- Setup before the first bgv call: LI 4; BLTU notaken; MV a0,txBase.
    Lands at B+96 ready to jal. Requires 4 ≤ txLen (static). -/
theorem bvtHeaderSetup (spC : Word) (s : Saved)
    (txBase txLenW countW outBase balBase balLenW chainIdW : Word)
    (old5 old6 old7 : Word)
    (txLen : Nat)
    (htxLenW : txLenW = BitVec.ofNat 64 txLen)
    (hLen : 4 ≤ txLen)
    (hLenBound : txLen < 2 ^ 64) :
    cpsTripleWithin 3 (B + 84) (B + 96) bvtCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
        (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
        (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
        (.x27 ↦ᵣ s.s11) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        (.x10 ↦ᵣ txBase) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
        (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
        (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
        (.x27 ↦ᵣ s.s11) **
        (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        (.x10 ↦ᵣ txBase) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) := by
  -- instr 21: LI x5, 4
  have h0 := li_spec_gen_within .x5 old5 (4 : Word) (B + 84) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 84) bvtProg 21
      (.LI .x5 (4 : Word)) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) h0
  have e0F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
      (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
      (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x27 ↦ᵣ s.s11) **
      (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
      (.x10 ↦ᵣ txBase) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) e0
  -- instr 22: BLTU x9, x5, fail — not taken when 4 ≤ txLen
  have hbr0 := bltu_spec_gen_within .x9 .x5 (216 : BitVec 13) txLenW (4 : Word)
    (B + 88)
  have hbr0C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 88) bvtProg 22
      (.BLTU .x9 .x5 (216 : BitVec 13)) (by bv_omega) (by rw [bvt_length]; decide)
      rfl (by rw [bvt_length]; decide)) hbr0
  have h_not_ult : ¬ (BitVec.ult txLenW (4 : Word) = true) := by
    simp only [BitVec.ult, decide_eq_true_eq, not_lt]
    rw [htxLenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLenBound]
    exact hLen
  have hnt0 : cpsTripleWithin 1 (B + 88) (B + 92) bvtCode
      ((.x9 ↦ᵣ txLenW) ** (.x5 ↦ᵣ (4 : Word)))
      ((.x9 ↦ᵣ txLenW) ** (.x5 ↦ᵣ (4 : Word))) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr0C (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact h_not_ult ((sepConj_pure_right _).1 hQ).2)
    rw [show (B + 88 + 4 : Word) = B + 92 from by bv_omega] at hnt
    exact hnt
  have e1F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
      (.x8 ↦ᵣ txBase) **
      (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
      (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x27 ↦ᵣ s.s11) **
      (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
      (.x10 ↦ᵣ txBase) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hnt0
  -- instr 23: MV x10, x8
  have h2 := mv_spec_gen_within .x10 .x8 txBase txBase (B + 92) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 92) bvtProg 23
      (.MV .x10 .x8) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) h2
  have e2F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
      (.x9 ↦ᵣ txLenW) **
      (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
      (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x27 ↦ᵣ s.s11) **
      (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) e2
  -- Compose: e0F ;; e1F ;; e2F, then reshape PC/order to the theorem statement.
  have h01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e0F e1F
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h01 e2F
  rw [show (B + 92 + 4 : Word) = B + 96 from by bv_omega] at hall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
