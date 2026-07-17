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
import EvmAsm.Rv64.SAsm.AbiFrameCall
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

/-- Caller-private atoms framed across the header `bgv_u32le` call. -/
def headerBgvFrame (spC : Word) (s : Saved)
    (txBase txLenW countW outBase balBase balLenW chainIdW : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
  (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
  (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
  (.x27 ↦ᵣ s.s11) **
  (.x0 ↦ᵣ (0 : Word))

private theorem headerBgvFrame_pcFree (spC : Word) (s : Saved)
    (txBase txLenW countW outBase balBase balLenW chainIdW : Word) :
    (headerBgvFrame spC s txBase txLenW countW outBase balBase balLenW chainIdW).pcFree := by
  unfold headerBgvFrame; pcf

/-- Pure: 4-aligned Word has low 2 bits clear. -/
private theorem word_and_3_eq_zero_of_mod4
    (w : Word) (h : w.toNat % 4 = 0) : w &&& (3 : Word) = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (3 : Word).toNat = 3 from rfl]
  have key : w.toNat &&& 3 = w.toNat % 4 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod w.toNat 2
  rw [key, h]; rfl

private theorem se12_three : signExtend12 (3 : BitVec 12) = (3 : Word) := by decide

/-- JAL offset for the header `bgv_u32le` call (instr 24 @ B+96). -/
abbrev headerBgvJalOff : BitVec 21 :=
  jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_tx_state_gas_array + 96)

set_option maxRecDepth 8000 in
/-- Header `bgv_u32le` call (instr 24): lands at LinkHeaderBgv with `a0 = leU32`. -/
theorem bvtHeaderBgvCall (spC : Word) (s : Saved)
    (txBase txLenW countW outBase balBase balLenW chainIdW : Word)
    (txBlob : List (BitVec 8))
    (hLen : 4 ≤ txBlob.length)
    (hwf : (Region.mk txBase txBlob).wf) :
    cpsTripleWithin (1 + nBgvSteps) (B + 96) LinkHeaderBgv fullCode
      ((.x1 ↦ᵣ s.ra) **
        (.x10 ↦ᵣ txBase) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        headerBgvFrame spC s txBase txLenW countW outBase balBase balLenW chainIdW)
      ((.x1 ↦ᵣ LinkHeaderBgv) **
        (.x10 ↦ᵣ leU32 txBlob 0) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        headerBgvFrame spC s txBase txLenW countW outBase balBase balLenW chainIdW) := by
  have hflat := bgvFlat_spec LinkHeaderBgv txBase txBlob hLen hwf
    (by show LinkHeaderBgv &&& ~~~(1 : Word) = LinkHeaderBgv; decide)
  have hflatC := cpsTripleWithin_extend_code bgv_mono hflat
  have hflatF := cpsTripleWithin_frameR
    (headerBgvFrame spC s txBase txLenW countW outBase balBase balLenW chainIdW)
    (headerBgvFrame_pcFree spC s txBase txLenW countW outBase balBase balLenW chainIdW)
    hflatC
  have hcallee : cpsTripleWithin nBgvSteps Bgv LinkHeaderBgv fullCode
      ((.x1 ↦ᵣ LinkHeaderBgv) **
        ((.x10 ↦ᵣ txBase) ** regOwns bgvScratch ** bytesRegion txBase txBlob **
          headerBgvFrame spC s txBase txLenW countW outBase balBase balLenW chainIdW))
      ((.x1 ↦ᵣ LinkHeaderBgv) **
        ((.x10 ↦ᵣ leU32 txBlob 0) ** regOwns bgvScratch ** bytesRegion txBase txBlob **
          headerBgvFrame spC s txBase txLenW countW outBase balBase balLenW chainIdW)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hflatF
  have hcall := callWithin_spec (B + 96) Bgv s.ra headerBgvJalOff nBgvSteps
    (by show (B + 96) + signExtend21 headerBgvJalOff = Bgv; decide)
    (fun a i hi => bvt_mono a i
      (CodeReq.ofProg_mem_at B (B + 96) bvtProg 24
        (.JAL .x1 headerBgvJalOff) (by bv_omega) (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide) a i hi))
    (by
      apply pcFree_sepConj
      · exact pcFree_regIs
      · apply pcFree_sepConj
        · exact pcFree_regOwns _
        · apply pcFree_sepConj
          · exact bytesRegion_pcFree _ _
          · exact headerBgvFrame_pcFree _ _ _ _ _ _ _ _ _)
    hcallee
  rw [show (B + 96 + 4 : Word) = LinkHeaderBgv from by
    simp only [LinkHeaderBgv]; bv_omega] at hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hcall

/-- Tail of `bgvScratch` after peeling `x5` (ANDI dest). -/
def bgvScratchTail : List Reg :=
  [.x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem bgvScratch_cons :
    bgvScratch = (.x5 : Reg) :: bgvScratchTail := rfl

private theorem first_ushiftRight_eq_countW
    (txBlob : List (BitVec 8)) (count : Nat) (countW : Word)
    (hcountW : countW = BitVec.ofNat 64 count)
    (hok : HeaderOk txBlob count) :
    leU32 txBlob 0 >>> (2 : Nat) = countW := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, hcountW, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hlt : count < 2 ^ 64 := by
    have hspan := hok.hSpan
    have hlen := hok.hLenBound
    have hdiv := hok.hCount
    omega
  -- (leU32).toNat / 2^2 = count % 2^64
  change (leU32 txBlob 0).toNat / 4 = count % 2 ^ 64
  rw [hok.hCount, Nat.mod_eq_of_lt hlt]

/-- Local pcFree discharge for framed header atoms + regOwns. -/
local macro "bvt_pcf" : tactic =>
  `(tactic| repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_regOwns _
    | exact pcFree_emp
    | exact pcFree_pure)

set_option maxRecDepth 8000 in
/-- Post-bgv success checks (instr 25–31) under `HeaderOk`: land at LoopGuard
    with `x20 = countW`, `x21 = 0`, `x10 = first`. -/
theorem bvtHeaderChecks (spC : Word) (s : Saved)
    (txBase txLenW countW outBase balBase balLenW chainIdW : Word)
    (txBlob : List (BitVec 8)) (count : Nat)
    (htxLenW : txLenW = BitVec.ofNat 64 txBlob.length)
    (hcountW : countW = BitVec.ofNat 64 count)
    (hok : HeaderOk txBlob count) :
    let first := leU32 txBlob 0
    cpsTripleWithin 7 LinkHeaderBgv LoopGuard bvtCode
      ((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
        (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
        (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
        (.x27 ↦ᵣ s.s11) **
        (.x10 ↦ᵣ first) ** regOwns bgvScratch **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
        (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ countW) ** (.x21 ↦ᵣ (0 : Word)) **
        (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
        (.x27 ↦ᵣ s.s11) **
        (.x10 ↦ᵣ first) ** (.x5 ↦ᵣ (0 : Word)) ** regOwns bgvScratchTail **
        (.x0 ↦ᵣ (0 : Word))) := by
  intro first
  have hfirst_and : first &&& signExtend12 (3 : BitVec 12) = 0 := by
    rw [se12_three]; exact word_and_3_eq_zero_of_mod4 first hok.hAlign
  have hnW : first >>> (2 : Nat) = countW :=
    first_ushiftRight_eq_countW txBlob count countW hcountW hok
  -- instr 25: ANDI x5, x10, 3  (peel regOwn x5 from bgvScratch)
  have e25 : cpsTripleWithin 1 LinkHeaderBgv (B + 104) bvtCode
      ((.x10 ↦ᵣ first) ** regOwns bgvScratch)
      ((.x10 ↦ᵣ first) ** (.x5 ↦ᵣ (0 : Word)) ** regOwns bgvScratchTail) := by
    rw [bgvScratch_cons, regOwns_cons]
    -- pre = x10 ** (regOwn x5 ** tail) → peel via of_forall
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
        (P := (.x10 ↦ᵣ first) ** regOwns bgvScratchTail)
        (fun vOld => ?_))
    have h := andi_spec_gen_within .x5 .x10 vOld first (3 : BitVec 12)
      LinkHeaderBgv (by decide)
    have e := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at B LinkHeaderBgv bvtProg 25
        (.ANDI .x5 .x10 (3 : BitVec 12)) (by bv_omega) (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide)) h
    have eF := cpsTripleWithin_frameR (regOwns bgvScratchTail) (pcFree_regOwns _) e
    rw [show (LinkHeaderBgv + 4 : Word) = B + 104 from by
      simp only [LinkHeaderBgv]; bv_omega] at eF
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        rw [hfirst_and] at hq
        xperm_hyp hq) eF
  have e25F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
      (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
      (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x27 ↦ᵣ s.s11) **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) e25
  -- instr 26: BNE x5, x0 → fail1  (not taken: x5 = 0)
  have hbr26 := bne_spec_gen_within .x5 .x0 (200 : BitVec 13) (0 : Word) (0 : Word) (B + 104)
  have hbr26C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 104) bvtProg 26
      (.BNE .x5 .x0 (200 : BitVec 13)) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr26
  have e26 : cpsTripleWithin 1 (B + 104) (B + 108) bvtCode
      ((.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr26C (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 rfl)
    rw [show (B + 104 + 4 : Word) = B + 108 from by bv_omega] at hnt
    exact hnt
  have e26F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
      (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
      (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x27 ↦ᵣ s.s11) **
      (.x10 ↦ᵣ first) ** regOwns bgvScratchTail) (by bvt_pcf) e26
  -- instr 27: BLTU x9, x10 → fail2  (not taken: first ≤ len)
  have h_not_ult : ¬ BitVec.ult txLenW first = true := by
    simp only [BitVec.ult, decide_eq_true_eq, not_lt]
    rw [htxLenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hok.hLenBound]
    exact hok.hSpan
  have hbr27 := bltu_spec_gen_within .x9 .x10 (196 : BitVec 13) txLenW first (B + 108)
  have hbr27C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 108) bvtProg 27
      (.BLTU .x9 .x10 (196 : BitVec 13)) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr27
  have e27 : cpsTripleWithin 1 (B + 108) (B + 112) bvtCode
      ((.x9 ↦ᵣ txLenW) ** (.x10 ↦ᵣ first))
      ((.x9 ↦ᵣ txLenW) ** (.x10 ↦ᵣ first)) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr27C (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact h_not_ult ((sepConj_pure_right _).1 hQ).2)
    rw [show (B + 108 + 4 : Word) = B + 112 from by bv_omega] at hnt
    exact hnt
  have e27F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) **
      (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
      (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x27 ↦ᵣ s.s11) **
      (.x5 ↦ᵣ (0 : Word)) ** regOwns bgvScratchTail **
      (.x0 ↦ᵣ (0 : Word))) (by bvt_pcf) e27
  -- instr 28: SRLI x20, x10, 2
  have h28 := srli_spec_gen_within .x20 .x10 s.s4 first (2 : BitVec 6) (B + 112) (by decide)
  have e28 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 112) bvtProg 28
      (.SRLI .x20 .x10 (2 : BitVec 6)) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) h28
  have e28' : cpsTripleWithin 1 (B + 112) (B + 116) bvtCode
      ((.x10 ↦ᵣ first) ** (.x20 ↦ᵣ s.s4))
      ((.x10 ↦ᵣ first) ** (.x20 ↦ᵣ countW)) := by
    have eF := e28
    rw [show (B + 112 + 4 : Word) = B + 116 from by bv_omega] at eF
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by
        have : first >>> (2 : BitVec 6).toNat = first >>> (2 : Nat) := rfl
        rw [this, hnW] at hq; exact hq) eF
  have e28F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
      (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
      (.x21 ↦ᵣ s.s5) **
      (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x27 ↦ᵣ s.s11) **
      (.x5 ↦ᵣ (0 : Word)) ** regOwns bgvScratchTail **
      (.x0 ↦ᵣ (0 : Word))) (by bvt_pcf) e28'
  -- instr 29: BNE x20, x18 → fail2  (not taken: n = count)
  have hbr29 := bne_spec_gen_within .x20 .x18 (196 : BitVec 13) countW countW (B + 116)
  have hbr29C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 116) bvtProg 29
      (.BNE .x20 .x18 (196 : BitVec 13)) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr29
  have e29 : cpsTripleWithin 1 (B + 116) (B + 120) bvtCode
      ((.x20 ↦ᵣ countW) ** (.x18 ↦ᵣ countW))
      ((.x20 ↦ᵣ countW) ** (.x18 ↦ᵣ countW)) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr29C (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 rfl)
    rw [show (B + 116 + 4 : Word) = B + 120 from by bv_omega] at hnt
    exact hnt
  have e29F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
      (.x19 ↦ᵣ outBase) **
      (.x21 ↦ᵣ s.s5) **
      (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x27 ↦ᵣ s.s11) **
      (.x10 ↦ᵣ first) ** (.x5 ↦ᵣ (0 : Word)) ** regOwns bgvScratchTail **
      (.x0 ↦ᵣ (0 : Word))) (by bvt_pcf) e29
  -- instr 30: BEQ x20, x0 → ok  (not taken: count ≠ 0)
  have h_ne_zero : countW ≠ (0 : Word) := by
    intro heq
    have : count = 0 := by
      have h1 := congrArg BitVec.toNat heq
      rw [hcountW, BitVec.toNat_ofNat] at h1
      change count % 2 ^ 64 = 0 at h1
      have hlt : count < 2 ^ 64 := by
        have := hok.hSpan; have := hok.hLenBound; have := hok.hCount; omega
      rw [Nat.mod_eq_of_lt hlt] at h1; exact h1
    exact hok.hNonEmpty this
  have hbr30 := beq_spec_gen_within .x20 .x0 (176 : BitVec 13) countW (0 : Word) (B + 120)
  have hbr30C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 120) bvtProg 30
      (.BEQ .x20 .x0 (176 : BitVec 13)) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr30
  have e30 : cpsTripleWithin 1 (B + 120) (B + 124) bvtCode
      ((.x20 ↦ᵣ countW) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ countW) ** (.x0 ↦ᵣ (0 : Word))) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr30C (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact h_ne_zero ((sepConj_pure_right _).1 hQ).2)
    rw [show (B + 120 + 4 : Word) = B + 124 from by bv_omega] at hnt
    exact hnt
  have e30F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
      (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
      (.x21 ↦ᵣ s.s5) **
      (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x27 ↦ᵣ s.s11) **
      (.x10 ↦ᵣ first) ** (.x5 ↦ᵣ (0 : Word)) ** regOwns bgvScratchTail)
    (by bvt_pcf) e30
  -- instr 31: MV x21, x0
  have h31 := mv_spec_gen_within .x21 .x0 (0 : Word) s.s5 (B + 124) (by decide)
  have e31 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 124) bvtProg 31
      (.MV .x21 .x0) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) h31
  -- MV focus owns x0 + x21; frame excludes both
  have e31F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
      (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ countW) **
      (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x27 ↦ᵣ s.s11) **
      (.x10 ↦ᵣ first) ** (.x5 ↦ᵣ (0 : Word)) ** regOwns bgvScratchTail)
    (by bvt_pcf) e31
  -- Compose 25..31
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e25F e26F
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 e27F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 e28F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 e29F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 e30F
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 e31F
  rw [show (B + 124 + 4 : Word) = LoopGuard from by
    simp only [LoopGuard]; bv_omega] at c06
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c06

/-- a-temps in `bgvScratch` not touched by header setup LI/MV. -/
def bgvScratchATemps : List Reg :=
  [.x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem bgvScratch_eq_setup_list :
    bgvScratch =
      (.x5 :: .x6 :: .x7 :: .x28 :: .x29 :: .x30 :: .x31 :: bgvScratchATemps) :=
  rfl

/-- Pack concrete t0–t2 + owned s-temps + a-temps into `regOwns bgvScratch`. -/
private theorem pack_bgvScratch (v5 v6 v7 : Word) :
    ∀ h, (((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            regOwns bgvScratchATemps) h) →
      (regOwns bgvScratch) h := by
  intro h hp
  rw [bgvScratch_eq_setup_list, regOwns_cons, regOwns_cons, regOwns_cons,
    regOwns_cons, regOwns_cons, regOwns_cons, regOwns_cons]
  exact sepConj_mono (regIs_to_regOwn .x5 v5)
    (sepConj_mono (regIs_to_regOwn .x6 v6)
      (sepConj_mono (regIs_to_regOwn .x7 v7) (fun _ hh => hh))) h hp

/-- Step budget: setup(3) + jal+bgv(1+nBgv) + checks(7). -/
def nHeaderSuccessSteps : Nat := 3 + (1 + nBgvSteps) + 7

set_option maxRecDepth 8000 in
/-- Full header success path under `HeaderOk`: B+84 → LoopGuard with
    `x20 = countW`, `x21 = 0`, first u32 in `x10`, payload/frame preserved. -/
theorem bvtHeaderSuccess (spC : Word) (s : Saved)
    (txBase txLenW countW outBase balBase balLenW chainIdW : Word)
    (old5 old6 old7 : Word)
    (txBlob : List (BitVec 8)) (count : Nat)
    (htxLenW : txLenW = BitVec.ofNat 64 txBlob.length)
    (hcountW : countW = BitVec.ofNat 64 count)
    (hok : HeaderOk txBlob count)
    (hwf : (Region.mk txBase txBlob).wf) :
    let first := leU32 txBlob 0
    cpsTripleWithin nHeaderSuccessSteps (B + 84) LoopGuard fullCode
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
        regOwns bgvScratchATemps **
        bytesRegion txBase txBlob **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
        (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ countW) ** (.x21 ↦ᵣ (0 : Word)) **
        (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
        (.x27 ↦ᵣ s.s11) **
        (.x10 ↦ᵣ first) ** (.x5 ↦ᵣ (0 : Word)) ** regOwns bgvScratchTail **
        bytesRegion txBase txBlob **
        (.x0 ↦ᵣ (0 : Word))) := by
  intro first
  -- Phase 1: setup framed with a-temps + RO region, lifted to fullCode
  have hsetup0 := bvtHeaderSetup spC s txBase txLenW countW outBase
    balBase balLenW chainIdW old5 old6 old7 txBlob.length htxLenW
    hok.hLen hok.hLenBound
  have hsetupF := cpsTripleWithin_frameR
    (regOwns bgvScratchATemps ** bytesRegion txBase txBlob)
    (by
      apply pcFree_sepConj
      · exact pcFree_regOwns _
      · exact bytesRegion_pcFree _ _) hsetup0
  have hsetupC := cpsTripleWithin_extend_code bvt_mono hsetupF
  -- Reshape setup post → call pre (pack scratch owns via sepConj_mono)
  have hsetup' : cpsTripleWithin 3 (B + 84) (B + 96) fullCode
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
        regOwns bgvScratchATemps **
        bytesRegion txBase txBlob **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ s.ra) **
        (.x10 ↦ᵣ txBase) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        headerBgvFrame spC s txBase txLenW countW outBase balBase balLenW
          chainIdW) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_ hsetupC
    intro h hq
    -- Pull packable scratch atoms left; remainder = ra/a0/bytes/frame.
    have hq1 :
        (((.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            regOwns bgvScratchATemps) **
          ((.x1 ↦ᵣ s.ra) ** (.x10 ↦ᵣ txBase) ** bytesRegion txBase txBlob **
            headerBgvFrame spC s txBase txLenW countW outBase balBase balLenW
              chainIdW)) h := by
      unfold headerBgvFrame
      xperm_hyp hq
    have hq2 :=
      sepConj_mono (pack_bgvScratch (4 : Word) old6 old7) (fun _ hh => hh) h hq1
    xperm_hyp hq2
  -- Phase 2: bgv call (post already matches checks pre after xperm)
  have hcall := bvtHeaderBgvCall spC s txBase txLenW countW outBase
    balBase balLenW chainIdW txBlob hok.hLen hwf
  -- Phase 3: checks framed with RO region, lifted to fullCode
  have hchk0 := bvtHeaderChecks spC s txBase txLenW countW outBase
    balBase balLenW chainIdW txBlob count htxLenW hcountW hok
  have hchkF := cpsTripleWithin_frameR (bytesRegion txBase txBlob)
    (bytesRegion_pcFree _ _) hchk0
  have hchkC := cpsTripleWithin_extend_code bvt_mono hchkF
  -- Compose: setup' ;; call ;; checks (xperm across frame unfold)
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsetup' hcall
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      -- call post: ra ** a0 ** regOwns bgvScratch ** bytes ** headerBgvFrame
      -- checks pre: (ra ** s-regs ** a0 ** regOwns bgvScratch ** x0) ** bytes
      unfold headerBgvFrame at hp
      xperm_hyp hp) c01 hchkC
  change cpsTripleWithin (3 + (1 + nBgvSteps) + 7) (B + 84) LoopGuard fullCode
    _ _ at c02
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c02

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
