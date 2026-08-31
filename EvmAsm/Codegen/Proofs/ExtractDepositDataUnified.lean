/-
  EvmAsm.Codegen.Proofs.ExtractDepositDataUnified

  #13070 step 2: ONE whole-routine contract for `extract_deposit_data`
  with the case split internal, subsuming the twelve arm triples.  The
  key collapse: every failure arm — wrong length, or ABI check `k`
  rejecting — leaves the SAME machine state (a0 = 1, registers/frame
  restored, no memory written), so the post is a two-way `if` on the
  decidable acceptance predicate `eddAccept`, not a twelve-way match.

  Still pinned to the deployed probe arenas (`dp`/`op`);
  the arena-parametric generalization is #13070's recorded remainder
  (step 1).
-/

import EvmAsm.Codegen.Proofs.ExtractDepositDataOkSpec
import EvmAsm.Codegen.Proofs.ExtractDepositDataFailSpec

namespace EvmAsm.Codegen.ExtractDepositDataUnified

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen (extractDepositData_prog
  extractDepositDataBundle_prog)
open EvmAsm.Codegen.ExtractDepositDataOkSpec

/-- Local `pcFree` discharge covering the framed atoms. -/
local macro "u_pcfree" : tactic => `(tactic| repeat (first
  | apply pcFree_sepConj
  | exact pcFree_regIs
  | exact pcFree_regOwn
  | exact pcFree_memIs
  | exact pcFree_emp
  | exact pcFree_pure
  | exact bytesRegion_pcFree _ _
  | exact pcFree_regAtomsOf _ _
  | exact pcFree_regOwns _))

/-- The acceptance predicate: canonical length and all ten ABI header
    checks pass.  Decidable, so the unified post can case on it. -/
def eddAccept (dp lenW : Word)
    (b0 b32 b64 b96 b128 b160 b256 b320 b384 b512 : List (BitVec 8)) : Prop :=
  lenW = (576 : Word) ∧
  EddBe32EqSAsm.eddOk dp b0 (160 : Word) ∧
  EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 32) b32 (256 : Word) ∧
  EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 64) b64 (320 : Word) ∧
  EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 96) b96 (384 : Word) ∧
  EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 128) b128 (512 : Word) ∧
  EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 160) b160 (48 : Word) ∧
  EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 256) b256 (32 : Word) ∧
  EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 320) b320 (8 : Word) ∧
  EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 384) b384 (96 : Word) ∧
  EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 512) b512 (8 : Word)

instance (dp lenW : Word) (b0 b32 b64 b96 b128 b160 b256 b320 b384 b512 : List (BitVec 8)) :
    Decidable (eddAccept dp lenW b0 b32 b64 b96 b128 b160 b256 b320 b384 b512) := by
  unfold eddAccept
  infer_instance

/-- The accept-arm post: `a0 = 0`, the five raw fields copied to the
    output arena, registers and frame restored. -/
def eddOkPost (dp op sp0 ret v8 v9 : Word)
    (b0 b32 b64 b96 b128 b160 b256 b320 b384 b512 s192 s288 s352 s416 s544 : List (BitVec 8)) : Assertion :=
  ((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
    ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    regOwns eddScr14 **
    ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ ret) **
    ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ v8) **
    ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ v9) **
    bytesRegion dp b0 **
    bytesRegion (dp + BitVec.ofNat 64 32) b32 **
    bytesRegion (dp + BitVec.ofNat 64 64) b64 **
    bytesRegion (dp + BitVec.ofNat 64 96) b96 **
    bytesRegion (dp + BitVec.ofNat 64 128) b128 **
    bytesRegion (dp + BitVec.ofNat 64 160) b160 **
    bytesRegion (dp + BitVec.ofNat 64 256) b256 **
    bytesRegion (dp + BitVec.ofNat 64 320) b320 **
    bytesRegion (dp + BitVec.ofNat 64 384) b384 **
    bytesRegion (dp + BitVec.ofNat 64 512) b512 **
    bytesRegion (dp + BitVec.ofNat 64 192) s192 **
    bytesRegion (dp + BitVec.ofNat 64 288) s288 **
    bytesRegion (dp + BitVec.ofNat 64 352) s352 **
    bytesRegion (dp + BitVec.ofNat 64 416) s416 **
    bytesRegion (dp + BitVec.ofNat 64 544) s544 **
    bytesRegion op s192 **
    bytesRegion (op + BitVec.ofNat 64 48) s288 **
    bytesRegion (op + BitVec.ofNat 64 80) s352 **
    bytesRegion (op + BitVec.ofNat 64 88) s416 **
    bytesRegion (op + BitVec.ofNat 64 184) s544

/-- The shared failure post (wrong length OR any check rejecting):
    `a0 = 1`, registers and frame restored, NOTHING written — every
    memory region intact. -/
def eddRejPost (dp op sp0 ret v8 v9 : Word)
    (b0 b32 b64 b96 b128 b160 b256 b320 b384 b512 s192 s288 s352 s416 s544 w0 w48 w80 w88 w184 : List (BitVec 8)) : Assertion :=
  ((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
    ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
    ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    regOwns eddScr14 **
    ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ ret) **
    ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ v8) **
    ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ v9) **
    bytesRegion dp b0 **
    bytesRegion (dp + BitVec.ofNat 64 32) b32 **
    bytesRegion (dp + BitVec.ofNat 64 64) b64 **
    bytesRegion (dp + BitVec.ofNat 64 96) b96 **
    bytesRegion (dp + BitVec.ofNat 64 128) b128 **
    bytesRegion (dp + BitVec.ofNat 64 160) b160 **
    bytesRegion (dp + BitVec.ofNat 64 256) b256 **
    bytesRegion (dp + BitVec.ofNat 64 320) b320 **
    bytesRegion (dp + BitVec.ofNat 64 384) b384 **
    bytesRegion (dp + BitVec.ofNat 64 512) b512 **
    bytesRegion (dp + BitVec.ofNat 64 192) s192 **
    bytesRegion (dp + BitVec.ofNat 64 288) s288 **
    bytesRegion (dp + BitVec.ofNat 64 352) s352 **
    bytesRegion (dp + BitVec.ofNat 64 416) s416 **
    bytesRegion (dp + BitVec.ofNat 64 544) s544 **
    bytesRegion op w0 **
    bytesRegion (op + BitVec.ofNat 64 48) w48 **
    bytesRegion (op + BitVec.ofNat 64 80) w80 **
    bytesRegion (op + BitVec.ofNat 64 88) w88 **
    bytesRegion (op + BitVec.ofNat 64 184) w184

private theorem cps_fuel_mono {n m : Nat} {entry exit_ : Word}
    {cr : CodeReq} {P Q : Assertion} (hnm : n ≤ m)
    (h : cpsTripleWithin n entry exit_ cr P Q) :
    cpsTripleWithin m entry exit_ cr P Q := by
  intro R hR s hcr hp hpc
  obtain ⟨k, hk, rest⟩ := h R hR s hcr hp hpc
  exact ⟨k, Nat.le_trans hk hnm, rest⟩

set_option maxRecDepth 20000 in
/-- The main-body image is the bundle's prefix. -/
private theorem main_sub :
    ∀ a i, CodeReq.ofProg EddB (extractDepositData_prog : List Instr)
        a = some i →
      eddbCode a = some i :=
  CodeReq.ofProg_mono_sub EddB EddB
    extractDepositDataBundle_prog extractDepositData_prog 0
    (by decide) (by decide) (by decide) (by decide)

/-- The failure arms' scratch recombination: the three argument
    registers the prologue pinned rejoin the eleven merely-owned ones. -/
private theorem edd_owns_fail_recombine :
    ∀ h, ((regOwn .x5 ** regOwn .x11 ** regOwn .x12) **
        regOwns eddScrPre) h →
      regOwns eddScr14 h := by
  intro h hp
  show regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x11, .x12, .x13, .x14, .x15, .x16, .x17] h
  simp only [regOwns_cons, regOwns_nil]
  simp only [eddScrPre, regOwns_cons, regOwns_nil] at hp
  xperm_hyp hp

set_option maxRecDepth 400000 in
/-- ⭐ **The unified whole-routine contract of `extract_deposit_data`**
    (#13070): one triple, total over the payload — the post cases on the
    decidable `eddAccept` (canonical length ∧ all ten ABI checks).  On
    accept the five raw fields land in the output arena and `a0 = 0`;
    otherwise `a0 = 1` and nothing is written.  Subsumes the twelve arm
    triples (their per-arm statements remain the proof's dispatch
    targets). -/
theorem extractDepositData_spec
    (dp op : Word)
    (hdp : eddDataArenaOk dp) (hop : eddOutArenaOk op)
    (hdj : eddArenasDisjoint dp op)
    (sp0 ret v5 v8 v9 m0 m1 m2 lenW : Word)
    (b0 b32 b64 b96 b128 b160 b256 b320 b384 b512 : List (BitVec 8))
    (s192 s288 s352 s416 s544 : List (BitVec 8))
    (w0 w48 w80 w88 w184 : List (BitVec 8))
    (hb0 : b0.length = 32) (hb32 : b32.length = 32)
    (hb64 : b64.length = 32) (hb96 : b96.length = 32)
    (hb128 : b128.length = 32) (hb160 : b160.length = 32)
    (hb256 : b256.length = 32) (hb320 : b320.length = 32)
    (hb384 : b384.length = 32) (hb512 : b512.length = 32)
    (hs192 : s192.length = 48) (hs288 : s288.length = 32)
    (hs352 : s352.length = 8) (hs416 : s416.length = 96)
    (hs544 : s544.length = 8)
    (hw0 : w0.length = 48) (hw48 : w48.length = 32)
    (hw80 : w80.length = 8) (hw88 : w88.length = 96)
    (hw184 : w184.length = 8)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 7749 EddB (ret &&& ~~~1) eddbCode
      (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ dp) ** ((.x11 : Reg) ↦ᵣ lenW) **
        ((.x12 : Reg) ↦ᵣ op) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns eddScrPre **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2) **
        bytesRegion dp b0 **
        bytesRegion (dp + BitVec.ofNat 64 32) b32 **
        bytesRegion (dp + BitVec.ofNat 64 64) b64 **
        bytesRegion (dp + BitVec.ofNat 64 96) b96 **
        bytesRegion (dp + BitVec.ofNat 64 128) b128 **
        bytesRegion (dp + BitVec.ofNat 64 160) b160 **
        bytesRegion (dp + BitVec.ofNat 64 256) b256 **
        bytesRegion (dp + BitVec.ofNat 64 320) b320 **
        bytesRegion (dp + BitVec.ofNat 64 384) b384 **
        bytesRegion (dp + BitVec.ofNat 64 512) b512 **
        bytesRegion (dp + BitVec.ofNat 64 192) s192 **
        bytesRegion (dp + BitVec.ofNat 64 288) s288 **
        bytesRegion (dp + BitVec.ofNat 64 352) s352 **
        bytesRegion (dp + BitVec.ofNat 64 416) s416 **
        bytesRegion (dp + BitVec.ofNat 64 544) s544 **
        bytesRegion op w0 **
        bytesRegion (op + BitVec.ofNat 64 48) w48 **
        bytesRegion (op + BitVec.ofNat 64 80) w80 **
        bytesRegion (op + BitVec.ofNat 64 88) w88 **
        bytesRegion (op + BitVec.ofNat 64 184) w184)
      (fun h =>
        if eddAccept dp lenW b0 b32 b64 b96 b128 b160 b256 b320 b384 b512
        then eddOkPost dp op sp0 ret v8 v9 b0 b32 b64 b96 b128 b160 b256 b320 b384 b512 s192 s288 s352 s416 s544 h
        else eddRejPost dp op sp0 ret v8 v9 b0 b32 b64 b96 b128 b160 b256 b320 b384 b512 s192 s288 s352 s416 s544 w0 w48 w80 w88 w184 h) := by
  by_cases hlen : lenW = (576 : Word)
  case neg =>
    -- wrong length: the guard takes the fail tail
    have hf := EvmAsm.Codegen.ExtractDepositDataFailSpec.extractDepositData_lenFail_spec
      sp0 ret dp lenW op v5 v8 v9 m0 m1 m2 hlen halign
    have hfB := cpsTripleWithin_extend_code main_sub hf
    have hfF := cpsTripleWithin_frameR
      (regOwns eddScrPre **
        bytesRegion dp b0 **
        bytesRegion (dp + BitVec.ofNat 64 32) b32 **
        bytesRegion (dp + BitVec.ofNat 64 64) b64 **
        bytesRegion (dp + BitVec.ofNat 64 96) b96 **
        bytesRegion (dp + BitVec.ofNat 64 128) b128 **
        bytesRegion (dp + BitVec.ofNat 64 160) b160 **
        bytesRegion (dp + BitVec.ofNat 64 256) b256 **
        bytesRegion (dp + BitVec.ofNat 64 320) b320 **
        bytesRegion (dp + BitVec.ofNat 64 384) b384 **
        bytesRegion (dp + BitVec.ofNat 64 512) b512 **
        bytesRegion (dp + BitVec.ofNat 64 192) s192 **
        bytesRegion (dp + BitVec.ofNat 64 288) s288 **
        bytesRegion (dp + BitVec.ofNat 64 352) s352 **
        bytesRegion (dp + BitVec.ofNat 64 416) s416 **
        bytesRegion (dp + BitVec.ofNat 64 544) s544 **
        bytesRegion op w0 **
        bytesRegion (op + BitVec.ofNat 64 48) w48 **
        bytesRegion (op + BitVec.ofNat 64 80) w80 **
        bytesRegion (op + BitVec.ofNat 64 88) w88 **
        bytesRegion (op + BitVec.ofNat 64 184) w184)
      (by u_pcfree) hfB
    refine cps_fuel_mono (by norm_num)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hq => ?_) hfF)
    rw [if_neg (fun hacc => hlen hacc.1)]
    dsimp only [eddRejPost]
    have hq1 : (((((.x5 : Reg) ↦ᵣ (576 : Word)) **
        ((.x11 : Reg) ↦ᵣ lenW) ** ((.x12 : Reg) ↦ᵣ op)) **
        regOwns eddScrPre) **
        (((.x2 : Reg) ↦ᵣ sp0) **
          ((.x1 : Reg) ↦ᵣ ret) **
          ((.x8 : Reg) ↦ᵣ v8) **
          ((.x9 : Reg) ↦ᵣ v9) **
          ((.x10 : Reg) ↦ᵣ (1 : Word)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ ret) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ v8) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ v9) **
          bytesRegion dp b0 **
          bytesRegion (dp + BitVec.ofNat 64 32) b32 **
          bytesRegion (dp + BitVec.ofNat 64 64) b64 **
          bytesRegion (dp + BitVec.ofNat 64 96) b96 **
          bytesRegion (dp + BitVec.ofNat 64 128) b128 **
          bytesRegion (dp + BitVec.ofNat 64 160) b160 **
          bytesRegion (dp + BitVec.ofNat 64 256) b256 **
          bytesRegion (dp + BitVec.ofNat 64 320) b320 **
          bytesRegion (dp + BitVec.ofNat 64 384) b384 **
          bytesRegion (dp + BitVec.ofNat 64 512) b512 **
          bytesRegion (dp + BitVec.ofNat 64 192) s192 **
          bytesRegion (dp + BitVec.ofNat 64 288) s288 **
          bytesRegion (dp + BitVec.ofNat 64 352) s352 **
          bytesRegion (dp + BitVec.ofNat 64 416) s416 **
          bytesRegion (dp + BitVec.ofNat 64 544) s544 **
          bytesRegion op w0 **
          bytesRegion (op + BitVec.ofNat 64 48) w48 **
          bytesRegion (op + BitVec.ofNat 64 80) w80 **
          bytesRegion (op + BitVec.ofNat 64 88) w88 **
          bytesRegion (op + BitVec.ofNat 64 184) w184)) h := by xperm_hyp hq
    have hq2 := sepConj_mono_left (fun h' hx =>
      edd_owns_fail_recombine h'
        (sepConj_mono_left (fun h'' hy =>
          sepConj_mono (regIs_to_regOwn .x5 (576 : Word))
            (sepConj_mono (regIs_to_regOwn .x11 lenW)
              (regIs_to_regOwn .x12 op)) h'' hy) h' hx)) h hq1
    xperm_hyp hq2
  case pos =>
    subst hlen
    by_cases h0 : EddBe32EqSAsm.eddOk dp b0 (160 : Word)
    case neg =>
      have hr := extractDepositData_reject1_spec dp hdp op sp0 ret v5 v8 v9
        m0 m1 m2 b0 hb0  h0
      have hrF := cpsTripleWithin_frameR
        (bytesRegion (dp + BitVec.ofNat 64 32) b32 **
              bytesRegion (dp + BitVec.ofNat 64 64) b64 **
              bytesRegion (dp + BitVec.ofNat 64 96) b96 **
              bytesRegion (dp + BitVec.ofNat 64 128) b128 **
              bytesRegion (dp + BitVec.ofNat 64 160) b160 **
              bytesRegion (dp + BitVec.ofNat 64 256) b256 **
              bytesRegion (dp + BitVec.ofNat 64 320) b320 **
              bytesRegion (dp + BitVec.ofNat 64 384) b384 **
              bytesRegion (dp + BitVec.ofNat 64 512) b512 **
              bytesRegion (dp + BitVec.ofNat 64 192) s192 **
              bytesRegion (dp + BitVec.ofNat 64 288) s288 **
              bytesRegion (dp + BitVec.ofNat 64 352) s352 **
              bytesRegion (dp + BitVec.ofNat 64 416) s416 **
              bytesRegion (dp + BitVec.ofNat 64 544) s544 **
              bytesRegion op w0 **
              bytesRegion (op + BitVec.ofNat 64 48) w48 **
              bytesRegion (op + BitVec.ofNat 64 80) w80 **
              bytesRegion (op + BitVec.ofNat 64 88) w88 **
              bytesRegion (op + BitVec.ofNat 64 184) w184)
        (by u_pcfree) hr
      refine cps_fuel_mono (by norm_num)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
          (fun h hq => ?_) hrF)
      rw [if_neg (fun hacc => h0 hacc.2.1)]
      dsimp only [eddRejPost]
      xperm_hyp hq
    case pos =>
      by_cases h32 : EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 32) b32 (256 : Word)
      case neg =>
        have hr := extractDepositData_reject2_spec dp hdp op sp0 ret v5 v8 v9
          m0 m1 m2 b0 b32 hb0 hb32 h0 h32
        have hrF := cpsTripleWithin_frameR
          (bytesRegion (dp + BitVec.ofNat 64 64) b64 **
                  bytesRegion (dp + BitVec.ofNat 64 96) b96 **
                  bytesRegion (dp + BitVec.ofNat 64 128) b128 **
                  bytesRegion (dp + BitVec.ofNat 64 160) b160 **
                  bytesRegion (dp + BitVec.ofNat 64 256) b256 **
                  bytesRegion (dp + BitVec.ofNat 64 320) b320 **
                  bytesRegion (dp + BitVec.ofNat 64 384) b384 **
                  bytesRegion (dp + BitVec.ofNat 64 512) b512 **
                  bytesRegion (dp + BitVec.ofNat 64 192) s192 **
                  bytesRegion (dp + BitVec.ofNat 64 288) s288 **
                  bytesRegion (dp + BitVec.ofNat 64 352) s352 **
                  bytesRegion (dp + BitVec.ofNat 64 416) s416 **
                  bytesRegion (dp + BitVec.ofNat 64 544) s544 **
                  bytesRegion op w0 **
                  bytesRegion (op + BitVec.ofNat 64 48) w48 **
                  bytesRegion (op + BitVec.ofNat 64 80) w80 **
                  bytesRegion (op + BitVec.ofNat 64 88) w88 **
                  bytesRegion (op + BitVec.ofNat 64 184) w184)
          (by u_pcfree) hr
        refine cps_fuel_mono (by norm_num)
          (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
            (fun h hq => ?_) hrF)
        rw [if_neg (fun hacc => h32 hacc.2.2.1)]
        dsimp only [eddRejPost]
        xperm_hyp hq
      case pos =>
        by_cases h64 : EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 64) b64 (320 : Word)
        case neg =>
          have hr := extractDepositData_reject3_spec dp hdp op sp0 ret v5 v8 v9
            m0 m1 m2 b0 b32 b64 hb0 hb32 hb64 h0 h32 h64
          have hrF := cpsTripleWithin_frameR
            (bytesRegion (dp + BitVec.ofNat 64 96) b96 **
                      bytesRegion (dp + BitVec.ofNat 64 128) b128 **
                      bytesRegion (dp + BitVec.ofNat 64 160) b160 **
                      bytesRegion (dp + BitVec.ofNat 64 256) b256 **
                      bytesRegion (dp + BitVec.ofNat 64 320) b320 **
                      bytesRegion (dp + BitVec.ofNat 64 384) b384 **
                      bytesRegion (dp + BitVec.ofNat 64 512) b512 **
                      bytesRegion (dp + BitVec.ofNat 64 192) s192 **
                      bytesRegion (dp + BitVec.ofNat 64 288) s288 **
                      bytesRegion (dp + BitVec.ofNat 64 352) s352 **
                      bytesRegion (dp + BitVec.ofNat 64 416) s416 **
                      bytesRegion (dp + BitVec.ofNat 64 544) s544 **
                      bytesRegion op w0 **
                      bytesRegion (op + BitVec.ofNat 64 48) w48 **
                      bytesRegion (op + BitVec.ofNat 64 80) w80 **
                      bytesRegion (op + BitVec.ofNat 64 88) w88 **
                      bytesRegion (op + BitVec.ofNat 64 184) w184)
            (by u_pcfree) hr
          refine cps_fuel_mono (by norm_num)
            (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
              (fun h hq => ?_) hrF)
          rw [if_neg (fun hacc => h64 hacc.2.2.2.1)]
          dsimp only [eddRejPost]
          xperm_hyp hq
        case pos =>
          by_cases h96 : EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 96) b96 (384 : Word)
          case neg =>
            have hr := extractDepositData_reject4_spec dp hdp op sp0 ret v5 v8 v9
              m0 m1 m2 b0 b32 b64 b96 hb0 hb32 hb64 hb96 h0 h32 h64 h96
            have hrF := cpsTripleWithin_frameR
              (bytesRegion (dp + BitVec.ofNat 64 128) b128 **
                          bytesRegion (dp + BitVec.ofNat 64 160) b160 **
                          bytesRegion (dp + BitVec.ofNat 64 256) b256 **
                          bytesRegion (dp + BitVec.ofNat 64 320) b320 **
                          bytesRegion (dp + BitVec.ofNat 64 384) b384 **
                          bytesRegion (dp + BitVec.ofNat 64 512) b512 **
                          bytesRegion (dp + BitVec.ofNat 64 192) s192 **
                          bytesRegion (dp + BitVec.ofNat 64 288) s288 **
                          bytesRegion (dp + BitVec.ofNat 64 352) s352 **
                          bytesRegion (dp + BitVec.ofNat 64 416) s416 **
                          bytesRegion (dp + BitVec.ofNat 64 544) s544 **
                          bytesRegion op w0 **
                          bytesRegion (op + BitVec.ofNat 64 48) w48 **
                          bytesRegion (op + BitVec.ofNat 64 80) w80 **
                          bytesRegion (op + BitVec.ofNat 64 88) w88 **
                          bytesRegion (op + BitVec.ofNat 64 184) w184)
              (by u_pcfree) hr
            refine cps_fuel_mono (by norm_num)
              (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
                (fun h hq => ?_) hrF)
            rw [if_neg (fun hacc => h96 hacc.2.2.2.2.1)]
            dsimp only [eddRejPost]
            xperm_hyp hq
          case pos =>
            by_cases h128 : EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 128) b128 (512 : Word)
            case neg =>
              have hr := extractDepositData_reject5_spec dp hdp op sp0 ret v5 v8 v9
                m0 m1 m2 b0 b32 b64 b96 b128 hb0 hb32 hb64 hb96 hb128 h0 h32 h64 h96 h128
              have hrF := cpsTripleWithin_frameR
                (bytesRegion (dp + BitVec.ofNat 64 160) b160 **
                              bytesRegion (dp + BitVec.ofNat 64 256) b256 **
                              bytesRegion (dp + BitVec.ofNat 64 320) b320 **
                              bytesRegion (dp + BitVec.ofNat 64 384) b384 **
                              bytesRegion (dp + BitVec.ofNat 64 512) b512 **
                              bytesRegion (dp + BitVec.ofNat 64 192) s192 **
                              bytesRegion (dp + BitVec.ofNat 64 288) s288 **
                              bytesRegion (dp + BitVec.ofNat 64 352) s352 **
                              bytesRegion (dp + BitVec.ofNat 64 416) s416 **
                              bytesRegion (dp + BitVec.ofNat 64 544) s544 **
                              bytesRegion op w0 **
                              bytesRegion (op + BitVec.ofNat 64 48) w48 **
                              bytesRegion (op + BitVec.ofNat 64 80) w80 **
                              bytesRegion (op + BitVec.ofNat 64 88) w88 **
                              bytesRegion (op + BitVec.ofNat 64 184) w184)
                (by u_pcfree) hr
              refine cps_fuel_mono (by norm_num)
                (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
                  (fun h hq => ?_) hrF)
              rw [if_neg (fun hacc => h128 hacc.2.2.2.2.2.1)]
              dsimp only [eddRejPost]
              xperm_hyp hq
            case pos =>
              by_cases h160 : EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 160) b160 (48 : Word)
              case neg =>
                have hr := extractDepositData_reject6_spec dp hdp op sp0 ret v5 v8 v9
                  m0 m1 m2 b0 b32 b64 b96 b128 b160 hb0 hb32 hb64 hb96 hb128 hb160 h0 h32 h64 h96 h128 h160
                have hrF := cpsTripleWithin_frameR
                  (bytesRegion (dp + BitVec.ofNat 64 256) b256 **
                                  bytesRegion (dp + BitVec.ofNat 64 320) b320 **
                                  bytesRegion (dp + BitVec.ofNat 64 384) b384 **
                                  bytesRegion (dp + BitVec.ofNat 64 512) b512 **
                                  bytesRegion (dp + BitVec.ofNat 64 192) s192 **
                                  bytesRegion (dp + BitVec.ofNat 64 288) s288 **
                                  bytesRegion (dp + BitVec.ofNat 64 352) s352 **
                                  bytesRegion (dp + BitVec.ofNat 64 416) s416 **
                                  bytesRegion (dp + BitVec.ofNat 64 544) s544 **
                                  bytesRegion op w0 **
                                  bytesRegion (op + BitVec.ofNat 64 48) w48 **
                                  bytesRegion (op + BitVec.ofNat 64 80) w80 **
                                  bytesRegion (op + BitVec.ofNat 64 88) w88 **
                                  bytesRegion (op + BitVec.ofNat 64 184) w184)
                  (by u_pcfree) hr
                refine cps_fuel_mono (by norm_num)
                  (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
                    (fun h hq => ?_) hrF)
                rw [if_neg (fun hacc => h160 hacc.2.2.2.2.2.2.1)]
                dsimp only [eddRejPost]
                xperm_hyp hq
              case pos =>
                by_cases h256 : EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 256) b256 (32 : Word)
                case neg =>
                  have hr := extractDepositData_reject7_spec dp hdp op sp0 ret v5 v8 v9
                    m0 m1 m2 b0 b32 b64 b96 b128 b160 b256 hb0 hb32 hb64 hb96 hb128 hb160 hb256 h0 h32 h64 h96 h128 h160 h256
                  have hrF := cpsTripleWithin_frameR
                    (bytesRegion (dp + BitVec.ofNat 64 320) b320 **
                                      bytesRegion (dp + BitVec.ofNat 64 384) b384 **
                                      bytesRegion (dp + BitVec.ofNat 64 512) b512 **
                                      bytesRegion (dp + BitVec.ofNat 64 192) s192 **
                                      bytesRegion (dp + BitVec.ofNat 64 288) s288 **
                                      bytesRegion (dp + BitVec.ofNat 64 352) s352 **
                                      bytesRegion (dp + BitVec.ofNat 64 416) s416 **
                                      bytesRegion (dp + BitVec.ofNat 64 544) s544 **
                                      bytesRegion op w0 **
                                      bytesRegion (op + BitVec.ofNat 64 48) w48 **
                                      bytesRegion (op + BitVec.ofNat 64 80) w80 **
                                      bytesRegion (op + BitVec.ofNat 64 88) w88 **
                                      bytesRegion (op + BitVec.ofNat 64 184) w184)
                    (by u_pcfree) hr
                  refine cps_fuel_mono (by norm_num)
                    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
                      (fun h hq => ?_) hrF)
                  rw [if_neg (fun hacc => h256 hacc.2.2.2.2.2.2.2.1)]
                  dsimp only [eddRejPost]
                  xperm_hyp hq
                case pos =>
                  by_cases h320 : EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 320) b320 (8 : Word)
                  case neg =>
                    have hr := extractDepositData_reject8_spec dp hdp op sp0 ret v5 v8 v9
                      m0 m1 m2 b0 b32 b64 b96 b128 b160 b256 b320 hb0 hb32 hb64 hb96 hb128 hb160 hb256 hb320 h0 h32 h64 h96 h128 h160 h256 h320
                    have hrF := cpsTripleWithin_frameR
                      (bytesRegion (dp + BitVec.ofNat 64 384) b384 **
                                          bytesRegion (dp + BitVec.ofNat 64 512) b512 **
                                          bytesRegion (dp + BitVec.ofNat 64 192) s192 **
                                          bytesRegion (dp + BitVec.ofNat 64 288) s288 **
                                          bytesRegion (dp + BitVec.ofNat 64 352) s352 **
                                          bytesRegion (dp + BitVec.ofNat 64 416) s416 **
                                          bytesRegion (dp + BitVec.ofNat 64 544) s544 **
                                          bytesRegion op w0 **
                                          bytesRegion (op + BitVec.ofNat 64 48) w48 **
                                          bytesRegion (op + BitVec.ofNat 64 80) w80 **
                                          bytesRegion (op + BitVec.ofNat 64 88) w88 **
                                          bytesRegion (op + BitVec.ofNat 64 184) w184)
                      (by u_pcfree) hr
                    refine cps_fuel_mono (by norm_num)
                      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
                        (fun h hq => ?_) hrF)
                    rw [if_neg (fun hacc => h320 hacc.2.2.2.2.2.2.2.2.1)]
                    dsimp only [eddRejPost]
                    xperm_hyp hq
                  case pos =>
                    by_cases h384 : EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 384) b384 (96 : Word)
                    case neg =>
                      have hr := extractDepositData_reject9_spec dp hdp op sp0 ret v5 v8 v9
                        m0 m1 m2 b0 b32 b64 b96 b128 b160 b256 b320 b384 hb0 hb32 hb64 hb96 hb128 hb160 hb256 hb320 hb384 h0 h32 h64 h96 h128 h160 h256 h320 h384
                      have hrF := cpsTripleWithin_frameR
                        (bytesRegion (dp + BitVec.ofNat 64 512) b512 **
                                              bytesRegion (dp + BitVec.ofNat 64 192) s192 **
                                              bytesRegion (dp + BitVec.ofNat 64 288) s288 **
                                              bytesRegion (dp + BitVec.ofNat 64 352) s352 **
                                              bytesRegion (dp + BitVec.ofNat 64 416) s416 **
                                              bytesRegion (dp + BitVec.ofNat 64 544) s544 **
                                              bytesRegion op w0 **
                                              bytesRegion (op + BitVec.ofNat 64 48) w48 **
                                              bytesRegion (op + BitVec.ofNat 64 80) w80 **
                                              bytesRegion (op + BitVec.ofNat 64 88) w88 **
                                              bytesRegion (op + BitVec.ofNat 64 184) w184)
                        (by u_pcfree) hr
                      refine cps_fuel_mono (by norm_num)
                        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
                          (fun h hq => ?_) hrF)
                      rw [if_neg (fun hacc => h384 hacc.2.2.2.2.2.2.2.2.2.1)]
                      dsimp only [eddRejPost]
                      xperm_hyp hq
                    case pos =>
                      by_cases h512 : EddBe32EqSAsm.eddOk (dp + BitVec.ofNat 64 512) b512 (8 : Word)
                      case neg =>
                        have hr := extractDepositData_reject10_spec dp hdp op sp0 ret v5 v8 v9
                          m0 m1 m2 b0 b32 b64 b96 b128 b160 b256 b320 b384 b512 hb0 hb32 hb64 hb96 hb128 hb160 hb256 hb320 hb384 hb512 h0 h32 h64 h96 h128 h160 h256 h320 h384 h512
                        have hrF := cpsTripleWithin_frameR
                          (bytesRegion (dp + BitVec.ofNat 64 192) s192 **
                                                  bytesRegion (dp + BitVec.ofNat 64 288) s288 **
                                                  bytesRegion (dp + BitVec.ofNat 64 352) s352 **
                                                  bytesRegion (dp + BitVec.ofNat 64 416) s416 **
                                                  bytesRegion (dp + BitVec.ofNat 64 544) s544 **
                                                  bytesRegion op w0 **
                                                  bytesRegion (op + BitVec.ofNat 64 48) w48 **
                                                  bytesRegion (op + BitVec.ofNat 64 80) w80 **
                                                  bytesRegion (op + BitVec.ofNat 64 88) w88 **
                                                  bytesRegion (op + BitVec.ofNat 64 184) w184)
                          (by u_pcfree) hr
                        refine cps_fuel_mono (by norm_num)
                          (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
                            (fun h hq => ?_) hrF)
                        rw [if_neg (fun hacc => h512 hacc.2.2.2.2.2.2.2.2.2.2)]
                        dsimp only [eddRejPost]
                        xperm_hyp hq
                      case pos =>
                        -- all ten checks pass: the ok path
                        have ho := extractDepositData_ok_spec dp op hdp hop hdj sp0 ret v5 v8 v9 m0 m1 m2
                          b0 b32 b64 b96 b128 b160 b256 b320 b384 b512 s192 s288 s352 s416 s544 w0 w48 w80 w88 w184
                          hb0 hb32 hb64 hb96 hb128 hb160 hb256 hb320 hb384 hb512 hs192 hs288 hs352 hs416 hs544
                          hw0 hw48 hw80 hw88 hw184
                          h0 h32 h64 h96 h128 h160 h256 h320 h384 h512 halign
                        refine cps_fuel_mono (by norm_num)
                          (cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) ho)
                        rw [if_pos (show eddAccept dp (576 : Word) b0 b32 b64 b96 b128 b160 b256 b320 b384 b512 from
                          ⟨rfl, h0, h32, h64, h96, h128, h160, h256, h320, h384, h512⟩)]
                        dsimp only [eddOkPost]
                        xperm_hyp hq

/-! ## The deployed-probe instance -/

set_option maxRecDepth 8000 in
/-- The payload arena the deployed probe passes satisfies the arena
    facts. -/
theorem eddDataArenaOk_probe :
    eddDataArenaOk EvmAsm.Codegen.eddDataPtr := by
  have hbase : EvmAsm.Codegen.eddDataPtr.toNat = 0x40000010 := by decide
  refine ⟨by decide, by decide, fun k hk => ?_⟩
  have haddr : (EvmAsm.Codegen.eddDataPtr + BitVec.ofNat 64 k).toNat
      = 0x40000010 + k := by
    rw [EvmAsm.Codegen.edd_toNat_add2 _ _ (by rw [hbase]; omega), hbase]
  show isValidMemAddr (EvmAsm.Codegen.eddDataPtr + BitVec.ofNat 64 k) = true
  simp only [isValidMemAddr, haddr, EvmAsm.Rv64.MEM_START,
    EvmAsm.Rv64.MEM_END, EvmAsm.Rv64.INPUT_MEM_START,
    EvmAsm.Rv64.INPUT_MEM_END, EvmAsm.Rv64.RAM_MEM_START,
    EvmAsm.Rv64.RAM_MEM_END, decide_eq_true_eq, Bool.and_eq_true,
    Bool.or_eq_true]
  omega

set_option maxRecDepth 8000 in
/-- The output arena the deployed probe passes satisfies the arena
    facts. -/
theorem eddOutArenaOk_probe :
    eddOutArenaOk EvmAsm.Codegen.eddOutPtr := by
  have hbase : EvmAsm.Codegen.eddOutPtr.toNat = 0xa0010008 := by decide
  refine ⟨by decide, by decide, fun k hk => ?_⟩
  have haddr : (EvmAsm.Codegen.eddOutPtr + BitVec.ofNat 64 k).toNat
      = 0xa0010008 + k := by
    rw [EvmAsm.Codegen.edd_toNat_add2 _ _ (by rw [hbase]; omega), hbase]
  show isValidMemAddr (EvmAsm.Codegen.eddOutPtr + BitVec.ofNat 64 k) = true
  simp only [isValidMemAddr, haddr, EvmAsm.Rv64.MEM_START,
    EvmAsm.Rv64.MEM_END, EvmAsm.Rv64.INPUT_MEM_START,
    EvmAsm.Rv64.INPUT_MEM_END, EvmAsm.Rv64.RAM_MEM_START,
    EvmAsm.Rv64.RAM_MEM_END, decide_eq_true_eq, Bool.and_eq_true,
    Bool.or_eq_true]
  omega

theorem eddArenasDisjoint_probe :
    eddArenasDisjoint EvmAsm.Codegen.eddDataPtr EvmAsm.Codegen.eddOutPtr := by
  exact Or.inl (by decide)

/-- The unified contract at the deployed probe arenas — the instance
    the linked caller consumes. -/
noncomputable abbrev extractDepositData_probe_spec
    (sp0 ret v5 v8 v9 m0 m1 m2 lenW : Word) :=
  extractDepositData_spec EvmAsm.Codegen.eddDataPtr
    EvmAsm.Codegen.eddOutPtr eddDataArenaOk_probe eddOutArenaOk_probe
    eddArenasDisjoint_probe sp0 ret v5 v8 v9 m0 m1 m2 lenW

#print axioms extractDepositData_spec

end EvmAsm.Codegen.ExtractDepositDataUnified
