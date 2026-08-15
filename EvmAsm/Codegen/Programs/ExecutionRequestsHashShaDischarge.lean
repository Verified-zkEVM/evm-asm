/-
  ExecutionRequestsHashShaDischarge — retire `h_sha` via `zkvm_sha256_spec_within`.

  #12018 follow-up: establish the callWithin at erh_hash_one's JAL site from the
  landed machine triple, without widening that triple's digest post.

  out0: arbitrary length-32 initial output is sound by `sha256SqueezePrefix_full`
  (SqueezeLoop.lean) — the squeeze loop fully overwrites all 32 bytes.

  BSS: lives in the callee footprint (not F) because contents change.
  hsem*: remain as named accelerator assumptions (not a silent relabel of h_sha).
  Parent #12011: this unblocks the hash-half compose; it does NOT discharge it.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.ExecutionRequestsHashShaResidual
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOne
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneBody
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Proofs.HashBridgeSha256Top
import EvmAsm.Codegen.Proofs.HashBridgeSha256Frame
import EvmAsm.Codegen.Proofs.HashBridgeSha256Body
import EvmAsm.Stateless.SpecRef.Crypto
import EvmAsm.Rv64.SAsm.HandleWiden

namespace EvmAsm.Codegen.ExecutionRequestsHashShaDischarge

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashShaResidual
open EvmAsm.Codegen.ExecutionRequestsHashHashOne
open EvmAsm.Codegen.ExecutionRequestsHashHashOneBody
open EvmAsm.Codegen.Proofs
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

local macro "pcf" : tactic =>
  `(tactic| repeat' first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_stackFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regOwns _
      | exact pcFree_emp
      | assumption)

private abbrev ShaState : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_state
private abbrev ShaInput : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_input
private abbrev ShaIv : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_iv
private abbrev ShaParams : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_params

/-- Machine fuel for one sha256 call. Sites discharge under this bound;
    `shaResidualFuel = 500` covers the erh empty arm (N=0,rem=1 → 381). -/
theorem sha256MachineFuel_empty_le :
    7 + sha256BodyFuel 0 1 + 8 ≤ shaResidualFuel := by
  simp only [sha256BodyFuel, shaResidualFuel]; norm_num

/-- `fullCodeHo` covers the sha256 text. -/
theorem lift_sha {n : Nat} {entry exit_ : Word} {P Q : Assertion}
    (h : cpsTripleWithin n entry exit_ (CodeReq.ofProg ShaB zkvmSha256_prog) P Q) :
    cpsTripleWithin n entry exit_ fullCodeHo P Q :=
  cpsTripleWithin_extend_code
    (fun a i hi => by
      unfold fullCodeHo
      exact CodeReq.mono_union_right wrapper_sha_disjoint
        (fun _ _ h' => h') a i hi) h

/-- Named accelerator + arena hypotheses the discharge needs.
    These remain as named assumptions on the erh tops (item 3 option a) —
    not a silent relabel of `h_sha`. -/
structure ShaDischargeHyps (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (st0 scratch0 iv params : List (BitVec 8)) : Prop where
  hlen : input.length = 64 * N + rem
  hrem : rem < 64
  hst : st0.length = 32
  hscratch : scratch0.length = 64
  hiv : iv.length = 32
  hivEq : iv = sha256IvBytes
  hparams : params.length = 16
  hNbound : 64 * N + rem < 2 ^ 63
  hcur : inputBase.toNat + 64 * N < 2 ^ 64
  hcurAlign : (sha256AbsorbCursor inputBase N).toNat % 8 = 0
  hcurOver : (sha256AbsorbCursor inputBase N).toNat + rem ≤ 2 ^ 64
  houtAlign : outputBase.toNat % 8 = 0
  houtOver : outputBase.toNat + 32 ≤ 2 ^ 64
  hvalidS : ∀ i < rem,
    isValidByteAccess (sha256AbsorbCursor inputBase N + BitVec.ofNat 64 i) = true
  hvalidScratch : ∀ i < 64,
    isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true
  hvalidSq : ∀ i < 32,
    isValidByteAccess (ShaState + BitVec.ofNat 64 (i ^^^ 3)) = true
  hvalidD : ∀ i < 32, isValidByteAccess (outputBase + BitVec.ofNat 64 i) = true
  hsemOuter : sha256OuterHsem inputBase ShaState ShaInput ShaParams input params iv N
  hsemSqLt : rem < 56 →
    sha256BodySqueezeHsem_lt56 ShaState ShaInput ShaParams iv input params N rem
  hsemMid : 56 ≤ rem →
    sha256BodyPadMidHsem ShaState ShaInput ShaParams iv input params N rem
  hsemSqGe : 56 ≤ rem →
    sha256BodySqueezeHsem_ge56 ShaState ShaInput ShaParams iv input params N rem

/-- Empty-arm specialization: blob = `[typeByte]`, so N=0, rem=1. -/
def shaDischargeHyps_empty (outputBase : Word) (typeB : BitVec 8)
    (st0 scratch0 iv params : List (BitVec 8)) : Prop :=
  ShaDischargeHyps Blob outputBase (hashOneBlob typeB []) 0 1 st0 scratch0 iv params

/-- `stackFree sp 6` occupies the same six dwords as `frameSlotsOwn sha256Frame`
    under `sp + signExtend12 (-48)`. -/
theorem stackFree6_eq_sha256FrameSlotsOwn (sp : Word) :
    stackFree sp 6 =
      frameSlotsOwn sha256Frame (sp + signExtend12 (-48 : BitVec 12)) := by
  show (memOwn (sp - BitVec.ofNat 64 (8 * 6)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 5)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 4)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 3)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 2)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 1)) ** empAssertion) = _
  show _ = (memOwn ((sp + signExtend12 (-48 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-48 : BitVec 12)) +
          signExtend12 (8 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-48 : BitVec 12)) +
          signExtend12 (16 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-48 : BitVec 12)) +
          signExtend12 (24 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-48 : BitVec 12)) +
          signExtend12 (32 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-48 : BitVec 12)) +
          signExtend12 (40 : BitVec 12)) ** empAssertion)
  rw [show signExtend12 (-48 : BitVec 12) = (-48 : Word) from by decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
    show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide,
    show sp - BitVec.ofNat 64 (8 * 6) = sp + (-48 : Word) + (0 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 5) = sp + (-48 : Word) + (8 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 4) = sp + (-48 : Word) + (16 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 3) = sp + (-48 : Word) + (24 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 2) = sp + (-48 : Word) + (32 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 1) = sp + (-48 : Word) + (40 : Word) from by bv_omega]

/-- Step count of the sha256 leaf (matches `zkvm_sha256_spec_within`).
    `def` (not `abbrev`) so callers can treat the fuel as opaque in `omega`. -/
def nSha256 (N rem : Nat) : Nat := 7 + sha256BodyFuel N rem + 8

/-- Machine-shaped callWithin (keccak/`hvphKeccakCall` pattern).

    Pre: `stackFree 6` ↔ `frameSlotsOwn`; BSS + free temps live in `shaCallerPre`
    (callee P), not F. Post keeps `frameSlotsSaved` + `shaCallerPost` (SpecRef
    digest + BSS finals) — same as keccak; thin `shaCallReturn` reshape is next. -/
theorem sha256_callWithin_machine
    (callerPC vOld sp0 : Word) (offset : BitVec 21)
    (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (v8 v9 v18 v19 v20 v21 : Word)
    (st0 scratch0 iv params : List (BitVec 8))
    (out0 : List (BitVec 8))
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hyps : ShaDischargeHyps inputBase outputBase input N rem st0 scratch0 iv params)
    (hout : out0.length = 32)
    (halign_ret : ((callerPC + 4) &&& ~~~(1 : Word)) = callerPC + 4)
    (htarget : callerPC + signExtend21 offset = ShaB)
    (hmem : ∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
      fullCodeHo a = some i) :
    let vals := sha256EntryVals v8 v9 v18 v19 v20 v21
    let lenW := BitVec.ofNat 64 (64 * N + rem)
    cpsTripleWithin (1 + nSha256 N rem) callerPC (callerPC + 4) fullCodeHo
      (((.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) **
          (stackFree sp0 6 ** regsAt sha256Frame vals **
            shaCallerPre inputBase lenW outputBase st0 scratch0 iv params input out0 A) **
          F))
      (((.x1 ↦ᵣ (callerPC + 4)) ** (.x2 ↦ᵣ sp0) **
          (frameSlotsSaved sha256Frame (sp0 + signExtend12 (-48 : BitVec 12)) vals **
            regsAt sha256Frame vals **
            shaCallerPost inputBase outputBase input params iv N rem A) **
          F)) := by
  intro vals lenW
  have hcallee0 := zkvm_sha256_spec_within sp0 (callerPC + 4)
    inputBase outputBase input N rem v8 v9 v18 v19 v20 v21
    st0 scratch0 iv params A hA
    halign_ret hyps.hlen hyps.hrem hyps.hst hyps.hscratch hyps.hiv hyps.hivEq
    hyps.hparams hyps.hNbound hyps.hcur hyps.hcurAlign hyps.hcurOver
    hyps.houtAlign hyps.houtOver hyps.hvalidS hyps.hvalidScratch hyps.hvalidSq
    hyps.hvalidD hyps.hsemOuter hyps.hsemSqLt hyps.hsemMid hyps.hsemSqGe
    out0 hout
  have hcallee' :
      cpsTripleWithin (nSha256 N rem) ShaB (callerPC + 4)
        (CodeReq.ofProg ShaB zkvmSha256_prog)
        ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ (callerPC + 4)) **
          regsAt sha256Frame vals **
          frameSlotsOwn sha256Frame (sp0 + signExtend12 (-48 : BitVec 12)) **
          shaCallerPre inputBase lenW outputBase st0 scratch0 iv params input out0 A)
        ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ (callerPC + 4)) **
          regsAt sha256Frame vals **
          frameSlotsSaved sha256Frame (sp0 + signExtend12 (-48 : BitVec 12)) vals **
          shaCallerPost inputBase outputBase input params iv N rem A) := by
    simpa [nSha256, vals, lenW, ShaB] using hcallee0
  rw [← stackFree6_eq_sha256FrameSlotsOwn sp0] at hcallee'
  have hcalleeFull :
      cpsTripleWithin (nSha256 N rem) ShaB (callerPC + 4) fullCodeHo
        ((.x1 ↦ᵣ (callerPC + 4)) ** (.x2 ↦ᵣ sp0) **
          (stackFree sp0 6 ** regsAt sha256Frame vals **
            shaCallerPre inputBase lenW outputBase st0 scratch0 iv params input out0 A))
        ((.x1 ↦ᵣ (callerPC + 4)) ** (.x2 ↦ᵣ sp0) **
          (frameSlotsSaved sha256Frame (sp0 + signExtend12 (-48 : BitVec 12)) vals **
            regsAt sha256Frame vals **
            shaCallerPost inputBase outputBase input params iv N rem A)) := by
    have h := lift_sha hcallee'
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h
  have hcall := abiFrameCall_spec (cr := fullCodeHo)
    (calleePre := stackFree sp0 6 ** regsAt sha256Frame vals **
      shaCallerPre inputBase lenW outputBase st0 scratch0 iv params input out0 A)
    (calleePost := frameSlotsSaved sha256Frame
        (sp0 + signExtend12 (-48 : BitVec 12)) vals **
      regsAt sha256Frame vals **
      shaCallerPost inputBase outputBase input params iv N rem A)
    (F := F) callerPC ShaB vOld sp0 offset
    0 (nSha256 N rem)
    htarget hmem
    (by
      refine pcFree_sepConj (pcFree_stackFree _ _)
        (pcFree_sepConj (pcFree_regsAt _ _) ?_)
      exact shaCallerPre_pcFree inputBase lenW outputBase st0 scratch0 iv params
        input out0 A hA)
    hF
    (by
      simpa only [stackFree_zero, sepConj_emp_left', sepConj_emp_right',
        nSha256] using hcalleeFull)
  simpa only [stackFree_zero, sepConj_emp_left', nSha256] using hcall

/-- Release `frameSlotsSaved sha256Frame` to `stackFree sp 6`. -/
theorem frameSlotsSaved_sha256_implies_stackFree (sp : Word) (vals : Reg → Word) :
    ∀ h, (frameSlotsSaved sha256Frame (sp + signExtend12 (-48 : BitVec 12)) vals) h →
      (stackFree sp 6) h := by
  intro h hp
  have hp' :
      (memIs ((sp + signExtend12 (-48 : BitVec 12)) + signExtend12 (0 : BitVec 12))
          (vals .x8) **
        memIs ((sp + signExtend12 (-48 : BitVec 12)) + signExtend12 (8 : BitVec 12))
          (vals .x9) **
        memIs ((sp + signExtend12 (-48 : BitVec 12)) + signExtend12 (16 : BitVec 12))
          (vals .x18) **
        memIs ((sp + signExtend12 (-48 : BitVec 12)) + signExtend12 (24 : BitVec 12))
          (vals .x19) **
        memIs ((sp + signExtend12 (-48 : BitVec 12)) + signExtend12 (32 : BitVec 12))
          (vals .x20) **
        memIs ((sp + signExtend12 (-48 : BitVec 12)) + signExtend12 (40 : BitVec 12))
          (vals .x21)) h := by
    simpa [sha256Frame, frameSlotsSaved, List.foldr, sepConj_emp_right'] using hp
  have hq :=
    sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)))) h hp'
  rw [stackFree6_eq_sha256FrameSlotsOwn sp]
  simpa [sha256Frame, frameSlotsOwn, List.foldr, sepConj_emp_right'] using hq

/-- BSS finals after sha256 (contents of `sha256PadFreeBss` with `A = emp`). -/
def shaBssPost (input params iv : List (BitVec 8)) (N rem : Nat) : Assertion :=
  sha256PadFreeBss input params iv N rem empAssertion

theorem shaBssPost_pcFree (input params iv : List (BitVec 8)) (N rem : Nat) :
    (shaBssPost input params iv N rem).pcFree :=
  sha256PadFreeBss_pcFree input params iv N rem empAssertion (by pcf)

/-- For N=0: pad-free input split is just the intact input region. -/
theorem sha256PadFreeA_N0 (inputBase : Word) (input params iv : List (BitVec 8))
    (rem : Nat) (A : Assertion) :
    sha256PadFreeA inputBase input params iv 0 rem A =
      (sha256PadFreeBss input params iv 0 rem
        (bytesRegion inputBase input ** A)) := by
  simp only [sha256PadFreeA]
  rw [sha256AbsorbCursor_zero]
  -- take (64*0)=[], residual = drop 0 = input; empty region is emp
  change sha256PadFreeBss input params iv 0 rem
      (bytesRegion inputBase (input.take 0) **
        bytesRegion inputBase (input.drop 0) ** A) = _
  simp only [List.take_zero, List.drop_zero, bytesRegion_nil, sepConj_emp_left']

/-- Machine post (N=0) → stackFree + regsAt + thin ABI/digest/input + BSS finals + free temps. -/
theorem shaCallerPost_reshape_N0 (sp0 inputBase outputBase : Word)
    (input params iv : List (BitVec 8)) (rem : Nat)
    (vals : Reg → Word) (A : Assertion) :
    ∀ h,
      ((.x2 ↦ᵣ sp0) **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 (-48 : BitVec 12)) vals **
        regsAt sha256Frame vals **
        shaCallerPost inputBase outputBase input params iv 0 rem A) h →
      ((.x2 ↦ᵣ sp0) ** stackFree sp0 6 **
        regsAt sha256Frame vals **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x0 **
        regOwns sha256BodyFreeTemps **
        bytesRegion outputBase (sha256 input) **
        sha256PadFreeBss input params iv 0 rem (bytesRegion inputBase input ** A)) h := by
  intro h hp
  have hp1 :
      ((frameSlotsSaved sha256Frame (sp0 + signExtend12 (-48 : BitVec 12)) vals **
          ((.x2 ↦ᵣ sp0) ** regsAt sha256Frame vals **
            shaCallerPost inputBase outputBase input params iv 0 rem A))) h := by
    xperm_hyp hp
  have hp2 :=
    sepConj_mono (frameSlotsSaved_sha256_implies_stackFree sp0 vals) (fun _ => id) h hp1
  simp only [shaCallerPost, sha256PadFreeA_N0] at hp2
  xperm_hyp hp2

/-- Unfold `shaBssPost ** input ** A` from nested pad-free BSS. -/
theorem sha256PadFreeBss_split_input (inputBase : Word)
    (input params iv : List (BitVec 8)) (N rem : Nat) (A : Assertion) :
    sha256PadFreeBss input params iv N rem (bytesRegion inputBase input ** A) =
      (shaBssPost input params iv N rem ** bytesRegion inputBase input ** A) := by
  simp only [shaBssPost, sha256PadFreeBss, sepConj_emp_right', ← sepConj_assoc']

private theorem erh_sha_jal_target :
    (pc 19 : Word) + signExtend21
      (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76)) = ShaB := by
  change BitVec.ofNat 64 GuestAddrs.erh_hash_one + BitVec.ofNat 64 76 + _ =
    BitVec.ofNat 64 GuestAddrs.zkvm_sha256
  exact jalOff_correct_add GuestAddrs.zkvm_sha256
    GuestAddrs.erh_hash_one 76
    (by decide) (by decide) (by decide) (by decide)

private theorem erh_sha_jal_hpc : pc 19 = B1 + BitVec.ofNat 64 (4 * 19) := by
  simp only [pc]

private theorem erh_sha_jal_ins :
    hoProgL[19]'(by rw [hoProgL_len]; norm_num) =
      .JAL .x1 (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76)) := by
  simp only [hoProgL, erhHashOne_prog]; decide

private theorem erh_sha_jal_mem :
    ∀ a i, CodeReq.singleton (pc 19)
        (.JAL .x1 (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76)))
        a = some i →
      fullCodeHo a = some i :=
  mem_at 19 _ (pc 19) erh_sha_jal_hpc (by rw [hoProgL_len]; norm_num) erh_sha_jal_ins

private theorem erh_sha_ret_align :
    (((pc 19 : Word) + 4) &&& ~~~(1 : Word)) = (pc 19 : Word) + 4 := by
  simp only [pc]; decide

private theorem erh_sha_pc1920 : (pc 19 : Word) + 4 = pc 20 := by
  simp only [pc]; decide

/-- Empty-arm discharged call at erh_hash_one+76: no `h_sha`.
    Ambient carries callee-saved `regsAt` + BSS + free-temp owns (incl. x29/x30).
    Post: thin `shaCallReturn` + leftovers (regsAt, BSS finals, free temps, caller F). -/
theorem hash_one_sha_call_empty_discharged
    (newSp raVal bodyPtr typeW destPtr : Word)
    (outOld : List (BitVec 8))
    (v8 v9 v18 v19 v20 v21 : Word)
    (st0 scratch0 iv params : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hyps : shaDischargeHyps_empty destPtr (typeByte typeW) st0 scratch0 iv params)
    (hout : outOld.length = 32) :
    let vals := sha256EntryVals v8 v9 v18 v19 v20 v21
    let input := hashOneBlob (typeByte typeW) []
    let F : Assertion :=
      frameSlotsSaved hoFrame newSp (hoVals raVal) **
        (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ destPtr) ** bytesRegion bodyPtr ([] : List (BitVec 8)) ** A
    cpsTripleWithin (1 + nSha256 0 1) (pc 19) (pc 20) fullCodeHo
      (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ newSp) **
          (stackFree newSp 6 ** regsAt sha256Frame vals **
            shaCallerPre Blob (BitVec.ofNat 64 1) destPtr
              st0 scratch0 iv params input outOld empAssertion) ** F))
      (((.x1 ↦ᵣ (pc 20)) **
          shaCallReturn newSp Blob destPtr input) **
        (regsAt sha256Frame vals **
          shaBssPost input params iv 0 1 **
          regOwns sha256BodyFreeTemps ** F)) := by
  intro vals input F
  have hF : F.pcFree := by
    dsimp only [F]
    exact pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) <|
      pcFree_sepConj pcFree_regIs <|
        pcFree_sepConj pcFree_regIs <|
          pcFree_sepConj pcFree_regIs <|
            pcFree_sepConj pcFree_regIs <|
              pcFree_sepConj (bytesRegion_pcFree _ _) hA
  have hcall0 := sha256_callWithin_machine (pc 19) raVal newSp
    (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76))
    Blob destPtr input 0 1 v8 v9 v18 v19 v20 v21
    st0 scratch0 iv params outOld empAssertion F (by exact pcFree_emp) hF hyps hout
    erh_sha_ret_align erh_sha_jal_target erh_sha_jal_mem
  have hcall : cpsTripleWithin (1 + nSha256 0 1) (pc 19) (pc 20) fullCodeHo
      (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ newSp) **
          (stackFree newSp 6 ** regsAt sha256Frame vals **
            shaCallerPre Blob (BitVec.ofNat 64 1) destPtr
              st0 scratch0 iv params input outOld empAssertion) ** F))
      (((.x1 ↦ᵣ (pc 20)) ** (.x2 ↦ᵣ newSp) **
          (frameSlotsSaved sha256Frame (newSp + signExtend12 (-48 : BitVec 12)) vals **
            regsAt sha256Frame vals **
            shaCallerPost Blob destPtr input params iv 0 1 empAssertion) ** F)) := by
    simpa [erh_sha_pc1920, vals, input,
      show BitVec.ofNat 64 (64 * 0 + 1) = BitVec.ofNat 64 1 from rfl] using hcall0
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hcall
  have hqMid :
      (((.x1 ↦ᵣ (pc 20)) **
          ((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
            regsAt sha256Frame vals **
            regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x0 **
            regOwns sha256BodyFreeTemps **
            bytesRegion destPtr (sha256 input) **
            sha256PadFreeBss input params iv 0 1
              (bytesRegion Blob input ** empAssertion)) ** F)) h := by
    refine sepConj_mono (fun _ => id)
      (sepConj_mono (shaCallerPost_reshape_N0 newSp Blob destPtr input params iv 1 vals
          empAssertion) (fun _ => id)) h ?_
    xperm_hyp hq
  rw [sha256PadFreeBss_split_input, sepConj_emp_right'] at hqMid
  dsimp only [shaCallReturn]
  xperm_hyp hqMid

/-! ## Nonempty / general-N reshape + discharged call -/

/-- Recombine pad-free split input into one `bytesRegion`. -/
theorem sha256PadFreeA_recombine (inputBase : Word)
    (input params iv : List (BitVec 8)) (N rem : Nat) (A : Assertion)
    (hlen : input.length = 64 * N + rem) :
    sha256PadFreeA inputBase input params iv N rem A =
      (sha256PadFreeBss input params iv N rem
        (bytesRegion inputBase input ** A)) := by
  simp only [sha256PadFreeA, sha256AbsorbCursor_eq_ofNat64, sha256Residual_drop64]
  have htake : (input.take (64 * N)).length = 64 * N := by
    simp only [List.length_take, hlen]; omega
  have h8 : 8 ∣ (input.take (64 * N)).length := by
    rw [htake]; exact ⟨8 * N, by omega⟩
  have happ := bytesRegion_append inputBase (input.take (64 * N)) (input.drop (64 * N)) h8
  rw [htake] at happ
  -- BSS (take ** drop ** A) → BSS ((take ** drop) ** A) → BSS (input ** A)
  simp only [← sepConj_assoc']
  rw [← happ, List.take_append_drop]

/-- Machine post → stackFree + regsAt + thin ABI/digest/input + nested BSS+input. -/
theorem shaCallerPost_reshape (sp0 inputBase outputBase : Word)
    (input params iv : List (BitVec 8)) (N rem : Nat)
    (vals : Reg → Word) (A : Assertion)
    (hlen : input.length = 64 * N + rem) :
    ∀ h,
      ((.x2 ↦ᵣ sp0) **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 (-48 : BitVec 12)) vals **
        regsAt sha256Frame vals **
        shaCallerPost inputBase outputBase input params iv N rem A) h →
      ((.x2 ↦ᵣ sp0) ** stackFree sp0 6 **
        regsAt sha256Frame vals **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x0 **
        regOwns sha256BodyFreeTemps **
        bytesRegion outputBase (sha256 input) **
        sha256PadFreeBss input params iv N rem (bytesRegion inputBase input ** A)) h := by
  intro h hp
  have hp1 :
      ((frameSlotsSaved sha256Frame (sp0 + signExtend12 (-48 : BitVec 12)) vals **
          ((.x2 ↦ᵣ sp0) ** regsAt sha256Frame vals **
            shaCallerPost inputBase outputBase input params iv N rem A))) h := by
    xperm_hyp hp
  have hp2 :=
    sepConj_mono (frameSlotsSaved_sha256_implies_stackFree sp0 vals) (fun _ => id) h hp1
  simp only [shaCallerPost, sha256PadFreeA_recombine inputBase input params iv N rem A hlen] at hp2
  xperm_hyp hp2

/-- General discharged call at erh_hash_one+76: no `h_sha`.
    `lenW` is the body length word; ABI a1 = lenW+1 = |type‖body|. -/
theorem hash_one_sha_call_discharged
    (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body outOld : List (BitVec 8)) (N rem : Nat)
    (v8 v9 v18 v19 v20 v21 : Word)
    (st0 scratch0 iv params : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hyps : ShaDischargeHyps Blob destPtr (hashOneBlob (typeByte typeW) body)
        N rem st0 scratch0 iv params)
    (_hlenW : lenW = BitVec.ofNat 64 body.length)
    (hout : outOld.length = 32)
    (hpart : body.length + 1 = 64 * N + rem) :
    let vals := sha256EntryVals v8 v9 v18 v19 v20 v21
    let input := hashOneBlob (typeByte typeW) body
    let F : Assertion :=
      frameSlotsSaved hoFrame newSp (hoVals raVal) **
        (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) **
        (.x24 ↦ᵣ destPtr) ** bytesRegion bodyPtr body ** A
    cpsTripleWithin (1 + nSha256 N rem) (pc 19) (pc 20) fullCodeHo
      (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ newSp) **
          (stackFree newSp 6 ** regsAt sha256Frame vals **
            shaCallerPre Blob (BitVec.ofNat 64 (64 * N + rem)) destPtr
              st0 scratch0 iv params input outOld empAssertion) ** F))
      (((.x1 ↦ᵣ (pc 20)) **
          shaCallReturn newSp Blob destPtr input) **
        (regsAt sha256Frame vals **
          shaBssPost input params iv N rem **
          regOwns sha256BodyFreeTemps ** F)) := by
  intro vals input F
  have hF : F.pcFree := by
    dsimp only [F]
    exact pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) <|
      pcFree_sepConj pcFree_regIs <|
        pcFree_sepConj pcFree_regIs <|
          pcFree_sepConj pcFree_regIs <|
            pcFree_sepConj pcFree_regIs <|
              pcFree_sepConj (bytesRegion_pcFree _ _) hA
  have hlenEq : input.length = 64 * N + rem := by
    simp only [input, hashOneBlob, List.length_cons, hpart]
  -- hyps.hlen should match; use hyps for the machine
  have hcall0 := sha256_callWithin_machine (pc 19) raVal newSp
    (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76))
    Blob destPtr input N rem v8 v9 v18 v19 v20 v21
    st0 scratch0 iv params outOld empAssertion F (by exact pcFree_emp) hF hyps hout
    erh_sha_ret_align erh_sha_jal_target erh_sha_jal_mem
  have hcall : cpsTripleWithin (1 + nSha256 N rem) (pc 19) (pc 20) fullCodeHo
      (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ newSp) **
          (stackFree newSp 6 ** regsAt sha256Frame vals **
            shaCallerPre Blob (BitVec.ofNat 64 (64 * N + rem)) destPtr
              st0 scratch0 iv params input outOld empAssertion) ** F))
      (((.x1 ↦ᵣ (pc 20)) ** (.x2 ↦ᵣ newSp) **
          (frameSlotsSaved sha256Frame (newSp + signExtend12 (-48 : BitVec 12)) vals **
            regsAt sha256Frame vals **
            shaCallerPost Blob destPtr input params iv N rem empAssertion) ** F)) := by
    simpa [erh_sha_pc1920, vals, input] using hcall0
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hcall
  have hqMid :
      (((.x1 ↦ᵣ (pc 20)) **
          ((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
            regsAt sha256Frame vals **
            regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x0 **
            regOwns sha256BodyFreeTemps **
            bytesRegion destPtr (sha256 input) **
            sha256PadFreeBss input params iv N rem
              (bytesRegion Blob input ** empAssertion)) ** F)) h := by
    refine sepConj_mono (fun _ => id)
      (sepConj_mono (shaCallerPost_reshape newSp Blob destPtr input params iv N rem vals
          empAssertion hlenEq) (fun _ => id)) h ?_
    xperm_hyp hq
  rw [sha256PadFreeBss_split_input, sepConj_emp_right'] at hqMid
  dsimp only [shaCallReturn]
  xperm_hyp hqMid

end EvmAsm.Codegen.ExecutionRequestsHashShaDischarge
