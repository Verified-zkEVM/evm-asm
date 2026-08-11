/-
  ExecutionRequestsHashWrap — prologue + framed body → hash-entry.

  Validation accept prefix only (hash half residual from B+300):
    ADDI sp,-96 + storeSeq (13) @ B
    body setup..gates (122) @ B+52
  → B+300. Fuel 135 = 13+122.

  Domain: listBase%8=0, 20≤bs.length, ¬ult endW 20, mono+gates on
  decoded offsets. Parent: #11578 rescope.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.Programs.ExecutionRequestsHashBody
import EvmAsm.Codegen.Programs.ExecutionRequestsHashEpi
import EvmAsm.Codegen.Programs.ExecutionRequestsHashBgv
import EvmAsm.Codegen.Programs.ExecutionRequestsHashGates
import EvmAsm.Codegen.Programs.ExecutionRequestsHashMono
import EvmAsm.Codegen.Programs.ExecutionRequestsHashReads
import EvmAsm.Codegen.Programs.ExecutionRequestsHashVal
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Evm64.EvmWordArith.MultiLimb

namespace EvmAsm.Codegen.ExecutionRequestsHashWrap

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)
open EvmAsm.Codegen.ExecutionRequestsHashBody
open EvmAsm.Codegen.ExecutionRequestsHashEpi
open EvmAsm.Codegen.ExecutionRequestsHashBgv
open EvmAsm.Codegen.ExecutionRequestsHashGates
open EvmAsm.Codegen.ExecutionRequestsHashMono
open EvmAsm.Codegen.ExecutionRequestsHashReads
open EvmAsm.Codegen.ExecutionRequestsHashVal
open EvmAsm.Evm64.EvmWord

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.execution_requests_hash
private abbrev erhProgL : List Instr := executionRequestsHash_prog

private theorem erhProgL_len : erhProgL.length = 135 := by
  simp only [erhProgL, executionRequestsHash_prog]; decide

private theorem erhProgL_bound : 4 * erhProgL.length < 2 ^ 64 := by
  rw [erhProgL_len]; norm_num

local macro "pcf" : tactic =>
  `(tactic| repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact bytesRegion_pcFree _ _
      | exact pcFree_emp
      | exact pcFree_pure
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _)

private theorem lift_erh {n : Nat} {entry exit_ : Word} {P Q : Assertion}
    (h : cpsTripleWithin n entry exit_ (CodeReq.ofProg B executionRequestsHash_prog) P Q) :
    cpsTripleWithin n entry exit_ fullCode P Q :=
  cpsTripleWithin_extend_code
    (fun a i hi => by
      unfold fullCode
      exact CodeReq.union_mono_left a i hi) h

/-- Prologue: ADDI sp,-96 + 12×SD. Fuel 13. B → B+52. -/
theorem erh_prologue
    (sp0 : Word) (s : ErhSaved)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 13 B (B + 52) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt erhFrame (erhSavedVals s) **
        frameSlotsOwn erhFrame (sp0 + signExtend12 (-96 : BitVec 12)) ** A)
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-96 : BitVec 12))) **
        regsAt erhFrame (erhSavedVals s) **
        frameSlotsSaved erhFrame (sp0 + signExtend12 (-96 : BitVec 12))
          (erhSavedVals s) ** A) := by
  set newSp := sp0 + signExtend12 (-96 : BitVec 12) with hNS
  have hbound : 4 * erhFrame.length < 2 ^ 64 := by
    simp only [erhFrame, List.length_cons, List.length_nil]; norm_num
  have hne_x2 : Reg.x2 ≠ .x0 := by decide
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-96 : BitVec 12) B hne_x2
  rw [← hNS] at ha0
  have haC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B B erhProgL 0
      (.ADDI .x2 .x2 (-96 : BitVec 12))
      (by bv_omega) (by rw [erhProgL_len]; decide) rfl erhProgL_bound) ha0
  have hFpc : (regsAt erhFrame (erhSavedVals s) **
      frameSlotsOwn erhFrame newSp ** A).pcFree := by
    exact pcFree_sepConj (pcFree_regsAt _ _)
      (pcFree_sepConj (pcFree_frameSlotsOwn _ _) hA)
  have haF := cpsTripleWithin_frameR
    (regsAt erhFrame (erhSavedVals s) ** frameSlotsOwn erhFrame newSp ** A)
    hFpc haC
  -- frameR F with F = regsAt ** own ** A already right-assoc matches goal
  have ha := lift_erh haF
  have hs0 := storeSeq_spec erhFrame newSp (erhSavedVals s) (B + 4) hbound
  have h_storeMono : ∀ a i,
      CodeReq.ofProg (B + 4) (storeProg erhFrame) a = some i →
        (CodeReq.ofProg B erhProgL) a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub B (B + 4) erhProgL (storeProg erhFrame) 1
      (by bv_omega) (by rfl)
      (by rw [erhProgL_len]; simp [erhFrame, storeProg])
      erhProgL_bound a i h_mem
  have hs1 := cpsTripleWithin_extend_code h_storeMono hs0
  have hsF := cpsTripleWithin_frameR A hA hs1
  rw [show (B + 4 : Word) + BitVec.ofNat 64 (4 * erhFrame.length) = B + 52 from by
    simp only [erhFrame, List.length_cons, List.length_nil]; bv_omega] at hsF
  -- frameR A: ((x2 ** regsAt ** slots) ** A) → x2 ** regsAt ** slots ** A
  -- Use Assertion-level sepConj_assoc' (not holds-iff sepConj_assoc)
  have hsFlat :
      cpsTripleWithin erhFrame.length (B + 4) (B + 52)
        (CodeReq.ofProg B erhProgL)
        ((.x2 ↦ᵣ newSp) ** regsAt erhFrame (erhSavedVals s) **
          frameSlotsOwn erhFrame newSp ** A)
        ((.x2 ↦ᵣ newSp) ** regsAt erhFrame (erhSavedVals s) **
          frameSlotsSaved erhFrame newSp (erhSavedVals s) ** A) := by
    convert hsF using 1
    · -- ((x2 ** (regsAt ** own)) ** A) = x2 ** regsAt ** own ** A
      rw [sepConj_assoc' (.x2 ↦ᵣ newSp)
        (regsAt erhFrame (erhSavedVals s) ** frameSlotsOwn erhFrame newSp) A]
      rw [sepConj_assoc' (regsAt erhFrame (erhSavedVals s))
        (frameSlotsOwn erhFrame newSp) A]
    · rw [sepConj_assoc' (.x2 ↦ᵣ newSp)
        (regsAt erhFrame (erhSavedVals s) **
          frameSlotsSaved erhFrame newSp (erhSavedVals s)) A]
      rw [sepConj_assoc' (regsAt erhFrame (erhSavedVals s))
        (frameSlotsSaved erhFrame newSp (erhSavedVals s)) A]
  have hs := lift_erh hsFlat
  have hall := cpsTripleWithin_seq_same_cr ha hs
  have hn : 1 + erhFrame.length = 13 := by
    simp only [erhFrame, List.length_cons, List.length_nil]
  rw [hn] at hall
  exact hall

/-- sp + saved frame slots ambient. -/
def bodyFrameAmb (spC : Word) (s : ErhSaved) (A : Assertion) : Assertion :=
  (.x2 ↦ᵣ spC) ** frameSlotsSaved erhFrame spC (erhSavedVals s) ** A

/-- Untouched frame regs x24–x26 framed through the body. -/
def bodyHiRegs (s : ErhSaved) : Assertion :=
  (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10)

/-- Body under frame ambient: B+52 → B+300. Fuel 122.
    Entry x8/x9/x18/x19–x23 come from regsAt (saved s0–s7).
    x24–x26 preserved (hash half re-inits x24). -/
theorem erh_validation_accept_body_framed
    (spC listBase endW outW : Word) (bs : List (BitVec 8))
    (s : ErhSaved)
    (v5 v6 v7 v28 : Word)
    (A : Assertion) (hA : A.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 20 ≤ bs.length)
    (h_over : listBase.toNat + 19 < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_ge : ¬ BitVec.ult endW (20 : Word))
    (hmono : erhOffsetsMonoW (erhOffsetsFromBytes bs endW))
    (hgates : erhGatesOkW (erhOffsetsFromBytes bs endW)) :
    cpsTripleWithin 122 (B + 52) (B + 300) fullCode
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        regsAt erhFrame (erhSavedVals s) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
        bodyFrameAmb spC s A)
      (let o := erhOffsetsFromBytes bs endW
       (.x1 ↦ᵣ (B + 128)) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ o.bexit) **
         (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) ** (.x18 ↦ᵣ outW) **
         erhOffsetRegs o **
         erhGateTemps (o.end_ - o.bexit) (68 : Word)
           (rv64_divu (o.end_ - o.bexit) (68 : Word)) (16 : Word) **
         bytesRegion listBase bs **
         bodyHiRegs s ** bodyFrameAmb spC s A) := by
  have hAmb : (bodyHiRegs s ** bodyFrameAmb spC s A).pcFree := by
    simp only [bodyHiRegs, bodyFrameAmb]; pcf; exact hA
  have hbody := erh_validation_accept_body listBase endW outW bs
    s.s0 s.s1 s.s2 v5 v6 v7 s.s3 s.s4 s.s5 s.s6 s.s7 v28 s.ra
    (bodyHiRegs s ** bodyFrameAmb spC s A) hAmb
    h_align h_fit h_over h_valid h_ge hmono hgates
  refine cpsTripleWithin_weaken ?hpre ?hpost hbody
  · intro st hp
    -- Goal: body pre under ambient → body entry with hiRegs ** frameAmb
    simp only [regsAt_erhFrame, bodyHiRegs, bodyFrameAmb] at hp ⊢
    xperm_chunked hp
  · intro st hq
    simp only [bodyHiRegs, bodyFrameAmb] at hq ⊢
    xperm_chunked hq

/-- Top: entry → hash-entry B+300 under validation accept. Fuel 135.
    Hash half residual. Frame still live (sp-96, slots saved).
    ABI: a0=listBase, a1=endW, a2=outW. -/
theorem execution_requests_hash_validation_accept
    (sp0 listBase endW outW : Word) (bs : List (BitVec 8))
    (s : ErhSaved)
    (v5 v6 v7 v28 : Word)
    (A : Assertion) (hA : A.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 20 ≤ bs.length)
    (h_over : listBase.toNat + 19 < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_ge : ¬ BitVec.ult endW (20 : Word))
    (hmono : erhOffsetsMonoW (erhOffsetsFromBytes bs endW))
    (hgates : erhGatesOkW (erhOffsetsFromBytes bs endW)) :
    let newSp := sp0 + signExtend12 (-96 : BitVec 12)
    cpsTripleWithin 135 B (B + 300) fullCode
      ((.x2 ↦ᵣ sp0) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        regsAt erhFrame (erhSavedVals s) **
        frameSlotsOwn erhFrame newSp **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A)
      (let o := erhOffsetsFromBytes bs endW
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (B + 128)) ** (.x8 ↦ᵣ listBase) **
         (.x10 ↦ᵣ o.bexit) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
         (.x18 ↦ᵣ outW) ** erhOffsetRegs o **
         erhGateTemps (o.end_ - o.bexit) (68 : Word)
           (rv64_divu (o.end_ - o.bexit) (68 : Word)) (16 : Word) **
         bytesRegion listBase bs **
         bodyHiRegs s **
         frameSlotsSaved erhFrame newSp (erhSavedVals s) ** A) := by
  intro newSp
  let Fpro : Assertion :=
    (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A
  have hFpro : Fpro.pcFree := by simp only [Fpro]; pcf; exact hA
  have hp0 := erh_prologue sp0 s Fpro hFpro
  have hns : newSp = sp0 + signExtend12 (-96 : BitVec 12) := rfl
  have hp : cpsTripleWithin 13 B (B + 52) fullCode
      ((.x2 ↦ᵣ sp0) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        regsAt erhFrame (erhSavedVals s) **
        frameSlotsOwn erhFrame newSp **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A)
      ((.x2 ↦ᵣ newSp) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        regsAt erhFrame (erhSavedVals s) **
        frameSlotsSaved erhFrame newSp (erhSavedVals s) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A) := by
    rw [hns]
    exact cpsTripleWithin_weaken
      (fun _ hx => by simp only [Fpro] at hx ⊢; xperm_chunked hx)
      (fun _ hx => by simp only [Fpro] at hx ⊢; xperm_chunked hx) hp0
  have hb0 := erh_validation_accept_body_framed newSp listBase endW outW bs s
    v5 v6 v7 v28 A hA
    h_align h_fit h_over h_valid h_ge hmono hgates
  have hb : cpsTripleWithin 122 (B + 52) (B + 300) fullCode
      ((.x2 ↦ᵣ newSp) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        regsAt erhFrame (erhSavedVals s) **
        frameSlotsSaved erhFrame newSp (erhSavedVals s) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A)
      (let o := erhOffsetsFromBytes bs endW
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (B + 128)) ** (.x8 ↦ᵣ listBase) **
         (.x10 ↦ᵣ o.bexit) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
         (.x18 ↦ᵣ outW) ** erhOffsetRegs o **
         erhGateTemps (o.end_ - o.bexit) (68 : Word)
           (rv64_divu (o.end_ - o.bexit) (68 : Word)) (16 : Word) **
         bytesRegion listBase bs **
         bodyHiRegs s **
         frameSlotsSaved erhFrame newSp (erhSavedVals s) ** A) :=
    cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [bodyFrameAmb] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [bodyFrameAmb, bodyHiRegs] at hq ⊢; xperm_chunked hq) hb0
  have hall := cpsTripleWithin_seq_same_cr hp hb
  have hn : 13 + 122 = 135 := rfl
  rw [hn] at hall
  exact hall

end EvmAsm.Codegen.ExecutionRequestsHashWrap
