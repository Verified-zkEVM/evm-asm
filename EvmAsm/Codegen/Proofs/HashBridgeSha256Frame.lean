/-
  EvmAsm.Codegen.Proofs.HashBridgeSha256Frame

  6-slot no-ra ABI frame for `zkvm_sha256`:
    frame = [(x8,0),(x9,8),(x18,16),(x19,24),(x20,32),(x21,40)]
    prologue ADDI sp,-48 + 6×SD; epilogue 6×LD + ADDI sp,+48 + JALR x0,x1
  Unlike `abiFrame_spec`, ra is NOT saved (body must preserve x1=ret).
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakWrap
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-- Saved-register frame for zkvm_keccak256 (no ra). -/
def sha256Frame : FrameDesc :=
  [(.x8, (0 : BitVec 12)), (.x9, (8 : BitVec 12)),
   (.x18, (16 : BitVec 12)), (.x19, (24 : BitVec 12)),
   (.x20, (32 : BitVec 12)), (.x21, (40 : BitVec 12))]

theorem sha256Frame_length : sha256Frame.length = 6 := rfl

theorem sha256Frame_hne : ∀ p ∈ sha256Frame, p.1 ≠ .x0 := by
  intro p hp
  simp only [sha256Frame, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h <;> (subst h; decide)

private theorem signExtend12_neg48 :
    signExtend12 ((-48 : BitVec 12)) = BitVec.ofInt 64 (-48) := by decide

private theorem signExtend12_pos48 :
    signExtend12 ((48 : BitVec 12)) = (48 : Word) := by decide

private theorem neg48_add_48 :
    BitVec.ofInt 64 (-48) + (48 : Word) = (0 : Word) := by decide

private theorem frame_restore (sp0 : Word) :
    (sp0 + signExtend12 ((-48 : BitVec 12))) + signExtend12 ((48 : BitVec 12)) =
      sp0 := by
  rw [signExtend12_neg48, signExtend12_pos48, BitVec.add_assoc, neg48_add_48]
  exact BitVec.add_zero sp0

/-- Body entry = base+28 (idx 7, after addi+6 sd). -/
abbrev sha256BodyEntry (base : Word) : Word := base + (28 : Word)

/-- Body exit = base+452 (idx 113, first epilogue LD after LI a0,0). -/
abbrev sha256BodyExit (base : Word) : Word := base + (452 : Word)

private theorem add_ofNat24 (p : Word) :
    p + BitVec.ofNat 64 24 = p + (24 : Word) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rfl

/-- Prologue: ADDI sp,-48. -/
theorem sha256Prologue_alloc (cr : CodeReq) (base : Word) (sp0 : Word)
    (hmem : ∀ a i, CodeReq.singleton base (.ADDI .x2 .x2 (-48 : BitVec 12)) a = some i →
      cr a = some i) :
    cpsTripleWithin 1 base (base + 4) cr
      (.x2 ↦ᵣ sp0)
      (.x2 ↦ᵣ (sp0 + signExtend12 ((-48 : BitVec 12)))) := by
  have h := cpsTripleWithin_extend_code hmem
    (addi_spec_gen_same_within .x2 sp0 (-48 : BitVec 12) base (by decide))
  rw [show base + 4 = base + 4 from rfl] at h
  exact h

/-- Prologue stores: 6× SD. Fuel 6. -/
theorem sha256Prologue_store (newSp : Word) (vals : Reg → Word) (startAddr : Word) :
    cpsTripleWithin 6 startAddr (startAddr + (24 : Word))
      (CodeReq.ofProg startAddr (storeProg sha256Frame))
      ((.x2 ↦ᵣ newSp) ** regsAt sha256Frame vals ** frameSlotsOwn sha256Frame newSp)
      ((.x2 ↦ᵣ newSp) ** regsAt sha256Frame vals **
        frameSlotsSaved sha256Frame newSp vals) := by
  have h := storeSeq_spec sha256Frame newSp vals startAddr (by decide)
  -- exit = start + 4*6 = start+24
  have hexit : startAddr + BitVec.ofNat 64 (4 * sha256Frame.length) =
      startAddr + (24 : Word) := by
    simp only [sha256Frame_length]
    exact add_ofNat24 startAddr
  rwa [hexit] at h

/-- Full prologue fuel 7: alloc + store. -/
theorem sha256Prologue_spec (cr : CodeReq) (base : Word) (sp0 : Word)
    (vals : Reg → Word)
    (hmemA : ∀ a i, CodeReq.singleton base (.ADDI .x2 .x2 (-48 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemS : ∀ a i, CodeReq.ofProg (base + 4) (storeProg sha256Frame) a = some i →
      cr a = some i) :
    cpsTripleWithin 7 base (sha256BodyEntry base) cr
      ((.x2 ↦ᵣ sp0) ** regsAt sha256Frame vals **
        frameSlotsOwn sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))))
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-48 : BitVec 12)))) **
        regsAt sha256Frame vals **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) vals) := by
  set newSp := sp0 + signExtend12 ((-48 : BitVec 12))
  have halloc := sha256Prologue_alloc cr base sp0 hmemA
  have hallocF := cpsTripleWithin_frameR
    (regsAt sha256Frame vals ** frameSlotsOwn sha256Frame newSp)
    (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsOwn _ _)) halloc
  have c0 : cpsTripleWithin 1 base (base + 4) cr
      ((.x2 ↦ᵣ sp0) ** regsAt sha256Frame vals **
        frameSlotsOwn sha256Frame newSp)
      ((.x2 ↦ᵣ newSp) ** regsAt sha256Frame vals **
        frameSlotsOwn sha256Frame newSp) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hallocF
  have hstore0 := sha256Prologue_store newSp vals (base + 4)
  have hstore := cpsTripleWithin_extend_code hmemS hstore0
  have hpc : (base + 4 : Word) + (24 : Word) = sha256BodyEntry base := by
    simp only [sha256BodyEntry]
    rw [BitVec.add_assoc, show ((4 : Word) + 24) = (28 : Word) from by decide]
  rw [hpc] at hstore
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 hstore

/-- Epilogue loads: 6× LD. Fuel 6. Restores vals regardless of body vals'. -/
theorem sha256Epilogue_load (newSp : Word) (vals vals' : Reg → Word) (startAddr : Word) :
    cpsTripleWithin 6 startAddr (startAddr + (24 : Word))
      (CodeReq.ofProg startAddr (loadProg sha256Frame))
      ((.x2 ↦ᵣ newSp) ** regsAt sha256Frame vals' **
        frameSlotsSaved sha256Frame newSp vals)
      ((.x2 ↦ᵣ newSp) ** regsAt sha256Frame vals **
        frameSlotsSaved sha256Frame newSp vals) := by
  have h := loadSeq_spec sha256Frame newSp vals vals' startAddr
    (by decide) sha256Frame_hne
  have hexit : startAddr + BitVec.ofNat 64 (4 * sha256Frame.length) =
      startAddr + (24 : Word) := by
    simp only [sha256Frame_length]
    exact add_ofNat24 startAddr
  rwa [hexit] at h

/-- Epilogue dealloc ADDI sp,+48. -/
theorem sha256Epilogue_dealloc (cr : CodeReq) (entry : Word) (newSp sp0 : Word)
    (hrest : newSp + signExtend12 ((48 : BitVec 12)) = sp0)
    (hmem : ∀ a i, CodeReq.singleton entry (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i →
      cr a = some i) :
    cpsTripleWithin 1 entry (entry + 4) cr
      (.x2 ↦ᵣ newSp)
      (.x2 ↦ᵣ sp0) := by
  have h := cpsTripleWithin_extend_code hmem
    (addi_spec_gen_same_within .x2 newSp (48 : BitVec 12) entry (by decide))
  rw [show entry + 4 = entry + 4 from rfl] at h
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => ?_) h
  -- hq : (.x2 ↦ newSp + sext32) s; need (.x2 ↦ sp0) s
  rw [hrest] at hq
  exact hq

/-- JALR x0,x1 → ret (ra even). -/
theorem sha256Ret_spec (cr : CodeReq) (entry ret : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hmem : ∀ a i, CodeReq.singleton entry (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
      cr a = some i) :
    cpsTripleWithin 1 entry ret cr
      (.x1 ↦ᵣ ret)
      (.x1 ↦ᵣ ret) := by
  have h := cpsTripleWithin_extend_code hmem
    (jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) entry)
  -- target = (ret + sext0) &&& ~~~1 = ret
  have hz : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hpc : (ret + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = ret := by
    rw [hz, show ret + (0 : Word) = ret from BitVec.add_zero ret, halign]
  rwa [hpc] at h

/-- Full epilogue: load + dealloc + JALR. Fuel 6.
    Entry = bodyExit = base+412. Exit = ret. -/
theorem sha256Epilogue_spec (cr : CodeReq) (base sp0 ret : Word)
    (vals vals' : Reg → Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hmemL : ∀ a i, CodeReq.ofProg (sha256BodyExit base) (loadProg sha256Frame) a = some i →
      cr a = some i)
    (hmemD : ∀ a i, CodeReq.singleton (sha256BodyExit base + (24 : Word))
        (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemR : ∀ a i, CodeReq.singleton (sha256BodyExit base + (28 : Word))
        (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
      cr a = some i) :
    cpsTripleWithin 8 (sha256BodyExit base) ret cr
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-48 : BitVec 12)))) **
        (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals' **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) vals)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) vals) := by
  set newSp := sp0 + signExtend12 ((-48 : BitVec 12))
  have hrest := frame_restore sp0
  -- load
  have hload0 := sha256Epilogue_load newSp vals vals' (sha256BodyExit base)
  have hload := cpsTripleWithin_extend_code hmemL hload0
  have hloadF := cpsTripleWithin_frameR (.x1 ↦ᵣ ret) (by pcf) hload
  have c0 : cpsTripleWithin 6 (sha256BodyExit base)
      (sha256BodyExit base + (24 : Word)) cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals' ** frameSlotsSaved sha256Frame newSp vals)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hloadF
  -- dealloc
  have hde := sha256Epilogue_dealloc cr (sha256BodyExit base + (24 : Word)) newSp sp0
    hrest hmemD
  have hdeF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsSaved _ _ _)))
    hde
  have c1 : cpsTripleWithin 1 (sha256BodyExit base + (24 : Word))
      (sha256BodyExit base + (28 : Word)) cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals) := by
    have hpc : (sha256BodyExit base + (24 : Word)) + 4 =
        sha256BodyExit base + (28 : Word) := by
      rw [BitVec.add_assoc, show ((24 : Word) + 4) = (28 : Word) from by decide]
    rw [← hpc]
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hdeF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  -- ret
  have hret := sha256Ret_spec cr (sha256BodyExit base + (28 : Word)) ret halign hmemR
  have hretF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) ** regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsSaved _ _ _)))
    hret
  have c2 : cpsTripleWithin 1 (sha256BodyExit base + (28 : Word)) ret cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hretF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2

/-- No-ra frame wrap: prologue + body + epilogue.
    Body hyp must preserve x1=ret and frame slots; may clobber saved regs (restored). -/
theorem sha256Frame_spec (cr : CodeReq) (base sp0 ret : Word)
    (vals vals' : Reg → Word) (bodySteps : Nat)
    (callerPre callerPost : Assertion)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hcpF : callerPre.pcFree) (hcpF' : callerPost.pcFree)
    (hmemA : ∀ a i, CodeReq.singleton base (.ADDI .x2 .x2 (-48 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemS : ∀ a i, CodeReq.ofProg (base + 4) (storeProg sha256Frame) a = some i →
      cr a = some i)
    (hmemL : ∀ a i, CodeReq.ofProg (sha256BodyExit base) (loadProg sha256Frame) a = some i →
      cr a = some i)
    (hmemD : ∀ a i, CodeReq.singleton (sha256BodyExit base + (24 : Word))
        (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemR : ∀ a i, CodeReq.singleton (sha256BodyExit base + (28 : Word))
        (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
      cr a = some i)
    (hbody : cpsTripleWithin bodySteps (sha256BodyEntry base) (sha256BodyExit base) cr
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-48 : BitVec 12)))) **
        (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) vals **
        callerPre)
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-48 : BitVec 12)))) **
        (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals' **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) vals **
        callerPost)) :
    cpsTripleWithin (7 + bodySteps + 8) base ret cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals **
        frameSlotsOwn sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) **
        callerPre)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) vals **
        callerPost) := by
  set newSp := sp0 + signExtend12 ((-48 : BitVec 12))
  -- prologue
  have hpro0 := sha256Prologue_spec cr base sp0 vals hmemA hmemS
  have hproF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** callerPre)
    (pcFree_sepConj (by pcf) hcpF) hpro0
  have cPro : cpsTripleWithin 7 base (sha256BodyEntry base) cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsOwn sha256Frame newSp ** callerPre)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals **
        callerPre) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hproF
  -- body
  have cBody : cpsTripleWithin bodySteps (sha256BodyEntry base) (sha256BodyExit base) cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals **
        callerPre)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals' ** frameSlotsSaved sha256Frame newSp vals **
        callerPost) := hbody
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) cPro cBody
  -- epilogue
  have hepi0 := sha256Epilogue_spec cr base sp0 ret vals vals' halign hmemL hmemD hmemR
  have hepiF := cpsTripleWithin_frameR callerPost hcpF' hepi0
  have cEpi : cpsTripleWithin 8 (sha256BodyExit base) ret cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals' ** frameSlotsSaved sha256Frame newSp vals **
        callerPost)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals **
        callerPost) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hepiF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 cEpi

/-- Epilogue with OWNED saved regs at body exit (values dead; loads restore). -/
theorem sha256Epilogue_spec_own (cr : CodeReq) (base sp0 ret : Word)
    (vals : Reg → Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hmemL : ∀ a i, CodeReq.ofProg (sha256BodyExit base) (loadProg sha256Frame) a = some i →
      cr a = some i)
    (hmemD : ∀ a i, CodeReq.singleton (sha256BodyExit base + (24 : Word))
        (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemR : ∀ a i, CodeReq.singleton (sha256BodyExit base + (28 : Word))
        (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
      cr a = some i) :
    cpsTripleWithin 8 (sha256BodyExit base) ret cr
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-48 : BitVec 12)))) **
        (.x1 ↦ᵣ ret) **
        regsOwnAt sha256Frame **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) vals)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) vals) := by
  set newSp := sp0 + signExtend12 ((-48 : BitVec 12))
  have hrest := frame_restore sp0
  have hload0 := loadSeq_spec_own sha256Frame newSp vals (sha256BodyExit base)
    (by decide) sha256Frame_hne
  have hload := cpsTripleWithin_extend_code hmemL hload0
  have hexit : sha256BodyExit base + BitVec.ofNat 64 (4 * sha256Frame.length) =
      sha256BodyExit base + (24 : Word) := by
    simp only [sha256Frame_length]
    exact add_ofNat24 (sha256BodyExit base)
  rw [hexit] at hload
  have hloadF := cpsTripleWithin_frameR (.x1 ↦ᵣ ret) (by pcf) hload
  have c0 : cpsTripleWithin 6 (sha256BodyExit base)
      (sha256BodyExit base + (24 : Word)) cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsOwnAt sha256Frame ** frameSlotsSaved sha256Frame newSp vals)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hloadF
  have hde := sha256Epilogue_dealloc cr (sha256BodyExit base + (24 : Word)) newSp sp0
    hrest hmemD
  have hdeF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsSaved _ _ _)))
    hde
  have c1 : cpsTripleWithin 1 (sha256BodyExit base + (24 : Word))
      (sha256BodyExit base + (28 : Word)) cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals) := by
    have hpc : (sha256BodyExit base + (24 : Word)) + 4 =
        sha256BodyExit base + (28 : Word) := by
      rw [BitVec.add_assoc, show ((24 : Word) + 4) = (28 : Word) from by decide]
    rw [← hpc]
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hdeF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  have hret := sha256Ret_spec cr (sha256BodyExit base + (28 : Word)) ret halign hmemR
  have hretF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) ** regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsSaved _ _ _)))
    hret
  have c2 : cpsTripleWithin 1 (sha256BodyExit base + (28 : Word)) ret cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hretF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2

/-- No-ra frame wrap with body ending in `regsOwnAt` (dead exit values). -/
theorem sha256Frame_spec_own (cr : CodeReq) (base sp0 ret : Word)
    (vals : Reg → Word) (bodySteps : Nat)
    (callerPre callerPost : Assertion)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hcpF : callerPre.pcFree) (hcpF' : callerPost.pcFree)
    (hmemA : ∀ a i, CodeReq.singleton base (.ADDI .x2 .x2 (-48 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemS : ∀ a i, CodeReq.ofProg (base + 4) (storeProg sha256Frame) a = some i →
      cr a = some i)
    (hmemL : ∀ a i, CodeReq.ofProg (sha256BodyExit base) (loadProg sha256Frame) a = some i →
      cr a = some i)
    (hmemD : ∀ a i, CodeReq.singleton (sha256BodyExit base + (24 : Word))
        (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemR : ∀ a i, CodeReq.singleton (sha256BodyExit base + (28 : Word))
        (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
      cr a = some i)
    (hbody : cpsTripleWithin bodySteps (sha256BodyEntry base) (sha256BodyExit base) cr
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-48 : BitVec 12)))) **
        (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) vals **
        callerPre)
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-48 : BitVec 12)))) **
        (.x1 ↦ᵣ ret) **
        regsOwnAt sha256Frame **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) vals **
        callerPost)) :
    cpsTripleWithin (7 + bodySteps + 8) base ret cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals **
        frameSlotsOwn sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) **
        callerPre)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals **
        frameSlotsSaved sha256Frame (sp0 + signExtend12 ((-48 : BitVec 12))) vals **
        callerPost) := by
  set newSp := sp0 + signExtend12 ((-48 : BitVec 12))
  have hpro0 := sha256Prologue_spec cr base sp0 vals hmemA hmemS
  have hproF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** callerPre)
    (pcFree_sepConj (by pcf) hcpF) hpro0
  have cPro : cpsTripleWithin 7 base (sha256BodyEntry base) cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsOwn sha256Frame newSp ** callerPre)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals **
        callerPre) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hproF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) cPro hbody
  have hepi0 := sha256Epilogue_spec_own cr base sp0 ret vals halign hmemL hmemD hmemR
  have hepiF := cpsTripleWithin_frameR callerPost hcpF' hepi0
  have cEpi : cpsTripleWithin 8 (sha256BodyExit base) ret cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsOwnAt sha256Frame ** frameSlotsSaved sha256Frame newSp vals **
        callerPost)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals ** frameSlotsSaved sha256Frame newSp vals **
        callerPost) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hepiF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 cEpi

end EvmAsm.Codegen.Proofs
