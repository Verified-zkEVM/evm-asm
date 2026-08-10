/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakFrame

  4-slot no-ra ABI frame for `zkvm_keccak256`:
    frame = [(x8,0),(x9,8),(x18,16),(x20,24)]
    prologue ADDI sp,-32 + 4×SD; epilogue 4×LD + ADDI sp,+32 + JALR x0,x1
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
def keccakFrame : FrameDesc :=
  [(.x8, (0 : BitVec 12)), (.x9, (8 : BitVec 12)),
   (.x18, (16 : BitVec 12)), (.x20, (24 : BitVec 12))]

theorem keccakFrame_length : keccakFrame.length = 4 := rfl

theorem keccakFrame_hne : ∀ p ∈ keccakFrame, p.1 ≠ .x0 := by
  intro p hp
  simp only [keccakFrame, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h <;> (subst h; decide)

private theorem signExtend12_neg32 :
    signExtend12 ((-32 : BitVec 12)) = BitVec.ofInt 64 (-32) := by decide

private theorem signExtend12_pos32 :
    signExtend12 ((32 : BitVec 12)) = (32 : Word) := by decide

private theorem neg32_add_32 :
    BitVec.ofInt 64 (-32) + (32 : Word) = (0 : Word) := by decide

private theorem frame_restore (sp0 : Word) :
    (sp0 + signExtend12 ((-32 : BitVec 12))) + signExtend12 ((32 : BitVec 12)) =
      sp0 := by
  rw [signExtend12_neg32, signExtend12_pos32, BitVec.add_assoc, neg32_add_32]
  exact BitVec.add_zero sp0

/-- Body entry = base+20 (idx 5, after addi+4 sd). -/
abbrev keccakBodyEntry (base : Word) : Word := base + (20 : Word)

/-- Body exit = base+252 (idx 63, first epilogue LD). -/
abbrev keccakBodyExit (base : Word) : Word := base + (252 : Word)

private theorem add_ofNat16 (p : Word) :
    p + BitVec.ofNat 64 16 = p + (16 : Word) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rfl

/-- Prologue: ADDI sp,-32. -/
theorem keccakPrologue_alloc (cr : CodeReq) (base : Word) (sp0 : Word)
    (hmem : ∀ a i, CodeReq.singleton base (.ADDI .x2 .x2 (-32 : BitVec 12)) a = some i →
      cr a = some i) :
    cpsTripleWithin 1 base (base + 4) cr
      (.x2 ↦ᵣ sp0)
      (.x2 ↦ᵣ (sp0 + signExtend12 ((-32 : BitVec 12)))) := by
  have h := cpsTripleWithin_extend_code hmem
    (addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12) base (by decide))
  rw [show base + 4 = base + 4 from rfl] at h
  exact h

/-- Prologue stores: 4× SD. Fuel 4. -/
theorem keccakPrologue_store (newSp : Word) (vals : Reg → Word) (startAddr : Word) :
    cpsTripleWithin 4 startAddr (startAddr + (16 : Word))
      (CodeReq.ofProg startAddr (storeProg keccakFrame))
      ((.x2 ↦ᵣ newSp) ** regsAt keccakFrame vals ** frameSlotsOwn keccakFrame newSp)
      ((.x2 ↦ᵣ newSp) ** regsAt keccakFrame vals **
        frameSlotsSaved keccakFrame newSp vals) := by
  have h := storeSeq_spec keccakFrame newSp vals startAddr (by decide)
  -- exit = start + 4*4 = start+16
  have hexit : startAddr + BitVec.ofNat 64 (4 * keccakFrame.length) =
      startAddr + (16 : Word) := by
    simp only [keccakFrame_length]
    exact add_ofNat16 startAddr
  rwa [hexit] at h

/-- Full prologue fuel 5: alloc + store. -/
theorem keccakPrologue_spec (cr : CodeReq) (base : Word) (sp0 : Word)
    (vals : Reg → Word)
    (hmemA : ∀ a i, CodeReq.singleton base (.ADDI .x2 .x2 (-32 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemS : ∀ a i, CodeReq.ofProg (base + 4) (storeProg keccakFrame) a = some i →
      cr a = some i) :
    cpsTripleWithin 5 base (keccakBodyEntry base) cr
      ((.x2 ↦ᵣ sp0) ** regsAt keccakFrame vals **
        frameSlotsOwn keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))))
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-32 : BitVec 12)))) **
        regsAt keccakFrame vals **
        frameSlotsSaved keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) vals) := by
  set newSp := sp0 + signExtend12 ((-32 : BitVec 12))
  have halloc := keccakPrologue_alloc cr base sp0 hmemA
  have hallocF := cpsTripleWithin_frameR
    (regsAt keccakFrame vals ** frameSlotsOwn keccakFrame newSp)
    (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsOwn _ _)) halloc
  have c0 : cpsTripleWithin 1 base (base + 4) cr
      ((.x2 ↦ᵣ sp0) ** regsAt keccakFrame vals **
        frameSlotsOwn keccakFrame newSp)
      ((.x2 ↦ᵣ newSp) ** regsAt keccakFrame vals **
        frameSlotsOwn keccakFrame newSp) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hallocF
  have hstore0 := keccakPrologue_store newSp vals (base + 4)
  have hstore := cpsTripleWithin_extend_code hmemS hstore0
  have hpc : (base + 4 : Word) + (16 : Word) = keccakBodyEntry base := by
    simp only [keccakBodyEntry]
    rw [BitVec.add_assoc, show ((4 : Word) + 16) = (20 : Word) from by decide]
  rw [hpc] at hstore
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 hstore

/-- Epilogue loads: 4× LD. Fuel 4. Restores vals regardless of body vals'. -/
theorem keccakEpilogue_load (newSp : Word) (vals vals' : Reg → Word) (startAddr : Word) :
    cpsTripleWithin 4 startAddr (startAddr + (16 : Word))
      (CodeReq.ofProg startAddr (loadProg keccakFrame))
      ((.x2 ↦ᵣ newSp) ** regsAt keccakFrame vals' **
        frameSlotsSaved keccakFrame newSp vals)
      ((.x2 ↦ᵣ newSp) ** regsAt keccakFrame vals **
        frameSlotsSaved keccakFrame newSp vals) := by
  have h := loadSeq_spec keccakFrame newSp vals vals' startAddr
    (by decide) keccakFrame_hne
  have hexit : startAddr + BitVec.ofNat 64 (4 * keccakFrame.length) =
      startAddr + (16 : Word) := by
    simp only [keccakFrame_length]
    exact add_ofNat16 startAddr
  rwa [hexit] at h

/-- Epilogue dealloc ADDI sp,+32. -/
theorem keccakEpilogue_dealloc (cr : CodeReq) (entry : Word) (newSp sp0 : Word)
    (hrest : newSp + signExtend12 ((32 : BitVec 12)) = sp0)
    (hmem : ∀ a i, CodeReq.singleton entry (.ADDI .x2 .x2 (32 : BitVec 12)) a = some i →
      cr a = some i) :
    cpsTripleWithin 1 entry (entry + 4) cr
      (.x2 ↦ᵣ newSp)
      (.x2 ↦ᵣ sp0) := by
  have h := cpsTripleWithin_extend_code hmem
    (addi_spec_gen_same_within .x2 newSp (32 : BitVec 12) entry (by decide))
  rw [show entry + 4 = entry + 4 from rfl] at h
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => ?_) h
  -- hq : (.x2 ↦ newSp + sext32) s; need (.x2 ↦ sp0) s
  rw [hrest] at hq
  exact hq

/-- JALR x0,x1 → ret (ra even). -/
theorem keccakRet_spec (cr : CodeReq) (entry ret : Word)
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
    Entry = bodyExit = base+252. Exit = ret. -/
theorem keccakEpilogue_spec (cr : CodeReq) (base sp0 ret : Word)
    (vals vals' : Reg → Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hmemL : ∀ a i, CodeReq.ofProg (keccakBodyExit base) (loadProg keccakFrame) a = some i →
      cr a = some i)
    (hmemD : ∀ a i, CodeReq.singleton (keccakBodyExit base + (16 : Word))
        (.ADDI .x2 .x2 (32 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemR : ∀ a i, CodeReq.singleton (keccakBodyExit base + (20 : Word))
        (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
      cr a = some i) :
    cpsTripleWithin 6 (keccakBodyExit base) ret cr
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-32 : BitVec 12)))) **
        (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals' **
        frameSlotsSaved keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) vals)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsSaved keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) vals) := by
  set newSp := sp0 + signExtend12 ((-32 : BitVec 12))
  have hrest := frame_restore sp0
  -- load
  have hload0 := keccakEpilogue_load newSp vals vals' (keccakBodyExit base)
  have hload := cpsTripleWithin_extend_code hmemL hload0
  have hloadF := cpsTripleWithin_frameR (.x1 ↦ᵣ ret) (by pcf) hload
  have c0 : cpsTripleWithin 4 (keccakBodyExit base)
      (keccakBodyExit base + (16 : Word)) cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals' ** frameSlotsSaved keccakFrame newSp vals)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hloadF
  -- dealloc
  have hde := keccakEpilogue_dealloc cr (keccakBodyExit base + (16 : Word)) newSp sp0
    hrest hmemD
  have hdeF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsSaved _ _ _)))
    hde
  have c1 : cpsTripleWithin 1 (keccakBodyExit base + (16 : Word))
      (keccakBodyExit base + (20 : Word)) cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals) := by
    have hpc : (keccakBodyExit base + (16 : Word)) + 4 =
        keccakBodyExit base + (20 : Word) := by
      rw [BitVec.add_assoc, show ((16 : Word) + 4) = (20 : Word) from by decide]
    rw [← hpc]
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hdeF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  -- ret
  have hret := keccakRet_spec cr (keccakBodyExit base + (20 : Word)) ret halign hmemR
  have hretF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) ** regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsSaved _ _ _)))
    hret
  have c2 : cpsTripleWithin 1 (keccakBodyExit base + (20 : Word)) ret cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hretF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2

/-- No-ra frame wrap: prologue + body + epilogue.
    Body hyp must preserve x1=ret and frame slots; may clobber saved regs (restored). -/
theorem keccakFrame_spec (cr : CodeReq) (base sp0 ret : Word)
    (vals vals' : Reg → Word) (bodySteps : Nat)
    (callerPre callerPost : Assertion)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hcpF : callerPre.pcFree) (hcpF' : callerPost.pcFree)
    (hmemA : ∀ a i, CodeReq.singleton base (.ADDI .x2 .x2 (-32 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemS : ∀ a i, CodeReq.ofProg (base + 4) (storeProg keccakFrame) a = some i →
      cr a = some i)
    (hmemL : ∀ a i, CodeReq.ofProg (keccakBodyExit base) (loadProg keccakFrame) a = some i →
      cr a = some i)
    (hmemD : ∀ a i, CodeReq.singleton (keccakBodyExit base + (16 : Word))
        (.ADDI .x2 .x2 (32 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemR : ∀ a i, CodeReq.singleton (keccakBodyExit base + (20 : Word))
        (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
      cr a = some i)
    (hbody : cpsTripleWithin bodySteps (keccakBodyEntry base) (keccakBodyExit base) cr
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-32 : BitVec 12)))) **
        (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsSaved keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) vals **
        callerPre)
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-32 : BitVec 12)))) **
        (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals' **
        frameSlotsSaved keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) vals **
        callerPost)) :
    cpsTripleWithin (5 + bodySteps + 6) base ret cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsOwn keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) **
        callerPre)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsSaved keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) vals **
        callerPost) := by
  set newSp := sp0 + signExtend12 ((-32 : BitVec 12))
  -- prologue
  have hpro0 := keccakPrologue_spec cr base sp0 vals hmemA hmemS
  have hproF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** callerPre)
    (pcFree_sepConj (by pcf) hcpF) hpro0
  have cPro : cpsTripleWithin 5 base (keccakBodyEntry base) cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsOwn keccakFrame newSp ** callerPre)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals **
        callerPre) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hproF
  -- body
  have cBody : cpsTripleWithin bodySteps (keccakBodyEntry base) (keccakBodyExit base) cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals **
        callerPre)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals' ** frameSlotsSaved keccakFrame newSp vals **
        callerPost) := hbody
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) cPro cBody
  -- epilogue
  have hepi0 := keccakEpilogue_spec cr base sp0 ret vals vals' halign hmemL hmemD hmemR
  have hepiF := cpsTripleWithin_frameR callerPost hcpF' hepi0
  have cEpi : cpsTripleWithin 6 (keccakBodyExit base) ret cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals' ** frameSlotsSaved keccakFrame newSp vals **
        callerPost)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals **
        callerPost) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hepiF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 cEpi

/-- Epilogue with OWNED saved regs at body exit (values dead; loads restore). -/
theorem keccakEpilogue_spec_own (cr : CodeReq) (base sp0 ret : Word)
    (vals : Reg → Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hmemL : ∀ a i, CodeReq.ofProg (keccakBodyExit base) (loadProg keccakFrame) a = some i →
      cr a = some i)
    (hmemD : ∀ a i, CodeReq.singleton (keccakBodyExit base + (16 : Word))
        (.ADDI .x2 .x2 (32 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemR : ∀ a i, CodeReq.singleton (keccakBodyExit base + (20 : Word))
        (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
      cr a = some i) :
    cpsTripleWithin 6 (keccakBodyExit base) ret cr
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-32 : BitVec 12)))) **
        (.x1 ↦ᵣ ret) **
        regsOwnAt keccakFrame **
        frameSlotsSaved keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) vals)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsSaved keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) vals) := by
  set newSp := sp0 + signExtend12 ((-32 : BitVec 12))
  have hrest := frame_restore sp0
  have hload0 := loadSeq_spec_own keccakFrame newSp vals (keccakBodyExit base)
    (by decide) keccakFrame_hne
  have hload := cpsTripleWithin_extend_code hmemL hload0
  have hexit : keccakBodyExit base + BitVec.ofNat 64 (4 * keccakFrame.length) =
      keccakBodyExit base + (16 : Word) := by
    simp only [keccakFrame_length]
    exact add_ofNat16 (keccakBodyExit base)
  rw [hexit] at hload
  have hloadF := cpsTripleWithin_frameR (.x1 ↦ᵣ ret) (by pcf) hload
  have c0 : cpsTripleWithin 4 (keccakBodyExit base)
      (keccakBodyExit base + (16 : Word)) cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsOwnAt keccakFrame ** frameSlotsSaved keccakFrame newSp vals)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hloadF
  have hde := keccakEpilogue_dealloc cr (keccakBodyExit base + (16 : Word)) newSp sp0
    hrest hmemD
  have hdeF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsSaved _ _ _)))
    hde
  have c1 : cpsTripleWithin 1 (keccakBodyExit base + (16 : Word))
      (keccakBodyExit base + (20 : Word)) cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals) := by
    have hpc : (keccakBodyExit base + (16 : Word)) + 4 =
        keccakBodyExit base + (20 : Word) := by
      rw [BitVec.add_assoc, show ((16 : Word) + 4) = (20 : Word) from by decide]
    rw [← hpc]
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hdeF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  have hret := keccakRet_spec cr (keccakBodyExit base + (20 : Word)) ret halign hmemR
  have hretF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) ** regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsSaved _ _ _)))
    hret
  have c2 : cpsTripleWithin 1 (keccakBodyExit base + (20 : Word)) ret cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hretF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2

/-- No-ra frame wrap with body ending in `regsOwnAt` (dead exit values). -/
theorem keccakFrame_spec_own (cr : CodeReq) (base sp0 ret : Word)
    (vals : Reg → Word) (bodySteps : Nat)
    (callerPre callerPost : Assertion)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hcpF : callerPre.pcFree) (hcpF' : callerPost.pcFree)
    (hmemA : ∀ a i, CodeReq.singleton base (.ADDI .x2 .x2 (-32 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemS : ∀ a i, CodeReq.ofProg (base + 4) (storeProg keccakFrame) a = some i →
      cr a = some i)
    (hmemL : ∀ a i, CodeReq.ofProg (keccakBodyExit base) (loadProg keccakFrame) a = some i →
      cr a = some i)
    (hmemD : ∀ a i, CodeReq.singleton (keccakBodyExit base + (16 : Word))
        (.ADDI .x2 .x2 (32 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemR : ∀ a i, CodeReq.singleton (keccakBodyExit base + (20 : Word))
        (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
      cr a = some i)
    (hbody : cpsTripleWithin bodySteps (keccakBodyEntry base) (keccakBodyExit base) cr
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-32 : BitVec 12)))) **
        (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsSaved keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) vals **
        callerPre)
      ((.x2 ↦ᵣ (sp0 + signExtend12 ((-32 : BitVec 12)))) **
        (.x1 ↦ᵣ ret) **
        regsOwnAt keccakFrame **
        frameSlotsSaved keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) vals **
        callerPost)) :
    cpsTripleWithin (5 + bodySteps + 6) base ret cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsOwn keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) **
        callerPre)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsSaved keccakFrame (sp0 + signExtend12 ((-32 : BitVec 12))) vals **
        callerPost) := by
  set newSp := sp0 + signExtend12 ((-32 : BitVec 12))
  have hpro0 := keccakPrologue_spec cr base sp0 vals hmemA hmemS
  have hproF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** callerPre)
    (pcFree_sepConj (by pcf) hcpF) hpro0
  have cPro : cpsTripleWithin 5 base (keccakBodyEntry base) cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsOwn keccakFrame newSp ** callerPre)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals **
        callerPre) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hproF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) cPro hbody
  have hepi0 := keccakEpilogue_spec_own cr base sp0 ret vals halign hmemL hmemD hmemR
  have hepiF := cpsTripleWithin_frameR callerPost hcpF' hepi0
  have cEpi : cpsTripleWithin 6 (keccakBodyExit base) ret cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsOwnAt keccakFrame ** frameSlotsSaved keccakFrame newSp vals **
        callerPost)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals ** frameSlotsSaved keccakFrame newSp vals **
        callerPost) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hepiF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 cEpi

end EvmAsm.Codegen.Proofs
