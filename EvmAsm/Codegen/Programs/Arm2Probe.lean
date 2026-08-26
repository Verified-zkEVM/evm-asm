import EvmAsm.Codegen.Programs.ValidateHeaderGasCorrespondence
import EvmAsm.Rv64.SAsm.FramePort

namespace EvmAsm.Codegen.ValidateHeaderGasCorrespondence

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics

def arm2Body : Program :=
  headerValidateExcessBlobGas_prog.drop 8 |>.take 57

def arm2Cr : CodeReq := CodeReq.ofProg (ExcessK + 32) arm2Body

def arm2CallerPre : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
  (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
  regOwns [.x5, .x6, .x28, .x29, .x30, .x31] **
  (.x0 ↦ᵣ (0 : Word))

def arm2Vals : Reg → Word := fun r => if r = .x1 then ExcessRet else 0

def arm2CallerPost : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)) **
  regOwns [.x6, .x28, .x29, .x30, .x31] **
  (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
  (.x0 ↦ᵣ (0 : Word))

def arm2AfterPrefixFrame (spC spSlot slotVal : Word) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) ** (.x8 ↦ᵣ (0 : Word)) **
  (.x9 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) **
  (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ (0 : Word)) ** (spSlot ↦ₘ slotVal) **
  (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
  (.x13 ↦ᵣ (0 : Word)) ** regOwns [.x6, .x28, .x29, .x30, .x31] **
  (.x0 ↦ᵣ (0 : Word))

def arm2Branch1Frame (spC spSlot slotVal : Word) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) ** (.x8 ↦ᵣ (0 : Word)) **
  (.x9 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
  (spSlot ↦ₘ slotVal) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
  (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
  regOwns [.x5, .x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word))

def arm2Branch2Frame (spC spSlot slotVal : Word) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) ** (.x8 ↦ᵣ (0 : Word)) **
  (.x9 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) **
  (.x21 ↦ᵣ (0 : Word)) ** (spSlot ↦ₘ slotVal) ** (.x10 ↦ᵣ (0 : Word)) **
  (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
  regOwns [.x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word))

def arm2AfterBranch2Frame (spC spSlot slotVal : Word) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) ** (.x8 ↦ᵣ (0 : Word)) **
  (.x9 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) **
  (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)) **
  (spSlot ↦ₘ slotVal) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
  (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
  regOwns [.x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word))

def arm2BneFrame (spC spSlot slotVal : Word) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) ** (.x9 ↦ᵣ (0 : Word)) **
  (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) ** (.x20 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)) **
  (spSlot ↦ₘ slotVal) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
  (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
  regOwns [.x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word))

def arm2Li10Frame (spC spSlot slotVal : Word) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) ** (.x8 ↦ᵣ (0 : Word)) **
  (.x9 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) **
  (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)) **
  (spSlot ↦ₘ slotVal) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
  (.x13 ↦ᵣ (0 : Word)) ** regOwns [.x6, .x28, .x29, .x30, .x31] **
  (.x0 ↦ᵣ (0 : Word))

#guard arm2Body.length = 57

example :
    abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) excessFrame arm2Body =
      headerValidateExcessBlobGas_prog := by
  decide

example :
    excessFrame = (.x1, (0 : BitVec 12)) :: excessSavedFrame := by
  rfl

example (sp0 : Word) :
    sp0 + signExtend12 (-64 : BitVec 12) + signExtend12 (0 : BitVec 12) =
      sp0 + signExtend12 (-64 : BitVec 12) := by
  rw [signExtend12_0, addr_add_zero_bv]

set_option maxRecDepth 8000 in
theorem arm2_prefix_spec (spC spSlot slotVal : Word) :
    cpsTripleWithin 5 (ExcessK + 32) (ExcessK + 52) arm2Cr
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) **
       (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) **
       (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
       (spSlot ↦ₘ slotVal) ** arm2CallerPre)
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) **
       (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) **
       (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
       (spSlot ↦ₘ slotVal) ** arm2CallerPre) := by
  unfold arm2CallerPre
  have h8 := mv_spec_gen_within .x8 .x10 (0 : Word) (0 : Word)
    (ExcessK + 32) (by decide)
  have h9 := mv_spec_gen_within .x9 .x11 (0 : Word) (0 : Word)
    (ExcessK + 36) (by decide)
  have h18 := mv_spec_gen_within .x18 .x12 (0 : Word) (0 : Word)
    (ExcessK + 40) (by decide)
  have h19 := mv_spec_gen_within .x19 .x13 (0 : Word) (0 : Word)
    (ExcessK + 44) (by decide)
  have h20 := add_spec_gen_within .x20 .x18 .x9
    (0 : Word) (0 : Word) (0 : Word) (ExcessK + 48) (by decide)
  have h20zero : (0 : Word) + (0 : Word) = 0 := by decide
  rw [h20zero] at h20
  have h8' := cpsTripleWithin_extend_code (cr' := arm2Cr) (by code_mem) h8
  have h9' := cpsTripleWithin_extend_code (cr' := arm2Cr) (by code_mem) h9
  have h18' := cpsTripleWithin_extend_code (cr' := arm2Cr) (by code_mem) h18
  have h19' := cpsTripleWithin_extend_code (cr' := arm2Cr) (by code_mem) h19
  have h20' := cpsTripleWithin_extend_code (cr' := arm2Cr) (by code_mem) h20
  have h8F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) ** (.x9 ↦ᵣ (0 : Word)) **
      (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) ** (.x20 ↦ᵣ (0 : Word)) **
      (.x21 ↦ᵣ (0 : Word)) ** (spSlot ↦ₘ slotVal) **
      (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
      regOwns [.x5, .x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) h8'
  have h9F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) ** (.x8 ↦ᵣ (0 : Word)) **
      (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) ** (.x20 ↦ᵣ (0 : Word)) **
      (.x21 ↦ᵣ (0 : Word)) ** (spSlot ↦ₘ slotVal) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
      regOwns [.x5, .x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) h9'
  have h18F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) ** (.x8 ↦ᵣ (0 : Word)) **
      (.x9 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) ** (.x20 ↦ᵣ (0 : Word)) **
      (.x21 ↦ᵣ (0 : Word)) ** (spSlot ↦ₘ slotVal) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
      regOwns [.x5, .x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) h18'
  have h19F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) ** (.x8 ↦ᵣ (0 : Word)) **
      (.x9 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (0 : Word)) ** (.x20 ↦ᵣ (0 : Word)) **
      (.x21 ↦ᵣ (0 : Word)) ** (spSlot ↦ₘ slotVal) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      regOwns [.x5, .x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) h19'
  have h20F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) ** (.x8 ↦ᵣ (0 : Word)) **
      (.x19 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ (0 : Word)) ** (spSlot ↦ₘ slotVal) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x13 ↦ᵣ (0 : Word)) ** regOwns [.x5, .x6, .x28, .x29, .x30, .x31] **
      (.x0 ↦ᵣ (0 : Word)))
    (by pcf) h20'
  have h12 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h8F h9F
  have h123 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h12 h18F
  have h1234 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h123 h19F
  have h12345 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h1234 h20F
  apply cpsTripleWithin_weaken (by xsimp) ?_ h12345
  intro h hq
  exact by xperm_hyp hq

set_option maxRecDepth 8000 in
theorem arm2_branch1_spec :
    cpsTripleWithin 1 (ExcessK + 52) (ExcessK + 56) arm2Cr
      ((.x20 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (0 : Word))) := by
  have hbr := bltu_spec_gen_within .x20 .x18 (196 : BitVec 13)
    (0 : Word) (0 : Word) (ExcessK + 52)
  rw [show (ExcessK + 52) + signExtend13 (196 : BitVec 13) = ExcessK + 248 from by decide,
    show (ExcessK + 52 : Word) + 4 = ExcessK + 56 from by decide] at hbr
  have hbr' := cpsBranchWithin_extend_code (cr' := arm2Cr) (by code_mem) hbr
  exact cpsBranchWithin_ntakenStripPure2 hbr' (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hInner⟩ := hQt
    have hPure := ((sepConj_pure_right _).1 hInner).2
    exact (by decide : ¬ (BitVec.ult (0 : Word) (0 : Word) = true)) hPure)

set_option maxRecDepth 8000 in
theorem arm2_lui_spec :
    cpsTripleWithin 1 (ExcessK + 56) (ExcessK + 60) arm2Cr
      (regOwn .x5)
      (.x5 ↦ᵣ (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn_single
  intro vOld
  exact cpsTripleWithin_extend_code (cr' := arm2Cr) (by code_mem)
    (lui_spec_gen_within .x5 vOld (448 : BitVec 20) (ExcessK + 56) (by decide))

set_option maxRecDepth 8000 in
theorem arm2_branch2_spec :
    cpsTripleWithin 1 (ExcessK + 60) (ExcessK + 232) arm2Cr
      ((.x20 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)))
      ((.x20 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64))) := by
  have hbr := bltu_spec_gen_within .x20 .x5 (172 : BitVec 13)
    (0 : Word) (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)
    (ExcessK + 60)
  rw [show (ExcessK + 60) + signExtend13 (172 : BitVec 13) = ExcessK + 232 from by decide,
    show (ExcessK + 60 : Word) + 4 = ExcessK + 64 from by decide] at hbr
  have hbr' := cpsBranchWithin_extend_code (cr' := arm2Cr) (by code_mem) hbr
  exact cpsBranchWithin_takenStripPure2 hbr' (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hInner⟩ := hQf
    have hPure := ((sepConj_pure_right _).1 hInner).2
    exact hPure (by decide))

set_option maxRecDepth 8000 in
theorem arm2_mid_spec (spC spSlot slotVal : Word) :
    cpsTripleWithin 12 (ExcessK + 32) (ExcessK + 260) arm2Cr
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ExcessRet) **
       (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) **
       (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
       (spSlot ↦ₘ slotVal) ** arm2CallerPre)
      ((.x5 ↦ᵣ (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)) **
       arm2AfterPrefixFrame spC spSlot slotVal) := by
  have hprefix := arm2_prefix_spec spC spSlot slotVal
  unfold arm2CallerPre at hprefix
  simp only [regOwns_cons, regOwns_nil] at hprefix
  have hbr1 := cpsTripleWithin_frameR (arm2Branch1Frame spC spSlot slotVal)
    (by pcf) arm2_branch1_spec
  unfold arm2Branch1Frame at hbr1
  simp only [regOwns_cons, regOwns_nil] at hbr1
  have h1 := cpsTripleWithin_seq_perm_same_cr (by xsimp) hprefix hbr1
  have hlui := cpsTripleWithin_frameR (arm2AfterPrefixFrame spC spSlot slotVal)
    (by pcf) arm2_lui_spec
  unfold arm2AfterPrefixFrame at hlui
  simp only [regOwns_cons, regOwns_nil] at hlui
  have h2 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h1 hlui
  have hbr2 := cpsTripleWithin_frameR (arm2Branch2Frame spC spSlot slotVal)
    (by pcf) arm2_branch2_spec
  unfold arm2Branch2Frame at hbr2
  simp only [regOwns_cons, regOwns_nil] at hbr2
  have h3 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h2 hbr2
  have hli21 := li_spec_gen_within .x21 (0 : Word) (0 : Word)
    (ExcessK + 232) (by decide)
  have hli21' := cpsTripleWithin_extend_code (cr' := arm2Cr) (by code_mem) hli21
  have hli21f := cpsTripleWithin_frameR (arm2AfterBranch2Frame spC spSlot slotVal)
    (by pcf) hli21'
  unfold arm2AfterBranch2Frame at hli21f
  simp only [regOwns_cons, regOwns_nil] at hli21f
  have h4 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h3 hli21f
  have hbne := bne_spec_gen_within .x8 .x21 (20 : BitVec 13)
    (0 : Word) (0 : Word) (ExcessK + 236)
  rw [show (ExcessK + 236) + signExtend13 (20 : BitVec 13) = ExcessK + 256 from by decide,
    show (ExcessK + 236 : Word) + 4 = ExcessK + 240 from by decide] at hbne
  have hbne' := cpsBranchWithin_extend_code (cr' := arm2Cr) (by code_mem) hbne
  have hbne'' := cpsBranchWithin_ntakenStripPure2 hbne' (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hInner⟩ := hQt
    have hPure := ((sepConj_pure_right _).1 hInner).2
    exact (by decide : ¬ ((0 : Word) ≠ (0 : Word))) hPure)
  have hbnef := cpsTripleWithin_frameR (arm2BneFrame spC spSlot slotVal)
    (by pcf) hbne''
  unfold arm2BneFrame at hbnef
  simp only [regOwns_cons, regOwns_nil] at hbnef
  have h5 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h4 hbnef
  have hli10 := li_spec_gen_within .x10 (0 : Word) (0 : Word)
    (ExcessK + 240) (by decide)
  have hli10' := cpsTripleWithin_extend_code (cr' := arm2Cr) (by code_mem) hli10
  have hli10f := cpsTripleWithin_frameR (arm2Li10Frame spC spSlot slotVal)
    (by pcf) hli10'
  unfold arm2Li10Frame at hli10f
  simp only [regOwns_cons, regOwns_nil] at hli10f
  have h6 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h5 hli10f
  have hjal := jal_x0_spec_gen_within (16 : BitVec 21) (ExcessK + 244)
  have hjal' := cpsTripleWithin_extend_code (cr' := arm2Cr) (by code_mem) hjal
  have hjalf := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)) **
      arm2AfterPrefixFrame spC spSlot slotVal) (by pcf) hjal'
  unfold arm2AfterPrefixFrame at hjalf
  simp only [regOwns_cons, regOwns_nil] at hjalf
  simp only [sepConj_emp_left'] at hjalf
  have h7 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h6 hjalf
  rw [show (ExcessK + 244) + signExtend21 (16 : BitVec 21) = ExcessK + 260 from by decide] at h7
  exact h7

set_option maxRecDepth 8000 in
theorem arm2_body_spec (sp0 : Word) :
    cpsTripleWithin 12 (ExcessK + 32) (ExcessK + 260)
      (CodeReq.ofProg ExcessK headerValidateExcessBlobGas_prog)
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-64 : BitVec 12))) **
       regsAt excessFrame arm2Vals **
       frameSlotsSaved excessFrame (sp0 + signExtend12 (-64 : BitVec 12)) arm2Vals **
       arm2CallerPre)
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-64 : BitVec 12))) **
       regsAt excessFrame arm2Vals **
       frameSlotsSaved excessFrame (sp0 + signExtend12 (-64 : BitVec 12)) arm2Vals **
       arm2CallerPost) := by
  let newSp := sp0 + signExtend12 (-64 : BitVec 12)
  let extra : Assertion :=
    ((newSp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
    ((newSp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
    ((newSp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
    ((newSp + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
    ((newSp + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
    ((newSp + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word))
  have hslots : frameSlotsSaved excessFrame newSp arm2Vals =
      ((newSp ↦ₘ ExcessRet) ** extra) := by
    have haddr : newSp + signExtend12 (0 : BitVec 12) = newSp := by
      rw [signExtend12_0, addr_add_zero_bv]
    have hmem : (newSp + signExtend12 (0 : BitVec 12) ↦ₘ ExcessRet) =
        (newSp ↦ₘ ExcessRet) := congrArg (fun p : Word => p ↦ₘ ExcessRet) haddr
    calc
      frameSlotsSaved excessFrame newSp arm2Vals =
          ((newSp + signExtend12 (0 : BitVec 12) ↦ₘ ExcessRet) ** extra) := by
        simp [frameSlotsSaved_cons, frameSlotsSaved_nil, excessFrame, arm2Vals,
          extra, sepConj_emp_right']
      _ = ((newSp ↦ₘ ExcessRet) ** extra) := by
        exact congrArg (fun a : Assertion => a ** extra) hmem
  have hmid := arm2_mid_spec newSp newSp ExcessRet
  have hmidExtra := cpsTripleWithin_frameR extra (by pcf) hmid
  let pre : Program := [.ADDI .x2 .x2 (-64 : BitVec 12)] ++ storeProg excessFrame
  let suf : Program := frameEpilogue (64 : BitVec 12) excessFrame ++
    [.JALR .x0 .x1 (0 : BitVec 12)]
  have hfull : headerValidateExcessBlobGas_prog = pre ++ arm2Body ++ suf := by
    rfl
  have hslice : ∀ a i, arm2Cr a = some i →
      (CodeReq.ofProg ExcessK headerValidateExcessBlobGas_prog) a = some i := by
    intro a i hi
    have hi' : CodeReq.ofProg
        (ExcessK + BitVec.ofNat 64 (4 * pre.length)) arm2Body a = some i := by
      exact hi
    have hm := CodeReq.ofProg_mono_subrange ExcessK pre arm2Body suf (by decide) a i hi'
    simpa [hfull] using hm
  have hmidFull := cpsTripleWithin_extend_code (cr' :=
    CodeReq.ofProg ExcessK headerValidateExcessBlobGas_prog) hslice hmidExtra
  apply cpsTripleWithin_weaken (P :=
    (((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ExcessRet) ** (.x8 ↦ᵣ (0 : Word)) **
      (.x9 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) **
      (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ (0 : Word)) ** (newSp ↦ₘ ExcessRet) **
      arm2CallerPre) ** extra))
    (Q := (((.x5 ↦ᵣ (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)) **
      arm2AfterPrefixFrame newSp newSp ExcessRet) ** extra)) ?_ ?_ hmidFull
  · intro h hp
    rw [hslots] at hp
    simp [newSp, extra, excessFrame, regsAt, arm2Vals, arm2CallerPre] at hp ⊢
    simp only [sepConj_emp_right'] at hp ⊢
    xperm_hyp hp
  · intro h hq
    rw [hslots]
    simp [newSp, extra, excessFrame, regsAt, arm2Vals,
      arm2CallerPost, arm2AfterPrefixFrame] at hq ⊢
    simp only [sepConj_emp_right'] at hq ⊢
    xperm_hyp hq

set_option maxRecDepth 8000 in
theorem arm2_hcallee :
    cpsTripleWithin 29 ExcessK ExcessRet
      (CodeReq.ofProg ExcessK headerValidateExcessBlobGas_prog)
      ((.x1 ↦ᵣ ExcessRet) **
        excessEntryRest (0x40010000 : Word) arm2Vals
          (0 : Word) (0 : Word) (0 : Word) (0 : Word) empAssertion)
      (excessCalleePost (0x40010000 : Word) arm2Vals
        (0 : Word) ExcessRet empAssertion) := by
  let sp0 : Word := 0x40010000
  have hbody := arm2_body_spec sp0
  have habi := abiFrame_spec
    (base := ExcessK) (sp0 := sp0) (ret := ExcessRet)
    (negImm := (-64 : BitVec 12)) (posImm := (64 : BitVec 12))
    (frame := excessFrame) (raOfs := (0 : BitVec 12))
    (sregs := excessSavedFrame)
    (vals := arm2Vals) (vals' := arm2Vals)
    (body := arm2Body) (bodySteps := 12)
    (callerPre := arm2CallerPre) (callerPost := arm2CallerPost)
    (cr := CodeReq.ofProg ExcessK headerValidateExcessBlobGas_prog)
    (by rfl)
    (by decide)
    (by decide)
    (by decide)
    (by simp [arm2Vals])
    (by decide)
    (by decide)
    (by pcf)
    (by pcf)
    (by intro a i h; exact h)
    hbody
  refine cpsTripleWithin_weaken (P := _) (Q := _) ?_ ?_ habi
  · intro h hp
    simp [sp0, excessEntryRest, excessFrame, excessSavedFrame, regsAt,
      frameSlotsOwn, arm2Vals, arm2CallerPre] at hp ⊢
    simp only [sepConj_emp_right'] at hp ⊢
    xperm_hyp hp
  · intro h hq
    simp [sp0, excessCalleePost, excessFrame, excessSavedFrame,
      excessFrameVals, regsAt, frameSlotsSaved, arm2Vals, arm2CallerPost,
      sepConj_emp_right'] at hq ⊢
    let rest : Assertion :=
      (.x1 ↦ᵣ ExcessRet) ** (.x2 ↦ᵣ sp0) **
      frameSlotsSaved excessFrame (sp0 + signExtend12 (-64 : BitVec 12)) arm2Vals **
      regsAt excessSavedFrame arm2Vals ** (.x10 ↦ᵣ (0 : Word)) **
      regOwn .x6 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))
    let qConcrete : Assertion :=
      (.x5 ↦ᵣ (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)) **
      (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x13 ↦ᵣ (0 : Word)) ** rest
    let qOwn : Assertion :=
      regOwn .x5 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** rest
    have hqConcrete : qConcrete h := by
      simp [qConcrete, rest, excessFrame, excessSavedFrame, regsAt,
        frameSlotsSaved, arm2Vals, sp0, sepConj_emp_right']
      xperm_hyp hq
    have hqOwn : qOwn h := by
      dsimp [qOwn, qConcrete]
      have hqConcrete' :
          ((.x5 ↦ᵣ (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)) **
            (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
            (.x13 ↦ᵣ (0 : Word)) ** rest) h := by
        simpa only [qConcrete] using hqConcrete
      exact sepConj_mono (regIs_implies_regOwn (r := .x5))
        (sepConj_mono (regIs_implies_regOwn (r := .x11))
            (sepConj_mono (regIs_implies_regOwn (r := .x12))
            (sepConj_mono (regIs_implies_regOwn (r := .x13))
              (fun _ hrest => hrest)))) h hqConcrete'
    dsimp [qOwn, rest, sp0] at hqOwn
    simp [frameSlotsSaved, excessFrame, arm2Vals, regsAt, excessSavedFrame,
      sepConj_emp_right'] at hqOwn
    xperm_hyp hqOwn

end EvmAsm.Codegen.ValidateHeaderGasCorrespondence
