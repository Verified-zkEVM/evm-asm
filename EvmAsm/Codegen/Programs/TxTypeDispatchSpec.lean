/-
  Fn.Spec for `tx_type_dispatch` (45-instr leaf, no frame) — a4gbr.2 residual.

  Success arms write type/inner_offset and return a0=0:
    legacy (first ≥ 0xc0) → type=0, inner=0
    type 1..4             → type=N,  inner=1
  Fail arms (empty / unknown prefix) return a0=1.

  No frame, no callees. LBU needs 8-aligned `txBase` (bytesRegion_lbu_within).
  classical-3 only; no native_decide / sorry.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxTypeDispatchSpec

open EvmAsm.Rv64
open EvmAsm.Codegen

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact bytesRegion_pcFree _ _
      | exact pcFree_emp
      | exact pcFree_pure)

abbrev D : Word := BitVec.ofNat 64 GuestAddrs.tx_type_dispatch
abbrev typeProg : Program := txTypeDispatch_prog
abbrev typeCode : CodeReq := CodeReq.ofProg D typeProg

theorem type_length : typeProg.length = 45 := by decide

private theorem se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

private theorem type_bound : 4 * typeProg.length < 2 ^ 64 := by
  simp only [type_length]; decide

abbrev FailLi : Word := D + 164

private theorem FailLi_eq : FailLi = D + BitVec.ofNat 64 (4 * 41) := by
  simp only [FailLi, D, GuestAddrs.tx_type_dispatch]; decide

private theorem D168 : D + 168 = D + BitVec.ofNat 64 (4 * 42) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D172 : D + 172 = D + BitVec.ofNat 64 (4 * 43) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D176 : D + 176 = D + BitVec.ofNat 64 (4 * 44) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

/-- Pure: first byte is a success-path typed-tx prefix. -/
def isValidTypeByte (b : BitVec 8) : Prop :=
  b.toNat ≥ 0xc0 ∨ b.toNat = 1 ∨ b.toNat = 2 ∨ b.toNat = 3 ∨ b.toNat = 4

set_option maxRecDepth 8000 in
/-- Fail tail at FailLi (instr 41–44): SD type0, SD inner0, LI a0=1, JALR. -/
theorem typeFailRet_spec
    (raIn txBase typePtr innerPtr oldT oldI a0v a1v v5 v6 : Word)
    (txBytes : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn) :
    cpsTripleWithin 4 FailLi raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (0 : Word)) ** (innerPtr ↦ₘ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word))) := by
  -- [41] SD x12, x0, 0  (rs1=x12 addr, rs2=x0 data)
  have h0 := sd_spec_gen_within .x12 .x0 typePtr (0 : Word) oldT
    (0 : BitVec 12) FailLi
  rw [show typePtr + signExtend12 (0 : BitVec 12) = typePtr from by
    rw [se12_zero]; exact BitVec.add_zero typePtr] at h0
  have h0e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D FailLi typeProg 41
      (.SD .x12 .x0 (0 : BitVec 12))
      FailLi_eq (by rw [type_length]; decide) rfl type_bound) h0
  have h0pc : FailLi + 4 = D + 168 := by
    simp only [FailLi, D, GuestAddrs.tx_type_dispatch]; decide
  rw [h0pc] at h0e
  have h0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x13 ↦ᵣ innerPtr) ** bytesRegion txBase txBytes **
        (innerPtr ↦ₘ oldI) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      (by pcf) h0e
  -- post h0F: x12 ** x0 ** typePtr↦0 ** frame
  -- [42] SD x13, x0, 0
  have h1 := sd_spec_gen_within .x13 .x0 innerPtr (0 : Word) oldI
    (0 : BitVec 12) (D + 168)
  rw [show innerPtr + signExtend12 (0 : BitVec 12) = innerPtr from by
    rw [se12_zero]; exact BitVec.add_zero innerPtr] at h1
  have h1e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 168) typeProg 42
      (.SD .x13 .x0 (0 : BitVec 12))
      D168 (by rw [type_length]; decide) rfl type_bound) h1
  have h1pc : (D + 168) + 4 = D + 172 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h1pc] at h1e
  have h1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** bytesRegion txBase txBytes **
        (typePtr ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      (by pcf) h1e
  -- [43] LI x10, 1
  have h2 := li_spec_gen_within .x10 a0v (1 : Word) (D + 172) (by decide)
  have h2e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 172) typeProg 43
      (.LI .x10 (1 : Word))
      D172 (by rw [type_length]; decide) rfl type_bound) h2
  have h2pc : (D + 172) + 4 = D + 176 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h2pc] at h2e
  have h2F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (0 : Word)) ** (innerPtr ↦ₘ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h2e
  -- [44] JALR
  have hexit : ((raIn + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = raIn := by
    have hz : raIn + signExtend12 (0 : BitVec 12) = raIn := by
      rw [se12_zero]; exact BitVec.add_zero raIn
    rw [hz, hret]
  have h3 : cpsTripleWithin 1 (D + 176) raIn typeCode
      (.x1 ↦ᵣ raIn) (.x1 ↦ᵣ raIn) := by
    have hj := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) (D + 176)
    rw [hexit] at hj
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 176) typeProg 44
        (.JALR .x0 .x1 (0 : BitVec 12))
        D176 (by rw [type_length]; decide) rfl type_bound) hj
  have h3F :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (0 : Word)) ** (innerPtr ↦ₘ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h3
  -- Reshape h0F post → h1F pre (xperm)
  have c01 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      -- h0F post: (x12 ** x0 ** type↦0) ** frame0
      -- h1F pre:  (x13 ** x0 ** inner↦oldI) ** frame1
      xperm_hyp hp) h0F h1F
  have c02 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h2F
  have c03 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 h3F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) c03

set_option maxRecDepth 8000 in
/-- Empty input: BEQ a1=0 taken → FailLi → a0=1 (5 steps). -/
theorem txTypeDispatch_empty_fail_spec_within
    (raIn txBase typePtr innerPtr oldT oldI v5 v6 : Word)
    (txBytes : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (_hlen0 : txBytes.length = 0) :
    cpsTripleWithin 5 D raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (0 : Word)) ** (innerPtr ↦ₘ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D D typeProg 0
      (.BEQ .x11 .x0 (164 : BitVec 13))
      (by decide) (by rw [type_length]; decide) rfl type_bound)
    (beq_spec_gen_within .x11 .x0 (164 : BitVec 13)
      (0 : Word) (0 : Word) D)
  have hpc : D + signExtend13 (164 : BitVec 13) = FailLi := by
    simp only [FailLi, D, GuestAddrs.tx_type_dispatch]; decide
  rw [hpc] at hbr
  have htk := cpsBranchWithin_takenStripPure2 hbr (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have htkF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr))
      (by pcf) htk
  have hfail :=
    typeFailRet_spec raIn txBase typePtr innerPtr oldT oldI txBase 0 v5 v6
      txBytes hret
  have c01 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) htkF hfail
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) c01

abbrev LegacyLi : Word := D + 52

private theorem LegacyLi_eq : LegacyLi = D + BitVec.ofNat 64 (4 * 13) := by
  simp only [LegacyLi, D, GuestAddrs.tx_type_dispatch]; decide
private theorem D56 : D + 56 = D + BitVec.ofNat 64 (4 * 14) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D60 : D + 60 = D + BitVec.ofNat 64 (4 * 15) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D64 : D + 64 = D + BitVec.ofNat 64 (4 * 16) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

set_option maxRecDepth 8000 in
/-- Legacy success tail at LegacyLi (instr 13–16): SD type0, SD inner0, LI a0=0, JALR. -/
theorem typeLegacyOkRet_spec
    (raIn txBase typePtr innerPtr oldT oldI a0v a1v v5 v6 : Word)
    (txBytes : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn) :
    cpsTripleWithin 4 LegacyLi raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (0 : Word)) ** (innerPtr ↦ₘ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word))) := by
  have h0 := sd_spec_gen_within .x12 .x0 typePtr (0 : Word) oldT
    (0 : BitVec 12) LegacyLi
  rw [show typePtr + signExtend12 (0 : BitVec 12) = typePtr from by
    rw [se12_zero]; exact BitVec.add_zero typePtr] at h0
  have h0e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D LegacyLi typeProg 13
      (.SD .x12 .x0 (0 : BitVec 12))
      LegacyLi_eq (by rw [type_length]; decide) rfl type_bound) h0
  have h0pc : LegacyLi + 4 = D + 56 := by
    simp only [LegacyLi, D, GuestAddrs.tx_type_dispatch]; decide
  rw [h0pc] at h0e
  have h0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x13 ↦ᵣ innerPtr) ** bytesRegion txBase txBytes **
        (innerPtr ↦ₘ oldI) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      (by pcf) h0e
  have h1 := sd_spec_gen_within .x13 .x0 innerPtr (0 : Word) oldI
    (0 : BitVec 12) (D + 56)
  rw [show innerPtr + signExtend12 (0 : BitVec 12) = innerPtr from by
    rw [se12_zero]; exact BitVec.add_zero innerPtr] at h1
  have h1e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 56) typeProg 14
      (.SD .x13 .x0 (0 : BitVec 12))
      D56 (by rw [type_length]; decide) rfl type_bound) h1
  have h1pc : (D + 56) + 4 = D + 60 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h1pc] at h1e
  have h1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** bytesRegion txBase txBytes **
        (typePtr ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      (by pcf) h1e
  have h2 := li_spec_gen_within .x10 a0v (0 : Word) (D + 60) (by decide)
  have h2e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 60) typeProg 15
      (.LI .x10 (0 : Word))
      D60 (by rw [type_length]; decide) rfl type_bound) h2
  have h2pc : (D + 60) + 4 = D + 64 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h2pc] at h2e
  have h2F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (0 : Word)) ** (innerPtr ↦ₘ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h2e
  have hexit : ((raIn + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = raIn := by
    have hz : raIn + signExtend12 (0 : BitVec 12) = raIn := by
      rw [se12_zero]; exact BitVec.add_zero raIn
    rw [hz, hret]
  have h3 : cpsTripleWithin 1 (D + 64) raIn typeCode
      (.x1 ↦ᵣ raIn) (.x1 ↦ᵣ raIn) := by
    have hj := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) (D + 64)
    rw [hexit] at hj
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 64) typeProg 16
        (.JALR .x0 .x1 (0 : BitVec 12))
        D64 (by rw [type_length]; decide) rfl type_bound) hj
  have h3F :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (0 : Word)) ** (innerPtr ↦ₘ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h3
  have c01 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have c02 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h2F
  have c03 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 h3F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) c03

#print axioms typeFailRet_spec
#print axioms txTypeDispatch_empty_fail_spec_within
#print axioms typeLegacyOkRet_spec

end EvmAsm.Codegen.TxTypeDispatchSpec
