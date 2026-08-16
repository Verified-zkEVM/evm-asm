import EvmAsm.Codegen.Programs.HeaderChain
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Codegen.Programs.BlockHashFromHeaderSpec
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SAsm.DualReadByteScan

namespace EvmAsm.Codegen.ValidateParentHashLinkSpec
set_option maxRecDepth 8000
open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.RlpListNthItemSAsm

abbrev vphlBase : Word := (GuestAddrs.validate_parent_hash_link : Word)
abbrev vphlClaimedAddr : Word := (GuestAddrs.vphl_claimed : Word)
abbrev vphlComputedAddr : Word := (GuestAddrs.vphl_computed : Word)

def vphlBodyCode : CodeReq :=
  CodeReq.ofProg vphlBase validateParentHashLink_prog
theorem vphlProg_length : validateParentHashLink_prog.length = 80 := by decide

instance (regionBase : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion regionBase bs) :=
  ⟨EvmAsm.Rv64.bytesRegion_pcFree _ _⟩

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _)

abbrev vphlClaimedOwn (claimedBytes : List (BitVec 8)) : Assertion :=
  bytesRegion vphlClaimedAddr claimedBytes

abbrev vphlDwordAt (bs : List (BitVec 8)) (q : Nat) : Word :=
  packBytes ((bs.drop (8 * q)).take 8)

theorem vphl_dwords_eq_iff
    (claimedBytes computedBytes : List (BitVec 8))
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32) :
    (∀ q, q < 4 → vphlDwordAt claimedBytes q = vphlDwordAt computedBytes q) ↔
      claimedBytes = computedBytes := by
  constructor
  · intro h
    apply List.ext_getElem
    · omega
    · intro i hi hc
      have hq : i / 8 < 4 := by omega
      have hk : i % 8 < 8 := Nat.mod_lt _ (by omega)
      have hleft : i % 8 < ((claimedBytes.drop (8 * (i / 8))).take 8).length := by
        simp only [List.length_take, List.length_drop]
        omega
      have hright : i % 8 < ((computedBytes.drop (8 * (i / 8))).take 8).length := by
        simp only [List.length_take, List.length_drop]
        omega
      have hd := congrArg (fun w : Word => extractByte w (i % 8)) (h (i / 8) hq)
      dsimp [vphlDwordAt] at hd
      rw [extractByte_packBytes _ _ hk hleft,
        extractByte_packBytes _ _ hk hright] at hd
      rw [List.getElem_take, List.getElem_drop,
        List.getElem_take, List.getElem_drop] at hd
      have hidx : 8 * (i / 8) + i % 8 = i := by omega
      simpa only [hidx] using hd
  · intro h q hq
    subst computedBytes
    rfl

/-! ## 4-dword compare (instr 22–33): LD claimed ;; LD computed ;; BNE → status-2

    Equal fall-through advances `+12` per round; mismatch BNE targets `vphlBase+144`. -/

set_option maxRecDepth 8000 in
/-- Round 0 equal: `LD/LD/BNE` at `vphlBase+88` fall through to `vphlBase+100`. -/
theorem vphlCompareRound0Eq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_eq : vphlDwordAt claimedBytes 0 = vphlDwordAt computedBytes 0) :
    cpsTripleWithin 3 (vphlBase + 200) (vphlBase + 212) vphlBodyCode
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes)
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ vphlDwordAt claimedBytes 0) ** (.x28 ↦ᵣ vphlDwordAt computedBytes 0) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 vphlClaimedAddr v7 (vphlBase + 200) claimedBytes 0
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 200) validateParentHashLink_prog 50 (.LD .x7 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ vphlComputedAddr) ** (.x28 ↦ᵣ v28) ** bytesRegion vphlComputedAddr computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 vphlComputedAddr v28 (vphlBase + 204) computedBytes 0
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 204) validateParentHashLink_prog 51 (.LD .x28 .x6 (0 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x7 ↦ᵣ vphlDwordAt claimedBytes 0) ** vphlClaimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (56 : BitVec 13)
    (vphlDwordAt claimedBytes 0) (vphlDwordAt computedBytes 0) (vphlBase + 208)
  rw [show (vphlBase + 208 : Word) + 4 = vphlBase + 212 from by bv_omega,
    show (vphlBase + 208) + signExtend13 (56 : BitVec 13) = vphlBase + 264 from by
      rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 208) validateParentHashLink_prog 52 (.BNE .x7 .x28 (56 : BitVec 13))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hbne
  have hfall0 := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_eq)
  have hfall := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
      vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) (by pcf) hfall0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hfall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 0 mismatch: `LD/LD/BNE` at `vphlBase+88` taken to `vphlBase+144` (status-2 site). -/
theorem vphlCompareRound0Ne
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : vphlDwordAt claimedBytes 0 ≠ vphlDwordAt computedBytes 0) :
    cpsTripleWithin 3 (vphlBase + 200) (vphlBase + 264) vphlBodyCode
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes)
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ vphlDwordAt claimedBytes 0) ** (.x28 ↦ᵣ vphlDwordAt computedBytes 0) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 vphlClaimedAddr v7 (vphlBase + 200) claimedBytes 0
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 200) validateParentHashLink_prog 50 (.LD .x7 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ vphlComputedAddr) ** (.x28 ↦ᵣ v28) ** bytesRegion vphlComputedAddr computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 vphlComputedAddr v28 (vphlBase + 204) computedBytes 0
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 204) validateParentHashLink_prog 51 (.LD .x28 .x6 (0 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x7 ↦ᵣ vphlDwordAt claimedBytes 0) ** vphlClaimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (56 : BitVec 13)
    (vphlDwordAt claimedBytes 0) (vphlDwordAt computedBytes 0) (vphlBase + 208)
  rw [show (vphlBase + 208 : Word) + 4 = vphlBase + 212 from by bv_omega,
    show (vphlBase + 208) + signExtend13 (56 : BitVec 13) = vphlBase + 264 from by
      rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 208) validateParentHashLink_prog 52 (.BNE .x7 .x28 (56 : BitVec 13))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
      vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) (by pcf) htake0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 1 equal: `vphlBase+100` → `vphlBase+112`. -/
theorem vphlCompareRound1Eq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_eq : vphlDwordAt claimedBytes 1 = vphlDwordAt computedBytes 1) :
    cpsTripleWithin 3 (vphlBase + 212) (vphlBase + 224) vphlBodyCode
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes)
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ vphlDwordAt claimedBytes 1) ** (.x28 ↦ᵣ vphlDwordAt computedBytes 1) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 vphlClaimedAddr v7 (vphlBase + 212) claimedBytes 1
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 212) validateParentHashLink_prog 53 (.LD .x7 .x5 (8 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ vphlComputedAddr) ** (.x28 ↦ᵣ v28) ** bytesRegion vphlComputedAddr computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 vphlComputedAddr v28 (vphlBase + 216) computedBytes 1
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 216) validateParentHashLink_prog 54 (.LD .x28 .x6 (8 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x7 ↦ᵣ vphlDwordAt claimedBytes 1) ** vphlClaimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (44 : BitVec 13)
    (vphlDwordAt claimedBytes 1) (vphlDwordAt computedBytes 1) (vphlBase + 220)
  rw [show (vphlBase + 220 : Word) + 4 = vphlBase + 224 from by bv_omega,
    show (vphlBase + 220) + signExtend13 (44 : BitVec 13) = vphlBase + 264 from by
      rw [show signExtend13 (44 : BitVec 13) = (44 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 220) validateParentHashLink_prog 55 (.BNE .x7 .x28 (44 : BitVec 13))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hbne
  have hfall0 := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_eq)
  have hfall := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
      vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) (by pcf) hfall0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hfall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 1 mismatch: `vphlBase+100` → `vphlBase+144`. -/
theorem vphlCompareRound1Ne
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : vphlDwordAt claimedBytes 1 ≠ vphlDwordAt computedBytes 1) :
    cpsTripleWithin 3 (vphlBase + 212) (vphlBase + 264) vphlBodyCode
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes)
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ vphlDwordAt claimedBytes 1) ** (.x28 ↦ᵣ vphlDwordAt computedBytes 1) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 vphlClaimedAddr v7 (vphlBase + 212) claimedBytes 1
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 212) validateParentHashLink_prog 53 (.LD .x7 .x5 (8 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ vphlComputedAddr) ** (.x28 ↦ᵣ v28) ** bytesRegion vphlComputedAddr computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 vphlComputedAddr v28 (vphlBase + 216) computedBytes 1
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 216) validateParentHashLink_prog 54 (.LD .x28 .x6 (8 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x7 ↦ᵣ vphlDwordAt claimedBytes 1) ** vphlClaimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (44 : BitVec 13)
    (vphlDwordAt claimedBytes 1) (vphlDwordAt computedBytes 1) (vphlBase + 220)
  rw [show (vphlBase + 220 : Word) + 4 = vphlBase + 224 from by bv_omega,
    show (vphlBase + 220) + signExtend13 (44 : BitVec 13) = vphlBase + 264 from by
      rw [show signExtend13 (44 : BitVec 13) = (44 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 220) validateParentHashLink_prog 55 (.BNE .x7 .x28 (44 : BitVec 13))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
      vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) (by pcf) htake0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 2 equal: `vphlBase+112` → `vphlBase+124`. -/
theorem vphlCompareRound2Eq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_eq : vphlDwordAt claimedBytes 2 = vphlDwordAt computedBytes 2) :
    cpsTripleWithin 3 (vphlBase + 224) (vphlBase + 236) vphlBodyCode
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes)
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ vphlDwordAt claimedBytes 2) ** (.x28 ↦ᵣ vphlDwordAt computedBytes 2) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 vphlClaimedAddr v7 (vphlBase + 224) claimedBytes 2
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 224) validateParentHashLink_prog 56 (.LD .x7 .x5 (16 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ vphlComputedAddr) ** (.x28 ↦ᵣ v28) ** bytesRegion vphlComputedAddr computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 vphlComputedAddr v28 (vphlBase + 228) computedBytes 2
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 228) validateParentHashLink_prog 57 (.LD .x28 .x6 (16 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x7 ↦ᵣ vphlDwordAt claimedBytes 2) ** vphlClaimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (32 : BitVec 13)
    (vphlDwordAt claimedBytes 2) (vphlDwordAt computedBytes 2) (vphlBase + 232)
  rw [show (vphlBase + 232 : Word) + 4 = vphlBase + 236 from by bv_omega,
    show (vphlBase + 232) + signExtend13 (32 : BitVec 13) = vphlBase + 264 from by
      rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 232) validateParentHashLink_prog 58 (.BNE .x7 .x28 (32 : BitVec 13))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hbne
  have hfall0 := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_eq)
  have hfall := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
      vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) (by pcf) hfall0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hfall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 2 mismatch: `vphlBase+112` → `vphlBase+144`. -/
theorem vphlCompareRound2Ne
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : vphlDwordAt claimedBytes 2 ≠ vphlDwordAt computedBytes 2) :
    cpsTripleWithin 3 (vphlBase + 224) (vphlBase + 264) vphlBodyCode
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes)
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ vphlDwordAt claimedBytes 2) ** (.x28 ↦ᵣ vphlDwordAt computedBytes 2) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 vphlClaimedAddr v7 (vphlBase + 224) claimedBytes 2
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 224) validateParentHashLink_prog 56 (.LD .x7 .x5 (16 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ vphlComputedAddr) ** (.x28 ↦ᵣ v28) ** bytesRegion vphlComputedAddr computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 vphlComputedAddr v28 (vphlBase + 228) computedBytes 2
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 228) validateParentHashLink_prog 57 (.LD .x28 .x6 (16 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x7 ↦ᵣ vphlDwordAt claimedBytes 2) ** vphlClaimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (32 : BitVec 13)
    (vphlDwordAt claimedBytes 2) (vphlDwordAt computedBytes 2) (vphlBase + 232)
  rw [show (vphlBase + 232 : Word) + 4 = vphlBase + 236 from by bv_omega,
    show (vphlBase + 232) + signExtend13 (32 : BitVec 13) = vphlBase + 264 from by
      rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 232) validateParentHashLink_prog 58 (.BNE .x7 .x28 (32 : BitVec 13))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
      vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) (by pcf) htake0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 3 equal: `vphlBase+124` → `vphlBase+136` (status-0 site). -/
theorem vphlCompareRound3Eq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_eq : vphlDwordAt claimedBytes 3 = vphlDwordAt computedBytes 3) :
    cpsTripleWithin 3 (vphlBase + 236) (vphlBase + 248) vphlBodyCode
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes)
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ vphlDwordAt claimedBytes 3) ** (.x28 ↦ᵣ vphlDwordAt computedBytes 3) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 vphlClaimedAddr v7 (vphlBase + 236) claimedBytes 3
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 236) validateParentHashLink_prog 59 (.LD .x7 .x5 (24 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ vphlComputedAddr) ** (.x28 ↦ᵣ v28) ** bytesRegion vphlComputedAddr computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 vphlComputedAddr v28 (vphlBase + 240) computedBytes 3
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 240) validateParentHashLink_prog 60 (.LD .x28 .x6 (24 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x7 ↦ᵣ vphlDwordAt claimedBytes 3) ** vphlClaimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (20 : BitVec 13)
    (vphlDwordAt claimedBytes 3) (vphlDwordAt computedBytes 3) (vphlBase + 244)
  rw [show (vphlBase + 244 : Word) + 4 = vphlBase + 248 from by bv_omega,
    show (vphlBase + 244) + signExtend13 (20 : BitVec 13) = vphlBase + 264 from by
      rw [show signExtend13 (20 : BitVec 13) = (20 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 244) validateParentHashLink_prog 61 (.BNE .x7 .x28 (20 : BitVec 13))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hbne
  have hfall0 := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_eq)
  have hfall := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
      vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) (by pcf) hfall0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hfall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 3 mismatch: `vphlBase+124` → `vphlBase+144`. -/
theorem vphlCompareRound3Ne
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : vphlDwordAt claimedBytes 3 ≠ vphlDwordAt computedBytes 3) :
    cpsTripleWithin 3 (vphlBase + 236) (vphlBase + 264) vphlBodyCode
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes)
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ vphlDwordAt claimedBytes 3) ** (.x28 ↦ᵣ vphlDwordAt computedBytes 3) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 vphlClaimedAddr v7 (vphlBase + 236) claimedBytes 3
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 236) validateParentHashLink_prog 59 (.LD .x7 .x5 (24 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ vphlComputedAddr) ** (.x28 ↦ᵣ v28) ** bytesRegion vphlComputedAddr computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 vphlComputedAddr v28 (vphlBase + 240) computedBytes 3
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 240) validateParentHashLink_prog 60 (.LD .x28 .x6 (24 : BitVec 12))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x7 ↦ᵣ vphlDwordAt claimedBytes 3) ** vphlClaimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (20 : BitVec 13)
    (vphlDwordAt claimedBytes 3) (vphlDwordAt computedBytes 3) (vphlBase + 244)
  rw [show (vphlBase + 244 : Word) + 4 = vphlBase + 248 from by bv_omega,
    show (vphlBase + 244) + signExtend13 (20 : BitVec 13) = vphlBase + 264 from by
      rw [show signExtend13 (20 : BitVec 13) = (20 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 244) validateParentHashLink_prog 61 (.BNE .x7 .x28 (20 : BitVec 13))
      (by bv_omega) (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
      vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) (by pcf) htake0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- All four dwords equal: `vphlBase+88` → `vphlBase+136` (12 steps). -/
theorem vphlCompareAllEq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : vphlDwordAt claimedBytes 0 = vphlDwordAt computedBytes 0)
    (h1 : vphlDwordAt claimedBytes 1 = vphlDwordAt computedBytes 1)
    (h2 : vphlDwordAt claimedBytes 2 = vphlDwordAt computedBytes 2)
    (h3 : vphlDwordAt claimedBytes 3 = vphlDwordAt computedBytes 3) :
    cpsTripleWithin 12 (vphlBase + 200) (vphlBase + 248) vphlBodyCode
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes)
      ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
        (.x7 ↦ᵣ vphlDwordAt claimedBytes 3) ** (.x28 ↦ᵣ vphlDwordAt computedBytes 3) **
        vphlClaimedOwn claimedBytes ** bytesRegion vphlComputedAddr computedBytes) := by
  have r0 := vphlCompareRound0Eq claimedBytes computedBytes v7 v28 hclen hcdlen h0
  have r1 := vphlCompareRound1Eq claimedBytes computedBytes
    (vphlDwordAt claimedBytes 0) (vphlDwordAt computedBytes 0) hclen hcdlen h1
  have r2 := vphlCompareRound2Eq claimedBytes computedBytes
    (vphlDwordAt claimedBytes 1) (vphlDwordAt computedBytes 1) hclen hcdlen h2
  have r3 := vphlCompareRound3Eq claimedBytes computedBytes
    (vphlDwordAt claimedBytes 2) (vphlDwordAt computedBytes 2) hclen hcdlen h3
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) r0 r1
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 r2
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 r3
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

theorem vphl_choose12 {B : Assertion} {h : PartialState}
    (hp : (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** B) h) :
    ∃ v5 v6 v7 v13 v14 v15 v16 v17 v28 v29 v30 v31,
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** B) h := by
  have h5 : (regOwn .x5 ** (regOwn .x6 ** regOwn .x7 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** B)) h := by
    xperm_hyp hp
  obtain ⟨v5, h5⟩ := sepConj_choose_regOwn h5
  have h6 : (regOwn .x6 ** ((.x5 ↦ᵣ v5) ** regOwn .x7 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** B)) h := by
    xperm_hyp h5
  obtain ⟨v6, h6⟩ := sepConj_choose_regOwn h6
  have h7 : (regOwn .x7 ** ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** B)) h := by xperm_hyp h6
  obtain ⟨v7, h7⟩ := sepConj_choose_regOwn h7
  have h13 : (regOwn .x13 ** ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x17 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** B)) h := by xperm_hyp h7
  obtain ⟨v13, h13⟩ := sepConj_choose_regOwn h13
  have h14 : (regOwn .x14 ** ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x13 ↦ᵣ v13) ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** B)) h := by xperm_hyp h13
  obtain ⟨v14, h14⟩ := sepConj_choose_regOwn h14
  have h15 : (regOwn .x15 ** ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** B)) h := by xperm_hyp h14
  obtain ⟨v15, h15⟩ := sepConj_choose_regOwn h15
  have h16 : (regOwn .x16 ** ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** B)) h := by xperm_hyp h15
  obtain ⟨v16, h16⟩ := sepConj_choose_regOwn h16
  have h17 : (regOwn .x17 ** ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) **
      regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** B)) h := by xperm_hyp h16
  obtain ⟨v17, h17⟩ := sepConj_choose_regOwn h17
  have h28 : (regOwn .x28 ** ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) **
      (.x17 ↦ᵣ v17) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** B)) h := by xperm_hyp h17
  obtain ⟨v28, h28⟩ := sepConj_choose_regOwn h28
  have h29 : (regOwn .x29 ** ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) **
      (.x17 ↦ᵣ v17) ** (.x28 ↦ᵣ v28) ** regOwn .x30 ** regOwn .x31 ** B)) h := by xperm_hyp h28
  obtain ⟨v29, h29⟩ := sepConj_choose_regOwn h29
  have h30 : (regOwn .x30 ** ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) **
      (.x17 ↦ᵣ v17) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** regOwn .x31 ** B)) h := by xperm_hyp h29
  obtain ⟨v30, h30⟩ := sepConj_choose_regOwn h30
  have h31pre : (regOwn .x31 ** ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) **
      (.x17 ↦ᵣ v17) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** B)) h := by
    xperm_hyp h30
  obtain ⟨v31, h31⟩ := sepConj_choose_regOwn h31pre
  exact ⟨v5, v6, v7, v13, v14, v15, v16, v17, v28, v29, v30, v31,
    by xperm_hyp h31⟩

set_option maxRecDepth 8000 in
theorem vphlCompareMatchTail
    (outPtr oldOut : Word) (G : Assertion) (hG : G.pcFree) :
    cpsTripleWithin 4 (vphlBase + 248) (vphlBase + 288) vphlBodyCode
      ((.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ vphlClaimedAddr) ** (.x10 ↦ᵣ (0 : Word)) **
        (outPtr ↦ₘ oldOut) ** G)
      ((.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (outPtr ↦ₘ (1 : Word)) ** G) := by
  have hli := li_spec_gen_within .x5 vphlClaimedAddr (1 : Word)
    (vphlBase + 248) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 248) validateParentHashLink_prog 62
      (.LI .x5 (1 : Word)) (by bv_omega) (by rw [vphlProg_length]; decide)
      rfl (by rw [vphlProg_length]; decide)) hli
  have hlif := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ oldOut) ** G)
    (by pcf; exact hG) hlic
  have hsd := sd_spec_gen_within .x20 .x5 outPtr (1 : Word) oldOut
    (0 : BitVec 12) (vphlBase + 252)
  simp only [signExtend12_0] at hsd
  have hzero : outPtr + (0 : Word) = outPtr := by bv_omega
  rw [hzero] at hsd
  have hsdc := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 252) validateParentHashLink_prog 63
      (.SD .x20 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hsd
  have hsdf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** G) (by pcf; exact hG) hsdc
  have hli0 := li_spec_gen_within .x10 (0 : Word) (0 : Word)
    (vphlBase + 256) (by decide)
  have hli0c := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 256) validateParentHashLink_prog 64
      (.LI .x10 (0 : Word)) (by bv_omega)
      (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hli0
  have hli0f := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (outPtr ↦ₘ (1 : Word)) ** G)
    (by pcf; exact hG) hli0c
  have hj := jal_x0_spec_gen_within (28 : BitVec 21) (vphlBase + 260)
  rw [show (vphlBase + 260) + signExtend21 (28 : BitVec 21) = vphlBase + 288 by
    rw [show signExtend21 (28 : BitVec 21) = (28 : Word) by decide]; bv_omega] at hj
  have hjc := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 260) validateParentHashLink_prog 65
      (.JAL .x0 (28 : BitVec 21)) (by bv_omega)
      (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hj
  have hjf := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
      (outPtr ↦ₘ (1 : Word)) ** G) (by pcf; exact hG) hjc
  simp only [sepConj_emp_left'] at hjf
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlif hsdf
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hli0f
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 hjf
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
theorem vphlCompareMismatchTail
    (outPtr oldOut : Word) (G : Assertion) (hG : G.pcFree) :
    cpsTripleWithin 3 (vphlBase + 264) (vphlBase + 288) vphlBodyCode
      ((.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ vphlClaimedAddr) ** (.x10 ↦ᵣ (0 : Word)) **
        (outPtr ↦ₘ oldOut) ** G)
      ((.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ vphlClaimedAddr) ** (.x10 ↦ᵣ (0 : Word)) **
        (outPtr ↦ₘ (0 : Word)) ** G) := by
  have hsd := generic_sd_x0_spec_within .x20 outPtr oldOut
    (0 : BitVec 12) (vphlBase + 264)
  simp only [signExtend12_0] at hsd
  have hzero : outPtr + (0 : Word) = outPtr := by bv_omega
  rw [hzero] at hsd
  have hsdc := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 264) validateParentHashLink_prog 66
      (.SD .x20 .x0 (0 : BitVec 12)) (by bv_omega)
      (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hsd
  have hsdf := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x10 ↦ᵣ (0 : Word)) ** G) (by pcf; exact hG) hsdc
  have hli := li_spec_gen_within .x10 (0 : Word) (0 : Word)
    (vphlBase + 268) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 268) validateParentHashLink_prog 67
      (.LI .x10 (0 : Word)) (by bv_omega)
      (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hli
  have hlif := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ vphlClaimedAddr) ** (outPtr ↦ₘ (0 : Word)) ** G)
    (by pcf; exact hG) hlic
  have hj := jal_x0_spec_gen_within (16 : BitVec 21) (vphlBase + 272)
  rw [show (vphlBase + 272) + signExtend21 (16 : BitVec 21) = vphlBase + 288 by
    rw [show signExtend21 (16 : BitVec 21) = (16 : Word) by decide]; bv_omega] at hj
  have hjc := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at vphlBase (vphlBase + 272) validateParentHashLink_prog 68
      (.JAL .x0 (16 : BitVec 21)) (by bv_omega)
      (by rw [vphlProg_length]; decide) rfl (by rw [vphlProg_length]; decide)) hj
  have hjf := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ vphlClaimedAddr) ** (.x10 ↦ᵣ (0 : Word)) **
      (outPtr ↦ₘ (0 : Word)) ** G) (by pcf; exact hG) hjc
  simp only [sepConj_emp_left'] at hjf
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsdf hlif
  have hall2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hall hjf
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall2

end EvmAsm.Codegen.ValidateParentHashLinkSpec
