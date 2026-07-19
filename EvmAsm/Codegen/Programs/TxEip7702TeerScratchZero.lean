/-
  Teer scratch-zero: `li s10,0` + 4×(`la t0, teer_*; sd zero, 0(t0)`).
  Instr 20–32 → AtBalCheck (E+132).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerPrologue
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure)

abbrev RegularRefundAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_regular_refund
abbrev SuccessCountAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_success_count
abbrev PredelegatedAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_predelegated_count
abbrev RolledBackAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_rolled_back

/-- The four scratch cells zeroed by the early prologue. -/
def teerScratchZeroOwn : Assertion :=
  memOwn RegularRefundAddr **
  memOwn SuccessCountAddr **
  memOwn PredelegatedAddr **
  memOwn RolledBackAddr

theorem pcFree_teerScratchZeroOwn : teerScratchZeroOwn.pcFree := by
  unfold teerScratchZeroOwn
  repeat' (first | exact pcFree_memOwn | apply pcFree_sepConj)

/-- `li s10, 0` at E+80. -/
theorem teerLiS10 (v : Word) :
    cpsTripleWithin 1 AfterAbiMoves AfterLiS10 teerCode
      (.x26 ↦ᵣ v) (.x26 ↦ᵣ (0 : Word)) := by
  have h0 := li_spec_within .x26 v (0 : Word) AfterAbiMoves (by decide)
  exact cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E AfterAbiMoves teerProg 20
      (.LI .x26 (0 : Word)) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide)) h0

/-- `la x5, teer_regular_refund` at E+84. -/
theorem teerLaRegularRefund (v : Word) :
    cpsTripleWithin 2 AfterLiS10 (E + 92) teerCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ RegularRefundAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterLiS10
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_regular_refund
        (GuestAddrs.tx_eip7702_existing_authority_refund + 84)))
        a = some i → teerCode a = some i := fun a i hi =>
    CodeReq.ofProg_mem_at E AfterLiS10 teerProg 21
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_regular_refund
        (GuestAddrs.tx_eip7702_existing_authority_refund + 84)))
      (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide) a i hi
  have had : ∀ a i, CodeReq.singleton (AfterLiS10 + 4)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_regular_refund
        (GuestAddrs.tx_eip7702_existing_authority_refund + 84)))
        a = some i → teerCode a = some i := fun a i hi =>
    CodeReq.ofProg_mem_at E (AfterLiS10 + 4) teerProg 22
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_regular_refund
        (GuestAddrs.tx_eip7702_existing_authority_refund + 84)))
      (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide) a i hi
  have h := la_materialize_within .x5 v AfterLiS10 RegularRefundAddr
    (by decide) (by decide) hau had
  rw [show (AfterLiS10 : Word) + 8 = E + 92 from by simp [AfterLiS10, E]; bv_omega] at h
  exact h

private theorem addr_add_off0 (a : Word) : a + signExtend12 (0 : BitVec 12) = a := by
  simp [signExtend12]

/-- Store zero keeps value-carrying `addr ↦ₘ 0` (foundation for RolledZero thread). -/
private theorem teerSdZeroCell_is (addr pc : Word)
    (hmem : ∀ a i, CodeReq.singleton pc (.SD .x5 .x0 (0 : BitVec 12)) a = some i →
      teerCode a = some i) :
    cpsTripleWithin 1 pc (pc + 4) teerCode
      ((.x5 ↦ᵣ addr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn addr)
      ((.x5 ↦ᵣ addr) ** (.x0 ↦ᵣ (0 : Word)) ** (addr ↦ₘ (0 : Word))) := by
  have heq := addr_add_off0 addr
  have h0 := sd_spec_gen_own_within .x5 .x0 addr (0 : Word) (0 : BitVec 12) pc
  have h1 := cpsTripleWithin_extend_code hmem h0
  convert h1 using 1 <;> simp only [heq]

private theorem teerSdZeroCell (addr pc : Word)
    (hmem : ∀ a i, CodeReq.singleton pc (.SD .x5 .x0 (0 : BitVec 12)) a = some i →
      teerCode a = some i) :
    cpsTripleWithin 1 pc (pc + 4) teerCode
      ((.x5 ↦ᵣ addr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn addr)
      ((.x5 ↦ᵣ addr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn addr) := by
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq)
    (teerSdZeroCell_is addr pc hmem)

/-- `sd x0, 0(x5)` into regular_refund (memOwn → memOwn). -/
theorem teerSdRegularRefund (v5 : Word) (hv : v5 = RegularRefundAddr) :
    cpsTripleWithin 1 (E + 92) (E + 96) teerCode
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn RegularRefundAddr)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn RegularRefundAddr) := by
  subst hv
  have h := teerSdZeroCell RegularRefundAddr (E + 92)
    (CodeReq.ofProg_mem_at E (E + 92) teerProg 23
      (.SD .x5 .x0 (0 : BitVec 12)) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide))
  rw [show (E + 92 : Word) + 4 = E + 96 from by bv_omega] at h
  exact h

/-- `la x5, teer_success_count` at E+96. -/
theorem teerLaSuccessCount (v : Word) :
    cpsTripleWithin 2 (E + 96) (E + 104) teerCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ SuccessCountAddr) := by
  have hau : ∀ a i, CodeReq.singleton (E + 96)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_success_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 96)))
        a = some i → teerCode a = some i := fun a i hi =>
    CodeReq.ofProg_mem_at E (E + 96) teerProg 24
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_success_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 96)))
      (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide) a i hi
  have had : ∀ a i, CodeReq.singleton (E + 100)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_success_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 96)))
        a = some i → teerCode a = some i := fun a i hi =>
    CodeReq.ofProg_mem_at E (E + 100) teerProg 25
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_success_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 96)))
      (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide) a i hi
  have h := la_materialize_within .x5 v (E + 96) SuccessCountAddr
    (by decide) (by decide) hau had
  rw [show (E + 96 : Word) + 8 = E + 104 from by bv_omega] at h
  exact h

theorem teerSdSuccessCount (v5 : Word) (hv : v5 = SuccessCountAddr) :
    cpsTripleWithin 1 (E + 104) (E + 108) teerCode
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn SuccessCountAddr)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn SuccessCountAddr) := by
  subst hv
  have h := teerSdZeroCell SuccessCountAddr (E + 104)
    (CodeReq.ofProg_mem_at E (E + 104) teerProg 26
      (.SD .x5 .x0 (0 : BitVec 12)) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide))
  rw [show (E + 104 : Word) + 4 = E + 108 from by bv_omega] at h
  exact h

/-- `la x5, teer_predelegated_count` at E+108. -/
theorem teerLaPredelegated (v : Word) :
    cpsTripleWithin 2 (E + 108) (E + 116) teerCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ PredelegatedAddr) := by
  have hau : ∀ a i, CodeReq.singleton (E + 108)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_predelegated_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 108)))
        a = some i → teerCode a = some i := fun a i hi =>
    CodeReq.ofProg_mem_at E (E + 108) teerProg 27
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_predelegated_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 108)))
      (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide) a i hi
  have had : ∀ a i, CodeReq.singleton (E + 112)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_predelegated_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 108)))
        a = some i → teerCode a = some i := fun a i hi =>
    CodeReq.ofProg_mem_at E (E + 112) teerProg 28
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_predelegated_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 108)))
      (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide) a i hi
  have h := la_materialize_within .x5 v (E + 108) PredelegatedAddr
    (by decide) (by decide) hau had
  rw [show (E + 108 : Word) + 8 = E + 116 from by bv_omega] at h
  exact h

theorem teerSdPredelegated (v5 : Word) (hv : v5 = PredelegatedAddr) :
    cpsTripleWithin 1 (E + 116) (E + 120) teerCode
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn PredelegatedAddr)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn PredelegatedAddr) := by
  subst hv
  have h := teerSdZeroCell PredelegatedAddr (E + 116)
    (CodeReq.ofProg_mem_at E (E + 116) teerProg 29
      (.SD .x5 .x0 (0 : BitVec 12)) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide))
  rw [show (E + 116 : Word) + 4 = E + 120 from by bv_omega] at h
  exact h

/-- `la x5, teer_rolled_back` at E+120. -/
theorem teerLaRolledBack (v : Word) :
    cpsTripleWithin 2 (E + 120) (E + 128) teerCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ RolledBackAddr) := by
  have hau : ∀ a i, CodeReq.singleton (E + 120)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_rolled_back
        (GuestAddrs.tx_eip7702_existing_authority_refund + 120)))
        a = some i → teerCode a = some i := fun a i hi =>
    CodeReq.ofProg_mem_at E (E + 120) teerProg 30
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_rolled_back
        (GuestAddrs.tx_eip7702_existing_authority_refund + 120)))
      (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide) a i hi
  have had : ∀ a i, CodeReq.singleton (E + 124)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_rolled_back
        (GuestAddrs.tx_eip7702_existing_authority_refund + 120)))
        a = some i → teerCode a = some i := fun a i hi =>
    CodeReq.ofProg_mem_at E (E + 124) teerProg 31
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_rolled_back
        (GuestAddrs.tx_eip7702_existing_authority_refund + 120)))
      (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide) a i hi
  have h := la_materialize_within .x5 v (E + 120) RolledBackAddr
    (by decide) (by decide) hau had
  rw [show (E + 120 : Word) + 8 = E + 128 from by bv_omega] at h
  exact h

theorem teerSdRolledBack (v5 : Word) (hv : v5 = RolledBackAddr) :
    cpsTripleWithin 1 (E + 128) AtBalCheck teerCode
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn RolledBackAddr)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn RolledBackAddr) := by
  subst hv
  have h := teerSdZeroCell RolledBackAddr (E + 128)
    (CodeReq.ofProg_mem_at E (E + 128) teerProg 32
      (.SD .x5 .x0 (0 : BitVec 12)) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide))
  rw [show (E + 128 : Word) + 4 = AtBalCheck from by simp [AtBalCheck, E]; bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Full scratch-zero block (instr 20–32): li s10 + 4× la/sd → AtBalCheck. -/
theorem teerScratchZero (v26 v5 : Word) :
    cpsTripleWithin 13 AfterAbiMoves AtBalCheck teerCode
      ((.x26 ↦ᵣ v26) ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        teerScratchZeroOwn)
      ((.x26 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ RolledBackAddr) ** (.x0 ↦ᵣ (0 : Word)) **
        teerScratchZeroOwn) := by
  unfold teerScratchZeroOwn
  have hli := teerLiS10 v26
  have hliF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
      memOwn RegularRefundAddr ** memOwn SuccessCountAddr **
      memOwn PredelegatedAddr ** memOwn RolledBackAddr) (by pcf) hli
  -- regular_refund la+sd
  have hla0 := teerLaRegularRefund v5
  have hla0F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      memOwn RegularRefundAddr ** memOwn SuccessCountAddr **
      memOwn PredelegatedAddr ** memOwn RolledBackAddr) (by pcf) hla0
  have hsd0 := teerSdRegularRefund RegularRefundAddr rfl
  have hsd0F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) **
      memOwn SuccessCountAddr ** memOwn PredelegatedAddr ** memOwn RolledBackAddr)
    (by pcf) hsd0
  have c0a := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hla0F
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0a hsd0F
  -- success_count la+sd
  have hla1 := teerLaSuccessCount RegularRefundAddr
  have hla1F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      memOwn RegularRefundAddr ** memOwn SuccessCountAddr **
      memOwn PredelegatedAddr ** memOwn RolledBackAddr) (by pcf) hla1
  have hsd1 := teerSdSuccessCount SuccessCountAddr rfl
  have hsd1F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) **
      memOwn RegularRefundAddr ** memOwn PredelegatedAddr ** memOwn RolledBackAddr)
    (by pcf) hsd1
  have c1a := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 hla1F
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1a hsd1F
  -- predelegated la+sd
  have hla2 := teerLaPredelegated SuccessCountAddr
  have hla2F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      memOwn RegularRefundAddr ** memOwn SuccessCountAddr **
      memOwn PredelegatedAddr ** memOwn RolledBackAddr) (by pcf) hla2
  have hsd2 := teerSdPredelegated PredelegatedAddr rfl
  have hsd2F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) **
      memOwn RegularRefundAddr ** memOwn SuccessCountAddr ** memOwn RolledBackAddr)
    (by pcf) hsd2
  have c2a := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hla2F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2a hsd2F
  -- rolled_back la+sd
  have hla3 := teerLaRolledBack PredelegatedAddr
  have hla3F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      memOwn RegularRefundAddr ** memOwn SuccessCountAddr **
      memOwn PredelegatedAddr ** memOwn RolledBackAddr) (by pcf) hla3
  have hsd3 := teerSdRolledBack RolledBackAddr rfl
  have hsd3F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) **
      memOwn RegularRefundAddr ** memOwn SuccessCountAddr ** memOwn PredelegatedAddr)
    (by pcf) hsd3
  have c3a := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 hla3F
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3a hsd3F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c3

/-! ## Value-carrying scratch-zero (RolledZero foundation)

`teerScratchZero` discards written zeros via `memIs → memOwn`. Empty-auth
RolledZero needs `RolledBack ↦ₘ 0` threaded; this dual keeps the zeros. -/

/-- Four scratch cells after zero-store, value-carrying. -/
def teerScratchZeroIs : Assertion :=
  (RegularRefundAddr ↦ₘ (0 : Word)) **
  (SuccessCountAddr ↦ₘ (0 : Word)) **
  (PredelegatedAddr ↦ₘ (0 : Word)) **
  (RolledBackAddr ↦ₘ (0 : Word))

theorem pcFree_teerScratchZeroIs : teerScratchZeroIs.pcFree := by
  unfold teerScratchZeroIs
  repeat' (first | exact pcFree_memIs | apply pcFree_sepConj)

theorem teerScratchZeroIs_to_own :
    ∀ h, teerScratchZeroIs h → teerScratchZeroOwn h := by
  intro h hp
  unfold teerScratchZeroIs teerScratchZeroOwn at *
  -- Right-assoc: A ** B ** C ** D
  obtain ⟨h1, h2, hd, hu, hA, hBCD⟩ := hp
  obtain ⟨h1', h2', hd', hu', hB, hCD⟩ := hBCD
  obtain ⟨h1'', h2'', hd'', hu'', hC, hD⟩ := hCD
  exact ⟨h1, h2, hd, hu, memIs_implies_memOwn _ hA,
    ⟨h1', h2', hd', hu', memIs_implies_memOwn _ hB,
      ⟨h1'', h2'', hd'', hu'', memIs_implies_memOwn _ hC,
        memIs_implies_memOwn _ hD⟩⟩⟩

/-- `sd` duals posting `↦ₘ 0` (not memOwn). -/
theorem teerSdRegularRefund_is (v5 : Word) (hv : v5 = RegularRefundAddr) :
    cpsTripleWithin 1 (E + 92) (E + 96) teerCode
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn RegularRefundAddr)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (RegularRefundAddr ↦ₘ (0 : Word))) := by
  subst hv
  have h := teerSdZeroCell_is RegularRefundAddr (E + 92)
    (CodeReq.ofProg_mem_at E (E + 92) teerProg 23
      (.SD .x5 .x0 (0 : BitVec 12)) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide))
  rw [show (E + 92 : Word) + 4 = E + 96 from by bv_omega] at h
  exact h

theorem teerSdSuccessCount_is (v5 : Word) (hv : v5 = SuccessCountAddr) :
    cpsTripleWithin 1 (E + 104) (E + 108) teerCode
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn SuccessCountAddr)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (SuccessCountAddr ↦ₘ (0 : Word))) := by
  subst hv
  have h := teerSdZeroCell_is SuccessCountAddr (E + 104)
    (CodeReq.ofProg_mem_at E (E + 104) teerProg 26
      (.SD .x5 .x0 (0 : BitVec 12)) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide))
  rw [show (E + 104 : Word) + 4 = E + 108 from by bv_omega] at h
  exact h

theorem teerSdPredelegated_is (v5 : Word) (hv : v5 = PredelegatedAddr) :
    cpsTripleWithin 1 (E + 116) (E + 120) teerCode
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn PredelegatedAddr)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (PredelegatedAddr ↦ₘ (0 : Word))) := by
  subst hv
  have h := teerSdZeroCell_is PredelegatedAddr (E + 116)
    (CodeReq.ofProg_mem_at E (E + 116) teerProg 29
      (.SD .x5 .x0 (0 : BitVec 12)) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide))
  rw [show (E + 116 : Word) + 4 = E + 120 from by bv_omega] at h
  exact h

theorem teerSdRolledBack_is (v5 : Word) (hv : v5 = RolledBackAddr) :
    cpsTripleWithin 1 (E + 128) AtBalCheck teerCode
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn RolledBackAddr)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (RolledBackAddr ↦ₘ (0 : Word))) := by
  subst hv
  have h := teerSdZeroCell_is RolledBackAddr (E + 128)
    (CodeReq.ofProg_mem_at E (E + 128) teerProg 32
      (.SD .x5 .x0 (0 : BitVec 12)) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide))
  rw [show (E + 128 : Word) + 4 = AtBalCheck from by simp [AtBalCheck, E]; bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Scratch-zero posting value-carrying zeros (empty-auth RolledZero thread). -/
theorem teerScratchZero_is (v26 v5 : Word) :
    cpsTripleWithin 13 AfterAbiMoves AtBalCheck teerCode
      ((.x26 ↦ᵣ v26) ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        teerScratchZeroOwn)
      ((.x26 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ RolledBackAddr) ** (.x0 ↦ᵣ (0 : Word)) **
        teerScratchZeroIs) := by
  unfold teerScratchZeroOwn teerScratchZeroIs
  have hli := teerLiS10 v26
  have hliF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
      memOwn RegularRefundAddr ** memOwn SuccessCountAddr **
      memOwn PredelegatedAddr ** memOwn RolledBackAddr) (by pcf) hli
  have hla0 := teerLaRegularRefund v5
  have hla0F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      memOwn RegularRefundAddr ** memOwn SuccessCountAddr **
      memOwn PredelegatedAddr ** memOwn RolledBackAddr) (by pcf) hla0
  have hsd0 := teerSdRegularRefund_is RegularRefundAddr rfl
  have hsd0F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) **
      memOwn SuccessCountAddr ** memOwn PredelegatedAddr ** memOwn RolledBackAddr)
    (by pcf) hsd0
  have c0a := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hla0F
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0a hsd0F
  have hla1 := teerLaSuccessCount RegularRefundAddr
  have hla1F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ (0 : Word)) ** memOwn SuccessCountAddr **
      memOwn PredelegatedAddr ** memOwn RolledBackAddr) (by pcf) hla1
  have hsd1 := teerSdSuccessCount_is SuccessCountAddr rfl
  have hsd1F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ (0 : Word)) ** memOwn PredelegatedAddr **
      memOwn RolledBackAddr)
    (by pcf) hsd1
  have c1a := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 hla1F
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1a hsd1F
  have hla2 := teerLaPredelegated SuccessCountAddr
  have hla2F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ (0 : Word)) ** (SuccessCountAddr ↦ₘ (0 : Word)) **
      memOwn PredelegatedAddr ** memOwn RolledBackAddr) (by pcf) hla2
  have hsd2 := teerSdPredelegated_is PredelegatedAddr rfl
  have hsd2F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ (0 : Word)) ** (SuccessCountAddr ↦ₘ (0 : Word)) **
      memOwn RolledBackAddr)
    (by pcf) hsd2
  have c2a := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hla2F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2a hsd2F
  have hla3 := teerLaRolledBack PredelegatedAddr
  have hla3F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ (0 : Word)) ** (SuccessCountAddr ↦ₘ (0 : Word)) **
      (PredelegatedAddr ↦ₘ (0 : Word)) ** memOwn RolledBackAddr) (by pcf) hla3
  have hsd3 := teerSdRolledBack_is RolledBackAddr rfl
  have hsd3F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ (0 : Word)) ** (SuccessCountAddr ↦ₘ (0 : Word)) **
      (PredelegatedAddr ↦ₘ (0 : Word)))
    (by pcf) hsd3
  have c3a := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 hla3F
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3a hsd3F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c3

#print axioms teerLiS10
#print axioms teerLaRegularRefund
#print axioms teerSdRegularRefund
#print axioms teerScratchZero
#print axioms teerScratchZero_is
#print axioms teerScratchZeroIs_to_own

end EvmAsm.Codegen.TxEip7702TeerSpec
