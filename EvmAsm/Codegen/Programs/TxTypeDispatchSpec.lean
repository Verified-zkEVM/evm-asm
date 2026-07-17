/-
  Fn.Spec for `tx_type_dispatch` (45-instr leaf, no frame) — a4gbr.2 residual.

  Success arms write type/inner_offset and return a0=0:
    legacy (first ≥ 0xc0) → type=0, inner=0
    type 1..4             → type=N,  inner=1
  Fail arms (empty / unknown prefix) return a0=1.

  No frame, no callees. LBU needs 8-aligned `txBase` (bytesRegion_lbu_within).
  classical-3 only; no `native_decide` / `sorry`.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.LoopFuel
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

/-- Step budget matching prover1 `nTxTypeDispatchSteps`. -/
def nTxTypeDispatchSteps : Nat := 256

/-- EIP-2718 classification matching prover1 `teerTxTypeDispatch`. -/
def teerTxTypeDispatch (txBytes : List (BitVec 8)) : Word × Word × Word :=
  match txBytes with
  | [] => (1, 0, 0)
  | b :: _ =>
    if 192 ≤ b.toNat then (0, 0, 0)
    else if b = (1 : BitVec 8) then (0, 1, 1)
    else if b = (2 : BitVec 8) then (0, 2, 1)
    else if b = (3 : BitVec 8) then (0, 3, 1)
    else if b = (4 : BitVec 8) then (0, 4, 1)
    else (1, 0, 0)

theorem type_length : typeProg.length = 45 := by decide

private theorem se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

private theorem type_bound : 4 * typeProg.length < 2 ^ 64 := by
  simp only [type_length]; decide

private theorem ofNat_ne_zero {a : Nat} (h0 : a ≠ 0) (hlt : a < 2 ^ 64) :
    BitVec.ofNat 64 a ≠ (0 : Word) := by
  intro h
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h2
  have hz : ((0 : Word).toNat) = 0 := by decide
  omega

private theorem not_ult_zx_192 (b : BitVec 8) (h : 192 ≤ b.toNat) :
    ¬ BitVec.ult (b.zeroExtend 64 : Word) (192 : Word) := by
  intro hult
  have hlt : (b.zeroExtend 64 : Word).toNat < (192 : Word).toNat := by
    rwa [← BitVec.ult_iff_toNat_lt]
  have hz := SAsm.toNat_zeroExtend_byte b
  have h192 : (192 : Word).toNat = 192 := by decide
  omega

private theorem ult_zx_192 (b : BitVec 8) (h : b.toNat < 192) :
    BitVec.ult (b.zeroExtend 64 : Word) (192 : Word) := by
  have hlt : (b.zeroExtend 64 : Word).toNat < (192 : Word).toNat := by
    have hz := SAsm.toNat_zeroExtend_byte b
    have h192 : (192 : Word).toNat = 192 := by decide
    omega
  rwa [BitVec.ult_iff_toNat_lt]

private theorem zx_byte_eq (n : Nat) (hn : n < 256) :
    ((BitVec.ofNat 8 n).zeroExtend 64 : Word) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [SAsm.toNat_zeroExtend_byte]
  simp only [BitVec.toNat_ofNat]
  have : n % 256 = n := Nat.mod_eq_of_lt hn
  have : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  omega

private theorem base_add_zero (base : Word) :
    base + BitVec.ofNat 64 0 = base := BitVec.add_zero base

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

private theorem D4 : D + 4 = D + BitVec.ofNat 64 (4 * 1) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D8 : D + 8 = D + BitVec.ofNat 64 (4 * 2) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D12 : D + 12 = D + BitVec.ofNat 64 (4 * 3) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

set_option maxRecDepth 8000 in
/-- Full legacy path: non-empty + first byte ≥ 0xc0 → type=0, inner=0, a0=0 (8 steps). -/
theorem txTypeDispatch_legacy_spec_within
    (raIn txBase typePtr innerPtr oldT oldI v5 v6 : Word)
    (txBytes : List (BitVec 8)) (b : BitVec 8) (rest : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hbytes : txBytes = b :: rest)
    (hlegacy : 192 ≤ b.toNat)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 8 D raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (0 : Word)) ** (innerPtr ↦ₘ (0 : Word)) **
        (.x5 ↦ᵣ (b.zeroExtend 64)) ** (.x6 ↦ᵣ (192 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  have hlen_pos : 0 < txBytes.length := by simp only [hbytes, List.length_cons]; omega
  have hlen_ne : BitVec.ofNat 64 txBytes.length ≠ (0 : Word) := by
    have hpos : txBytes.length ≠ 0 := Nat.ne_of_gt hlen_pos
    have hlt : txBytes.length < 2 ^ 64 := by omega
    exact ofNat_ne_zero hpos hlt
  -- [0] BEQ a1,x0 +164 ntaken
  have hbr0 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D D typeProg 0
      (.BEQ .x11 .x0 (164 : BitVec 13))
      (by decide) (by rw [type_length]; decide) rfl type_bound)
    (beq_spec_gen_within .x11 .x0 (164 : BitVec 13)
      (BitVec.ofNat 64 txBytes.length) (0 : Word) D)
  have hnt0 := cpsBranchWithin_ntakenStripPure2 hbr0 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hlen_ne)
  have hnt0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      (by pcf) hnt0
  -- [1] LBU x5, 0(x10)
  have hover0 : txBase.toNat + 0 < 2 ^ 64 := by omega
  have hlbu0 := bytesRegion_lbu_within .x5 .x10 txBase v5 (D + 4) txBytes 0
    (by decide) halign hlen_pos hover0 hvalid0
  have hptr : txBase + BitVec.ofNat 64 0 = txBase := base_add_zero txBase
  have hbyte : (txBytes[0]'hlen_pos).zeroExtend 64 = b.zeroExtend 64 := by
    simp only [hbytes, List.getElem_cons_zero]
  have hlbu0' : cpsTripleWithin 1 (D + 4) (D + 8)
      (CodeReq.singleton (D + 4) (.LBU .x5 .x10 (0 : BitVec 12)))
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ v5) ** bytesRegion txBase txBytes)
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ (b.zeroExtend 64)) ** bytesRegion txBase txBytes) := by
    have hpc : (D + 4) + 4 = D + 8 := by
      simp only [D, GuestAddrs.tx_type_dispatch]; decide
    rw [← hpc]
    refine cpsTripleWithin_weaken
      (fun _ hp => by rwa [hptr])
      (fun _ hq => by rwa [hptr, hbyte] at hq) hlbu0
  have hlbuE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 4) typeProg 1
      (.LBU .x5 .x10 (0 : BitVec 12))
      D4 (by rw [type_length]; decide) rfl type_bound) hlbu0'
  have hlbuF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hlbuE
  -- [2] LI x6, 192
  have hli := li_spec_gen_within .x6 v6 (192 : Word) (D + 8) (by decide)
  have hliE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 8) typeProg 2
      (.LI .x6 (192 : Word))
      D8 (by rw [type_length]; decide) rfl type_bound) hli
  have hliF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ (b.zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hliE
  -- [3] BGEU x5,x6 +40 TAKEN → LegacyLi
  have hbr3 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 12) typeProg 3
      (.BGEU .x5 .x6 (40 : BitVec 13))
      D12 (by rw [type_length]; decide) rfl type_bound)
    (bgeu_spec_gen_within .x5 .x6 (40 : BitVec 13)
      (b.zeroExtend 64) (192 : Word) (D + 12))
  have hpc3 : (D + 12) + signExtend13 (40 : BitVec 13) = LegacyLi := by
    simp only [LegacyLi, D, GuestAddrs.tx_type_dispatch]; decide
  rw [hpc3] at hbr3
  have htk3 := cpsBranchWithin_takenStripPure2 hbr3 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact (not_ult_zx_192 b hlegacy) ((sepConj_pure_right _).1 hrest).2)
  have htk3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) htk3
  have hleg :=
    typeLegacyOkRet_spec raIn txBase typePtr innerPtr oldT oldI
      txBase (BitVec.ofNat 64 txBytes.length) (b.zeroExtend 64) (192 : Word)
      txBytes hret
  -- compose
  have c01 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hnt0F hlbuF
  have c02 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hliF
  have c03 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 htk3F
  have c04 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 hleg
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c04

abbrev Type1Li : Word := D + 68
abbrev Type2Li : Word := D + 92
abbrev Type3Li : Word := D + 116
abbrev Type4Li : Word := D + 140

private theorem Type1Li_eq : Type1Li = D + BitVec.ofNat 64 (4 * 17) := by
  simp only [Type1Li, D, GuestAddrs.tx_type_dispatch]; decide
private theorem Type2Li_eq : Type2Li = D + BitVec.ofNat 64 (4 * 23) := by
  simp only [Type2Li, D, GuestAddrs.tx_type_dispatch]; decide
private theorem Type3Li_eq : Type3Li = D + BitVec.ofNat 64 (4 * 29) := by
  simp only [Type3Li, D, GuestAddrs.tx_type_dispatch]; decide
private theorem Type4Li_eq : Type4Li = D + BitVec.ofNat 64 (4 * 35) := by
  simp only [Type4Li, D, GuestAddrs.tx_type_dispatch]; decide

-- Type-1 success tail at Type1Li (instr 17–22).
set_option maxRecDepth 8000 in
theorem type1OkRet_spec
    (raIn txBase typePtr innerPtr oldT oldI a0v a1v v5 v6 : Word)
    (txBytes : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn) :
    cpsTripleWithin 6 Type1Li raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (1 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  have h0 := li_spec_gen_within .x5 v5 (1 : Word) Type1Li (by decide)
  have h0e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D Type1Li typeProg 17
      (.LI .x5 (1 : Word))
      Type1Li_eq (by rw [type_length]; decide) rfl type_bound) h0
  have h0pc : Type1Li + 4 = D + 72 := by
    simp only [Type1Li, D, GuestAddrs.tx_type_dispatch]; decide
  rw [h0pc] at h0e
  have h0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h0e
  have h1 := sd_spec_gen_within .x12 .x5 typePtr (1 : Word) oldT
    (0 : BitVec 12) (D + 72)
  rw [show typePtr + signExtend12 (0 : BitVec 12) = typePtr from by
    rw [se12_zero]; exact BitVec.add_zero typePtr] at h1
  have h1e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 72) typeProg 18
      (.SD .x12 .x5 (0 : BitVec 12))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h1
  have h1pc : (D + 72) + 4 = D + 76 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h1pc] at h1e
  have h1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x13 ↦ᵣ innerPtr) ** bytesRegion txBase txBytes **
        (innerPtr ↦ₘ oldI) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h1e
  have h2 := li_spec_gen_within .x6 v6 (1 : Word) (D + 76) (by decide)
  have h2e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 76) typeProg 19
      (.LI .x6 (1 : Word))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h2
  have h2pc : (D + 76) + 4 = D + 80 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h2pc] at h2e
  have h2F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (1 : Word)) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h2e
  have h3 := sd_spec_gen_within .x13 .x6 innerPtr (1 : Word) oldI
    (0 : BitVec 12) (D + 80)
  rw [show innerPtr + signExtend12 (0 : BitVec 12) = innerPtr from by
    rw [se12_zero]; exact BitVec.add_zero innerPtr] at h3
  have h3e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 80) typeProg 20
      (.SD .x13 .x6 (0 : BitVec 12))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h3
  have h3pc : (D + 80) + 4 = D + 84 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h3pc] at h3e
  have h3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** bytesRegion txBase txBytes **
        (typePtr ↦ₘ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h3e
  have h4 := li_spec_gen_within .x10 a0v (0 : Word) (D + 84) (by decide)
  have h4e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 84) typeProg 21
      (.LI .x10 (0 : Word))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h4
  have h4pc : (D + 84) + 4 = D + 88 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h4pc] at h4e
  have h4F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (1 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h4e
  have hexit : ((raIn + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = raIn := by
    have hz : raIn + signExtend12 (0 : BitVec 12) = raIn := by
      rw [se12_zero]; exact BitVec.add_zero raIn
    rw [hz, hret]
  have h5 : cpsTripleWithin 1 (D + 88) raIn typeCode
      (.x1 ↦ᵣ raIn) (.x1 ↦ᵣ raIn) := by
    have hj := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) (D + 88)
    rw [hexit] at hj
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 88) typeProg 22
        (.JALR .x0 .x1 (0 : BitVec 12))
        (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
        (by rw [type_length]; decide) rfl type_bound) hj
  have h5F :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (1 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h5
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h2F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 h3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 h4F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 h5F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) c05

set_option maxRecDepth 8000 in
theorem type2OkRet_spec
    (raIn txBase typePtr innerPtr oldT oldI a0v a1v v5 v6 : Word)
    (txBytes : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn) :
    cpsTripleWithin 6 Type2Li raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (2 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  have h0 := li_spec_gen_within .x5 v5 (2 : Word) Type2Li (by decide)
  have h0e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D Type2Li typeProg 23
      (.LI .x5 (2 : Word))
      Type2Li_eq (by rw [type_length]; decide) rfl type_bound) h0
  have h0pc : Type2Li + 4 = D + 96 := by
    simp only [Type2Li, D, GuestAddrs.tx_type_dispatch]; decide
  rw [h0pc] at h0e
  have h0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h0e
  have h1 := sd_spec_gen_within .x12 .x5 typePtr (2 : Word) oldT
    (0 : BitVec 12) (D + 96)
  rw [show typePtr + signExtend12 (0 : BitVec 12) = typePtr from by
    rw [se12_zero]; exact BitVec.add_zero typePtr] at h1
  have h1e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 96) typeProg 24
      (.SD .x12 .x5 (0 : BitVec 12))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h1
  have h1pc : (D + 96) + 4 = D + 100 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h1pc] at h1e
  have h1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x13 ↦ᵣ innerPtr) ** bytesRegion txBase txBytes **
        (innerPtr ↦ₘ oldI) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h1e
  have h2 := li_spec_gen_within .x6 v6 (1 : Word) (D + 100) (by decide)
  have h2e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 100) typeProg 25
      (.LI .x6 (1 : Word))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h2
  have h2pc : (D + 100) + 4 = D + 104 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h2pc] at h2e
  have h2F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (2 : Word)) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ (2 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h2e
  have h3 := sd_spec_gen_within .x13 .x6 innerPtr (1 : Word) oldI
    (0 : BitVec 12) (D + 104)
  rw [show innerPtr + signExtend12 (0 : BitVec 12) = innerPtr from by
    rw [se12_zero]; exact BitVec.add_zero innerPtr] at h3
  have h3e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 104) typeProg 26
      (.SD .x13 .x6 (0 : BitVec 12))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h3
  have h3pc : (D + 104) + 4 = D + 108 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h3pc] at h3e
  have h3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** bytesRegion txBase txBytes **
        (typePtr ↦ₘ (2 : Word)) ** (.x5 ↦ᵣ (2 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h3e
  have h4 := li_spec_gen_within .x10 a0v (0 : Word) (D + 108) (by decide)
  have h4e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 108) typeProg 27
      (.LI .x10 (0 : Word))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h4
  have h4pc : (D + 108) + 4 = D + 112 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h4pc] at h4e
  have h4F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (2 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h4e
  have hexit : ((raIn + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = raIn := by
    have hz : raIn + signExtend12 (0 : BitVec 12) = raIn := by
      rw [se12_zero]; exact BitVec.add_zero raIn
    rw [hz, hret]
  have h5 : cpsTripleWithin 1 (D + 112) raIn typeCode
      (.x1 ↦ᵣ raIn) (.x1 ↦ᵣ raIn) := by
    have hj := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) (D + 112)
    rw [hexit] at hj
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 112) typeProg 28
        (.JALR .x0 .x1 (0 : BitVec 12))
        (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
        (by rw [type_length]; decide) rfl type_bound) hj
  have h5F :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (2 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h5
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h2F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 h3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 h4F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 h5F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) c05

set_option maxRecDepth 8000 in
theorem type3OkRet_spec
    (raIn txBase typePtr innerPtr oldT oldI a0v a1v v5 v6 : Word)
    (txBytes : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn) :
    cpsTripleWithin 6 Type3Li raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (3 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (3 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  have h0 := li_spec_gen_within .x5 v5 (3 : Word) Type3Li (by decide)
  have h0e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D Type3Li typeProg 29
      (.LI .x5 (3 : Word))
      Type3Li_eq (by rw [type_length]; decide) rfl type_bound) h0
  have h0pc : Type3Li + 4 = D + 120 := by
    simp only [Type3Li, D, GuestAddrs.tx_type_dispatch]; decide
  rw [h0pc] at h0e
  have h0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h0e
  have h1 := sd_spec_gen_within .x12 .x5 typePtr (3 : Word) oldT
    (0 : BitVec 12) (D + 120)
  rw [show typePtr + signExtend12 (0 : BitVec 12) = typePtr from by
    rw [se12_zero]; exact BitVec.add_zero typePtr] at h1
  have h1e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 120) typeProg 30
      (.SD .x12 .x5 (0 : BitVec 12))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h1
  have h1pc : (D + 120) + 4 = D + 124 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h1pc] at h1e
  have h1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x13 ↦ᵣ innerPtr) ** bytesRegion txBase txBytes **
        (innerPtr ↦ₘ oldI) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h1e
  have h2 := li_spec_gen_within .x6 v6 (1 : Word) (D + 124) (by decide)
  have h2e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 124) typeProg 31
      (.LI .x6 (1 : Word))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h2
  have h2pc : (D + 124) + 4 = D + 128 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h2pc] at h2e
  have h2F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (3 : Word)) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ (3 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h2e
  have h3 := sd_spec_gen_within .x13 .x6 innerPtr (1 : Word) oldI
    (0 : BitVec 12) (D + 128)
  rw [show innerPtr + signExtend12 (0 : BitVec 12) = innerPtr from by
    rw [se12_zero]; exact BitVec.add_zero innerPtr] at h3
  have h3e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 128) typeProg 32
      (.SD .x13 .x6 (0 : BitVec 12))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h3
  have h3pc : (D + 128) + 4 = D + 132 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h3pc] at h3e
  have h3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** bytesRegion txBase txBytes **
        (typePtr ↦ₘ (3 : Word)) ** (.x5 ↦ᵣ (3 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h3e
  have h4 := li_spec_gen_within .x10 a0v (0 : Word) (D + 132) (by decide)
  have h4e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 132) typeProg 33
      (.LI .x10 (0 : Word))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h4
  have h4pc : (D + 132) + 4 = D + 136 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h4pc] at h4e
  have h4F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (3 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (3 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h4e
  have hexit : ((raIn + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = raIn := by
    have hz : raIn + signExtend12 (0 : BitVec 12) = raIn := by
      rw [se12_zero]; exact BitVec.add_zero raIn
    rw [hz, hret]
  have h5 : cpsTripleWithin 1 (D + 136) raIn typeCode
      (.x1 ↦ᵣ raIn) (.x1 ↦ᵣ raIn) := by
    have hj := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) (D + 136)
    rw [hexit] at hj
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 136) typeProg 34
        (.JALR .x0 .x1 (0 : BitVec 12))
        (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
        (by rw [type_length]; decide) rfl type_bound) hj
  have h5F :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (3 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (3 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h5
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h2F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 h3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 h4F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 h5F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) c05

set_option maxRecDepth 8000 in
theorem type4OkRet_spec
    (raIn txBase typePtr innerPtr oldT oldI a0v a1v v5 v6 : Word)
    (txBytes : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn) :
    cpsTripleWithin 6 Type4Li raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (4 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  have h0 := li_spec_gen_within .x5 v5 (4 : Word) Type4Li (by decide)
  have h0e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D Type4Li typeProg 35
      (.LI .x5 (4 : Word))
      Type4Li_eq (by rw [type_length]; decide) rfl type_bound) h0
  have h0pc : Type4Li + 4 = D + 144 := by
    simp only [Type4Li, D, GuestAddrs.tx_type_dispatch]; decide
  rw [h0pc] at h0e
  have h0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h0e
  have h1 := sd_spec_gen_within .x12 .x5 typePtr (4 : Word) oldT
    (0 : BitVec 12) (D + 144)
  rw [show typePtr + signExtend12 (0 : BitVec 12) = typePtr from by
    rw [se12_zero]; exact BitVec.add_zero typePtr] at h1
  have h1e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 144) typeProg 36
      (.SD .x12 .x5 (0 : BitVec 12))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h1
  have h1pc : (D + 144) + 4 = D + 148 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h1pc] at h1e
  have h1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x13 ↦ᵣ innerPtr) ** bytesRegion txBase txBytes **
        (innerPtr ↦ₘ oldI) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h1e
  have h2 := li_spec_gen_within .x6 v6 (1 : Word) (D + 148) (by decide)
  have h2e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 148) typeProg 37
      (.LI .x6 (1 : Word))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h2
  have h2pc : (D + 148) + 4 = D + 152 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h2pc] at h2e
  have h2F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (4 : Word)) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ (4 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h2e
  have h3 := sd_spec_gen_within .x13 .x6 innerPtr (1 : Word) oldI
    (0 : BitVec 12) (D + 152)
  rw [show innerPtr + signExtend12 (0 : BitVec 12) = innerPtr from by
    rw [se12_zero]; exact BitVec.add_zero innerPtr] at h3
  have h3e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 152) typeProg 38
      (.SD .x13 .x6 (0 : BitVec 12))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h3
  have h3pc : (D + 152) + 4 = D + 156 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h3pc] at h3e
  have h3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** bytesRegion txBase txBytes **
        (typePtr ↦ₘ (4 : Word)) ** (.x5 ↦ᵣ (4 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h3e
  have h4 := li_spec_gen_within .x10 a0v (0 : Word) (D + 156) (by decide)
  have h4e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 156) typeProg 39
      (.LI .x10 (0 : Word))
      (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
      (by rw [type_length]; decide) rfl type_bound) h4
  have h4pc : (D + 156) + 4 = D + 160 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  rw [h4pc] at h4e
  have h4F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (4 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h4e
  have hexit : ((raIn + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = raIn := by
    have hz : raIn + signExtend12 (0 : BitVec 12) = raIn := by
      rw [se12_zero]; exact BitVec.add_zero raIn
    rw [hz, hret]
  have h5 : cpsTripleWithin 1 (D + 160) raIn typeCode
      (.x1 ↦ᵣ raIn) (.x1 ↦ᵣ raIn) := by
    have hj := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) (D + 160)
    rw [hexit] at hj
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 160) typeProg 40
        (.JALR .x0 .x1 (0 : BitVec 12))
        (by simp only [D, GuestAddrs.tx_type_dispatch]; decide)
        (by rw [type_length]; decide) rfl type_bound) hj
  have h5F :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (4 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h5
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h2F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 h3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 h4F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 h5F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) c05

private theorem D16 : D + 16 = D + BitVec.ofNat 64 (4 * 4) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D20 : D + 20 = D + BitVec.ofNat 64 (4 * 5) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- Full type-1 path: non-empty, first byte = 1 → type=1, inner=1, a0=0 (12 steps).
set_option maxRecDepth 8000 in
theorem txTypeDispatch_type1_spec_within
    (raIn txBase typePtr innerPtr oldT oldI v5 v6 : Word)
    (txBytes : List (BitVec 8)) (rest : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hbytes : txBytes = (1 : BitVec 8) :: rest)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 12 D raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (1 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  have hlen_pos : 0 < txBytes.length := by simp only [hbytes, List.length_cons]; omega
  have hlen_ne : BitVec.ofNat 64 txBytes.length ≠ (0 : Word) :=
    ofNat_ne_zero (Nat.ne_of_gt hlen_pos) (by omega)
  have hb1 : (1 : BitVec 8).toNat < 192 := by decide
  have hzx1 : (((1 : BitVec 8).zeroExtend 64) : Word) = (1 : Word) := by decide
  -- [0] BEQ empty ntaken
  have hbr0 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D D typeProg 0
      (.BEQ .x11 .x0 (164 : BitVec 13))
      (by decide) (by rw [type_length]; decide) rfl type_bound)
    (beq_spec_gen_within .x11 .x0 (164 : BitVec 13)
      (BitVec.ofNat 64 txBytes.length) (0 : Word) D)
  have hnt0 := cpsBranchWithin_ntakenStripPure2 hbr0 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hlen_ne)
  have hnt0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      (by pcf) hnt0
  -- [1] LBU
  have hover0 : txBase.toNat + 0 < 2 ^ 64 := by omega
  have hlbu0 := bytesRegion_lbu_within .x5 .x10 txBase v5 (D + 4) txBytes 0
    (by decide) halign hlen_pos hover0 hvalid0
  have hptr : txBase + BitVec.ofNat 64 0 = txBase := base_add_zero txBase
  have hbyte : (txBytes[0]'hlen_pos).zeroExtend 64 = ((1 : BitVec 8).zeroExtend 64) := by
    simp only [hbytes, List.getElem_cons_zero]
  have hlbu0' : cpsTripleWithin 1 (D + 4) (D + 8)
      (CodeReq.singleton (D + 4) (.LBU .x5 .x10 (0 : BitVec 12)))
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ v5) ** bytesRegion txBase txBytes)
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ ((1 : BitVec 8).zeroExtend 64)) **
        bytesRegion txBase txBytes) := by
    have hpc : (D + 4) + 4 = D + 8 := by
      simp only [D, GuestAddrs.tx_type_dispatch]; decide
    rw [← hpc]
    refine cpsTripleWithin_weaken
      (fun _ hp => by rwa [hptr])
      (fun _ hq => by rwa [hptr, hbyte] at hq) hlbu0
  have hlbuE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 4) typeProg 1
      (.LBU .x5 .x10 (0 : BitVec 12))
      D4 (by rw [type_length]; decide) rfl type_bound) hlbu0'
  have hlbuF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hlbuE
  -- [2] LI x6, 192
  have hli192 := li_spec_gen_within .x6 v6 (192 : Word) (D + 8) (by decide)
  have hli192E := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 8) typeProg 2
      (.LI .x6 (192 : Word))
      D8 (by rw [type_length]; decide) rfl type_bound) hli192
  have hli192F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ ((1 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hli192E
  -- [3] BGEU ntaken (byte < 192)
  have hbr3 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 12) typeProg 3
      (.BGEU .x5 .x6 (40 : BitVec 13))
      D12 (by rw [type_length]; decide) rfl type_bound)
    (bgeu_spec_gen_within .x5 .x6 (40 : BitVec 13)
      ((1 : BitVec 8).zeroExtend 64) (192 : Word) (D + 12))
  have hnt3 := cpsBranchWithin_ntakenStripPure2 hbr3 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    -- taken pure is ¬ult; we have ult
    exact ((sepConj_pure_right _).1 hrest).2 (ult_zx_192 _ hb1))
  have hnt3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hnt3
  -- [4] LI x6, 1
  have hli1 := li_spec_gen_within .x6 (192 : Word) (1 : Word) (D + 16) (by decide)
  have hli1E := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 16) typeProg 4
      (.LI .x6 (1 : Word))
      D16 (by rw [type_length]; decide) rfl type_bound) hli1
  have hli1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ ((1 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hli1E
  -- [5] BEQ x5,x6 +48 TAKEN → Type1Li
  have hbr5 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 20) typeProg 5
      (.BEQ .x5 .x6 (48 : BitVec 13))
      D20 (by rw [type_length]; decide) rfl type_bound)
    (beq_spec_gen_within .x5 .x6 (48 : BitVec 13)
      ((1 : BitVec 8).zeroExtend 64) (1 : Word) (D + 20))
  have hpc5 : (D + 20) + signExtend13 (48 : BitVec 13) = Type1Li := by
    simp only [Type1Li, D, GuestAddrs.tx_type_dispatch]; decide
  rw [hpc5] at hbr5
  have htk5 := cpsBranchWithin_takenStripPure2 hbr5 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd hzx1 ((sepConj_pure_right _).1 hrest).2)
  have htk5F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) htk5
  have hret1 :=
    type1OkRet_spec raIn txBase typePtr innerPtr oldT oldI
      txBase (BitVec.ofNat 64 txBytes.length)
      ((1 : BitVec 8).zeroExtend 64) (1 : Word) txBytes hret
  -- compose 6 prefix steps + 6 ret = 12
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hnt0F hlbuF
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hli192F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 hnt3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 hli1F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 htk5F
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 hret1
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c06

private theorem D24 : D + 24 = D + BitVec.ofNat 64 (4 * 6) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D28 : D + 28 = D + BitVec.ofNat 64 (4 * 7) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- Full type-2 path (14 steps): prefix + LI1/BEQ-ntaken + LI2/BEQ-taken + type2OkRet.
set_option maxRecDepth 8000 in
theorem txTypeDispatch_type2_spec_within
    (raIn txBase typePtr innerPtr oldT oldI v5 v6 : Word)
    (txBytes : List (BitVec 8)) (rest : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hbytes : txBytes = (2 : BitVec 8) :: rest)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 14 D raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (2 : Word)) ** (innerPtr ↦ₘ (1 : Word)) **
        (.x5 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (1 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  have hlen_pos : 0 < txBytes.length := by simp only [hbytes, List.length_cons]; omega
  have hlen_ne : BitVec.ofNat 64 txBytes.length ≠ (0 : Word) :=
    ofNat_ne_zero (Nat.ne_of_gt hlen_pos) (by omega)
  have hb2 : (2 : BitVec 8).toNat < 192 := by decide
  have hzx2 : (((2 : BitVec 8).zeroExtend 64) : Word) = (2 : Word) := by decide
  have hne21 : (((2 : BitVec 8).zeroExtend 64) : Word) ≠ (1 : Word) := by decide
  -- [0] BEQ empty ntaken
  have hbr0 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D D typeProg 0
      (.BEQ .x11 .x0 (164 : BitVec 13))
      (by decide) (by rw [type_length]; decide) rfl type_bound)
    (beq_spec_gen_within .x11 .x0 (164 : BitVec 13)
      (BitVec.ofNat 64 txBytes.length) (0 : Word) D)
  have hnt0 := cpsBranchWithin_ntakenStripPure2 hbr0 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hlen_ne)
  have hnt0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      (by pcf) hnt0
  -- [1] LBU
  have hover0 : txBase.toNat + 0 < 2 ^ 64 := by omega
  have hlbu0 := bytesRegion_lbu_within .x5 .x10 txBase v5 (D + 4) txBytes 0
    (by decide) halign hlen_pos hover0 hvalid0
  have hptr : txBase + BitVec.ofNat 64 0 = txBase := base_add_zero txBase
  have hbyte : (txBytes[0]'hlen_pos).zeroExtend 64 = ((2 : BitVec 8).zeroExtend 64) := by
    simp only [hbytes, List.getElem_cons_zero]
  have hlbu0' : cpsTripleWithin 1 (D + 4) (D + 8)
      (CodeReq.singleton (D + 4) (.LBU .x5 .x10 (0 : BitVec 12)))
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ v5) ** bytesRegion txBase txBytes)
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ ((2 : BitVec 8).zeroExtend 64)) **
        bytesRegion txBase txBytes) := by
    have hpc : (D + 4) + 4 = D + 8 := by
      simp only [D, GuestAddrs.tx_type_dispatch]; decide
    rw [← hpc]
    refine cpsTripleWithin_weaken
      (fun _ hp => by rwa [hptr])
      (fun _ hq => by rwa [hptr, hbyte] at hq) hlbu0
  have hlbuE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 4) typeProg 1
      (.LBU .x5 .x10 (0 : BitVec 12))
      D4 (by rw [type_length]; decide) rfl type_bound) hlbu0'
  have hlbuF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hlbuE
  -- [2] LI 192
  have hli192 := li_spec_gen_within .x6 v6 (192 : Word) (D + 8) (by decide)
  have hli192E := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 8) typeProg 2
      (.LI .x6 (192 : Word))
      D8 (by rw [type_length]; decide) rfl type_bound) hli192
  have hli192F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ ((2 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hli192E
  -- [3] BGEU ntaken
  have hbr3 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 12) typeProg 3
      (.BGEU .x5 .x6 (40 : BitVec 13))
      D12 (by rw [type_length]; decide) rfl type_bound)
    (bgeu_spec_gen_within .x5 .x6 (40 : BitVec 13)
      ((2 : BitVec 8).zeroExtend 64) (192 : Word) (D + 12))
  have hnt3 := cpsBranchWithin_ntakenStripPure2 hbr3 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact ((sepConj_pure_right _).1 hrest).2 (ult_zx_192 _ hb2))
  have hnt3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hnt3
  -- [4] LI x6, 1
  have hli1 := li_spec_gen_within .x6 (192 : Word) (1 : Word) (D + 16) (by decide)
  have hli1E := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 16) typeProg 4
      (.LI .x6 (1 : Word))
      D16 (by rw [type_length]; decide) rfl type_bound) hli1
  have hli1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ ((2 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hli1E
  -- [5] BEQ x5,x6 +48 NTAKEN (2 ≠ 1)
  have hbr5 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 20) typeProg 5
      (.BEQ .x5 .x6 (48 : BitVec 13))
      D20 (by rw [type_length]; decide) rfl type_bound)
    (beq_spec_gen_within .x5 .x6 (48 : BitVec 13)
      ((2 : BitVec 8).zeroExtend 64) (1 : Word) (D + 20))
  have hnt5 := cpsBranchWithin_ntakenStripPure2 hbr5 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hne21)
  have hnt5F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hnt5
  -- [6] LI x6, 2
  have hli2 := li_spec_gen_within .x6 (1 : Word) (2 : Word) (D + 24) (by decide)
  have hli2E := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 24) typeProg 6
      (.LI .x6 (2 : Word))
      D24 (by rw [type_length]; decide) rfl type_bound) hli2
  have hli2F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ ((2 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hli2E
  -- [7] BEQ x5,x6 +64 TAKEN → Type2Li
  have hbr7 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 28) typeProg 7
      (.BEQ .x5 .x6 (64 : BitVec 13))
      D28 (by rw [type_length]; decide) rfl type_bound)
    (beq_spec_gen_within .x5 .x6 (64 : BitVec 13)
      ((2 : BitVec 8).zeroExtend 64) (2 : Word) (D + 28))
  have hpc7 : (D + 28) + signExtend13 (64 : BitVec 13) = Type2Li := by
    simp only [Type2Li, D, GuestAddrs.tx_type_dispatch]; decide
  rw [hpc7] at hbr7
  have htk7 := cpsBranchWithin_takenStripPure2 hbr7 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd hzx2 ((sepConj_pure_right _).1 hrest).2)
  have htk7F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) htk7
  have hret2 :=
    type2OkRet_spec raIn txBase typePtr innerPtr oldT oldI
      txBase (BitVec.ofNat 64 txBytes.length)
      ((2 : BitVec 8).zeroExtend 64) (2 : Word) txBytes hret
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hnt0F hlbuF
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hli192F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 hnt3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 hli1F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 hnt5F
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 hli2F
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 htk7F
  have c08 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c07 hret2
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c08

#print axioms typeFailRet_spec
#print axioms txTypeDispatch_empty_fail_spec_within
#print axioms typeLegacyOkRet_spec
#print axioms txTypeDispatch_legacy_spec_within
#print axioms type1OkRet_spec
#print axioms type2OkRet_spec
#print axioms type3OkRet_spec
#print axioms type4OkRet_spec
#print axioms txTypeDispatch_type1_spec_within
#print axioms txTypeDispatch_type2_spec_within

end EvmAsm.Codegen.TxTypeDispatchSpec
