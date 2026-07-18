/-
  Unknown-prefix fail path + top theorem for `tx_type_dispatch`.
  Matches prover1 `TxTypeDispatchAssumed.flat` shape (mono ≤ 256).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.LoopFuel
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchTyped
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

private theorem ofNat_ne_zero {a : Nat} (h0 : a ≠ 0) (hlt : a < 2 ^ 64) :
    BitVec.ofNat 64 a ≠ (0 : Word) := by
  intro h
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h2
  have hz : ((0 : Word).toNat) = 0 := by decide
  omega

private theorem ult_zx_192 (b : BitVec 8) (h : b.toNat < 192) :
    BitVec.ult (b.zeroExtend 64 : Word) (192 : Word) := by
  have hlt : (b.zeroExtend 64 : Word).toNat < (192 : Word).toNat := by
    have hz := SAsm.toNat_zeroExtend_byte b
    have h192 : (192 : Word).toNat = 192 := by decide
    omega
  rwa [BitVec.ult_iff_toNat_lt]

private theorem base_add_zero (base : Word) :
    base + BitVec.ofNat 64 0 = base := BitVec.add_zero base

private theorem type_bound : 4 * typeProg.length < 2 ^ 64 := by
  simp only [type_length]; decide

private theorem zx_ne_ofNat (b : BitVec 8) (n : Nat) (hn : n < 256)
    (hne : b ≠ BitVec.ofNat 8 n) :
    (b.zeroExtend 64 : Word) ≠ BitVec.ofNat 64 n := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [SAsm.toNat_zeroExtend_byte] at ht
  simp only [BitVec.toNat_ofNat] at ht
  have hmod : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  have hmod8 : n % 256 = n := Nat.mod_eq_of_lt hn
  have : b.toNat = n := by omega
  exact hne (BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega))

private theorem D4 : D + 4 = D + BitVec.ofNat 64 (4 * 1) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D8 : D + 8 = D + BitVec.ofNat 64 (4 * 2) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D12 : D + 12 = D + BitVec.ofNat 64 (4 * 3) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D16 : D + 16 = D + BitVec.ofNat 64 (4 * 4) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D20 : D + 20 = D + BitVec.ofNat 64 (4 * 5) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D24 : D + 24 = D + BitVec.ofNat 64 (4 * 6) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D28 : D + 28 = D + BitVec.ofNat 64 (4 * 7) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D32 : D + 32 = D + BitVec.ofNat 64 (4 * 8) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D36 : D + 36 = D + BitVec.ofNat 64 (4 * 9) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D40 : D + 40 = D + BitVec.ofNat 64 (4 * 10) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D44 : D + 44 = D + BitVec.ofNat 64 (4 * 11) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem D48 : D + 48 = D + BitVec.ofNat 64 (4 * 12) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- Unknown prefix fail (17 steps): all typed BEQs ntaken + JAL → FailLi → a0=1.
set_option maxRecDepth 8000 in
theorem txTypeDispatch_unknown_fail_spec_within
    (raIn txBase typePtr innerPtr oldT oldI v5 v6 : Word)
    (txBytes : List (BitVec 8)) (b : BitVec 8) (rest : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hbytes : txBytes = b :: rest)
    (hult : b.toNat < 192)
    (hne1 : b ≠ (1 : BitVec 8))
    (hne2 : b ≠ (2 : BitVec 8))
    (hne3 : b ≠ (3 : BitVec 8))
    (hne4 : b ≠ (4 : BitVec 8))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 17 D raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (1 : Word)) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (0 : Word)) ** (innerPtr ↦ₘ (0 : Word)) **
        (.x5 ↦ᵣ (b.zeroExtend 64 : Word)) ** (.x6 ↦ᵣ (4 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  have hlen_pos : 0 < txBytes.length := by simp only [hbytes, List.length_cons]; omega
  have hlen_ne : BitVec.ofNat 64 txBytes.length ≠ (0 : Word) :=
    ofNat_ne_zero (Nat.ne_of_gt hlen_pos) (by omega)
  have hne_zx1 := zx_ne_ofNat b 1 (by decide) hne1
  have hne_zx2 := zx_ne_ofNat b 2 (by decide) hne2
  have hne_zx3 := zx_ne_ofNat b 3 (by decide) hne3
  have hne_zx4 := zx_ne_ofNat b 4 (by decide) hne4
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
  have hbyte : (txBytes[0]'hlen_pos).zeroExtend 64 = (b.zeroExtend 64 : Word) := by
    simp only [hbytes, List.getElem_cons_zero]
  have hlbu0' : cpsTripleWithin 1 (D + 4) (D + 8)
      (CodeReq.singleton (D + 4) (.LBU .x5 .x10 (0 : BitVec 12)))
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ v5) ** bytesRegion txBase txBytes)
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ (b.zeroExtend 64 : Word)) **
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
        (.x5 ↦ᵣ (b.zeroExtend 64 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hli192E
  -- [3] BGEU ntaken
  have hbr3 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 12) typeProg 3
      (.BGEU .x5 .x6 (40 : BitVec 13))
      D12 (by rw [type_length]; decide) rfl type_bound)
    (bgeu_spec_gen_within .x5 .x6 (40 : BitVec 13)
      (b.zeroExtend 64 : Word) (192 : Word) (D + 12))
  have hnt3 := cpsBranchWithin_ntakenStripPure2 hbr3 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact ((sepConj_pure_right _).1 hrest).2 (ult_zx_192 b hult))
  have hnt3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hnt3
  -- [4] LI 1
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
        (.x5 ↦ᵣ (b.zeroExtend 64 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hli1E
  -- [5] BEQ type1 ntaken
  have hbr5 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 20) typeProg 5
      (.BEQ .x5 .x6 (48 : BitVec 13))
      D20 (by rw [type_length]; decide) rfl type_bound)
    (beq_spec_gen_within .x5 .x6 (48 : BitVec 13)
      (b.zeroExtend 64 : Word) (1 : Word) (D + 20))
  have hnt5 := cpsBranchWithin_ntakenStripPure2 hbr5 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hne_zx1)
  have hnt5F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hnt5
  -- [6] LI 2
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
        (.x5 ↦ᵣ (b.zeroExtend 64 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hli2E
  -- [7] BEQ type2 ntaken
  have hbr7 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 28) typeProg 7
      (.BEQ .x5 .x6 (64 : BitVec 13))
      D28 (by rw [type_length]; decide) rfl type_bound)
    (beq_spec_gen_within .x5 .x6 (64 : BitVec 13)
      (b.zeroExtend 64 : Word) (2 : Word) (D + 28))
  have hnt7 := cpsBranchWithin_ntakenStripPure2 hbr7 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hne_zx2)
  have hnt7F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hnt7
  -- [8] LI 3
  have hli3 := li_spec_gen_within .x6 (2 : Word) (3 : Word) (D + 32) (by decide)
  have hli3E := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 32) typeProg 8
      (.LI .x6 (3 : Word))
      D32 (by rw [type_length]; decide) rfl type_bound) hli3
  have hli3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ (b.zeroExtend 64 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hli3E
  -- [9] BEQ type3 ntaken
  have hbr9 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 36) typeProg 9
      (.BEQ .x5 .x6 (80 : BitVec 13))
      D36 (by rw [type_length]; decide) rfl type_bound)
    (beq_spec_gen_within .x5 .x6 (80 : BitVec 13)
      (b.zeroExtend 64 : Word) (3 : Word) (D + 36))
  have hnt9 := cpsBranchWithin_ntakenStripPure2 hbr9 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hne_zx3)
  have hnt9F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hnt9
  -- [10] LI 4
  have hli4 := li_spec_gen_within .x6 (3 : Word) (4 : Word) (D + 40) (by decide)
  have hli4E := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 40) typeProg 10
      (.LI .x6 (4 : Word))
      D40 (by rw [type_length]; decide) rfl type_bound) hli4
  have hli4F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ (b.zeroExtend 64 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hli4E
  -- [11] BEQ type4 ntaken
  have hbr11 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 44) typeProg 11
      (.BEQ .x5 .x6 (96 : BitVec 13))
      D44 (by rw [type_length]; decide) rfl type_bound)
    (beq_spec_gen_within .x5 .x6 (96 : BitVec 13)
      (b.zeroExtend 64 : Word) (4 : Word) (D + 44))
  have hnt11 := cpsBranchWithin_ntakenStripPure2 hbr11 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hne_zx4)
  have hnt11F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hnt11
  -- [12] JAL +116 → FailLi
  have hjal0 := jal_x0_spec_gen_within (116 : BitVec 21) (D + 48)
  have hpcJ : (D + 48) + signExtend21 (116 : BitVec 21) = FailLi := by
    simp only [FailLi, D, GuestAddrs.tx_type_dispatch]; decide
  rw [hpcJ] at hjal0
  have hjalE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 48) typeProg 12
      (.JAL .x0 (116 : BitVec 21))
      D48 (by rw [type_length]; decide) rfl type_bound) hjal0
  -- frameR emp ** ambient; cancel emp via sepConj_emp_left'
  let ambient : Assertion :=
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) **
      (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
      (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
      bytesRegion txBase txBytes **
      (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
      (.x5 ↦ᵣ (b.zeroExtend 64 : Word)) ** (.x6 ↦ᵣ (4 : Word)) **
      (.x0 ↦ᵣ (0 : Word)))
  have hjalF0 := cpsTripleWithin_frameR ambient (by pcf) hjalE
  have hjalF : cpsTripleWithin 1 (D + 48) FailLi typeCode ambient ambient := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by rwa [sepConj_emp_left' ambient])
      (fun _ hq => by rwa [sepConj_emp_left' ambient] at hq) hjalF0
  have hfail :=
    typeFailRet_spec raIn txBase typePtr innerPtr oldT oldI
      txBase (BitVec.ofNat 64 txBytes.length)
      (b.zeroExtend 64 : Word) (4 : Word) txBytes hret
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hnt0F hlbuF
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hli192F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 hnt3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 hli1F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 hnt5F
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 hli2F
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 hnt7F
  have c08 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c07 hli3F
  have c09 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c08 hnt9F
  have c10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c09 hli4F
  have c11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c10 hnt11F
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c11 hjalF
  have c13 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hfail
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c13

#print axioms txTypeDispatch_unknown_fail_spec_within

/-- Flat pre matching prover1 `TxTypeDispatchAssumed`. -/
def typeFlatPre (raIn txBase txLen typePtr innerPtr t0Old t1Old typeOld innerOld : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLen) **
    (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
    (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion txBase txBytes ** (typePtr ↦ₘ typeOld) ** (innerPtr ↦ₘ innerOld))

/-- Flat post matching prover1 `TxTypeDispatchAssumed` after a1–a3 regOwn fix:
    status/type/inner from `teerTxTypeDispatch`; temps + a1–a3 regOwn. -/
def typeFlatPostOf (raIn txBase typePtr innerPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  (regOwn .x5 ** regOwn .x6 ** (.x1 ↦ᵣ raIn) ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion txBase txBytes **
    (.x10 ↦ᵣ (teerTxTypeDispatch txBytes).1) **
    (typePtr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
    (innerPtr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13)

private theorem teer_empty : teerTxTypeDispatch ([] : List (BitVec 8)) = (1, 0, 0) := rfl
private theorem teer_legacy (b : BitVec 8) (rest : List (BitVec 8)) (h : 192 ≤ b.toNat) :
    teerTxTypeDispatch (b :: rest) = (0, 0, 0) := by
  simp only [teerTxTypeDispatch, h, ↓reduceIte]
private theorem teer_type1 (rest : List (BitVec 8)) :
    teerTxTypeDispatch ((1 : BitVec 8) :: rest) = (0, 1, 1) := by
  simp only [teerTxTypeDispatch]; decide
private theorem teer_type2 (rest : List (BitVec 8)) :
    teerTxTypeDispatch ((2 : BitVec 8) :: rest) = (0, 2, 1) := by
  simp only [teerTxTypeDispatch]; decide
private theorem teer_type3 (rest : List (BitVec 8)) :
    teerTxTypeDispatch ((3 : BitVec 8) :: rest) = (0, 3, 1) := by
  simp only [teerTxTypeDispatch]; decide
private theorem teer_type4 (rest : List (BitVec 8)) :
    teerTxTypeDispatch ((4 : BitVec 8) :: rest) = (0, 4, 1) := by
  simp only [teerTxTypeDispatch]; decide
private theorem teer_unknown (b : BitVec 8) (rest : List (BitVec 8))
    (hult : b.toNat < 192)
    (hne1 : b ≠ (1 : BitVec 8)) (hne2 : b ≠ (2 : BitVec 8))
    (hne3 : b ≠ (3 : BitVec 8)) (hne4 : b ≠ (4 : BitVec 8)) :
    teerTxTypeDispatch (b :: rest) = (1, 0, 0) := by
  simp only [teerTxTypeDispatch]
  have hnot : ¬ (192 ≤ b.toNat) := Nat.not_le_of_gt hult
  simp only [hnot, ↓reduceIte, hne1, hne2, hne3, hne4, ↓reduceIte]

private theorem arm_post_to_flat
    (raIn txBase typePtr innerPtr status typeW innerW v5 v6 txLen : Word)
    (txBytes : List (BitVec 8))
    (hstatus : status = (teerTxTypeDispatch txBytes).1)
    (htype : typeW = (teerTxTypeDispatch txBytes).2.1)
    (hinner : innerW = (teerTxTypeDispatch txBytes).2.2) :
    ∀ h,
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ txLen) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ typeW) ** (innerPtr ↦ₘ innerW) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word))) h →
      typeFlatPostOf raIn txBase typePtr innerPtr txBytes h := by
  intro h hp
  simp only [typeFlatPostOf]
  have hp' :
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ raIn) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ (teerTxTypeDispatch txBytes).1) **
        (typePtr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (innerPtr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        (.x11 ↦ᵣ txLen) ** (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr)) h := by
    have hp0 :
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ raIn) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ status) ** (typePtr ↦ₘ typeW) ** (innerPtr ↦ₘ innerW) **
          (.x11 ↦ᵣ txLen) ** (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr)) h := by
      xperm_hyp hp
    rwa [hstatus, htype, hinner] at hp0
  exact sepConj_mono (regIs_to_regOwn .x5 v5)
    (sepConj_mono (regIs_to_regOwn .x6 v6)
      (sepConj_mono (fun _ hq => hq)
        (sepConj_mono (fun _ hq => hq)
          (sepConj_mono (fun _ hq => hq)
            (sepConj_mono (fun _ hq => hq)
              (sepConj_mono (fun _ hq => hq)
                (sepConj_mono (fun _ hq => hq)
                  (sepConj_mono (regIs_to_regOwn .x11 txLen)
                    (sepConj_mono (regIs_to_regOwn .x12 typePtr)
                      (regIs_to_regOwn .x13 innerPtr)))))))))) h hp'

set_option maxRecDepth 8000 in
/-- Top-level leaf Spec: classification matches `teerTxTypeDispatch`, step
    budget ≤ `nTxTypeDispatchSteps` (256). classical-3 only. -/
theorem txTypeDispatch_spec_within
    (raIn txBase typePtr innerPtr t0Old t1Old typeOld innerOld : Word)
    (txBytes : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : txBytes.length = 0 ∨
      isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin nTxTypeDispatchSteps D raIn typeCode
      (typeFlatPre raIn txBase (BitVec.ofNat 64 txBytes.length) typePtr innerPtr
        t0Old t1Old typeOld innerOld txBytes)
      (typeFlatPostOf raIn txBase typePtr innerPtr txBytes) := by
  match txBytes with
  | [] =>
    have h0 :=
      txTypeDispatch_empty_fail_spec_within raIn txBase typePtr innerPtr
        typeOld innerOld t0Old t1Old [] hret rfl
    have h0' := cpsTripleWithin_mono_nSteps (nSteps := 5) (nSteps' := nTxTypeDispatchSteps)
      (by simp only [nTxTypeDispatchSteps]; omega) h0
    have hlen0 : BitVec.ofNat 64 (List.length ([] : List (BitVec 8))) = (0 : Word) := by decide
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [typeFlatPre, hlen0] at hp
      xperm_hyp hp)
      (arm_post_to_flat raIn txBase typePtr innerPtr 1 0 0 t0Old t1Old
        (0 : Word) [] (by simp [teer_empty]) (by simp [teer_empty])
        (by simp [teer_empty])) h0'
  | b :: rest =>
    have hlen_pos : 0 < (b :: rest).length := by simp
    have hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true := by
      cases hvalid0 with
      | inl h => simp [h] at hlen_pos
      | inr h => exact h
    by_cases hleg : 192 ≤ b.toNat
    · have h0 :=
        txTypeDispatch_legacy_spec_within raIn txBase typePtr innerPtr
          typeOld innerOld t0Old t1Old (b :: rest) b rest hret rfl hleg
          halign hover hvalid
      have h0' := cpsTripleWithin_mono_nSteps (nSteps := 8) (nSteps' := nTxTypeDispatchSteps)
        (by simp only [nTxTypeDispatchSteps]; omega) h0
      refine cpsTripleWithin_weaken (fun _ hp => by
        simp only [typeFlatPre] at hp ⊢; xperm_hyp hp)
        (arm_post_to_flat raIn txBase typePtr innerPtr 0 0 0
          (b.zeroExtend 64) (192 : Word)
          (BitVec.ofNat 64 (b :: rest).length) (b :: rest)
          (by rw [teer_legacy b rest hleg]) (by rw [teer_legacy b rest hleg])
          (by rw [teer_legacy b rest hleg])) h0'
    · have hult : b.toNat < 192 := Nat.lt_of_not_ge hleg
      by_cases h1 : b = (1 : BitVec 8)
      · subst h1
        have h0 :=
          txTypeDispatch_type1_spec_within raIn txBase typePtr innerPtr
            typeOld innerOld t0Old t1Old (1 :: rest) rest hret rfl
            halign hover hvalid
        have h0' := cpsTripleWithin_mono_nSteps (nSteps := 12) (nSteps' := nTxTypeDispatchSteps)
          (by simp only [nTxTypeDispatchSteps]; omega) h0
        refine cpsTripleWithin_weaken (fun _ hp => by
          simp only [typeFlatPre] at hp ⊢; xperm_hyp hp)
          (arm_post_to_flat raIn txBase typePtr innerPtr 0 1 1
            (1 : Word) (1 : Word)
            (BitVec.ofNat 64 (1 :: rest).length) (1 :: rest)
            (by rw [teer_type1]) (by rw [teer_type1]) (by rw [teer_type1])) h0'
      · by_cases h2 : b = (2 : BitVec 8)
        · subst h2
          have h0 :=
            txTypeDispatch_type2_spec_within raIn txBase typePtr innerPtr
              typeOld innerOld t0Old t1Old (2 :: rest) rest hret rfl
              halign hover hvalid
          have h0' := cpsTripleWithin_mono_nSteps (nSteps := 14) (nSteps' := nTxTypeDispatchSteps)
            (by simp only [nTxTypeDispatchSteps]; omega) h0
          refine cpsTripleWithin_weaken (fun _ hp => by
            simp only [typeFlatPre] at hp ⊢; xperm_hyp hp)
            (arm_post_to_flat raIn txBase typePtr innerPtr 0 2 1
              (2 : Word) (1 : Word)
              (BitVec.ofNat 64 (2 :: rest).length) (2 :: rest)
              (by rw [teer_type2]) (by rw [teer_type2]) (by rw [teer_type2])) h0'
        · by_cases h3 : b = (3 : BitVec 8)
          · subst h3
            have h0 :=
              txTypeDispatch_type3_spec_within raIn txBase typePtr innerPtr
                typeOld innerOld t0Old t1Old (3 :: rest) rest hret rfl
                halign hover hvalid
            have h0' := cpsTripleWithin_mono_nSteps (nSteps := 16) (nSteps' := nTxTypeDispatchSteps)
              (by simp only [nTxTypeDispatchSteps]; omega) h0
            refine cpsTripleWithin_weaken (fun _ hp => by
              simp only [typeFlatPre] at hp ⊢; xperm_hyp hp)
              (arm_post_to_flat raIn txBase typePtr innerPtr 0 3 1
                (3 : Word) (1 : Word)
                (BitVec.ofNat 64 (3 :: rest).length) (3 :: rest)
                (by rw [teer_type3]) (by rw [teer_type3]) (by rw [teer_type3])) h0'
          · by_cases h4 : b = (4 : BitVec 8)
            · subst h4
              have h0 :=
                txTypeDispatch_type4_spec_within raIn txBase typePtr innerPtr
                  typeOld innerOld t0Old t1Old (4 :: rest) rest hret rfl
                  halign hover hvalid
              have h0' := cpsTripleWithin_mono_nSteps (nSteps := 18) (nSteps' := nTxTypeDispatchSteps)
                (by simp only [nTxTypeDispatchSteps]; omega) h0
              refine cpsTripleWithin_weaken (fun _ hp => by
                simp only [typeFlatPre] at hp ⊢; xperm_hyp hp)
                (arm_post_to_flat raIn txBase typePtr innerPtr 0 4 1
                  (4 : Word) (1 : Word)
                  (BitVec.ofNat 64 (4 :: rest).length) (4 :: rest)
                  (by rw [teer_type4]) (by rw [teer_type4]) (by rw [teer_type4])) h0'
            · have h0 :=
                txTypeDispatch_unknown_fail_spec_within raIn txBase typePtr innerPtr
                  typeOld innerOld t0Old t1Old (b :: rest) b rest hret rfl
                  hult h1 h2 h3 h4 halign hover hvalid
              have h0' := cpsTripleWithin_mono_nSteps (nSteps := 17) (nSteps' := nTxTypeDispatchSteps)
                (by simp only [nTxTypeDispatchSteps]; omega) h0
              refine cpsTripleWithin_weaken (fun _ hp => by
                simp only [typeFlatPre] at hp ⊢; xperm_hyp hp)
                (arm_post_to_flat raIn txBase typePtr innerPtr 1 0 0
                  (b.zeroExtend 64) (4 : Word)
                  (BitVec.ofNat 64 (b :: rest).length) (b :: rest)
                  (by rw [teer_unknown b rest hult h1 h2 h3 h4])
                  (by rw [teer_unknown b rest hult h1 h2 h3 h4])
                  (by rw [teer_unknown b rest hult h1 h2 h3 h4])) h0'

#print axioms txTypeDispatch_spec_within

end EvmAsm.Codegen.TxTypeDispatchSpec
