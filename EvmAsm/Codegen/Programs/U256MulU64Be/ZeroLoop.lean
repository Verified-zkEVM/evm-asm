/-
Copyright (c) 2026 zksecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: k3
-/
import EvmAsm.Codegen.Programs.U256MulU64Be.Common

/-!
# u256_mul_u64_be — zero-fill loop (prog[12..18], offsets +48..+72)

Five SDs zero the five dwords of the `u256m_acc` scratch cell.  The loop is a
single-exit countdown (`x6 = 5 - k`, cursor `x5 = accBase + 8k`), proven with
`retLoop_spec`; the accumulator bytes are tracked functionally by `zeroFilled`
so each SD's post bytes are definitional.
-/

namespace EvmAsm.Codegen.U256MulU64Be

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-- Bytes of the accumulator after `k` iterations of the zero loop, starting
from `bs`: dword slots `0..k-1` overwritten with zeros. -/
def zeroFilled (bs : List (BitVec 8)) : Nat → List (BitVec 8)
  | 0 => bs
  | k + 1 => Rv64.setBytes (zeroFilled bs k) (8 * k) (Rv64.dwordBytes (0 : Word))

@[simp] theorem zeroFilled_zero (bs : List (BitVec 8)) : zeroFilled bs 0 = bs := rfl

@[simp] theorem zeroFilled_succ (bs : List (BitVec 8)) (k : Nat) :
    zeroFilled bs (k + 1) = Rv64.setBytes (zeroFilled bs k) (8 * k) (Rv64.dwordBytes (0 : Word)) := rfl

theorem length_zeroFilled (bs : List (BitVec 8)) (k : Nat) :
    (zeroFilled bs k).length = bs.length := by
  induction k with
  | zero => rfl
  | succ k ih => simp [zeroFilled_succ, ih]

/-- SD with offset 0 whose base register holds `regionBase + 8*q`: the q-th
dword slot of a `bytesRegion` is overwritten with `v_data`.  Cursor companion
of `bytesRegion_ld_cursor_within`. -/
theorem bytesRegion_sd_cursor_within (rs1 rs2 : Reg) (regionBase v_data : Word)
    (base : Word) (bs : List (BitVec 8)) (q : Nat)
    (hq : 8 * q + 8 ≤ bs.length) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD rs1 rs2 (0 : BitVec 12)))
      ((rs1 ↦ᵣ regionBase + BitVec.ofNat 64 (8 * q)) **
        (rs2 ↦ᵣ v_data) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ regionBase + BitVec.ofNat 64 (8 * q)) **
        (rs2 ↦ᵣ v_data) **
          bytesRegion regionBase (Rv64.setBytes bs (8 * q) (Rv64.dwordBytes v_data))) := by
  obtain ⟨front, rest, hfpc, hrpc, hpre, hpost⟩ := bytesRegion_dword_at_setBytes regionBase bs
    (Rv64.dwordBytes v_data) q 0
    (by intro h; have h8 := Rv64.length_dwordBytes v_data; simp [h] at h8)
    (by simp) (by simpa using hq)
  simp only [Nat.add_zero] at hpost
  have hsd := sd_spec_within rs1 rs2 (regionBase + BitVec.ofNat 64 (8 * q)) v_data
    (Rv64.packBytes ((bs.drop (8 * q)).take 8)) (0 : BitVec 12) base
  simp only [Rv64.signExtend12_0] at hsd
  simp only [show ∀ x : Word, x + 0 = x from fun _ => by simp] at hsd
  refine cpsTripleWithin_weaken ?_ ?_
    (cpsTripleWithin_frameR front hfpc (cpsTripleWithin_frameR rest hrpc hsd)) <;> intro s hs
  · rw [hpre] at hs; xperm_hyp hs
  · rw [hpost, ← Rv64.packBytes_setBytes_dword _ v_data (by
      simp only [List.length_take, List.length_drop]; omega)]
    xperm_hyp hs

-- ============================================================
-- §2  Byte characterization of `zeroFilled`
-- ============================================================

theorem getByteAt_dwordBytes_zero (m : Nat) :
    Rv64.getByteAt (Rv64.dwordBytes (0 : Word)) m = 0 := by
  rw [Rv64.getByteAt]
  split
  · rename_i h
    rw [Rv64.length_dwordBytes] at h
    interval_cases m <;> rfl
  · rfl

theorem getByteAt_zeroFilled (bs : List (BitVec 8)) (k j : Nat) (hk8 : 8 * k ≤ bs.length) :
    Rv64.getByteAt (zeroFilled bs k) j =
      if j < 8 * k then 0 else Rv64.getByteAt bs j := by
  induction k with
  | zero => rw [if_neg (by omega), show zeroFilled bs 0 = bs from rfl]
  | succ k ih =>
      have hdlen : (Rv64.dwordBytes (0 : Word)).length = 8 := Rv64.length_dwordBytes _
      rw [zeroFilled_succ, Rv64.getByteAt_setBytes _ _ _ _ (by
        rw [length_zeroFilled, hdlen]; omega), hdlen,
        getByteAt_dwordBytes_zero, ih (by omega)]
      by_cases h1 : j < 8 * (k + 1)
      · rw [if_pos h1]
        by_cases h2 : 8 * k ≤ j
        · rw [if_pos ⟨h2, by omega⟩]
        · rw [if_neg (by omega), if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega), if_neg (by omega)]

theorem zeroFilled_five (bs : List (BitVec 8)) (hlen : bs.length = 40) :
    zeroFilled bs 5 = List.replicate 40 (0 : BitVec 8) := by
  apply List.ext_getElem (by rw [length_zeroFilled, hlen, List.length_replicate])
  intro i hi1 _
  rw [List.getElem_replicate]
  have hi40 : i < 40 := by rwa [length_zeroFilled, hlen] at hi1
  have hz : Rv64.getByteAt (zeroFilled bs 5) i = 0 := by
    rw [getByteAt_zeroFilled bs 5 i (by omega)]
    exact if_pos (by omega)
  rwa [Rv64.getByteAt, dif_pos hi1] at hz

theorem leBytesToNat_replicate_zero (n : Nat) :
    leBytesToNat (List.replicate n (0 : BitVec 8)) = 0 := by
  apply leBytesToNat_eq_zero_of_all_zero
  intro b hb
  rw [List.mem_replicate] at hb
  rw [hb.2]
  rfl

-- ============================================================
-- §3  Word helpers
-- ============================================================

theorem zeroCtr_dec (k : Nat) (hk : k < 5) :
    BitVec.ofNat 64 (5 - k) + Rv64.signExtend12 (-1 : BitVec 12) =
      BitVec.ofNat 64 (5 - (k + 1)) := by
  rw [show Rv64.signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  have e1 : (BitVec.ofNat 64 (5 - k)).toNat = 5 - k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have e2 : (BitVec.ofNat 64 (5 - (k + 1))).toNat = 5 - (k + 1) := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have e3 : ((-1 : Word)).toNat = 2 ^ 64 - 1 := by decide
  rw [BitVec.toNat_add, e1, e2, e3]
  omega

theorem zeroCtr_ne (k : Nat) (hk : k < 5) : BitVec.ofNat 64 (5 - k) ≠ 0 := by
  intro h0
  have h := congrArg BitVec.toNat h0
  simp [BitVec.toNat_ofNat] at h
  omega

theorem accCursor_succ (k : Nat) :
    accBase + BitVec.ofNat 64 (8 * k) + Rv64.signExtend12 (8 : BitVec 12) =
      accBase + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [show Rv64.signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    BitVec.add_assoc, show (8 : Word) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
    show 8 * k + 8 = 8 * (k + 1) from by omega]

-- ============================================================
-- §4  The zero loop
-- ============================================================

/-- Zero-loop invariant: after `k` stores, the first `k` dword slots of the
accumulator are zeroed.  Register facts mirror the prologue post. -/
def zeroInv (spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 : Word)
    (accBytes₀ : List (BitVec 8)) (k : Nat) : Assertion :=
  (.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) ** (.x18 ↦ᵣ outPtr) **
    (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ aPtr) **
    (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (accBase + BitVec.ofNat 64 (8 * k))) **
    (.x6 ↦ᵣ BitVec.ofNat 64 (5 - k)) ** bytesRegion accBase (zeroFilled accBytes₀ k) **
    frameSlots spNew vRa v8 v9 v18 v19 v20

/-- One iteration: guard (counter nonzero), one zeroing SD, cursor/counter
updates, back-edge.  The taken (exit) arm is vacuous under `hk`. -/
theorem zeroIter_spec (spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 : Word)
    (accBytes₀ : List (BitVec 8)) (hlen : accBytes₀.length = 40)
    (k : Nat) (hk : k < 5) :
    cpsBranchWithin 5 (mulBase + 56) mulCR
      (zeroInv spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 accBytes₀ k)
      (mulBase + 76) (zeroInv spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 accBytes₀ 5)
      (mulBase + 56) (zeroInv spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 accBytes₀ (k + 1)) := by
  unfold zeroInv
  have hbeq := cpsBranchWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (h := beq_spec_gen_within .x6 .x0 (20 : BitVec 13) (BitVec.ofNat 64 (5 - k)) 0 (mulBase + 56))
  rw [show mulBase + 56 + Rv64.signExtend13 (20 : BitVec 13) = mulBase + 76 from by decide] at hbeq
  have hbeqF := cpsBranchWithin_frameR
    ((.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) ** (.x18 ↦ᵣ outPtr) **
      (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ aPtr) ** (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) **
      (.x5 ↦ᵣ (accBase + BitVec.ofNat 64 (8 * k))) **
      bytesRegion accBase (zeroFilled accBytes₀ k) ** frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) hbeq
  have hsd := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (h := bytesRegion_sd_cursor_within .x5 .x0 accBase 0 (mulBase + 60) (zeroFilled accBytes₀ k) k
      (by rw [length_zeroFilled, hlen]; omega))
  have hsdF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) ** (.x18 ↦ᵣ outPtr) **
      (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ aPtr) ** (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) **
      (.x6 ↦ᵣ BitVec.ofNat 64 (5 - k)) ** frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) hsd
  have haddi5 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (h := addi_spec_gen_same_within .x5 (accBase + BitVec.ofNat 64 (8 * k)) (8 : BitVec 12)
      (mulBase + 64) (by decide))
  rw [show mulBase + 64 + 4 = mulBase + 68 from by decide, accCursor_succ] at haddi5
  have haddi5F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) ** (.x18 ↦ᵣ outPtr) **
      (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ aPtr) **
      (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** (.x6 ↦ᵣ BitVec.ofNat 64 (5 - k)) **
      bytesRegion accBase (Rv64.setBytes (zeroFilled accBytes₀ k) (8 * k) (Rv64.dwordBytes 0)) **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) haddi5
  have haddi6 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (h := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (5 - k)) (-1 : BitVec 12)
      (mulBase + 68) (by decide))
  rw [show mulBase + 68 + 4 = mulBase + 72 from by decide, zeroCtr_dec k hk] at haddi6
  have haddi6F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) ** (.x18 ↦ᵣ outPtr) **
      (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ aPtr) **
      (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (accBase + BitVec.ofNat 64 (8 * (k + 1)))) **
      bytesRegion accBase (Rv64.setBytes (zeroFilled accBytes₀ k) (8 * k) (Rv64.dwordBytes 0)) **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) haddi6
  have hjal := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (h := jal_x0_spec_gen_within (-16 : BitVec 21) (mulBase + 72))
  rw [show mulBase + 72 + Rv64.signExtend21 (-16 : BitVec 21) = mulBase + 56 from by decide] at hjal
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) ** (.x18 ↦ᵣ outPtr) **
      (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ aPtr) **
      (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (accBase + BitVec.ofNat 64 (8 * (k + 1)))) **
      (.x6 ↦ᵣ BitVec.ofNat 64 (5 - (k + 1))) **
      bytesRegion accBase (Rv64.setBytes (zeroFilled accBytes₀ k) (8 * k) (Rv64.dwordBytes 0)) **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) hjal
  rw [sepConj_emp_left'] at hjalF
  have hbody := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsdF haddi5F)
      haddi6F)
    hjalF
  refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_merge_branch_same_cr (m := 4) hbeqF ?taken ?fall)
  case taken =>
    refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_pure_pre
        (H := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (5 - k)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) **
          (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ aPtr) **
          (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (accBase + BitVec.ofNat 64 (8 * k))) **
          bytesRegion accBase (zeroFilled accBytes₀ k) **
          frameSlots spNew vRa v8 v9 v18 v19 v20))
        (fun hc => absurd hc (zeroCtr_ne k hk)))
  case fall =>
    refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_pure_pre
        (H := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (5 - k)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) **
          (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ aPtr) **
          (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (accBase + BitVec.ofNat 64 (8 * k))) **
          bytesRegion accBase (zeroFilled accBytes₀ k) **
          frameSlots spNew vRa v8 v9 v18 v19 v20))
        (fun _hne => ?_))
    refine cpsTripleWithin_as_cpsBranchWithin_right (mulBase + 76)
      (zeroInv spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 accBytes₀ 5) ?_
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => ?_) hbody
    rw [zeroFilled_succ]
    xperm_hyp hq

/-- Guard fires at counter 0: one step to the loop exit. -/
theorem zeroExh_spec (spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 : Word)
    (accBytes₀ : List (BitVec 8)) :
    cpsTripleWithin 1 (mulBase + 56) (mulBase + 76) mulCR
      (zeroInv spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 accBytes₀ 5)
      (zeroInv spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 accBytes₀ 5) := by
  unfold zeroInv
  have hbeq := cpsBranchWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (h := beq_spec_gen_within .x6 .x0 (20 : BitVec 13) (BitVec.ofNat 64 (5 - 5)) 0 (mulBase + 56))
  rw [show mulBase + 56 + Rv64.signExtend13 (20 : BitVec 13) = mulBase + 76 from by decide] at hbeq
  have hbeqF := cpsBranchWithin_frameR
    ((.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) ** (.x18 ↦ᵣ outPtr) **
      (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ aPtr) ** (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) **
      (.x5 ↦ᵣ (accBase + BitVec.ofNat 64 (8 * 5))) **
      bytesRegion accBase (zeroFilled accBytes₀ 5) ** frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) hbeq
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsBranchWithin_merge_same_cr (nSteps2 := 0) hbeqF ?taken ?fall)
  case taken =>
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (cpsTripleWithin_pure_pre
        (H := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (5 - 5)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) **
          (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ aPtr) **
          (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (accBase + BitVec.ofNat 64 (8 * 5))) **
          bytesRegion accBase (zeroFilled accBytes₀ 5) **
          frameSlots spNew vRa v8 v9 v18 v19 v20 : Assertion))
        (fun (_ : BitVec.ofNat 64 (5 - 5) = 0) => ?_))
    exact cpsTripleWithin_extend_code (cr' := mulCR)
      (hmono := fun a i h => by simp [CodeReq.empty] at h)
      (h := cpsTripleWithin_refl (fun _ hp => by xperm_hyp hp))
  case fall =>
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (cpsTripleWithin_pure_pre
        (H := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (5 - 5)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) **
          (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ aPtr) **
          (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (accBase + BitVec.ofNat 64 (8 * 5))) **
          bytesRegion accBase (zeroFilled accBytes₀ 5) **
          frameSlots spNew vRa v8 v9 v18 v19 v20 : Assertion))
        (fun (hne : BitVec.ofNat 64 (5 - 5) ≠ 0) => absurd (by decide) hne))

/-- The full zero loop: init (MV + LI), then the 5-iteration countdown. -/
theorem zeroLoop_spec (spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 v5 v6 : Word)
    (accBytes₀ : List (BitVec 8)) (hlen : accBytes₀.length = 40) :
    cpsTripleWithin 28 (mulBase + 48) (mulBase + 76) mulCR
      ((.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) ** (.x18 ↦ᵣ outPtr) **
        (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ aPtr) **
        (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion accBase accBytes₀ ** frameSlots spNew vRa v8 v9 v18 v19 v20)
      ((.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) ** (.x18 ↦ᵣ outPtr) **
        (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ aPtr) **
        (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (accBase + BitVec.ofNat 64 40)) **
        (.x6 ↦ᵣ (0 : Word)) ** bytesRegion accBase (List.replicate 40 (0 : BitVec 8)) **
        frameSlots spNew vRa v8 v9 v18 v19 v20) := by
  have hmv := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (h := mv_spec_gen_within .x5 .x19 accBase v5 (mulBase + 48) (by decide))
  have hmvF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) ** (.x18 ↦ᵣ outPtr) **
      (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ aPtr) ** (.x11 ↦ᵣ b) **
      (.x12 ↦ᵣ outPtr) ** (.x6 ↦ᵣ v6) ** bytesRegion accBase accBytes₀ **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) hmv
  have hli := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (h := li_spec_gen_within .x6 v6 (5 : Word) (mulBase + 52) (by decide))
  rw [show mulBase + 52 + 4 = mulBase + 56 from by decide] at hli
  have hliF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) ** (.x18 ↦ᵣ outPtr) **
      (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ aPtr) **
      (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ accBase) ** bytesRegion accBase accBytes₀ **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) hli
  have hinit := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmvF hliF
  have hloop := twoBreakRetLoop_spec 5 5 1
    (zeroInv spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 accBytes₀)
    (fun k hk => zeroIter_spec spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 accBytes₀ hlen k hk)
    (zeroExh_spec spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 accBytes₀)
  have hloopW := cpsTripleWithin_weaken
    (P' := (.x2 ↦ᵣ spNew) ** (.x1 ↦ᵣ vRa) ** (.x8 ↦ᵣ aPtr) ** (.x9 ↦ᵣ b) **
      (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ accBase) ** (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ aPtr) ** (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ accBase) **
      (.x6 ↦ᵣ (5 : Word)) ** bytesRegion accBase accBytes₀ **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (fun _ hp => by
      unfold zeroInv
      rw [show accBase + BitVec.ofNat 64 (8 * 0) = accBase from by decide,
        show BitVec.ofNat 64 (5 - 0) = (5 : Word) from by decide,
        show zeroFilled accBytes₀ 0 = accBytes₀ from rfl]
      xperm_hyp hp) (fun _ hq => hq) hloop
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hinit hloopW
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (Q := zeroInv spNew vRa v20 aPtr b outPtr v8 v9 v18 v19 accBytes₀ 5) (fun _ hq => ?_) hseq
  unfold zeroInv at hq
  rw [zeroFilled_five accBytes₀ hlen,
    show accBase + BitVec.ofNat 64 (8 * 5) = accBase + BitVec.ofNat 64 40 from by decide,
    show BitVec.ofNat 64 (5 - 5) = (0 : Word) from by decide] at hq
  xperm_hyp hq
