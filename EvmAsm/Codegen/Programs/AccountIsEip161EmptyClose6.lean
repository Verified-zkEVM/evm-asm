/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose6

  Field-1 (balance) and field-0 (nonce) OK-paths and the top-level whole-program
  assembly for the K137 contract `account_is_eip161_empty_spec_within`
  (`AccountFields.lean`).

  Builds on the field-3 subtree (`AccountIsEip161EmptyClose5.lean`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose5

namespace EvmAsm.Codegen.AccountIsEip161EmptySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

/-- Discharge a `.pcFree` side goal over frames of `bytesRegion`/`regIs`/`memIs`
    cells. -/
local macro "pcfR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | unfold aieSlots
    | unfold savedFrame)

/-- `k`-th instruction membership into the full closure `fullCode`. -/
local macro "aieFC" k:term ", " A:term ", " ins:term : term =>
  `((fun a i hi => aie_mono a i
      (CodeReq.ofProg_mem_at AB $A accountIsEip161Empty_prog $k $ins (by bv_omega)
        (by rw [aie_prog_length]; omega) rfl (by rw [aie_prog_length]; norm_num) a i hi)))

/-! ## Field-1 (balance) size-check head ([45]-[49], `AB+180 → {AB+396, AB+200}`) -/

set_option maxRecDepth 8000 in
theorem aieField1SizeHead (v5 v6 v7 len : Word) :
    cpsBranchWithin 5 (AB + 180) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (LenA ↦ₘ len))
      (AB + 396)
        ((.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
          (LenA ↦ₘ len) ** ⌜BitVec.ult (32 : Word) len⌝)
      (AB + 200)
        ((.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
          (LenA ↦ₘ len) ** ⌜¬ BitVec.ult (32 : Word) len⌝) := by
  -- [45-46] la x5 = aie_length
  have hau45 := CodeReq.ofProg_mem_at AB (AB + 180) accountIsEip161Empty_prog 45
    (.AUIPC .x5 (EvmAsm.Codegen.laHi GuestAddrs.aie_length
      (GuestAddrs.account_is_eip161_empty + 180))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had46 := CodeReq.ofProg_mem_at AB (AB + 184) accountIsEip161Empty_prog 46
    (.ADDI .x5 .x5 (EvmAsm.Codegen.laLo GuestAddrs.aie_length
      (GuestAddrs.account_is_eip161_empty + 180))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h46 := EvmAsm.Rv64.la_materialize_within .x5 v5 (AB + 180) LenA (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau45 a i hi))
    (fun a i hi => aie_mono a i (had46 a i hi))
  have f46 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (LenA ↦ₘ len)) (by pcfR) h46
  -- [47] LD x6 x5 0
  have h47 := ld_spec_gen_within .x6 .x5 LenA v6 len (0 : BitVec 12) (AB + 188) (by decide)
  rw [show LenA + signExtend12 (0 : BitVec 12) = LenA from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h47
  have e47 := cpsTripleWithin_extend_code (aieFC 47, (AB + 188), (.LD .x6 .x5 (0 : BitVec 12))) h47
  have f47 := cpsTripleWithin_frameR ((.x7 ↦ᵣ v7)) (by pcfR) e47
  -- [48] LI x7 32
  have h48 := li_spec_gen_within .x7 v7 (32 : Word) (AB + 192) (by decide)
  have e48 := cpsTripleWithin_extend_code (aieFC 48, (AB + 192), (.LI .x7 (32 : Word))) h48
  have f48 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len) ** (LenA ↦ₘ len)) (by pcfR) e48
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f46 f47
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f48
  -- [49] BLTU x7 x6 : 32 < len → AB+396 ; ¬ → AB+200
  have hbltu := bltu_spec_gen_within .x7 .x6 (200 : BitVec 13) (32 : Word) len (AB + 196)
  rw [show (AB + 196 : Word) + signExtend13 (200 : BitVec 13) = AB + 396 from by
      rw [show signExtend13 (200 : BitVec 13) = (200 : Word) from by decide]; bv_omega,
    show (AB + 196 : Word) + 4 = AB + 200 from by bv_omega] at hbltu
  have ebltu := cpsBranchWithin_extend_code
    (aieFC 49, (AB + 196), (.BLTU .x7 .x6 (200 : BitVec 13))) hbltu
  have fbltu := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ LenA) ** (LenA ↦ₘ len)) (by pcfR) ebltu
  have hbr := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_chunked hp) s2 fbltu
  refine cpsBranchWithin_mono_nSteps (by omega)
    (cpsBranchWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) (fun _ hp => by xperm_chunked hp) hbr)

#print axioms aieField1SizeHead

/-! ## Field-1 (balance) content-pointer setup ([50]-[53], `AB+200 → AB+216`) -/

set_option maxRecDepth 8000 in
theorem aieField1PtrSetup (v5 accBase v28 offset : Word) :
    cpsTripleWithin 4 (AB + 200) (AB + 216) fullCode
      ((.x5 ↦ᵣ v5) ** (.x8 ↦ᵣ accBase) ** (.x28 ↦ᵣ v28) ** (OffA ↦ₘ offset))
      ((.x5 ↦ᵣ OffA) ** (.x8 ↦ᵣ accBase) ** (.x28 ↦ᵣ (accBase + offset)) ** (OffA ↦ₘ offset)) := by
  -- [50-51] la x5 = aie_offset
  have hau50 := CodeReq.ofProg_mem_at AB (AB + 200) accountIsEip161Empty_prog 50
    (.AUIPC .x5 (EvmAsm.Codegen.laHi GuestAddrs.aie_offset
      (GuestAddrs.account_is_eip161_empty + 200))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had51 := CodeReq.ofProg_mem_at AB (AB + 204) accountIsEip161Empty_prog 51
    (.ADDI .x5 .x5 (EvmAsm.Codegen.laLo GuestAddrs.aie_offset
      (GuestAddrs.account_is_eip161_empty + 200))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h51 := EvmAsm.Rv64.la_materialize_within .x5 v5 (AB + 200) OffA (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau50 a i hi))
    (fun a i hi => aie_mono a i (had51 a i hi))
  have f51 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ accBase) ** (.x28 ↦ᵣ v28) ** (OffA ↦ₘ offset)) (by pcfR) h51
  -- [52] LD x28 x5 0
  have h52 := ld_spec_gen_within .x28 .x5 OffA v28 offset (0 : BitVec 12) (AB + 208) (by decide)
  rw [show OffA + signExtend12 (0 : BitVec 12) = OffA from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h52
  have e52 := cpsTripleWithin_extend_code (aieFC 52, (AB + 208), (.LD .x28 .x5 (0 : BitVec 12))) h52
  have f52 := cpsTripleWithin_frameR ((.x8 ↦ᵣ accBase)) (by pcfR) e52
  -- [53] ADD x28 x8 x28
  have h53 := add_spec_gen_rd_eq_rs2_within .x28 .x8 accBase offset (AB + 212) (by decide)
  have e53 := cpsTripleWithin_extend_code (aieFC 53, (AB + 212), (.ADD .x28 .x8 .x28)) h53
  have f53 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ OffA) ** (OffA ↦ₘ offset)) (by pcfR) e53
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f51 f52
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f53
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s2)

#print axioms aieField1PtrSetup

end EvmAsm.Codegen.AccountIsEip161EmptySpec
