/-
  The per-field length-check dispatches of `accountDecode_prog`
  (`Programs/State.lean`, PR-K27).  After each field's K20 call succeeds, the
  selected content length (`ad_length` cell) is loaded and compared:

    * field 0 (nonce)   [23]-[27] (`AB+92 → 504/112`):  `bltu 8, len`  → fail if `8 < len`.
    * field 1 (balance) [50]-[54] (`AB+200 → 504/220`): `bltu 32, len` → fail if `32 < len`.
    * field 2 (root)    [81]-[85] (`AB+324 → 504/344`): `bne  len, 32` → fail if `len ≠ 32`.
    * field 3 (code)    [107]-[111] (`AB+428 → 504/448`): `bne len, 32` → fail if `len ≠ 32`.

  Each dispatch is `la x5, ad_length ;; ld x6 ;; li x7,imm ;; branch`, a
  five-step `cpsBranchWithin` with the shared failure edge `AB+504` (the
  `li a0,1` fail tail) and a per-field continue edge.  Mirrors
  `WithdrawalDecodeSpec.wdLenCheck`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeCall
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## `la x5, ad_length` materialisers for the four length-check sites -/

/-- `la x5, ad_length` at field 0 [23]-[24] (`AB+92 → AB+100`). -/
private theorem adLaLenX5_92 (v : Word) :
    cpsTripleWithin 2 (AB + 92) (AB + 100) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 92)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 92)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 92) accountDecode_prog 23
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 92)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 96)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 92)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 96) accountDecode_prog 24
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 92)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 92) adLengthAddr (by decide) (by decide) hau had
  rw [show (AB + 92 : Word) + 8 = AB + 100 from by bv_omega] at h
  exact h

/-- `la x5, ad_length` at field 1 [50]-[51] (`AB+200 → AB+208`). -/
private theorem adLaLenX5_200 (v : Word) :
    cpsTripleWithin 2 (AB + 200) (AB + 208) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 200)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 200)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 200) accountDecode_prog 50
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 200)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 204)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 200)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 204) accountDecode_prog 51
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 200)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 200) adLengthAddr (by decide) (by decide) hau had
  rw [show (AB + 200 : Word) + 8 = AB + 208 from by bv_omega] at h
  exact h

/-- `la x5, ad_length` at field 2 [81]-[82] (`AB+324 → AB+332`). -/
private theorem adLaLenX5_324 (v : Word) :
    cpsTripleWithin 2 (AB + 324) (AB + 332) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 324)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 324)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 324) accountDecode_prog 81
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 324)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 328)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 324)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 328) accountDecode_prog 82
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 324)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 324) adLengthAddr (by decide) (by decide) hau had
  rw [show (AB + 324 : Word) + 8 = AB + 332 from by bv_omega] at h
  exact h

/-- `la x5, ad_length` at field 3 [107]-[108] (`AB+428 → AB+436`). -/
private theorem adLaLenX5_428 (v : Word) :
    cpsTripleWithin 2 (AB + 428) (AB + 436) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 428)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 428)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 428) accountDecode_prog 107
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 428)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 432)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 428)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 432) accountDecode_prog 108
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 428)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 428) adLengthAddr (by decide) (by decide) hau had
  rw [show (AB + 428 : Word) + 8 = AB + 436 from by bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Field-0 (nonce) length check [23]-[27] (`AB+92 → 504/112`): `bltu 8, len`.
    Fail edge (`AB+504`, `8 < len`) or continue (`AB+112`, `len ≤ 8`). -/
theorem adNonceLenCheck (v5old v6old v7old len : Word) :
    cpsBranchWithin 5 (AB + 92) fullCode
      (((.x5 : Reg) ↦ᵣ v5old) ** ((.x6 : Reg) ↦ᵣ v6old) **
       ((.x7 : Reg) ↦ᵣ v7old) ** (adLengthAddr ↦ₘ len))
      (AB + 504)
        ((((.x7 : Reg) ↦ᵣ (8 : Word)) ** ((.x6 : Reg) ↦ᵣ len) ** ⌜BitVec.ult (8 : Word) len⌝) **
         ((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len))
      (AB + 112)
        ((((.x7 : Reg) ↦ᵣ (8 : Word)) ** ((.x6 : Reg) ↦ᵣ len) ** ⌜¬BitVec.ult (8 : Word) len⌝) **
         ((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len)) := by
  have hla := adLaLenX5_92 v5old
  have hlaf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6old) ** ((.x7 : Reg) ↦ᵣ v7old) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hla
  have hld := ld_spec_gen_within .x6 .x5 adLengthAddr v6old len (0 : BitVec 12)
    (AB + 100) (by decide)
  rw [show adLengthAddr + signExtend12 (0 : BitVec 12) = adLengthAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 100 : Word) + 4 = AB + 104 from by bv_omega] at hld
  have hlde := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 100) accountDecode_prog 25
        (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hld)
  have hldf := cpsTripleWithin_frameR ((.x7 : Reg) ↦ᵣ v7old) pcFree_regIs hlde
  have hli := li_spec_gen_within .x7 v7old (8 : Word) (AB + 104) (by decide)
  rw [show (AB + 104 : Word) + 4 = AB + 108 from by bv_omega] at hli
  have hlie := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 104) accountDecode_prog 26
        (.LI .x7 (8 : Word)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hli)
  have hlif := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adLengthAddr) ** ((.x6 : Reg) ↦ᵣ len) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hlie
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaf hldf
  have sStraight := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hlif
  have hbltu := bltu_spec_gen_within .x7 .x6 (396 : BitVec 13) (8 : Word) len (AB + 108)
  rw [show (AB + 108 : Word) + signExtend13 (396 : BitVec 13) = AB + 504 from by
    rw [show signExtend13 (396 : BitVec 13) = (396 : Word) from by decide]; bv_omega,
    show (AB + 108 : Word) + 4 = AB + 112 from by bv_omega] at hbltu
  have hbltue := cpsBranchWithin_extend_code ad_mono
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 108) accountDecode_prog 27
        (.BLTU .x7 .x6 (396 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hbltu)
  have hbltuf := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hbltue
  have hcomposed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) sStraight hbltuf
  exact cpsBranchWithin_mono_nSteps (by omega) hcomposed

#print axioms adNonceLenCheck

set_option maxRecDepth 8000 in
/-- Field-1 (balance) length check [50]-[54] (`AB+200 → 504/220`): `bltu 32, len`. -/
theorem adBalLenCheck (v5old v6old v7old len : Word) :
    cpsBranchWithin 5 (AB + 200) fullCode
      (((.x5 : Reg) ↦ᵣ v5old) ** ((.x6 : Reg) ↦ᵣ v6old) **
       ((.x7 : Reg) ↦ᵣ v7old) ** (adLengthAddr ↦ₘ len))
      (AB + 504)
        ((((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x6 : Reg) ↦ᵣ len) ** ⌜BitVec.ult (32 : Word) len⌝) **
         ((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len))
      (AB + 220)
        ((((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x6 : Reg) ↦ᵣ len) ** ⌜¬BitVec.ult (32 : Word) len⌝) **
         ((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len)) := by
  have hla := adLaLenX5_200 v5old
  have hlaf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6old) ** ((.x7 : Reg) ↦ᵣ v7old) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hla
  have hld := ld_spec_gen_within .x6 .x5 adLengthAddr v6old len (0 : BitVec 12)
    (AB + 208) (by decide)
  rw [show adLengthAddr + signExtend12 (0 : BitVec 12) = adLengthAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 208 : Word) + 4 = AB + 212 from by bv_omega] at hld
  have hlde := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 208) accountDecode_prog 52
        (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hld)
  have hldf := cpsTripleWithin_frameR ((.x7 : Reg) ↦ᵣ v7old) pcFree_regIs hlde
  have hli := li_spec_gen_within .x7 v7old (32 : Word) (AB + 212) (by decide)
  rw [show (AB + 212 : Word) + 4 = AB + 216 from by bv_omega] at hli
  have hlie := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 212) accountDecode_prog 53
        (.LI .x7 (32 : Word)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hli)
  have hlif := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adLengthAddr) ** ((.x6 : Reg) ↦ᵣ len) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hlie
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaf hldf
  have sStraight := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hlif
  have hbltu := bltu_spec_gen_within .x7 .x6 (288 : BitVec 13) (32 : Word) len (AB + 216)
  rw [show (AB + 216 : Word) + signExtend13 (288 : BitVec 13) = AB + 504 from by
    rw [show signExtend13 (288 : BitVec 13) = (288 : Word) from by decide]; bv_omega,
    show (AB + 216 : Word) + 4 = AB + 220 from by bv_omega] at hbltu
  have hbltue := cpsBranchWithin_extend_code ad_mono
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 216) accountDecode_prog 54
        (.BLTU .x7 .x6 (288 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hbltu)
  have hbltuf := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hbltue
  have hcomposed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) sStraight hbltuf
  exact cpsBranchWithin_mono_nSteps (by omega) hcomposed

#print axioms adBalLenCheck

set_option maxRecDepth 8000 in
/-- Field-2 (storage_root) length check [81]-[85] (`AB+324 → 504/344`): `bne len, 32`. -/
theorem adRootLenCheck (v5old v6old v7old len : Word) :
    cpsBranchWithin 5 (AB + 324) fullCode
      (((.x5 : Reg) ↦ᵣ v5old) ** ((.x6 : Reg) ↦ᵣ v6old) **
       ((.x7 : Reg) ↦ᵣ v7old) ** (adLengthAddr ↦ₘ len))
      (AB + 504)
        ((((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ⌜len ≠ (32 : Word)⌝) **
         ((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len))
      (AB + 344)
        ((((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ⌜len = (32 : Word)⌝) **
         ((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len)) := by
  have hla := adLaLenX5_324 v5old
  have hlaf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6old) ** ((.x7 : Reg) ↦ᵣ v7old) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hla
  have hld := ld_spec_gen_within .x6 .x5 adLengthAddr v6old len (0 : BitVec 12)
    (AB + 332) (by decide)
  rw [show adLengthAddr + signExtend12 (0 : BitVec 12) = adLengthAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 332 : Word) + 4 = AB + 336 from by bv_omega] at hld
  have hlde := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 332) accountDecode_prog 83
        (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hld)
  have hldf := cpsTripleWithin_frameR ((.x7 : Reg) ↦ᵣ v7old) pcFree_regIs hlde
  have hli := li_spec_gen_within .x7 v7old (32 : Word) (AB + 336) (by decide)
  rw [show (AB + 336 : Word) + 4 = AB + 340 from by bv_omega] at hli
  have hlie := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 336) accountDecode_prog 84
        (.LI .x7 (32 : Word)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hli)
  have hlif := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adLengthAddr) ** ((.x6 : Reg) ↦ᵣ len) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hlie
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaf hldf
  have sStraight := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hlif
  have hbne := bne_spec_gen_within .x6 .x7 (164 : BitVec 13) len (32 : Word) (AB + 340)
  rw [show (AB + 340 : Word) + signExtend13 (164 : BitVec 13) = AB + 504 from by
    rw [show signExtend13 (164 : BitVec 13) = (164 : Word) from by decide]; bv_omega,
    show (AB + 340 : Word) + 4 = AB + 344 from by bv_omega] at hbne
  have hbnee := cpsBranchWithin_extend_code ad_mono
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 340) accountDecode_prog 85
        (.BNE .x6 .x7 (164 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hbne)
  have hbnef := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hbnee
  have hcomposed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) sStraight hbnef
  exact cpsBranchWithin_mono_nSteps (by omega) hcomposed

#print axioms adRootLenCheck

set_option maxRecDepth 8000 in
/-- Field-3 (code_hash) length check [107]-[111] (`AB+428 → 504/448`): `bne len, 32`. -/
theorem adCodeLenCheck (v5old v6old v7old len : Word) :
    cpsBranchWithin 5 (AB + 428) fullCode
      (((.x5 : Reg) ↦ᵣ v5old) ** ((.x6 : Reg) ↦ᵣ v6old) **
       ((.x7 : Reg) ↦ᵣ v7old) ** (adLengthAddr ↦ₘ len))
      (AB + 504)
        ((((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ⌜len ≠ (32 : Word)⌝) **
         ((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len))
      (AB + 448)
        ((((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ⌜len = (32 : Word)⌝) **
         ((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len)) := by
  have hla := adLaLenX5_428 v5old
  have hlaf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6old) ** ((.x7 : Reg) ↦ᵣ v7old) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hla
  have hld := ld_spec_gen_within .x6 .x5 adLengthAddr v6old len (0 : BitVec 12)
    (AB + 436) (by decide)
  rw [show adLengthAddr + signExtend12 (0 : BitVec 12) = adLengthAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 436 : Word) + 4 = AB + 440 from by bv_omega] at hld
  have hlde := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 436) accountDecode_prog 109
        (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hld)
  have hldf := cpsTripleWithin_frameR ((.x7 : Reg) ↦ᵣ v7old) pcFree_regIs hlde
  have hli := li_spec_gen_within .x7 v7old (32 : Word) (AB + 440) (by decide)
  rw [show (AB + 440 : Word) + 4 = AB + 444 from by bv_omega] at hli
  have hlie := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 440) accountDecode_prog 110
        (.LI .x7 (32 : Word)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hli)
  have hlif := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adLengthAddr) ** ((.x6 : Reg) ↦ᵣ len) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hlie
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaf hldf
  have sStraight := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hlif
  have hbne := bne_spec_gen_within .x6 .x7 (60 : BitVec 13) len (32 : Word) (AB + 444)
  rw [show (AB + 444 : Word) + signExtend13 (60 : BitVec 13) = AB + 504 from by
    rw [show signExtend13 (60 : BitVec 13) = (60 : Word) from by decide]; bv_omega,
    show (AB + 444 : Word) + 4 = AB + 448 from by bv_omega] at hbne
  have hbnee := cpsBranchWithin_extend_code ad_mono
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 444) accountDecode_prog 111
        (.BNE .x6 .x7 (60 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hbne)
  have hbnef := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hbnee
  have hcomposed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) sStraight hbnef
  exact cpsBranchWithin_mono_nSteps (by omega) hcomposed

#print axioms adCodeLenCheck

end EvmAsm.Codegen.AccountDecodeSpec
