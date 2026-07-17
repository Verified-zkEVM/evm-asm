/-
  The four `rlp_list_nth_item` (K20) call blocks of `accountDecode_prog`
  (`Programs/State.lean`, PR-K27).  Each field 0/1/2/3 is decoded by the same
  strict selector, differing only in the immediate `LI x12 = N`, the guest
  `la` immediates for the shared `ad_offset`/`ad_length` output cells, and the
  return address linked by the field's `jal`.

  Each call block is `arg-shuffle ;; jal ;; rlpListNthItem_flat_spec_within`:

    * arg shuffle (`adFieldNSetup`, 7 instrs): `mv a0,s0 ; mv a1,s1 ; li a2,N ;
      la a3,ad_offset ; la a4,ad_length` establishes K20's `entryRest`
      (`rlp_list_nth_item(listBase, len, N, &ad_offset, &ad_length)`).
    * the `jal` links `ra := return PC` and enters K20 at `B`.
    * K20's `flatReturnResult` (offset/length cells written, the field-`N`
      `Result` pinned) is returned.

  Mirrors `WithdrawalDecodeSpec.wdField2Call` (the K20 call site).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeSpec
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm (Saved entryRest flatReturnResult
  rlpListNthItem_flat_spec_within regsAt_listNthFrame savedVals listNthFrame B)

/-! ## Guest data-section cells written by every field's K20 call -/

/-- The `ad_offset` data cell (holds the selected content's relative offset). -/
abbrev adOffsetAddr : Word := (GuestAddrs.ad_offset : Word)
/-- The `ad_length` data cell (holds the selected content's length). -/
abbrev adLengthAddr : Word := (GuestAddrs.ad_length : Word)

/-! ## `la` materialisers for the four call sites -/

/-- `la x13, ad_offset` at field 0 [17]-[18] (`AB+68 → AB+76`). -/
theorem adLaOff68 (v : Word) :
    cpsTripleWithin 2 (AB + 68) (AB + 76) fullCode
      (.x13 ↦ᵣ v) (.x13 ↦ᵣ adOffsetAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 68)
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 68)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 68) accountDecode_prog 17
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 68)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 72)
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 68)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 72) accountDecode_prog 18
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 68)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x13 v (AB + 68) adOffsetAddr (by decide) (by decide) hau had
  rw [show (AB + 68 : Word) + 8 = AB + 76 from by bv_omega] at h
  exact h

/-- `la x14, ad_length` at field 0 [19]-[20] (`AB+76 → AB+84`). -/
theorem adLaLen76 (v : Word) :
    cpsTripleWithin 2 (AB + 76) (AB + 84) fullCode
      (.x14 ↦ᵣ v) (.x14 ↦ᵣ adLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 76)
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 76)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 76) accountDecode_prog 19
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 76)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 80)
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 76)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 80) accountDecode_prog 20
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 76)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x14 v (AB + 76) adLengthAddr (by decide) (by decide) hau had
  rw [show (AB + 76 : Word) + 8 = AB + 84 from by bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Field-0 call setup [14]-[20] (`AB+56 → AB+84`): `mv a0,s0 ; mv a1,s1 ;
    li a2,0 ; la a3,ad_offset ; la a4,ad_length` — arrange
    `rlp_list_nth_item(listBase, len, 0, &ad_offset, &ad_length)`. -/
theorem adField0Setup (v10 v11 v12 v13 v14 listBase len : Word) :
    cpsTripleWithin 7 (AB + 56) (AB + 84) fullCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len))
      (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x13 : Reg) ↦ᵣ adOffsetAddr) **
       ((.x14 : Reg) ↦ᵣ adLengthAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len)) := by
  have h14 := mv_spec_gen_within .x10 .x8 listBase v10 (AB + 56) (by decide)
  have h14e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 56) accountDecode_prog 14 (.MV .x10 .x8)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h14)
  have h15 := mv_spec_gen_within .x11 .x9 len v11 (AB + 60) (by decide)
  have h15e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 60) accountDecode_prog 15 (.MV .x11 .x9)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h15)
  have h16 := li_spec_gen_within .x12 v12 (0 : Word) (AB + 64) (by decide)
  have h16e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 64) accountDecode_prog 16 (.LI .x12 (0 : Word))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h16)
  have h17 := adLaOff68 v13
  have h19 := adLaLen76 v14
  have f14 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h14e
  have f15 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h15e
  have f16 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h16e
  have f17 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h17
  have f19 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
     ((.x13 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h19
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f14 f15
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f16
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f17
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 f19
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) s4)

#print axioms adField0Setup

open EvmAsm.Codegen.RlpListNthItemSAsm in
set_option maxRecDepth 8000 in
/-- Field-0 RLP call adapter [14]-[21] + the strict `rlp_list_nth_item` selector
    (index 0, outputs `ad_offset`/`ad_length`), `ra := AB+88`.  The post is
    K20's `flatReturnResult` (its offset/length cells written, its `Result`
    pinned). -/
theorem adField0Call
    (spW raIn listBase len s2v s3 s4 s5 oldOffset oldLen v10 v11 v12 v13 v14 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : Saved :=
      { ra := AB + 88, s0 := listBase, s1 := len, s2 := s2v, s3 := s3, s4 := s4,
        s5 := s5 }
    let n20 := (12 + ((85 + 93 * (0 + 2)) + 6)) + 9
    cpsTripleWithin (7 + (1 + n20)) (AB + 56) (AB + 88) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen))
      (flatReturnResult spW listBase (0 : Word) adOffsetAddr adLengthAddr oldOffset
        oldLen saved bytes listLen 0) := by
  intro saved n20
  have hsetup := adField0Setup v10 v11 v12 v13 v14 listBase len
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) **
     (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 **
     regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen))
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | exact pcFree_regOwn | exact pcFree_stackFree _ _ | apply pcFree_sepConj) hsetup
  have hhead : cpsTripleWithin 7 (AB + 56) (AB + 84) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen))
      ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
       (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
       stackFree spW 8 **
       entryRest listBase len (0 : Word) adOffsetAddr adLengthAddr oldOffset oldLen bytes) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by unfold entryRest; xperm_hyp hq) hsetupF
  have hjal := jal_link_spec_within
    (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_decode + 84)) (AB + 84) raIn
  rw [show (AB + 84) + signExtend21 (jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.account_decode + 84)) = B from by decide,
    show (AB + 84 + 4 : Word) = AB + 88 from by bv_omega] at hjal
  have hjale := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 84) accountDecode_prog 21
        (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_decode + 84)))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) ** (.x18 ↦ᵣ s2v) **
     (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** stackFree spW 8 **
     entryRest listBase len (0 : Word) adOffsetAddr adLengthAddr oldOffset oldLen bytes)
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_stackFree _ _
        | exact (by unfold entryRest; repeat' first
            | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
            | exact pcFree_regOwn | apply pcFree_sepConj : (entryRest listBase len (0 : Word)
              adOffsetAddr adLengthAddr oldOffset oldLen bytes).pcFree)
        | apply pcFree_sepConj) hjale
  have hk20 := rlpListNthItem_flat_spec_within spW listBase len (0 : Word) adOffsetAddr
    adLengthAddr oldOffset oldLen saved bytes listLen 0 hlenW (by decide) (by decide)
    hsalign hslack hover hvalid (by show (AB + 88) &&& ~~~(1 : Word) = AB + 88; decide)
  have hk20C := cpsTripleWithin_extend_code k20_mono hk20
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hhead hjalF
  have s2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [regsAt_listNthFrame]
      simp only [show saved.ra = AB + 88 from rfl, show saved.s0 = listBase from rfl,
        show saved.s1 = len from rfl, show saved.s2 = s2v from rfl,
        show saved.s3 = s3 from rfl, show saved.s4 = s4 from rfl,
        show saved.s5 = s5 from rfl]
      xperm_hyp hp) s1 hk20C
  exact cpsTripleWithin_mono_nSteps (by omega) s2

#print axioms adField0Call

/-! ## Field 1 call block [41]-[48] (`AB+164 → AB+196`), index 1, `ra := AB+196` -/

/-- `la x13, ad_offset` at field 1 [44]-[45] (`AB+176 → AB+184`). -/
theorem adLaOff176 (v : Word) :
    cpsTripleWithin 2 (AB + 176) (AB + 184) fullCode
      (.x13 ↦ᵣ v) (.x13 ↦ᵣ adOffsetAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 176)
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 176)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 176) accountDecode_prog 44
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 176)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 180)
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 176)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 180) accountDecode_prog 45
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 176)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x13 v (AB + 176) adOffsetAddr (by decide) (by decide) hau had
  rw [show (AB + 176 : Word) + 8 = AB + 184 from by bv_omega] at h
  exact h

/-- `la x14, ad_length` at field 1 [46]-[47] (`AB+184 → AB+192`). -/
theorem adLaLen184 (v : Word) :
    cpsTripleWithin 2 (AB + 184) (AB + 192) fullCode
      (.x14 ↦ᵣ v) (.x14 ↦ᵣ adLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 184)
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 184)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 184) accountDecode_prog 46
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 184)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 188)
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 184)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 188) accountDecode_prog 47
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 184)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x14 v (AB + 184) adLengthAddr (by decide) (by decide) hau had
  rw [show (AB + 184 : Word) + 8 = AB + 192 from by bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Field-1 call setup [41]-[47] (`AB+164 → AB+192`): `li a2,1`. -/
theorem adField1Setup (v10 v11 v12 v13 v14 listBase len : Word) :
    cpsTripleWithin 7 (AB + 164) (AB + 192) fullCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len))
      (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) **
       ((.x12 : Reg) ↦ᵣ (1 : Word)) ** ((.x13 : Reg) ↦ᵣ adOffsetAddr) **
       ((.x14 : Reg) ↦ᵣ adLengthAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len)) := by
  have h41 := mv_spec_gen_within .x10 .x8 listBase v10 (AB + 164) (by decide)
  have h41e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 164) accountDecode_prog 41 (.MV .x10 .x8)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h41)
  have h42 := mv_spec_gen_within .x11 .x9 len v11 (AB + 168) (by decide)
  have h42e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 168) accountDecode_prog 42 (.MV .x11 .x9)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h42)
  have h43 := li_spec_gen_within .x12 v12 (1 : Word) (AB + 172) (by decide)
  have h43e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 172) accountDecode_prog 43 (.LI .x12 (1 : Word))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h43)
  have h44 := adLaOff176 v13
  have h46 := adLaLen184 v14
  have f41 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h41e
  have f42 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h42e
  have f43 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h43e
  have f44 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (1 : Word)) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h44
  have f46 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (1 : Word)) **
     ((.x13 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h46
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f41 f42
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f43
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f44
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 f46
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) s4)

open EvmAsm.Codegen.RlpListNthItemSAsm in
set_option maxRecDepth 8000 in
/-- Field-1 RLP call adapter [41]-[48] + `rlp_list_nth_item` (index 1), `ra := AB+196`. -/
theorem adField1Call
    (spW raIn listBase len s2v s3 s4 s5 oldOffset oldLen v10 v11 v12 v13 v14 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : Saved :=
      { ra := AB + 196, s0 := listBase, s1 := len, s2 := s2v, s3 := s3, s4 := s4,
        s5 := s5 }
    let n20 := (12 + ((85 + 93 * (1 + 2)) + 6)) + 9
    cpsTripleWithin (7 + (1 + n20)) (AB + 164) (AB + 196) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen))
      (flatReturnResult spW listBase (1 : Word) adOffsetAddr adLengthAddr oldOffset
        oldLen saved bytes listLen 1) := by
  intro saved n20
  have hsetup := adField1Setup v10 v11 v12 v13 v14 listBase len
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) **
     (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 **
     regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen))
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | exact pcFree_regOwn | exact pcFree_stackFree _ _ | apply pcFree_sepConj) hsetup
  have hhead : cpsTripleWithin 7 (AB + 164) (AB + 192) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen))
      ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
       (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
       stackFree spW 8 **
       entryRest listBase len (1 : Word) adOffsetAddr adLengthAddr oldOffset oldLen bytes) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by unfold entryRest; xperm_hyp hq) hsetupF
  have hjal := jal_link_spec_within
    (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_decode + 192)) (AB + 192) raIn
  rw [show (AB + 192) + signExtend21 (jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.account_decode + 192)) = B from by decide,
    show (AB + 192 + 4 : Word) = AB + 196 from by bv_omega] at hjal
  have hjale := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 192) accountDecode_prog 48
        (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_decode + 192)))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) ** (.x18 ↦ᵣ s2v) **
     (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** stackFree spW 8 **
     entryRest listBase len (1 : Word) adOffsetAddr adLengthAddr oldOffset oldLen bytes)
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_stackFree _ _
        | exact (by unfold entryRest; repeat' first
            | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
            | exact pcFree_regOwn | apply pcFree_sepConj : (entryRest listBase len (1 : Word)
              adOffsetAddr adLengthAddr oldOffset oldLen bytes).pcFree)
        | apply pcFree_sepConj) hjale
  have hk20 := rlpListNthItem_flat_spec_within spW listBase len (1 : Word) adOffsetAddr
    adLengthAddr oldOffset oldLen saved bytes listLen 1 hlenW (by decide) (by decide)
    hsalign hslack hover hvalid (by show (AB + 196) &&& ~~~(1 : Word) = AB + 196; decide)
  have hk20C := cpsTripleWithin_extend_code k20_mono hk20
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hhead hjalF
  have s2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [regsAt_listNthFrame]
      simp only [show saved.ra = AB + 196 from rfl, show saved.s0 = listBase from rfl,
        show saved.s1 = len from rfl, show saved.s2 = s2v from rfl,
        show saved.s3 = s3 from rfl, show saved.s4 = s4 from rfl,
        show saved.s5 = s5 from rfl]
      xperm_hyp hp) s1 hk20C
  exact cpsTripleWithin_mono_nSteps (by omega) s2

/-! ## Field 2 call block [72]-[79] (`AB+288 → AB+320`), index 2, `ra := AB+320` -/

/-- `la x13, ad_offset` at field 2 [75]-[76] (`AB+300 → AB+308`). -/
theorem adLaOff300 (v : Word) :
    cpsTripleWithin 2 (AB + 300) (AB + 308) fullCode
      (.x13 ↦ᵣ v) (.x13 ↦ᵣ adOffsetAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 300)
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 300)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 300) accountDecode_prog 75
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 300)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 304)
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 300)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 304) accountDecode_prog 76
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 300)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x13 v (AB + 300) adOffsetAddr (by decide) (by decide) hau had
  rw [show (AB + 300 : Word) + 8 = AB + 308 from by bv_omega] at h
  exact h

/-- `la x14, ad_length` at field 2 [77]-[78] (`AB+308 → AB+316`). -/
theorem adLaLen308 (v : Word) :
    cpsTripleWithin 2 (AB + 308) (AB + 316) fullCode
      (.x14 ↦ᵣ v) (.x14 ↦ᵣ adLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 308)
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 308)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 308) accountDecode_prog 77
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 308)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 312)
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 308)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 312) accountDecode_prog 78
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 308)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x14 v (AB + 308) adLengthAddr (by decide) (by decide) hau had
  rw [show (AB + 308 : Word) + 8 = AB + 316 from by bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Field-2 call setup [72]-[78] (`AB+288 → AB+316`): `li a2,2`. -/
theorem adField2Setup (v10 v11 v12 v13 v14 listBase len : Word) :
    cpsTripleWithin 7 (AB + 288) (AB + 316) fullCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len))
      (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) **
       ((.x12 : Reg) ↦ᵣ (2 : Word)) ** ((.x13 : Reg) ↦ᵣ adOffsetAddr) **
       ((.x14 : Reg) ↦ᵣ adLengthAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len)) := by
  have h72 := mv_spec_gen_within .x10 .x8 listBase v10 (AB + 288) (by decide)
  have h72e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 288) accountDecode_prog 72 (.MV .x10 .x8)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h72)
  have h73 := mv_spec_gen_within .x11 .x9 len v11 (AB + 292) (by decide)
  have h73e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 292) accountDecode_prog 73 (.MV .x11 .x9)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h73)
  have h74 := li_spec_gen_within .x12 v12 (2 : Word) (AB + 296) (by decide)
  have h74e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 296) accountDecode_prog 74 (.LI .x12 (2 : Word))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h74)
  have h75 := adLaOff300 v13
  have h77 := adLaLen308 v14
  have f72 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h72e
  have f73 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h73e
  have f74 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h74e
  have f75 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (2 : Word)) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h75
  have f77 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (2 : Word)) **
     ((.x13 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h77
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f72 f73
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f74
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f75
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 f77
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) s4)

open EvmAsm.Codegen.RlpListNthItemSAsm in
set_option maxRecDepth 8000 in
/-- Field-2 RLP call adapter [72]-[79] + `rlp_list_nth_item` (index 2), `ra := AB+320`. -/
theorem adField2Call
    (spW raIn listBase len s2v s3 s4 s5 oldOffset oldLen v10 v11 v12 v13 v14 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : Saved :=
      { ra := AB + 320, s0 := listBase, s1 := len, s2 := s2v, s3 := s3, s4 := s4,
        s5 := s5 }
    let n20 := (12 + ((85 + 93 * (2 + 2)) + 6)) + 9
    cpsTripleWithin (7 + (1 + n20)) (AB + 288) (AB + 320) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen))
      (flatReturnResult spW listBase (2 : Word) adOffsetAddr adLengthAddr oldOffset
        oldLen saved bytes listLen 2) := by
  intro saved n20
  have hsetup := adField2Setup v10 v11 v12 v13 v14 listBase len
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) **
     (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 **
     regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen))
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | exact pcFree_regOwn | exact pcFree_stackFree _ _ | apply pcFree_sepConj) hsetup
  have hhead : cpsTripleWithin 7 (AB + 288) (AB + 316) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen))
      ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
       (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
       stackFree spW 8 **
       entryRest listBase len (2 : Word) adOffsetAddr adLengthAddr oldOffset oldLen bytes) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by unfold entryRest; xperm_hyp hq) hsetupF
  have hjal := jal_link_spec_within
    (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_decode + 316)) (AB + 316) raIn
  rw [show (AB + 316) + signExtend21 (jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.account_decode + 316)) = B from by decide,
    show (AB + 316 + 4 : Word) = AB + 320 from by bv_omega] at hjal
  have hjale := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 316) accountDecode_prog 79
        (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_decode + 316)))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) ** (.x18 ↦ᵣ s2v) **
     (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** stackFree spW 8 **
     entryRest listBase len (2 : Word) adOffsetAddr adLengthAddr oldOffset oldLen bytes)
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_stackFree _ _
        | exact (by unfold entryRest; repeat' first
            | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
            | exact pcFree_regOwn | apply pcFree_sepConj : (entryRest listBase len (2 : Word)
              adOffsetAddr adLengthAddr oldOffset oldLen bytes).pcFree)
        | apply pcFree_sepConj) hjale
  have hk20 := rlpListNthItem_flat_spec_within spW listBase len (2 : Word) adOffsetAddr
    adLengthAddr oldOffset oldLen saved bytes listLen 2 hlenW (by decide) (by decide)
    hsalign hslack hover hvalid (by show (AB + 320) &&& ~~~(1 : Word) = AB + 320; decide)
  have hk20C := cpsTripleWithin_extend_code k20_mono hk20
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hhead hjalF
  have s2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [regsAt_listNthFrame]
      simp only [show saved.ra = AB + 320 from rfl, show saved.s0 = listBase from rfl,
        show saved.s1 = len from rfl, show saved.s2 = s2v from rfl,
        show saved.s3 = s3 from rfl, show saved.s4 = s4 from rfl,
        show saved.s5 = s5 from rfl]
      xperm_hyp hp) s1 hk20C
  exact cpsTripleWithin_mono_nSteps (by omega) s2

/-! ## Field 3 call block [98]-[105] (`AB+392 → AB+424`), index 3, `ra := AB+424` -/

/-- `la x13, ad_offset` at field 3 [101]-[102] (`AB+404 → AB+412`). -/
theorem adLaOff404 (v : Word) :
    cpsTripleWithin 2 (AB + 404) (AB + 412) fullCode
      (.x13 ↦ᵣ v) (.x13 ↦ᵣ adOffsetAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 404)
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 404)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 404) accountDecode_prog 101
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 404)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 408)
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 404)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 408) accountDecode_prog 102
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 404)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x13 v (AB + 404) adOffsetAddr (by decide) (by decide) hau had
  rw [show (AB + 404 : Word) + 8 = AB + 412 from by bv_omega] at h
  exact h

/-- `la x14, ad_length` at field 3 [103]-[104] (`AB+412 → AB+420`). -/
theorem adLaLen412 (v : Word) :
    cpsTripleWithin 2 (AB + 412) (AB + 420) fullCode
      (.x14 ↦ᵣ v) (.x14 ↦ᵣ adLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 412)
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 412)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 412) accountDecode_prog 103
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 412)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 416)
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 412)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 416) accountDecode_prog 104
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 412)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x14 v (AB + 412) adLengthAddr (by decide) (by decide) hau had
  rw [show (AB + 412 : Word) + 8 = AB + 420 from by bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Field-3 call setup [98]-[104] (`AB+392 → AB+420`): `li a2,3`. -/
theorem adField3Setup (v10 v11 v12 v13 v14 listBase len : Word) :
    cpsTripleWithin 7 (AB + 392) (AB + 420) fullCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len))
      (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) **
       ((.x12 : Reg) ↦ᵣ (3 : Word)) ** ((.x13 : Reg) ↦ᵣ adOffsetAddr) **
       ((.x14 : Reg) ↦ᵣ adLengthAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len)) := by
  have h98 := mv_spec_gen_within .x10 .x8 listBase v10 (AB + 392) (by decide)
  have h98e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 392) accountDecode_prog 98 (.MV .x10 .x8)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h98)
  have h99 := mv_spec_gen_within .x11 .x9 len v11 (AB + 396) (by decide)
  have h99e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 396) accountDecode_prog 99 (.MV .x11 .x9)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h99)
  have h100 := li_spec_gen_within .x12 v12 (3 : Word) (AB + 400) (by decide)
  have h100e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 400) accountDecode_prog 100 (.LI .x12 (3 : Word))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h100)
  have h101 := adLaOff404 v13
  have h103 := adLaLen412 v14
  have f98 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h98e
  have f99 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h99e
  have f100 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h100e
  have f101 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (3 : Word)) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h101
  have f103 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (3 : Word)) **
     ((.x13 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h103
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f98 f99
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f100
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f101
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 f103
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) s4)

open EvmAsm.Codegen.RlpListNthItemSAsm in
set_option maxRecDepth 8000 in
/-- Field-3 RLP call adapter [98]-[105] + `rlp_list_nth_item` (index 3), `ra := AB+424`. -/
theorem adField3Call
    (spW raIn listBase len s2v s3 s4 s5 oldOffset oldLen v10 v11 v12 v13 v14 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : Saved :=
      { ra := AB + 424, s0 := listBase, s1 := len, s2 := s2v, s3 := s3, s4 := s4,
        s5 := s5 }
    let n20 := (12 + ((85 + 93 * (3 + 2)) + 6)) + 9
    cpsTripleWithin (7 + (1 + n20)) (AB + 392) (AB + 424) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen))
      (flatReturnResult spW listBase (3 : Word) adOffsetAddr adLengthAddr oldOffset
        oldLen saved bytes listLen 3) := by
  intro saved n20
  have hsetup := adField3Setup v10 v11 v12 v13 v14 listBase len
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) **
     (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 **
     regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen))
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | exact pcFree_regOwn | exact pcFree_stackFree _ _ | apply pcFree_sepConj) hsetup
  have hhead : cpsTripleWithin 7 (AB + 392) (AB + 420) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen))
      ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
       (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
       stackFree spW 8 **
       entryRest listBase len (3 : Word) adOffsetAddr adLengthAddr oldOffset oldLen bytes) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by unfold entryRest; xperm_hyp hq) hsetupF
  have hjal := jal_link_spec_within
    (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_decode + 420)) (AB + 420) raIn
  rw [show (AB + 420) + signExtend21 (jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.account_decode + 420)) = B from by decide,
    show (AB + 420 + 4 : Word) = AB + 424 from by bv_omega] at hjal
  have hjale := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 420) accountDecode_prog 105
        (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_decode + 420)))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) ** (.x18 ↦ᵣ s2v) **
     (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** stackFree spW 8 **
     entryRest listBase len (3 : Word) adOffsetAddr adLengthAddr oldOffset oldLen bytes)
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_stackFree _ _
        | exact (by unfold entryRest; repeat' first
            | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
            | exact pcFree_regOwn | apply pcFree_sepConj : (entryRest listBase len (3 : Word)
              adOffsetAddr adLengthAddr oldOffset oldLen bytes).pcFree)
        | apply pcFree_sepConj) hjale
  have hk20 := rlpListNthItem_flat_spec_within spW listBase len (3 : Word) adOffsetAddr
    adLengthAddr oldOffset oldLen saved bytes listLen 3 hlenW (by decide) (by decide)
    hsalign hslack hover hvalid (by show (AB + 424) &&& ~~~(1 : Word) = AB + 424; decide)
  have hk20C := cpsTripleWithin_extend_code k20_mono hk20
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hhead hjalF
  have s2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [regsAt_listNthFrame]
      simp only [show saved.ra = AB + 424 from rfl, show saved.s0 = listBase from rfl,
        show saved.s1 = len from rfl, show saved.s2 = s2v from rfl,
        show saved.s3 = s3 from rfl, show saved.s4 = s4 from rfl,
        show saved.s5 = s5 from rfl]
      xperm_hyp hp) s1 hk20C
  exact cpsTripleWithin_mono_nSteps (by omega) s2

#print axioms adField1Call
#print axioms adField2Call
#print axioms adField3Call

end EvmAsm.Codegen.AccountDecodeSpec
