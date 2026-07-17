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

end EvmAsm.Codegen.AccountDecodeSpec
