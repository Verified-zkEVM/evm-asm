/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose4

  Field-body OK-paths and the top-level whole-program assembly for the K137
  contract `account_is_eip161_empty_spec_within` (`AccountFields.lean`).

  Builds on the dispatch infrastructure (`AccountIsEip161EmptyClose3.lean`),
  the RLP call adapters + prologue/epilogue (`AccountIsEip161EmptyClose.lean`),
  the three byte-scan loop lemmas (`AccountIsEip161EmptyLoop.lean`), and the
  verdict-store tails + return bridges (`AccountIsEip161EmptyClose2.lean`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose3

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
    | pcFree)

/-! ## Empty-code-hash constant region facts

    `ECB = aie_empty_code_hash = 0xa3000ce0` sits in the RAM window and is
    8-byte aligned; its 32 content bytes are all valid byte accesses. -/

theorem ecb_align : ECB.toNat % 8 = 0 := by decide

theorem ecb_over : ECB.toNat + 32 < 2 ^ 64 := by decide

theorem ecb_toNat_add (j : Nat) (hj : j < 32) :
    (ECB + BitVec.ofNat 64 j).toNat = 2734689504 + j := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 : (ECB : Word).toNat = 2734689504 := by decide
  rw [h1, Nat.mod_eq_of_lt (show j < 2 ^ 64 from by omega),
      Nat.mod_eq_of_lt (show 2734689504 + j < 2 ^ 64 from by omega)]

theorem ecb_valid (j : Nat) (hj : j < 32) :
    isValidByteAccess (ECB + BitVec.ofNat 64 j) = true := by
  rw [isValidByteAccess_eq, isValidMemAddr_eq, ecb_toNat_add j hj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  unfold Rv64.MEM_START Rv64.MEM_END Rv64.INPUT_MEM_START Rv64.INPUT_MEM_END
    Rv64.RAM_MEM_START Rv64.RAM_MEM_END
  omega

/-! ## The `accountEip161Empty` verdict, assembled from the three fields' facts

    The empty-path model constructor: the lenient EIP-161-empty predicate
    (`AccountIsEip161EmptySpec.lean:182`) built directly from the three
    `rlp_list_nth_item` successes and the per-byte content facts established by
    the three byte-scan loops. -/

theorem aieEmpty_of_facts (bytes : List (BitVec 8)) (accBase : Word) (listLen : Nat)
    (o0 l0 o1 l1 o3 l3 : Word)
    (hS0 : Success bytes accBase listLen 0 o0 l0) (hl0 : l0.toNat ≤ 8)
    (hz0 : ∀ k, k < l0.toNat → bytes.getD (o0.toNat + k) 0 = 0)
    (hS1 : Success bytes accBase listLen 1 o1 l1) (hl1 : l1.toNat ≤ 32)
    (hz1 : ∀ k, k < l1.toNat → bytes.getD (o1.toNat + k) 0 = 0)
    (hS3 : Success bytes accBase listLen 3 o3 l3) (hl3 : l3.toNat = 32)
    (hm3 : ∀ k, k < 32 → bytes.getD (o3.toNat + k) 0 = aieEmptyCodeHashBytes.getD k 0) :
    accountEip161Empty bytes accBase listLen :=
  ⟨o0, l0, o1, l1, o3, l3, hS0, hl0, hz0, hS1, hl1, hz1, hS3, hl3, hm3⟩

/-! ## The unified whole-program verdict classification and abstract return post

    `aieOutcome` records the four ABI outcomes; the empty branch carries the
    lenient model verdict (`accountEip161Empty`).  `aiePost` is the abstract
    caller-visible post at `raIn`: registers restored, `x10 = a0`, the output
    cell holding the verdict value, and the whole scratch/frame footprint owned.
    All four verdict-return bridges weaken into it. -/

/-- The four-way ABI classification of `(a0, outVal)`. -/
def aieOutcome (bytes : List (BitVec 8)) (accBase : Word) (listLen : Nat)
    (a0 outVal : Word) : Prop :=
  (a0 = 0 ∧ outVal = 1 ∧ accountEip161Empty bytes accBase listLen) ∨
  (a0 = 0 ∧ outVal = 0) ∨
  (a0 = 1 ∧ outVal = 0) ∨
  (a0 = 2 ∧ outVal = 0)

/-- The owned scratch/frame residual carried to the caller: all scratch
    registers, the two RLP scratch cells, the seven saved-frame slots, and the
    two `bytesRegion`s (account buffer + `EMPTY_CODE_HASH` constant). -/
def aieJunk (newSp accBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x19 ** regOwn .x20 ** regOwn .x21 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  memOwn OffA ** memOwn LenA **
  memOwn newSp ** memOwn (newSp + 8) ** memOwn (newSp + 16) ** memOwn (newSp + 24) **
  memOwn (newSp + 32) ** memOwn (newSp + 40) ** memOwn (newSp + 48) **
  bytesRegion accBase bytes ** bytesRegion ECB aieEmptyCodeHashBytes

theorem pcFree_aieJunk (newSp accBase : Word) (bytes : List (BitVec 8)) :
    (aieJunk newSp accBase bytes).pcFree := by
  unfold aieJunk
  repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj

/-- Abstract whole-program return post at `raIn`. -/
def aiePost (sp0 spA raIn c8 c9 c18 newSp accBase outPtr : Word)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ (a0 outVal : Word),
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ c8) ** (.x9 ↦ᵣ c9) ** (.x18 ↦ᵣ c18) **
      aieSlots spA raIn c8 c9 c18 ** (.x10 ↦ᵣ a0) ** (outPtr ↦ₘ outVal) **
      aieJunk newSp accBase bytes ** ⌜aieOutcome bytes accBase listLen a0 outVal⌝) h

/-! ## Field-3 (code_hash) size-check head ([69]-[73], `AB+276 → {AB+404, AB+296}`)

    `la x5 = aie_length ;; LD x6 = len ;; LI x7 = 32 ;; BNE x6, x7`.  A code-hash
    length `≠ 32` branches to the size-fail verdict `AB+404`; length `= 32`
    falls to the content-pointer setup at `AB+296`. -/

/-- `k`-th instruction membership into the full closure `fullCode`. -/
local macro "aieFC" k:term ", " A:term ", " ins:term : term =>
  `((fun a i hi => aie_mono a i
      (CodeReq.ofProg_mem_at AB $A accountIsEip161Empty_prog $k $ins (by bv_omega)
        (by rw [aie_prog_length]; omega) rfl (by rw [aie_prog_length]; norm_num) a i hi)))

set_option maxRecDepth 8000 in
theorem aieField3SizeHead (v5 v6 v7 len3 : Word) :
    cpsBranchWithin 5 (AB + 276) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (LenA ↦ₘ len3))
      (AB + 404)
        ((.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len3) ** (.x7 ↦ᵣ (32 : Word)) **
          (LenA ↦ₘ len3) ** ⌜len3 ≠ (32 : Word)⌝)
      (AB + 296)
        ((.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len3) ** (.x7 ↦ᵣ (32 : Word)) **
          (LenA ↦ₘ len3) ** ⌜len3 = (32 : Word)⌝) := by
  -- [69-70] la x5 = aie_length
  have hau69 := CodeReq.ofProg_mem_at AB (AB + 276) accountIsEip161Empty_prog 69
    (.AUIPC .x5 (EvmAsm.Codegen.laHi GuestAddrs.aie_length
      (GuestAddrs.account_is_eip161_empty + 276))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had70 := CodeReq.ofProg_mem_at AB (AB + 280) accountIsEip161Empty_prog 70
    (.ADDI .x5 .x5 (EvmAsm.Codegen.laLo GuestAddrs.aie_length
      (GuestAddrs.account_is_eip161_empty + 276))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h70 := EvmAsm.Rv64.la_materialize_within .x5 v5 (AB + 276) LenA (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau69 a i hi))
    (fun a i hi => aie_mono a i (had70 a i hi))
  have f70 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (LenA ↦ₘ len3)) (by pcfR) h70
  -- [71] LD x6 x5 0 : x6 := len3
  have h71 := ld_spec_gen_within .x6 .x5 LenA v6 len3 (0 : BitVec 12) (AB + 284) (by decide)
  rw [show LenA + signExtend12 (0 : BitVec 12) = LenA from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h71
  have e71 := cpsTripleWithin_extend_code (aieFC 71, (AB + 284), (.LD .x6 .x5 (0 : BitVec 12))) h71
  have f71 := cpsTripleWithin_frameR ((.x7 ↦ᵣ v7)) (by pcfR) e71
  -- [72] LI x7 32
  have h72 := li_spec_gen_within .x7 v7 (32 : Word) (AB + 288) (by decide)
  have e72 := cpsTripleWithin_extend_code (aieFC 72, (AB + 288), (.LI .x7 (32 : Word))) h72
  have f72 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len3) ** (LenA ↦ₘ len3)) (by pcfR) e72
  -- compose the four straight steps AB+276 → AB+292
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f70 f71
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f72
  -- [73] BNE x6, x7 : len3 ≠ 32 → AB+404 ; len3 = 32 → AB+296
  have hbne := bne_spec_gen_within .x6 .x7 (112 : BitVec 13) len3 (32 : Word) (AB + 292)
  rw [show (AB + 292 : Word) + signExtend13 (112 : BitVec 13) = AB + 404 from by
      rw [show signExtend13 (112 : BitVec 13) = (112 : Word) from by decide]; bv_omega,
    show (AB + 292 : Word) + 4 = AB + 296 from by bv_omega] at hbne
  have ebne := cpsBranchWithin_extend_code
    (aieFC 73, (AB + 292), (.BNE .x6 .x7 (112 : BitVec 13))) hbne
  have fbne := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ LenA) ** (LenA ↦ₘ len3)) (by pcfR) ebne
  -- glue: straight ;; branch
  have hbr := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_chunked hp) s2 fbne
  refine cpsBranchWithin_mono_nSteps (by omega)
    (cpsBranchWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) (fun _ hp => by xperm_chunked hp) hbr)


/-! ## Field-3 content-pointer setup ([74]-[79], `AB+296 → AB+320`)

    `la x5 = aie_offset ;; LD x28 = offset ;; ADD x28, x8, x28 ;; la x31 = ECB`.
    Materialises the content cursor `x28 = accBase + offset` and the
    `EMPTY_CODE_HASH` cursor `x31 = ECB`. -/

set_option maxRecDepth 8000 in
theorem aieField3PtrSetup (v5 accBase v28 v31 offset3 : Word) :
    cpsTripleWithin 6 (AB + 296) (AB + 320) fullCode
      ((.x5 ↦ᵣ v5) ** (.x8 ↦ᵣ accBase) ** (.x28 ↦ᵣ v28) ** (.x31 ↦ᵣ v31) **
        (OffA ↦ₘ offset3))
      ((.x5 ↦ᵣ OffA) ** (.x8 ↦ᵣ accBase) ** (.x28 ↦ᵣ (accBase + offset3)) **
        (.x31 ↦ᵣ ECB) ** (OffA ↦ₘ offset3)) := by
  -- [74-75] la x5 = aie_offset
  have hau74 := CodeReq.ofProg_mem_at AB (AB + 296) accountIsEip161Empty_prog 74
    (.AUIPC .x5 (EvmAsm.Codegen.laHi GuestAddrs.aie_offset
      (GuestAddrs.account_is_eip161_empty + 296))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had75 := CodeReq.ofProg_mem_at AB (AB + 300) accountIsEip161Empty_prog 75
    (.ADDI .x5 .x5 (EvmAsm.Codegen.laLo GuestAddrs.aie_offset
      (GuestAddrs.account_is_eip161_empty + 296))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h75 := EvmAsm.Rv64.la_materialize_within .x5 v5 (AB + 296) OffA (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau74 a i hi))
    (fun a i hi => aie_mono a i (had75 a i hi))
  have f75 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ accBase) ** (.x28 ↦ᵣ v28) ** (.x31 ↦ᵣ v31) ** (OffA ↦ₘ offset3))
    (by pcfR) h75
  -- [76] LD x28 x5 0 : x28 := offset3
  have h76 := ld_spec_gen_within .x28 .x5 OffA v28 offset3 (0 : BitVec 12) (AB + 304) (by decide)
  rw [show OffA + signExtend12 (0 : BitVec 12) = OffA from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h76
  have e76 := cpsTripleWithin_extend_code (aieFC 76, (AB + 304), (.LD .x28 .x5 (0 : BitVec 12))) h76
  have f76 := cpsTripleWithin_frameR ((.x8 ↦ᵣ accBase) ** (.x31 ↦ᵣ v31)) (by pcfR) e76
  -- [77] ADD x28 x8 x28 : x28 := accBase + offset3
  have h77 := add_spec_gen_rd_eq_rs2_within .x28 .x8 accBase offset3 (AB + 308) (by decide)
  have e77 := cpsTripleWithin_extend_code (aieFC 77, (AB + 308), (.ADD .x28 .x8 .x28)) h77
  have f77 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ OffA) ** (.x31 ↦ᵣ v31) ** (OffA ↦ₘ offset3)) (by pcfR) e77
  -- [78-79] la x31 = aie_empty_code_hash
  have hau78 := CodeReq.ofProg_mem_at AB (AB + 312) accountIsEip161Empty_prog 78
    (.AUIPC .x31 (EvmAsm.Codegen.laHi GuestAddrs.aie_empty_code_hash
      (GuestAddrs.account_is_eip161_empty + 312))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had79 := CodeReq.ofProg_mem_at AB (AB + 316) accountIsEip161Empty_prog 79
    (.ADDI .x31 .x31 (EvmAsm.Codegen.laLo GuestAddrs.aie_empty_code_hash
      (GuestAddrs.account_is_eip161_empty + 312))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h79 := EvmAsm.Rv64.la_materialize_within .x31 v31 (AB + 312) ECB (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau78 a i hi))
    (fun a i hi => aie_mono a i (had79 a i hi))
  have f79 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ OffA) ** (.x8 ↦ᵣ accBase) ** (.x28 ↦ᵣ (accBase + offset3)) **
      (OffA ↦ₘ offset3)) (by pcfR) h79
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f75 f76
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f77
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 f79
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s3)


end EvmAsm.Codegen.AccountIsEip161EmptySpec
