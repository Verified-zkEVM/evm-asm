/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose

  Whole-program caller contract `account_is_eip161_empty_spec_within` for the
  108-instruction `accountIsEip161Empty_prog` (K137, `AccountFields.lean`).

  Composes the three byte-scan loop lemmas (`AccountIsEip161EmptyLoop.lean`),
  the emptiness model (`AccountIsEip161EmptySpec.lean`, `accountEip161Empty`),
  and three calls to the strict `rlp_list_nth_item` selector
  (`RlpListNthItemSAsm.lean`, `rlpListNthItem_spec_within`) into the genuine,
  total, lenient contract:

    a0 = 0 ∧ out = (if accountEip161Empty bytes accBase listLen then 1 else 0)
    a0 = 1 ⟺ RLP parse failure ∨ nonce len > 8 ∨ balance len > 32
    a0 = 2 ⟺ code_hash len ≠ 32

  Follows the K20 call-adapter pattern of
  `HeaderValidateExtraDataLengthSpec.hvedCall` (#10337).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountIsEip161EmptyLoop
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.AccountIsEip161EmptySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

/-! ## Code-region monotonicity -/

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

theorem aie_disjoint : aieCode.Disjoint RlpListNthItemSAsm.code := by
  unfold aieCode RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [aie_prog_length]; decide
  · rw [RlpListNthItemSAsm.total_length]; decide
  · right
    rw [RlpListNthItemSAsm.total_length]; decide

#print axioms aie_disjoint

/-- K20's linked code is subsumed by the AIE full closure. -/
theorem k20_mono :
    ∀ a i, RlpListNthItemSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right aie_disjoint (fun _ _ h => h) a i hi

/-- The AIE body's own code is subsumed by the full closure. -/
theorem aie_mono : ∀ a i, aieCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

/-- `k`-th instruction membership into the full closure `fullCode`. -/
local macro "aieFC" k:term ", " A:term ", " ins:term : term =>
  `((fun a i hi => aie_mono a i
      (CodeReq.ofProg_mem_at AB $A accountIsEip161Empty_prog $k $ins (by bv_omega)
        (by rw [aie_prog_length]; omega) rfl (by rw [aie_prog_length]; norm_num) a i hi)))

/-! ## Output-cell scratch addresses -/

abbrev OffA : Word := (GuestAddrs.aie_offset : Word)
abbrev LenA : Word := (GuestAddrs.aie_length : Word)
abbrev ECB : Word := (GuestAddrs.aie_empty_code_hash : Word)

/-- The four AIE frame slots (`ra`, and the callee-saved `x8`/`x9`/`x18`) stored
    at `spA .. spA+24`, carrying the given values. -/
def aieSlots (spA raS c8 c9 c18 : Word) : Assertion :=
  (spA ↦ₘ raS) ** ((spA + 8) ↦ₘ c8) ** ((spA + 16) ↦ₘ c9) ** ((spA + 24) ↦ₘ c18)

/-- The K20-callee-saved snapshot at each AIE call: `x8/x9/x18 = accBase/lenW/outPtr`
    (set by the AIE prologue), `x19/x20/x21` the caller's `s3/s4/s5`, `ra` the
    per-call return address. -/
def mkSaved (ra accBase lenW outPtr s3 s4 s5 : Word) : Saved :=
  ⟨ra, accBase, lenW, outPtr, s3, s4, s5⟩

/-- K20 field-call precondition footprint at SP = `spA`, output cells
    `aie_offset`/`aie_length`, list `bytes` at `accBase`. -/
def aieCalleePre (spA newSp accBase lenW idxW oldOff oldLen : Word) (saved : Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spA) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
  (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) **
  (.x21 ↦ᵣ saved.s5) ** frameSlotsOwn listNthFrame newSp **
  entryRest accBase lenW idxW OffA LenA oldOff oldLen bytes

/-! ## Prologue chunk A — frame allocation and save ([0]-[4]) -/

set_option maxRecDepth 8000 in
/-- Allocate the 40-byte AIE frame and save `ra`, `x8`, `x9`, `x18`. -/
theorem aieChunkA (sp0 spA raIn c8 c9 c18 q0 q1 q2 q3 : Word)
    (hspA : spA = sp0 + signExtend12 (-40 : BitVec 12)) :
    cpsTripleWithin 5 AB (AB + 20) fullCode
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ c8) ** (.x9 ↦ᵣ c9) **
       (.x18 ↦ᵣ c18) ** aieSlots spA q0 q1 q2 q3)
      ((.x2 ↦ᵣ spA) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ c8) ** (.x9 ↦ᵣ c9) **
       (.x18 ↦ᵣ c18) ** aieSlots spA raIn c8 c9 c18) := by
  -- [0] ADDI x2 x2 -40 : sp0 → spA
  have h0 := addi_spec_gen_same_within .x2 sp0 (-40 : BitVec 12) AB (by decide)
  rw [← hspA] at h0
  have e0 := cpsTripleWithin_extend_code (aieFC 0, AB, (.ADDI .x2 .x2 (-40 : BitVec 12))) h0
  have f0 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ c8) ** (.x9 ↦ᵣ c9) ** (.x18 ↦ᵣ c18) **
     (spA ↦ₘ q0) ** ((spA + 8) ↦ₘ q1) ** ((spA + 16) ↦ₘ q2) ** ((spA + 24) ↦ₘ q3))
    (by pcfR) e0
  -- [1] SD x2 x1 0 : store raIn at [spA]
  have h1 := sd_spec_gen_within .x2 .x1 spA raIn q0 (0 : BitVec 12) (AB + 4)
  rw [show spA + signExtend12 (0 : BitVec 12) = spA from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h1
  have e1 := cpsTripleWithin_extend_code (aieFC 1, (AB + 4), (.SD .x2 .x1 (0 : BitVec 12))) h1
  have f1 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ c8) ** (.x9 ↦ᵣ c9) ** (.x18 ↦ᵣ c18) **
     ((spA + 8) ↦ₘ q1) ** ((spA + 16) ↦ₘ q2) ** ((spA + 24) ↦ₘ q3)) (by pcfR) e1
  -- [2] SD x2 x8 8 : store c8 at [spA+8]
  have h2 := sd_spec_gen_within .x2 .x8 spA c8 q1 (8 : BitVec 12) (AB + 8)
  rw [show spA + signExtend12 (8 : BitVec 12) = spA + 8 from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]] at h2
  have e2 := cpsTripleWithin_extend_code (aieFC 2, (AB + 8), (.SD .x2 .x8 (8 : BitVec 12))) h2
  have f2 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x9 ↦ᵣ c9) ** (.x18 ↦ᵣ c18) **
     (spA ↦ₘ raIn) ** ((spA + 16) ↦ₘ q2) ** ((spA + 24) ↦ₘ q3)) (by pcfR) e2
  -- [3] SD x2 x9 16 : store c9 at [spA+16]
  have h3 := sd_spec_gen_within .x2 .x9 spA c9 q2 (16 : BitVec 12) (AB + 12)
  rw [show spA + signExtend12 (16 : BitVec 12) = spA + 16 from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]] at h3
  have e3 := cpsTripleWithin_extend_code (aieFC 3, (AB + 12), (.SD .x2 .x9 (16 : BitVec 12))) h3
  have f3 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ c8) ** (.x18 ↦ᵣ c18) **
     (spA ↦ₘ raIn) ** ((spA + 8) ↦ₘ c8) ** ((spA + 24) ↦ₘ q3)) (by pcfR) e3
  -- [4] SD x2 x18 24 : store c18 at [spA+24]
  have h4 := sd_spec_gen_within .x2 .x18 spA c18 q3 (24 : BitVec 12) (AB + 16)
  rw [show spA + signExtend12 (24 : BitVec 12) = spA + 24 from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]] at h4
  have e4 := cpsTripleWithin_extend_code (aieFC 4, (AB + 16), (.SD .x2 .x18 (24 : BitVec 12))) h4
  have f4 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ c8) ** (.x9 ↦ᵣ c9) **
     (spA ↦ₘ raIn) ** ((spA + 8) ↦ₘ c8) ** ((spA + 16) ↦ₘ c9)) (by pcfR) e4
  have s01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f0 f1
  have s02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s01 f2
  have s03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s02 f3
  have s04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s03 f4
  refine cpsTripleWithin_weaken (fun _ hp => by unfold aieSlots at hp; xperm_chunked hp)
    (fun _ hq => by unfold aieSlots; xperm_chunked hq) s04

#print axioms aieChunkA

/-! ## Prologue chunk B — argument moves and output-cell zeroing ([5]-[8]) -/

set_option maxRecDepth 8000 in
/-- Move `accBase`/`lenW`/`outPtr` into `x8`/`x9`/`x18` and zero the output cell. -/
theorem aieChunkB (accBase lenW outPtr c8 c9 c18 oldOut : Word) :
    cpsTripleWithin 4 (AB + 20) (AB + 36) fullCode
      ((.x8 ↦ᵣ c8) ** (.x9 ↦ᵣ c9) ** (.x18 ↦ᵣ c18) ** (.x10 ↦ᵣ accBase) **
       (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ oldOut))
      ((.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outPtr) ** (.x10 ↦ᵣ accBase) **
       (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
       (outPtr ↦ₘ (0 : Word))) := by
  -- [5] MV x8 x10
  have h5 := mv_spec_gen_within .x8 .x10 accBase c8 (AB + 20) (by decide)
  have e5 := cpsTripleWithin_extend_code (aieFC 5, (AB + 20), (.MV .x8 .x10)) h5
  have f5 := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ c9) ** (.x18 ↦ᵣ c18) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outPtr) **
     (.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ oldOut)) (by pcfR) e5
  -- [6] MV x9 x11
  have h6 := mv_spec_gen_within .x9 .x11 lenW c9 (AB + 24) (by decide)
  have e6 := cpsTripleWithin_extend_code (aieFC 6, (AB + 24), (.MV .x9 .x11)) h6
  have f6 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ accBase) ** (.x18 ↦ᵣ c18) ** (.x10 ↦ᵣ accBase) ** (.x12 ↦ᵣ outPtr) **
     (.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ oldOut)) (by pcfR) e6
  -- [7] MV x18 x12
  have h7 := mv_spec_gen_within .x18 .x12 outPtr c18 (AB + 28) (by decide)
  have e7 := cpsTripleWithin_extend_code (aieFC 7, (AB + 28), (.MV .x18 .x12)) h7
  have f7 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) **
     (.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ oldOut)) (by pcfR) e7
  -- [8] SD x18 x0 0 : store 0 to the output cell
  have h8 := sd_spec_gen_within .x18 .x0 outPtr (0 : Word) oldOut (0 : BitVec 12) (AB + 32)
  rw [show outPtr + signExtend12 (0 : BitVec 12) = outPtr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h8
  have e8 := cpsTripleWithin_extend_code (aieFC 8, (AB + 32), (.SD .x18 .x0 (0 : BitVec 12))) h8
  have f8 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) **
     (.x12 ↦ᵣ outPtr)) (by pcfR) e8
  have s56 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f5 f6
  have s57 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s56 f7
  have s58 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s57 f8
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) s58

#print axioms aieChunkB

/-! ## Prologue chunk C — call-argument setup ([9]-[15]) -/

set_option maxRecDepth 8000 in
/-- Load the field-0 call arguments: `x10 = accBase`, `x11 = lenW`, `x12 = 0`,
    `x13 = &aie_offset`, `x14 = &aie_length`. -/
theorem aieChunkC (accBase lenW outPtr old13 old14 : Word) :
    cpsTripleWithin 7 (AB + 36) (AB + 64) fullCode
      ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW) **
       (.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14))
      ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW) **
       (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ OffA) ** (.x14 ↦ᵣ LenA)) := by
  -- [9] MV x10 x8
  have h9 := mv_spec_gen_within .x10 .x8 accBase accBase (AB + 36) (by decide)
  have e9 := cpsTripleWithin_extend_code (aieFC 9, (AB + 36), (.MV .x10 .x8)) h9
  have f9 := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW) ** (.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ old13) **
     (.x14 ↦ᵣ old14)) (by pcfR) e9
  -- [10] MV x11 x9
  have h10 := mv_spec_gen_within .x11 .x9 lenW lenW (AB + 40) (by decide)
  have e10 := cpsTripleWithin_extend_code (aieFC 10, (AB + 40), (.MV .x11 .x9)) h10
  have f10 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ old13) **
     (.x14 ↦ᵣ old14)) (by pcfR) e10
  -- [11] LI x12 0
  have h11 := li_spec_gen_within .x12 outPtr (0 : Word) (AB + 44) (by decide)
  have e11 := cpsTripleWithin_extend_code (aieFC 11, (AB + 44), (.LI .x12 (0 : Word))) h11
  have f11 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW) **
     (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14)) (by pcfR) e11
  -- [12-13] la x13 = aie_offset
  have hau12 := CodeReq.ofProg_mem_at AB (AB + 48) accountIsEip161Empty_prog 12
    (.AUIPC .x13 (EvmAsm.Codegen.laHi GuestAddrs.aie_offset
      (GuestAddrs.account_is_eip161_empty + 48))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had13 := CodeReq.ofProg_mem_at AB (AB + 52) accountIsEip161Empty_prog 13
    (.ADDI .x13 .x13 (EvmAsm.Codegen.laLo GuestAddrs.aie_offset
      (GuestAddrs.account_is_eip161_empty + 48))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h13 := EvmAsm.Rv64.la_materialize_within .x13 old13 (AB + 48) OffA (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau12 a i hi))
    (fun a i hi => aie_mono a i (had13 a i hi))
  have f13 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW) **
     (.x12 ↦ᵣ (0 : Word)) ** (.x14 ↦ᵣ old14)) (by pcfR) h13
  -- [14-15] la x14 = aie_length
  have hau14 := CodeReq.ofProg_mem_at AB (AB + 56) accountIsEip161Empty_prog 14
    (.AUIPC .x14 (EvmAsm.Codegen.laHi GuestAddrs.aie_length
      (GuestAddrs.account_is_eip161_empty + 56))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had15 := CodeReq.ofProg_mem_at AB (AB + 60) accountIsEip161Empty_prog 15
    (.ADDI .x14 .x14 (EvmAsm.Codegen.laLo GuestAddrs.aie_length
      (GuestAddrs.account_is_eip161_empty + 56))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h15 := EvmAsm.Rv64.la_materialize_within .x14 old14 (AB + 56) LenA (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau14 a i hi))
    (fun a i hi => aie_mono a i (had15 a i hi))
  have f15 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW) **
     (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ OffA)) (by pcfR) h15
  have s910 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f9 f10
  have s911 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s910 f11
  have s913 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s911 f13
  have s915 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s913 f15
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) s915

#print axioms aieChunkC

end EvmAsm.Codegen.AccountIsEip161EmptySpec
