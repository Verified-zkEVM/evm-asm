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

/-! ## Prologue — full caller footprint and composition ([0]-[15]) -/

/-- Pre-prologue caller footprint: ABI args `a0/a1/a2 = accBase/lenW/outPtr`,
    caller callee-saved `x8/x9/x18 = c8/c9/c18` (restored on return), `x19/x20/x21
    = s3/s4/s5` (preserved by K20), the AIE frame slots owned, the K20 stack frame
    below `newSp`, the output cell, and the two `aie_offset`/`aie_length` scratch
    cells. -/
def aiePre (sp0 spA newSp raIn accBase lenW outPtr c8 c9 c18 q0 q1 q2 q3
    old13 old14 oldOut oldOff oldLen s3 s4 s5 : Word) (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ c8) ** (.x9 ↦ᵣ c9) ** (.x18 ↦ᵣ c18) **
  aieSlots spA q0 q1 q2 q3 **
  (.x10 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outPtr) **
  (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) **
  (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion accBase bytes ** frameSlotsOwn listNthFrame newSp **
  (outPtr ↦ₘ oldOut) ** (OffA ↦ₘ oldOff) ** (LenA ↦ₘ oldLen)

set_option maxRecDepth 8000 in
/-- The full prologue [0]-[15]: from the caller footprint to K20's field-0 call
    footprint, framed by the wrapper's own saved slots, output cell, and the
    incumbent `x1 = raIn`. -/
theorem aieHead (sp0 spA newSp raIn accBase lenW outPtr c8 c9 c18 q0 q1 q2 q3
    old13 old14 oldOut oldOff oldLen s3 s4 s5 : Word) (bytes : List (BitVec 8))
    (hspA : spA = sp0 + signExtend12 (-40 : BitVec 12)) :
    cpsTripleWithin 16 AB (AB + 64) fullCode
      (aiePre sp0 spA newSp raIn accBase lenW outPtr c8 c9 c18 q0 q1 q2 q3
        old13 old14 oldOut oldOff oldLen s3 s4 s5 bytes)
      ((.x1 ↦ᵣ raIn) ** aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ (0 : Word)) **
        aieCalleePre spA newSp accBase lenW (0 : Word) oldOff oldLen
          (mkSaved (AB + 68) accBase lenW outPtr s3 s4 s5) bytes) := by
  have hA := aieChunkA sp0 spA raIn c8 c9 c18 q0 q1 q2 q3 hspA
  have hB := aieChunkB accBase lenW outPtr c8 c9 c18 oldOut
  have hC := aieChunkC accBase lenW outPtr old13 old14
  -- Frame each chunk against the shared active atoms the other chunks touch.
  have fA := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outPtr) **
     (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ oldOut))
    (by pcfR) hA
  have fB := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spA) ** aieSlots spA raIn c8 c9 c18 **
     (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14)) (by unfold aieSlots; pcfR) hB
  have fC := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spA) ** (.x18 ↦ᵣ outPtr) **
     aieSlots spA raIn c8 c9 c18 ** (.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (0 : Word)))
    (by unfold aieSlots; pcfR) hC
  have sAB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) fA fB
  have sABC := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) sAB fC
  -- Frame the untouched remainder around the whole prologue.
  have hframed := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** bytesRegion accBase bytes **
     frameSlotsOwn listNthFrame newSp ** (OffA ↦ₘ oldOff) ** (LenA ↦ₘ oldLen))
    (by pcfR) sABC
  refine cpsTripleWithin_weaken (fun _ hp => by
      unfold aiePre at hp; xperm_chunked hp) (fun _ hq => by
      unfold aieCalleePre entryRest mkSaved; xperm_chunked hq) hframed

#print axioms aieHead

/-! ## Field-0 (nonce) RLP call adapter — prologue ;; jal ;; K20 ([0]-[16]+callee) -/

set_option maxRecDepth 8000 in
/-- Prologue ;; `jal rlp_list_nth_item` (field index 0) ;; the strict K20 selector.
    The post is K20's `returnResult` for field 0 (its `aie_offset`/`aie_length`
    cells written, its `Result` pinned), framed by the AIE saved slots and the
    zeroed output cell. -/
theorem aieCall0 (sp0 spA newSp raIn accBase lenW outPtr c8 c9 c18 q0 q1 q2 q3
    old13 old14 oldOut oldOff oldLen s3 s4 s5 : Word) (bytes : List (BitVec 8))
    (listLen : Nat)
    (hspA : spA = sp0 + signExtend12 (-40 : BitVec 12))
    (hnewSp : newSp = spA + signExtend12 (-64 : BitVec 12))
    (hlistLenW : lenW = BitVec.ofNat 64 listLen)
    (hsalign : accBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (16 + 1 + ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9)) AB (AB + 68) fullCode
      (aiePre sp0 spA newSp raIn accBase lenW outPtr c8 c9 c18 q0 q1 q2 q3
        old13 old14 oldOut oldOff oldLen s3 s4 s5 bytes)
      (returnResult spA newSp accBase (0 : Word) OffA LenA oldOff oldLen
          (mkSaved (AB + 68) accBase lenW outPtr s3 s4 s5) bytes listLen 0 **
        aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ (0 : Word))) := by
  have hhead := aieHead sp0 spA newSp raIn accBase lenW outPtr c8 c9 c18 q0 q1 q2 q3
    old13 old14 oldOut oldOff oldLen s3 s4 s5 bytes hspA
  -- [16] jal x1, rlp_list_nth_item
  have hjal := jal_link_spec_within (EvmAsm.Codegen.jalOff GuestAddrs.rlp_list_nth_item
    (GuestAddrs.account_is_eip161_empty + 64)) (AB + 64) raIn
  rw [show (AB + 64) + signExtend21 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.account_is_eip161_empty + 64)) = B from by decide,
    show (AB + 64 + 4 : Word) = AB + 68 from by bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code (aieFC 16, (AB + 64),
    (.JAL .x1 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.account_is_eip161_empty + 64)))) hjal
  have hjalF := cpsTripleWithin_frameR
    (aieCalleePre spA newSp accBase lenW (0 : Word) oldOff oldLen
        (mkSaved (AB + 68) accBase lenW outPtr s3 s4 s5) bytes **
      aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ (0 : Word)))
    (by unfold aieCalleePre entryRest aieSlots; pcfR) hjalC
  -- The K20 selector.
  have hcallee0 := rlpListNthItem_spec_within spA newSp accBase lenW (0 : Word) OffA LenA
    oldOff oldLen (mkSaved (AB + 68) accBase lenW outPtr s3 s4 s5) bytes listLen 0
    hnewSp hlistLenW rfl (by decide) hsalign hslack hover hvalid
    (by show (AB + 68 : Word) &&& ~~~(1 : Word) = AB + 68; decide)
  have hcalleeC := cpsTripleWithin_extend_code k20_mono hcallee0
  have hcalleeF := cpsTripleWithin_frameR
    (aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ (0 : Word)))
    (by unfold aieSlots; pcfR) hcalleeC
  have hcallee : cpsTripleWithin ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9) B (AB + 68) fullCode
      ((.x1 ↦ᵣ (AB + 68)) **
        (aieCalleePre spA newSp accBase lenW (0 : Word) oldOff oldLen
            (mkSaved (AB + 68) accBase lenW outPtr s3 s4 s5) bytes **
          aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ (0 : Word))))
      (returnResult spA newSp accBase (0 : Word) OffA LenA oldOff oldLen
          (mkSaved (AB + 68) accBase lenW outPtr s3 s4 s5) bytes listLen 0 **
        aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ (0 : Word))) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold aieCalleePre entryRest at hp
      rw [regsAt_listNthFrame]
      unfold entryRest
      simp only [mkSaved] at hp ⊢
      xperm_chunked hp) (fun _ hq => hq) hcalleeF
  -- Compose head ;; jal ;; callee.
  have hhj := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hhead hjalF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hhj hcallee

#print axioms aieCall0

/-! ## Mid-call (fields 1/3) RLP call adapters

    Both later calls start from the same K20-ready footprint at their entry PC:
    the callee-saved arg registers (`x8/x9/x18 = accBase/lenW/outPtr`) live,
    SP still at `spA`, the K20 frame owned below `newSp`, the output cell and
    the `aie_offset`/`aie_length` scratch cells present, the dispatch scratch
    owned, and the AIE frame slots carried through. -/

/-- K20-ready footprint shared by the field-1 and field-3 call sites. -/
def aieMidPre (spA newSp accBase lenW outPtr raIn c8 c9 c18 v1 v10 v11 v12 v13 v14
    outv oldOff oldLen s3 s4 s5 : Word) (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spA) ** (.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outPtr) **
  (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  (.x1 ↦ᵣ v1) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
  (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion accBase bytes ** frameSlotsOwn listNthFrame newSp **
  (outPtr ↦ₘ outv) ** (OffA ↦ₘ oldOff) ** (LenA ↦ₘ oldLen) **
  aieSlots spA raIn c8 c9 c18

set_option maxRecDepth 8000 in
/-- Field-1 (balance) call adapter: setup [36]-[42] ;; `jal` [43] ;; K20 (index 1),
    `AB+144 → AB+176`. -/
theorem aieCall1 (spA newSp accBase lenW outPtr raIn c8 c9 c18 v1 v10 v11 v12 v13 v14
    outv oldOff oldLen s3 s4 s5 : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spA + signExtend12 (-64 : BitVec 12))
    (hlistLenW : lenW = BitVec.ofNat 64 listLen)
    (hsalign : accBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 + 1 + ((12 + ((85 + 93 * (1 + 2)) + 6)) + 9)) (AB + 144) (AB + 176)
      fullCode
      (aieMidPre spA newSp accBase lenW outPtr raIn c8 c9 c18 v1 v10 v11 v12 v13 v14
        outv oldOff oldLen s3 s4 s5 bytes)
      (returnResult spA newSp accBase (1 : Word) OffA LenA oldOff oldLen
          (mkSaved (AB + 176) accBase lenW outPtr s3 s4 s5) bytes listLen 1 **
        aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv)) := by
  -- setup [36] MV x10 x8
  have h36 := mv_spec_gen_within .x10 .x8 accBase v10 (AB + 144) (by decide)
  have e36 := cpsTripleWithin_extend_code (aieFC 36, (AB + 144), (.MV .x10 .x8)) h36
  have f36 := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x9 ↦ᵣ lenW) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
     (.x14 ↦ᵣ v14)) (by pcfR) e36
  -- [37] MV x11 x9
  have h37 := mv_spec_gen_within .x11 .x9 lenW v11 (AB + 148) (by decide)
  have e37 := cpsTripleWithin_extend_code (aieFC 37, (AB + 148), (.MV .x11 .x9)) h37
  have f37 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
     (.x14 ↦ᵣ v14)) (by pcfR) e37
  -- [38] LI x12 1
  have h38 := li_spec_gen_within .x12 v12 (1 : Word) (AB + 152) (by decide)
  have e38 := cpsTripleWithin_extend_code (aieFC 38, (AB + 152), (.LI .x12 (1 : Word))) h38
  have f38 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) (by pcfR) e38
  -- [39-40] la x13 = aie_offset
  have hau39 := CodeReq.ofProg_mem_at AB (AB + 156) accountIsEip161Empty_prog 39
    (.AUIPC .x13 (EvmAsm.Codegen.laHi GuestAddrs.aie_offset
      (GuestAddrs.account_is_eip161_empty + 156))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had40 := CodeReq.ofProg_mem_at AB (AB + 160) accountIsEip161Empty_prog 40
    (.ADDI .x13 .x13 (EvmAsm.Codegen.laLo GuestAddrs.aie_offset
      (GuestAddrs.account_is_eip161_empty + 156))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h40 := EvmAsm.Rv64.la_materialize_within .x13 v13 (AB + 156) OffA (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau39 a i hi))
    (fun a i hi => aie_mono a i (had40 a i hi))
  have f40 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW) **
     (.x12 ↦ᵣ (1 : Word)) ** (.x14 ↦ᵣ v14)) (by pcfR) h40
  -- [41-42] la x14 = aie_length
  have hau41 := CodeReq.ofProg_mem_at AB (AB + 164) accountIsEip161Empty_prog 41
    (.AUIPC .x14 (EvmAsm.Codegen.laHi GuestAddrs.aie_length
      (GuestAddrs.account_is_eip161_empty + 164))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had42 := CodeReq.ofProg_mem_at AB (AB + 168) accountIsEip161Empty_prog 42
    (.ADDI .x14 .x14 (EvmAsm.Codegen.laLo GuestAddrs.aie_length
      (GuestAddrs.account_is_eip161_empty + 164))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h42 := EvmAsm.Rv64.la_materialize_within .x14 v14 (AB + 164) LenA (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau41 a i hi))
    (fun a i hi => aie_mono a i (had42 a i hi))
  have f42 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW) **
     (.x12 ↦ᵣ (1 : Word)) ** (.x13 ↦ᵣ OffA)) (by pcfR) h42
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f36 f37
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f38
  have s3c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 f40
  have hsetup := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3c f42
  -- frame the payload carried through the setup, then attach jal + K20
  have hsetupF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spA) ** (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
     (.x21 ↦ᵣ s5) ** (.x1 ↦ᵣ v1) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion accBase bytes ** frameSlotsOwn listNthFrame newSp **
     (outPtr ↦ₘ outv) ** (OffA ↦ₘ oldOff) ** (LenA ↦ₘ oldLen) **
     aieSlots spA raIn c8 c9 c18) (by unfold aieSlots; pcfR) hsetup
  -- [43] jal x1, rlp_list_nth_item
  have hjal := jal_link_spec_within (EvmAsm.Codegen.jalOff GuestAddrs.rlp_list_nth_item
    (GuestAddrs.account_is_eip161_empty + 172)) (AB + 172) v1
  rw [show (AB + 172) + signExtend21 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.account_is_eip161_empty + 172)) = B from by decide,
    show (AB + 172 + 4 : Word) = AB + 176 from by bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code (aieFC 43, (AB + 172),
    (.JAL .x1 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.account_is_eip161_empty + 172)))) hjal
  have hjalF := cpsTripleWithin_frameR
    (aieCalleePre spA newSp accBase lenW (1 : Word) oldOff oldLen
        (mkSaved (AB + 176) accBase lenW outPtr s3 s4 s5) bytes **
      aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv))
    (by unfold aieCalleePre entryRest aieSlots; pcfR) hjalC
  -- K20 selector (index 1)
  have hcallee0 := rlpListNthItem_spec_within spA newSp accBase lenW (1 : Word) OffA LenA
    oldOff oldLen (mkSaved (AB + 176) accBase lenW outPtr s3 s4 s5) bytes listLen 1
    hnewSp hlistLenW rfl (by decide) hsalign hslack hover hvalid
    (by show (AB + 176 : Word) &&& ~~~(1 : Word) = AB + 176; decide)
  have hcalleeC := cpsTripleWithin_extend_code k20_mono hcallee0
  have hcalleeF := cpsTripleWithin_frameR
    (aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv))
    (by unfold aieSlots; pcfR) hcalleeC
  have hcallee : cpsTripleWithin ((12 + ((85 + 93 * (1 + 2)) + 6)) + 9) B (AB + 176) fullCode
      ((.x1 ↦ᵣ (AB + 176)) **
        (aieCalleePre spA newSp accBase lenW (1 : Word) oldOff oldLen
            (mkSaved (AB + 176) accBase lenW outPtr s3 s4 s5) bytes **
          aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv)))
      (returnResult spA newSp accBase (1 : Word) OffA LenA oldOff oldLen
          (mkSaved (AB + 176) accBase lenW outPtr s3 s4 s5) bytes listLen 1 **
        aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv)) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold aieCalleePre entryRest at hp
      rw [regsAt_listNthFrame]
      unfold entryRest
      simp only [mkSaved] at hp ⊢
      xperm_chunked hp) (fun _ hq => hq) hcalleeF
  -- Compose setup ;; jal ;; callee.
  have hsj := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold aieCalleePre entryRest; simp only [mkSaved]; xperm_chunked hp) hsetupF hjalF
  refine cpsTripleWithin_weaken (fun _ hp => by unfold aieMidPre at hp; xperm_chunked hp)
    (fun _ hq => hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hsj hcallee)

#print axioms aieCall1

set_option maxRecDepth 8000 in
/-- Field-3 (code_hash) call adapter: setup [60]-[66] ;; `jal` [67] ;; K20 (index 3),
    `AB+240 → AB+272`. -/
theorem aieCall3 (spA newSp accBase lenW outPtr raIn c8 c9 c18 v1 v10 v11 v12 v13 v14
    outv oldOff oldLen s3 s4 s5 : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spA + signExtend12 (-64 : BitVec 12))
    (hlistLenW : lenW = BitVec.ofNat 64 listLen)
    (hsalign : accBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 + 1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9)) (AB + 240) (AB + 272)
      fullCode
      (aieMidPre spA newSp accBase lenW outPtr raIn c8 c9 c18 v1 v10 v11 v12 v13 v14
        outv oldOff oldLen s3 s4 s5 bytes)
      (returnResult spA newSp accBase (3 : Word) OffA LenA oldOff oldLen
          (mkSaved (AB + 272) accBase lenW outPtr s3 s4 s5) bytes listLen 3 **
        aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv)) := by
  -- setup [60] MV x10 x8
  have h60 := mv_spec_gen_within .x10 .x8 accBase v10 (AB + 240) (by decide)
  have e60 := cpsTripleWithin_extend_code (aieFC 60, (AB + 240), (.MV .x10 .x8)) h60
  have f60 := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x9 ↦ᵣ lenW) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
     (.x14 ↦ᵣ v14)) (by pcfR) e60
  -- [61] MV x11 x9
  have h61 := mv_spec_gen_within .x11 .x9 lenW v11 (AB + 244) (by decide)
  have e61 := cpsTripleWithin_extend_code (aieFC 61, (AB + 244), (.MV .x11 .x9)) h61
  have f61 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
     (.x14 ↦ᵣ v14)) (by pcfR) e61
  -- [62] LI x12 3
  have h62 := li_spec_gen_within .x12 v12 (3 : Word) (AB + 248) (by decide)
  have e62 := cpsTripleWithin_extend_code (aieFC 62, (AB + 248), (.LI .x12 (3 : Word))) h62
  have f62 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) (by pcfR) e62
  -- [63-64] la x13 = aie_offset
  have hau63 := CodeReq.ofProg_mem_at AB (AB + 252) accountIsEip161Empty_prog 63
    (.AUIPC .x13 (EvmAsm.Codegen.laHi GuestAddrs.aie_offset
      (GuestAddrs.account_is_eip161_empty + 252))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had64 := CodeReq.ofProg_mem_at AB (AB + 256) accountIsEip161Empty_prog 64
    (.ADDI .x13 .x13 (EvmAsm.Codegen.laLo GuestAddrs.aie_offset
      (GuestAddrs.account_is_eip161_empty + 252))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h64 := EvmAsm.Rv64.la_materialize_within .x13 v13 (AB + 252) OffA (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau63 a i hi))
    (fun a i hi => aie_mono a i (had64 a i hi))
  have f64 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW) **
     (.x12 ↦ᵣ (3 : Word)) ** (.x14 ↦ᵣ v14)) (by pcfR) h64
  -- [65-66] la x14 = aie_length
  have hau65 := CodeReq.ofProg_mem_at AB (AB + 260) accountIsEip161Empty_prog 65
    (.AUIPC .x14 (EvmAsm.Codegen.laHi GuestAddrs.aie_length
      (GuestAddrs.account_is_eip161_empty + 260))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had66 := CodeReq.ofProg_mem_at AB (AB + 264) accountIsEip161Empty_prog 66
    (.ADDI .x14 .x14 (EvmAsm.Codegen.laLo GuestAddrs.aie_length
      (GuestAddrs.account_is_eip161_empty + 260))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h66 := EvmAsm.Rv64.la_materialize_within .x14 v14 (AB + 260) LenA (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau65 a i hi))
    (fun a i hi => aie_mono a i (had66 a i hi))
  have f66 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ accBase) ** (.x8 ↦ᵣ accBase) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW) **
     (.x12 ↦ᵣ (3 : Word)) ** (.x13 ↦ᵣ OffA)) (by pcfR) h66
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f60 f61
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f62
  have s3c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 f64
  have hsetup := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3c f66
  have hsetupF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spA) ** (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
     (.x21 ↦ᵣ s5) ** (.x1 ↦ᵣ v1) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion accBase bytes ** frameSlotsOwn listNthFrame newSp **
     (outPtr ↦ₘ outv) ** (OffA ↦ₘ oldOff) ** (LenA ↦ₘ oldLen) **
     aieSlots spA raIn c8 c9 c18) (by unfold aieSlots; pcfR) hsetup
  -- [67] jal x1, rlp_list_nth_item
  have hjal := jal_link_spec_within (EvmAsm.Codegen.jalOff GuestAddrs.rlp_list_nth_item
    (GuestAddrs.account_is_eip161_empty + 268)) (AB + 268) v1
  rw [show (AB + 268) + signExtend21 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.account_is_eip161_empty + 268)) = B from by decide,
    show (AB + 268 + 4 : Word) = AB + 272 from by bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code (aieFC 67, (AB + 268),
    (.JAL .x1 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.account_is_eip161_empty + 268)))) hjal
  have hjalF := cpsTripleWithin_frameR
    (aieCalleePre spA newSp accBase lenW (3 : Word) oldOff oldLen
        (mkSaved (AB + 272) accBase lenW outPtr s3 s4 s5) bytes **
      aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv))
    (by unfold aieCalleePre entryRest aieSlots; pcfR) hjalC
  have hcallee0 := rlpListNthItem_spec_within spA newSp accBase lenW (3 : Word) OffA LenA
    oldOff oldLen (mkSaved (AB + 272) accBase lenW outPtr s3 s4 s5) bytes listLen 3
    hnewSp hlistLenW rfl (by decide) hsalign hslack hover hvalid
    (by show (AB + 272 : Word) &&& ~~~(1 : Word) = AB + 272; decide)
  have hcalleeC := cpsTripleWithin_extend_code k20_mono hcallee0
  have hcalleeF := cpsTripleWithin_frameR
    (aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv))
    (by unfold aieSlots; pcfR) hcalleeC
  have hcallee : cpsTripleWithin ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9) B (AB + 272) fullCode
      ((.x1 ↦ᵣ (AB + 272)) **
        (aieCalleePre spA newSp accBase lenW (3 : Word) oldOff oldLen
            (mkSaved (AB + 272) accBase lenW outPtr s3 s4 s5) bytes **
          aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv)))
      (returnResult spA newSp accBase (3 : Word) OffA LenA oldOff oldLen
          (mkSaved (AB + 272) accBase lenW outPtr s3 s4 s5) bytes listLen 3 **
        aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv)) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold aieCalleePre entryRest at hp
      rw [regsAt_listNthFrame]
      unfold entryRest
      simp only [mkSaved] at hp ⊢
      xperm_chunked hp) (fun _ hq => hq) hcalleeF
  have hsj := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold aieCalleePre entryRest; simp only [mkSaved]; xperm_chunked hp) hsetupF hjalF
  refine cpsTripleWithin_weaken (fun _ hp => by unfold aieMidPre at hp; xperm_chunked hp)
    (fun _ hq => hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hsj hcallee)

#print axioms aieCall3

end EvmAsm.Codegen.AccountIsEip161EmptySpec
