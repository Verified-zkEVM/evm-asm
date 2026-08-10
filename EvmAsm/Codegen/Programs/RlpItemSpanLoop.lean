/-
  EvmAsm.Codegen.Programs.RlpItemSpanLoop

  Extracted from `RlpItemSpanBody.lean` to stay under the Codegen/Programs
  1500-line FileSizeGuard (#11577 / PR #11936). Holds the ambient/loop
  assertions and the k < i continue triple (precall / size call / postcall).
  The top-level `rlp_item_span_spec_within` remains in `RlpItemSpanBody.lean`.
-/

import EvmAsm.Codegen.Programs.RlpItemSpanMachine
import EvmAsm.Codegen.Programs.RlpItemSpanSizeOffset
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Codegen
namespace RlpItemSpanSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpSpliceHelperSpec
open EvmAsm.Codegen.MptSpliceSlotSpec

/-! ## Base + code membership -/

abbrev B : Word := rlpItemSpanBase

theorem span_len : rlpItemSpan_prog.length = 53 := rlpItemSpan_prog_length
theorem span_bound : 4 * rlpItemSpan_prog.length < 2 ^ 64 := by
  rw [span_len]; norm_num

/-- Unfold `Program` so `GetElem` / length facts reduce. -/
abbrev spanProg : List Instr := rlpItemSpan_prog

theorem spanProg_len : spanProg.length = 53 := span_len
theorem spanProg_bound : 4 * spanProg.length < 2 ^ 64 := span_bound

/-- Singleton at index `k` ⊆ ofProg ⊆ spanCr. -/
theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < spanProg.length)
    (hins : spanProg[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → spanCr a = some i :=
  fun a i h =>
    span_sub a i (CodeReq.ofProg_mem_at B A spanProg k ins hA hk hins spanProg_bound a i h)

/-! ## Ambient packing -/

/-- Frame + outs + bytes + zero + saved ra — stable across the body. -/
def amb (newSp listBase endPtr indexW outStart outSize
    st sz raVal : Word) (saved : Saved) (bs : List (BitVec 8)) : Assertion :=
  ((.x2 ↦ᵣ newSp) ** savedFrame newSp saved **
   (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
   (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
   (outStart ↦ₘ st) ** (outSize ↦ₘ sz) **
   (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)

theorem amb_pcFree (newSp listBase endPtr indexW outStart outSize
    st sz raVal : Word) (saved : Saved) (bs : List (BitVec 8)) :
    (amb newSp listBase endPtr indexW outStart outSize st sz raVal saved bs).pcFree := by
  unfold amb; pcf

/-- Loop inv at header: counter k, cursor at shortCursor k.
    `x5`/`x6` are `regOwn` (size callee clobbers them). -/
def inv (newSp listBase endPtr indexW outStart outSize
    st sz raVal : Word) (saved : Saved) (items : List RLPItem) (k : Nat)
    (v7 v10 v11 v12 v13 v14 : Word) : Assertion :=
  amb newSp listBase endPtr indexW outStart outSize st sz raVal saved
      (encode (.list items)) **
    ((.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items k))) **
     (.x22 ↦ᵣ BitVec.ofNat 64 k) **
     regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14))

theorem inv_pcFree (newSp listBase endPtr indexW outStart outSize
    st sz raVal : Word) (saved : Saved) (items : List RLPItem) (k : Nat)
    (v7 v10 v11 v12 v13 v14 : Word) :
    (inv newSp listBase endPtr indexW outStart outSize st sz raVal saved items k
      v7 v10 v11 v12 v13 v14).pcFree := by
  unfold inv amb; pcf

/-- Body-exit success post. -/
def bodyPost (newSp listBase endPtr indexW outStart outSize
    raVal : Word) (saved : Saved) (items : List RLPItem) (i : Nat)
    (hi : i < items.length) : Assertion :=
  let startOff := shortCursor items i
  let itemSz := (encode (items[i]'hi)).length
  amb newSp listBase endPtr indexW outStart outSize
      (BitVec.ofNat 64 startOff) (BitVec.ofNat 64 itemSz) raVal saved
      (encode (.list items)) **
    ((.x10 ↦ᵣ (0 : Word)) **
     (.x21 ↦ᵣ (listBase + BitVec.ofNat 64 startOff)) **
     (.x22 ↦ᵣ BitVec.ofNat 64 i) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14)

/-! ## Setup block (idx 9..13 → B+36 .. B+56) -/


/-! ## Loop step helpers (k < i) -/

theorem ofNat64_inj_of_lt (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (heq : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

/-- `listBase + ofNat n` toNat under a concrete envelope bound. -/
theorem listBase_add_toNat (listBase : Word) (n len : Nat)
    (hn : n ≤ len) (h_over : listBase.toNat + len < 2 ^ 64) :
    (listBase + BitVec.ofNat 64 n).toNat = listBase.toNat + n := by
  have hn64 : n < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  omega

/-- BEQ ntaken + BGEU ntaken + MV x10←x21: inv → call site at B+120. -/
theorem loop_continue_precall
    (newSp listBase endPtr indexW outStart outSize st sz raVal : Word)
    (saved : Saved) (items : List RLPItem) (k i : Nat)
    (v7 v10 v11 v12 v13 v14 : Word)
    (hshort : payloadLen items ≤ 55)
    (h_end : endPtr =
      listBase + BitVec.ofNat 64 (encode (.list items)).length)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (hi : i < items.length)
    (hk_lt : k < i)
    (h_idx : indexW = BitVec.ofNat 64 i) :
    cpsTripleWithin 3 (B + 108) (B + 120) spanCr
      (inv newSp listBase endPtr indexW outStart outSize st sz raVal
        saved items k v7 v10 v11 v12 v13 v14)
      (amb newSp listBase endPtr indexW outStart outSize st sz raVal saved
          (encode (.list items)) **
        ((.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items k))) **
         (.x22 ↦ᵣ BitVec.ofNat 64 k) **
         regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
         (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items k))) **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
         (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14))) := by
  set bs := encode (.list items)
  have hbs_len : bs.length = (encode (.list items)).length := rfl
  have hk_items : k < items.length := Nat.lt_trans hk_lt hi
  have hcur_lt := shortCursor_lt items k hk_items hshort
  have hcur_le : shortCursor items k ≤ bs.length := by
    rw [hbs_len]; exact Nat.le_of_lt hcur_lt
  have hilen := items_length_le_55 items hshort
  have hi64 : i < 2 ^ 64 := Nat.lt_of_lt_of_le hi (Nat.le_trans hilen (by norm_num))
  have hk64 : k < 2 ^ 64 := Nat.lt_trans hk_lt hi64
  have hk_ne : BitVec.ofNat 64 k ≠ BitVec.ofNat 64 i := by
    intro heq
    exact Nat.ne_of_lt hk_lt (ofNat64_inj_of_lt k i hk64 hi64 heq)
  have hult_cur : BitVec.ult
      (listBase + BitVec.ofNat 64 (shortCursor items k)) endPtr := by
    have hsum_c := listBase_add_toNat listBase (shortCursor items k) bs.length
      hcur_le (by rwa [hbs_len] at h_over ⊢)
    have hsum_e := listBase_add_toNat listBase bs.length bs.length
      (Nat.le_refl _) (by rwa [hbs_len] at h_over ⊢)
    rw [h_end, BitVec.ult, decide_eq_true_eq, hsum_c, hsum_e, hbs_len]
    have : shortCursor items k < (encode (.list items)).length := hcur_lt
    omega
  -- idx27 BEQ ntaken
  have hbr27 := cpsBranchWithin_extend_code
    (mem_at 27 (.BEQ .x22 .x18 (28 : BitVec 13)) (B + 108)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (beq_spec_gen_within .x22 .x18 (28 : BitVec 13)
      (BitVec.ofNat 64 k) indexW (B + 108))
  rw [show (B + 108 : Word) + signExtend13 (28 : BitVec 13) = B + 136 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega,
      show (B + 108 : Word) + 4 = B + 112 from by decide] at hbr27
  have hk_ne' : BitVec.ofNat 64 k ≠ indexW := by rw [h_idx]; exact hk_ne
  have hnt27 := cpsBranchWithin_ntakenStripPure2 hbr27 (fun _hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hk_ne' ((sepConj_pure_right _).1 hQ).2)
  -- idx28 BGEU ntaken
  have hbr28 := cpsBranchWithin_extend_code
    (mem_at 28 (.BGEU .x21 .x9 (56 : BitVec 13)) (B + 112)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (bgeu_spec_gen_within .x21 .x9 (56 : BitVec 13)
      (listBase + BitVec.ofNat 64 (shortCursor items k)) endPtr (B + 112))
  rw [show (B + 112 : Word) + signExtend13 (56 : BitVec 13) = B + 168 from by
        rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]; bv_omega,
      show (B + 112 : Word) + 4 = B + 116 from by decide] at hbr28
  have hnt28 := cpsBranchWithin_ntakenStripPure2 hbr28 (fun _hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 hult_cur)
  -- idx29 MV
  have hmv29 := cpsTripleWithin_extend_code
    (mem_at 29 (.MV .x10 .x21) (B + 116)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (mv_spec_gen_within .x10 .x21
      (listBase + BitVec.ofNat 64 (shortCursor items k)) v10 (B + 116) (by decide))
  rw [show (B + 116 : Word) + 4 = B + 120 from by decide] at hmv29
  have f27 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items k))) **
     savedFrame newSp saved **
     regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hnt27
  have f28 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x22 ↦ᵣ BitVec.ofNat 64 k) **
     savedFrame newSp saved **
     regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hnt28
  -- MV focuses x10 (rd) and x21 (rs1): frame must omit both.
  have f29 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x22 ↦ᵣ BitVec.ofNat 64 k) **
     savedFrame newSp saved **
     regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hmv29
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [savedFrame] at hp ⊢; xperm_chunked hp) f27 f28
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [savedFrame] at hp ⊢; xperm_chunked hp) c01 f29
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [inv, amb, savedFrame] at hp ⊢
      xperm_chunked hp)
    (fun h hq => by
      simp only [amb, savedFrame] at hq ⊢
      xperm_chunked hq)
    c02

/-- Size call at B+120: cursor in x10 → length in x10; ra becomes B+124. -/
theorem loop_continue_size_call
    (newSp listBase endPtr indexW outStart outSize st sz raVal : Word)
    (saved : Saved) (items : List RLPItem) (k : Nat)
    (v7 v11 v12 v13 v14 : Word)
    (hshort : payloadLen items ≤ 55)
    (h_align : listBase.toNat % 8 = 0)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (h_valid : ∀ j, j < (encode (.list items)).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 j) = true)
    (hk_items : k < items.length)
    (h_walk_k : SpanForm ((encode (items[k]'hk_items)).getD 0 0)) :
    cpsTripleWithin 13 (B + 120) (B + 124) spanCr
      (amb newSp listBase endPtr indexW outStart outSize st sz raVal saved
          (encode (.list items)) **
        ((.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items k))) **
         (.x22 ↦ᵣ BitVec.ofNat 64 k) **
         regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
         (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items k))) **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
         (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)))
      (amb newSp listBase endPtr indexW outStart outSize st sz (B + 124) saved
          (encode (.list items)) **
        ((.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items k))) **
         (.x22 ↦ᵣ BitVec.ofNat 64 k) **
         regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
         (.x10 ↦ᵣ BitVec.ofNat 64 (encode (items[k]'hk_items)).length) **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
         (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14))) := by
  set bs := encode (.list items)
  set cursor : Word := listBase + BitVec.ofNat 64 (shortCursor items k)
  set itemLenW : Word := BitVec.ofNat 64 (encode (items[k]'hk_items)).length
  have hbs_len : bs.length = (encode (.list items)).length := rfl
  have hcur_lt := shortCursor_lt items k hk_items hshort
  have h_off : shortCursor items k < bs.length := by rwa [hbs_len]
  have h_over_off : listBase.toNat + shortCursor items k < 2 ^ 64 := by
    have := hcur_lt; omega
  have hdec := decode_at_shortCursor items k hk_items hshort
  have hform := span_form_at_shortCursor items k hk_items hshort h_walk_k
  have hret_even : ((B + 124 : Word) &&& ~~~(1 : Word)) = B + 124 := by decide
  have hsize0 := rlp_item_size_offset_spec_within listBase (shortCursor items k)
    (B + 124) bs (items[k]'hk_items)
    (encode.encodeItems (items.drop (k + 1)))
    h_align h_off h_over_off (by intro j hj; rw [hbs_len] at hj; exact h_valid j hj)
    (by simpa [bs] using hdec) (by simpa [bs] using hform)
  rw [hret_even] at hsize0
  have hsizeC := cpsTripleWithin_extend_code size_sub hsize0
  -- callWithin wants exit = A+4 = B+120+4 and shape (x1 ** P)/(x1 ** Q).
  have hpc : (B + 120 + 4 : Word) = B + 124 := by decide
  have hsizeW : cpsTripleWithin 12 rlpItemSizeBase (B + 120 + 4) spanCr
      (((.x1 : Reg) ↦ᵣ (B + 120 + 4)) **
        (((.x10 : Reg) ↦ᵣ cursor) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
         regOwn .x5 ** regOwn .x6))
      (((.x1 : Reg) ↦ᵣ (B + 120 + 4)) **
        (((.x10 : Reg) ↦ᵣ itemLenW) **
         regOwn .x5 ** regOwn .x6 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) := by
    rw [hpc]
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [cursor] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        simp only [itemLenW] at hq ⊢
        xperm_chunked hq)
      hsizeC
  have htarget : (B + 120 : Word)
        + signExtend21
            (jalOff GuestAddrs.rlp_item_size (GuestAddrs.rlp_item_span + 120))
        = rlpItemSizeBase := by
    unfold B rlpItemSpanBase rlpItemSizeBase; decide
  have hcall := callWithin_spec (B + 120) rlpItemSizeBase raVal
    (jalOff GuestAddrs.rlp_item_size (GuestAddrs.rlp_item_span + 120)) 12
    htarget
    (mem_at 30
      (.JAL .x1 (jalOff GuestAddrs.rlp_item_size (GuestAddrs.rlp_item_span + 120)))
      (B + 120) (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (by pcf) hsizeW
  rw [hpc] at hcall
  have fcall := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ BitVec.ofNat 64 k) **
     savedFrame newSp saved **
     (.x7 ↦ᵣ v7) **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hcall
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [amb, cursor, savedFrame] at hp ⊢
      xperm_chunked hp)
    (fun h hq => by
      simp only [amb, cursor, itemLenW, savedFrame] at hq ⊢
      xperm_chunked hq)
    fcall

/-- ADD cursor, ADDI k, JAL back — post size-call → inv (k+1).
    Requires `k + 1 < items.length` (true in the continue arm: `k < i < length`). -/
theorem loop_continue_postcall
    (newSp listBase endPtr indexW outStart outSize st sz : Word)
    (saved : Saved) (items : List RLPItem) (k : Nat)
    (v7 v11 v12 v13 v14 : Word)
    (hshort : payloadLen items ≤ 55)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (hk_items : k < items.length)
    (hk_succ_lt : k + 1 < items.length) :
    cpsTripleWithin 3 (B + 124) (B + 108) spanCr
      (amb newSp listBase endPtr indexW outStart outSize st sz (B + 124) saved
          (encode (.list items)) **
        ((.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items k))) **
         (.x22 ↦ᵣ BitVec.ofNat 64 k) **
         regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
         (.x10 ↦ᵣ BitVec.ofNat 64 (encode (items[k]'hk_items)).length) **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
         (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)))
      (inv newSp listBase endPtr indexW outStart outSize st sz (B + 124)
        saved items (k + 1) v7
        (BitVec.ofNat 64 (encode (items[k]'hk_items)).length)
        v11 v12 v13 v14) := by
  set bs := encode (.list items)
  set itemLenW : Word := BitVec.ofNat 64 (encode (items[k]'hk_items)).length
  set cursor : Word := listBase + BitVec.ofNat 64 (shortCursor items k)
  have hbs_len : bs.length = (encode (.list items)).length := rfl
  have hilen := items_length_le_55 items hshort
  have hk64 : k + 1 < 2 ^ 64 := by
    have : k + 1 ≤ 55 :=
      Nat.le_trans (Nat.succ_le_of_lt hk_items) (Nat.le_trans hilen (by norm_num))
    omega
  have hcur_lt_k := shortCursor_lt items k hk_items hshort
  have hcur_lt_succ := shortCursor_lt items (k + 1) hk_succ_lt hshort
  have hadd31 := cpsTripleWithin_extend_code
    (mem_at 31 (.ADD .x21 .x21 .x10) (B + 124)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (add_spec_gen_rd_eq_rs1_within .x21 .x10 cursor itemLenW
      (B + 124) (by decide))
  rw [show (B + 124 : Word) + 4 = B + 128 from by decide] at hadd31
  have haddi32 := cpsTripleWithin_extend_code
    (mem_at 32 (.ADDI .x22 .x22 (1 : BitVec 12)) (B + 128)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (addi_spec_gen_same_within .x22 (BitVec.ofNat 64 k)
      (1 : BitVec 12) (B + 128) (by decide))
  rw [show (B + 128 : Word) + 4 = B + 132 from by decide] at haddi32
  have hjal33 := cpsTripleWithin_extend_code
    (mem_at 33 (.JAL .x0 (-24 : BitVec 21)) (B + 132)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (jal_x0_spec_gen_within (-24 : BitVec 21) (B + 132))
  rw [show (B + 132 : Word) + signExtend21 (-24 : BitVec 21) = B + 108 from by
        rw [show signExtend21 (-24 : BitVec 21) = BitVec.ofInt 64 (-24) from by decide]
        bv_omega] at hjal33
  -- Shared non-focus frame for ADD/ADDI/JAL (JAL is emp-only).
  set restFrame : Assertion :=
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (B + 124)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     savedFrame newSp saved **
     regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz))
  have hrest_pc : restFrame.pcFree := by
    simp only [restFrame, savedFrame]; pcf
  have f31 := cpsTripleWithin_frameR
    (restFrame ** (.x22 ↦ᵣ BitVec.ofNat 64 k)) (by
      simp only [restFrame, savedFrame]; pcf) hadd31
  have f32 := cpsTripleWithin_frameR
    (restFrame ** (.x21 ↦ᵣ (cursor + itemLenW)) ** (.x10 ↦ᵣ itemLenW)) (by
      simp only [restFrame, savedFrame]; pcf) haddi32
  -- JAL x0 is emp/emp: frame the full post-ADDI state, then strip emp.
  have f33raw := cpsTripleWithin_frameR
    (restFrame ** (.x21 ↦ᵣ (cursor + itemLenW)) ** (.x10 ↦ᵣ itemLenW) **
      (.x22 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12)))) (by
      simp only [restFrame, savedFrame]; pcf) hjal33
  have f33 : cpsTripleWithin 1 (B + 132) (B + 108) spanCr
      (restFrame ** (.x21 ↦ᵣ (cursor + itemLenW)) ** (.x10 ↦ᵣ itemLenW) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12))))
      (restFrame ** (.x21 ↦ᵣ (cursor + itemLenW)) ** (.x10 ↦ᵣ itemLenW) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12)))) :=
    cpsTripleWithin_weaken
      (fun _ hp => (sepConj_emp_left _).2 hp)
      (fun _ hq => (sepConj_emp_left _).1 hq)
      f33raw
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [restFrame, savedFrame] at hp ⊢; xperm_chunked hp) f31 f32
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [restFrame, savedFrame] at hp ⊢; xperm_chunked hp) c01 f33
  have hcur_succ : cursor + itemLenW
      = listBase + BitVec.ofNat 64 (shortCursor items (k + 1)) := by
    have hs := shortCursor_succ items k hk_items
    have ha : shortCursor items k + (encode (items[k]'hk_items)).length
        = shortCursor items (k + 1) := by omega
    have hsum_c := listBase_add_toNat listBase (shortCursor items k) bs.length
      (Nat.le_of_lt (by simpa [hbs_len] using hcur_lt_k))
      (by simpa [hbs_len] using h_over)
    have hsum2 := listBase_add_toNat listBase (shortCursor items (k + 1)) bs.length
      (Nat.le_of_lt (by simpa [hbs_len] using hcur_lt_succ))
      (by simpa [hbs_len] using h_over)
    have hsum1 :
        (cursor + itemLenW).toNat
          = listBase.toNat + shortCursor items k
              + (encode (items[k]'hk_items)).length := by
      simp only [cursor, itemLenW]
      have hlen64 : (encode (items[k]'hk_items)).length < 2 ^ 64 := by omega
      have hsum_bound :
          listBase.toNat + shortCursor items k
            + (encode (items[k]'hk_items)).length < 2 ^ 64 := by
        have : shortCursor items k + (encode (items[k]'hk_items)).length
            ≤ bs.length := by
          have : shortCursor items (k + 1) ≤ bs.length := by
            rw [hbs_len]; exact Nat.le_of_lt hcur_lt_succ
          omega
        omega
      rw [BitVec.toNat_add, hsum_c, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64,
        Nat.mod_eq_of_lt hsum_bound]
    apply BitVec.eq_of_toNat_eq
    rw [hsum1, hsum2, Nat.add_assoc, ha]
  have hk_succ_w :
      BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 (k + 1) := by
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
    have hk0 : k < 2 ^ 64 := Nat.lt_trans (Nat.lt_succ_self k) hk64
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : Word).toNat = 1 := rfl
    have hL : (BitVec.ofNat 64 k + (1 : Word)).toNat = k + 1 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1, Nat.mod_eq_of_lt hk0]
      rw [Nat.mod_eq_of_lt hk64]
    have hR : (BitVec.ofNat 64 (k + 1)).toNat = k + 1 := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
    omega
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [amb, cursor, itemLenW, restFrame, savedFrame] at hp ⊢
      xperm_chunked hp)
    (fun h hq => ?_) c02
  have hq1 :
      (restFrame ** (.x21 ↦ᵣ (cursor + itemLenW)) ** (.x10 ↦ᵣ itemLenW) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12)))) h := by
    simp only [restFrame, savedFrame] at hq ⊢
    xperm_chunked hq
  rw [hcur_succ, hk_succ_w] at hq1
  simp only [inv, amb, restFrame, savedFrame, itemLenW] at hq1 ⊢
  xperm_chunked hq1

/-- One loop iteration when `k < i`: inv k → inv (k+1) at header. -/
theorem loop_continue
    (newSp listBase endPtr indexW outStart outSize st sz raVal : Word)
    (saved : Saved) (items : List RLPItem) (k i : Nat)
    (v7 v10 v11 v12 v13 v14 : Word)
    (hshort : payloadLen items ≤ 55)
    (h_end : endPtr =
      listBase + BitVec.ofNat 64 (encode (.list items)).length)
    (h_align : listBase.toNat % 8 = 0)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (h_valid : ∀ j, j < (encode (.list items)).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 j) = true)
    (hi : i < items.length)
    (hk_lt : k < i)
    (h_idx : indexW = BitVec.ofNat 64 i)
    (h_walk : WalkedSpanForm items i) :
    cpsTripleWithin 19 (B + 108) (B + 108) spanCr
      (inv newSp listBase endPtr indexW outStart outSize st sz raVal
        saved items k v7 v10 v11 v12 v13 v14)
      (inv newSp listBase endPtr indexW outStart outSize st sz (B + 124)
        saved items (k + 1) v7
        (BitVec.ofNat 64 (encode (items[k]'(Nat.lt_trans hk_lt hi))).length)
        v11 v12 v13 v14) := by
  have hk_items : k < items.length := Nat.lt_trans hk_lt hi
  have hk_succ_lt : k + 1 < items.length :=
    Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk_lt) hi
  have h_walk_k : SpanForm ((encode (items[k]'hk_items)).getD 0 0) :=
    h_walk k (Nat.le_of_lt hk_lt) hk_items
  have h1 := loop_continue_precall newSp listBase endPtr indexW outStart outSize
    st sz raVal saved items k i v7 v10 v11 v12 v13 v14
    hshort h_end h_over hi hk_lt h_idx
  have h2 := loop_continue_size_call newSp listBase endPtr indexW outStart outSize
    st sz raVal saved items k v7 v11 v12 v13 v14
    hshort h_align h_over h_valid hk_items h_walk_k
  have h3 := loop_continue_postcall newSp listBase endPtr indexW outStart outSize
    st sz saved items k v7 v11 v12 v13 v14
    hshort h_over hk_items hk_succ_lt
  have c12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [savedFrame, amb] at hp ⊢; xperm_chunked hp) h1 h2
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [savedFrame, amb] at hp ⊢; xperm_chunked hp) c12 h3



end RlpItemSpanSpec
