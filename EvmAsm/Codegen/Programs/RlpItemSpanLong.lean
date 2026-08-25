/-
  EvmAsm.Codegen.Programs.RlpItemSpanLong

  **The LONG outer-header arm of `rlp_item_span`** (#10780).

  `RlpItemSpanBody.lean` proves the routine under a SHORT outer list header
  (`payloadLen ≤ 55`, head byte `0xC0 + len`), which is the arm the guest
  reaches through `ADDI s5, s0, 1` (idx 29).  This file proves the other
  arm — head byte `0xF7 + lenlen` (`payloadLen ≥ 56`) — which the guest
  reaches through idx 20..30:

  ```
    idx19  BLTU x5, 0xF8, +40   -- NOT taken (head ≥ 0xF8)
    idx20  LI   x6, 247
    idx21  SUB  x7, x5, x6      -- x7 = head - 0xF7 = lenlen
    idx22  ADDI x7, x7, 1       -- x7 = 1 + lenlen
    idx23  ADD  x21, x8, x7     -- cursor = listBase + 1 + lenlen
    idx24  BGEU x21, x9, +88    -- reject cursor beyond input
    idx25  ADDI x7, x8, 1       -- address the first length byte
    idx26  LBU  x7, 0(x7)       -- load the first length byte
    idx27  BEQ  x7, x0, +76     -- reject a leading zero
    idx28  JAL  x0, +8          -- skip the short-form arm
  ```

  Spec side (execution-specs `e5a8caf1b`,
  `.venv/.../ethereum_rlp/rlp.py`): `encode_sequence` (`:112-127`) emits
  `Bytes([0xF7 + len(len_be)]) + len_be + payload` once the payload reaches
  `0x38` bytes, and `decode_to_sequence` (`:428-434`) recovers the payload
  at `joined_encodings_start_idx = 1 + encoded_sequence[0] - 0xF7`.  That
  index is exactly `hdrLen`, and `listCursor` is built on it, so the walk
  loop, the exit gate and the two stores are shared verbatim with the short
  arm (`RlpItemSpanLoop.lean`, `RlpItemSpanBody.lean`): the header block is
  the ONLY form-specific code.

  Width coverage: the arm is stated for the whole long family at once, not
  per `lenlen`.  `long_lenlen_le_8` bounds `lenlen ≤ 8` from `h_over`
  alone (a payload that fits the 64-bit envelope needs at most 8 length
  bytes), so `0xF8 ≤ head ≤ 0xFF` and the `SUB`/`ADDI` pair computes
  `hdrLen` for every width.  With the short arm this covers EVERY outer
  header form; `rlp_item_span_any_header_spec_within` is the dispatch.

  NOT covered (named cut): non-canonical long headers whose payload length is
  below `0x38`.  The guest now rejects a leading-zero length field at the
  `BEQ` above, but it still does not check `len_joined_encodings < 0x38`
  (`rlp.py:441`).  That minimality condition holds by construction here
  because the domain is `bs = encode (.list items)`, i.e. a canonical
  encoding; this file therefore claims nothing about rejecting that malformed
  header.
  `WalkedSpanForm` is likewise inherited unchanged.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.RlpItemSpanBody

namespace EvmAsm.Codegen
namespace RlpItemSpanSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpSpliceHelperSpec
open EvmAsm.Codegen.MptSpliceSlotSpec

private def longFirstLenByte (items : List RLPItem) : Word :=
  ((encode (.list items)).getD 1 0).zeroExtend 64

/-! ## Same-register byte load -/

/- `LBU x7, 0(x7)` is an in-place read: the generic load rule owns the base
   and destination as separate register atoms, which cannot express this
   instruction.  Keep the one-register rule local to this file rather than
   importing an unrelated arithmetic proof module. -/

private theorem bytesRegion_lbu_same_reg_within
    (r : Reg) (regionBase base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hrd : r ≠ .x0)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.LBU r r 0))
      ((r ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
        bytesRegion regionBase bs)
      ((r ↦ᵣ (bs[i]'hi).zeroExtend 64) **
        bytesRegion regionBase bs) := by
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegion_dword_at regionBase bs (i / 8) (by omega)
  let dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8))
  let wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8)
  have hzero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr : regionBase + BitVec.ofNat 64 i + signExtend12 (0 : BitVec 12) =
      regionBase + BitVec.ofNat 64 i := by
    rw [hzero]
    exact BitVec.add_zero _
  have halign' : alignToDword (regionBase + BitVec.ofNat 64 i) = dwordAddr := by
    dsimp [dwordAddr]
    exact alignToDword_add_ofNat_of_aligned halign hover
  have hbyte : extractByte wordVal (byteOffset (regionBase + BitVec.ofNat 64 i)) =
      bs[i]'hi := by
    dsimp [wordVal]
    rw [byteOffset_add_ofNat_of_aligned halign hover,
      extractByte_packBytes _ _ (by omega)
        (by rw [List.length_take, List.length_drop]; omega),
      List.getElem_take, List.getElem_drop]
    congr 1
    omega
  intro R hR s hcr hPR hpc
  subst hpc
  have hfetch : s.code s.pc = some (.LBU r r 0) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hPR' := holdsFor_sepConj_assoc.mp hPR
  have hptr : s.getReg r = regionBase + BitVec.ofNat 64 i :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR')
  have hbytesR := holdsFor_sepConj_elim_right hPR'
  have hregion := holdsFor_sepConj_elim_left hbytesR
  rw [heq] at hregion
  have hmem : s.getMem dwordAddr = wordVal :=
    holdsFor_memIs_getMem
      (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right hregion))
  have hstep' : step s = some (execInstrBr s (.LBU r r 0)) :=
    step_lbu hfetch (hptr ▸ (by rw [haddr]; exact hvalid))
  have hexec' : execInstrBr s (.LBU r r 0) =
      (s.setReg r ((bs[i]'hi).zeroExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hptr, getByte_eq]
    rw [haddr, halign', hmem, hbyte]
  refine ⟨1, Nat.le_refl 1,
    (s.setReg r ((bs[i]'hi).zeroExtend 64)).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']
    rfl
  · have hset0 := holdsFor_sepConj_regIs_setReg
      (v' := (bs[i]'hi).zeroExtend 64) hrd hPR'
    have hset := holdsFor_sepConj_assoc.mpr hset0
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) hR) hset

/-! ## Header → loop, long form (idx 14..30: B+56 → B+124) -/

/-- Long-list header path lands at `loopHdr` with `cursor = listBase + hdrLen`
    (`= listBase + 1 + lenlen`) and `k = 0`.  Sixteen steps, versus the short
    arm's eight: the long arithmetic plus the cursor and leading-zero guards
    precede the shared loop. -/
theorem header_to_loop_long (newSp listBase endPtr indexW outStart outSize
    st sz raVal : Word) (saved : Saved) (items : List RLPItem)
    (v5 v6 v7 v10 v11 v12 v13 v14 s5 s6 : Word)
    (hlong : 56 ≤ payloadLen items)
    (h_end : endPtr =
      listBase + BitVec.ofNat 64 (encode (.list items)).length)
    (h_align : listBase.toNat % 8 = 0)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (h_valid : ∀ k, k < (encode (.list items)).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hlen_pos : 0 < (encode (.list items)).length) :
    cpsTripleWithin 16 (B + 56) (B + 124) spanCr
      ((.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
       (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
       (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
       savedFrame newSp saved **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz))
       (inv newSp listBase endPtr indexW outStart outSize st sz raVal
         saved items 0 (longFirstLenByte items) v10 v11 v12 v13 v14) := by
  set bs := encode (.list items)
  have hbs_len : bs.length = (encode (.list items)).length := rfl
  have hL64 : (encode (.list items)).length < 2 ^ 64 := by
    have hover' : listBase.toNat + bs.length < 2 ^ 64 := h_over
    rw [hbs_len] at hover'; omega
  have hgetD : bs.getD 0 0 = bs[0]'hlen_pos := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen_pos]; rfl
  have hll_pos := long_lenlen_pos items hlong
  have hll_le := long_lenlen_le_8 items hL64
  have hhead : (bs[0]'hlen_pos).toNat
      = 0xF7 + (Nat.toBytesBE (payloadLen items)).length := by
    have := long_list_head_toNat items hlong hL64
    rwa [← hgetD]
  have henc : bs =
      BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (payloadLen items)).length) ::
        (Nat.toBytesBE (payloadLen items) ++ encode.encodeItems items) := by
    simpa [bs, payloadLen] using
      (encode_list_long items (show 55 < payloadLen items by omega))
  obtain ⟨b1, tl1, hb1, hb1ne⟩ :=
    Nat.toBytesBE_eq_cons_of_pos (payloadLen items) (by omega)
  have h1pos : 1 < bs.length := by
    rw [henc, hb1]
    simp
  have hbyte1_eq : bs[1]'h1pos = b1 := by
    simp [henc, hb1]
  have hbyte1_getD : bs[1]'h1pos = bs.getD 1 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1pos]
  have hbyte1_ne :
      ((bs[1]'h1pos).zeroExtend 64) ≠ (0 : Word) := by
    rw [hbyte1_eq]
    intro hz
    apply hb1ne
    apply BitVec.eq_of_toNat_eq
    have hz' := congrArg BitVec.toNat hz
    rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth] at hz'
    have hb1lt : b1.toNat < 2 ^ 64 := by
      exact lt_trans b1.isLt (by norm_num)
    rw [Nat.mod_eq_of_lt hb1lt] at hz'
    exact hz'
  have hlo : (192 : Nat) ≤ (bs[0]'hlen_pos).toNat := by omega
  have hge : (248 : Nat) ≤ (bs[0]'hlen_pos).toNat := by omega
  have hult_end : BitVec.ult listBase endPtr := by
    have hsum : (listBase + BitVec.ofNat 64 bs.length).toNat
        = listBase.toNat + bs.length := by
      have ha := listBase.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [h_end, BitVec.ult, decide_eq_true_eq, hsum]
    omega
  have hcur_lt0 := listCursor_lt items 0 (by
    have hitems : 0 < items.length := by
      cases items with
      | nil =>
        change 56 ≤ (encode.encodeItems []).length at hlong
        simp [encode.encodeItems] at hlong
      | cons _ _ => simp
    omega)
  have hcur_le0 : listCursor items 0 ≤ bs.length := by
    rw [hbs_len]
    exact Nat.le_of_lt hcur_lt0
  have hult_cur0 : BitVec.ult
      (listBase + BitVec.ofNat 64 (listCursor items 0)) endPtr := by
    have hsum_c := listBase_add_toNat listBase (listCursor items 0) bs.length
      hcur_le0 (by rwa [hbs_len] at h_over ⊢)
    have hsum_e := listBase_add_toNat listBase bs.length bs.length
      (Nat.le_refl _) (by rwa [hbs_len] at h_over ⊢)
    rw [h_end, BitVec.ult, decide_eq_true_eq, hsum_c, hsum_e]
    have hlt : listCursor items 0 < (encode (.list items)).length := hcur_lt0
    omega
  have hx7 : (((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12)
      = BitVec.ofNat 64 (hdrLen items) := by
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      hdrLen_long items hlong]
    exact long_head_sub_addi (bs[0]'hlen_pos) _ hhead
  have hcur : listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12))
      = listBase + BitVec.ofNat 64 (listCursor items 0) := by
    rw [hx7, listCursor_zero]
  have hk0 : (0 : Word) = BitVec.ofNat 64 0 := rfl
  -- idx14 BGEU x8,x9,+128 @ B+56 — NOT taken → B+60
  have hbr14 := cpsBranchWithin_extend_code
    (mem_at 14 (.BGEU .x8 .x9 (128 : BitVec 13)) (B + 56)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (bgeu_spec_gen_within .x8 .x9 (128 : BitVec 13) listBase endPtr (B + 56))
  rw [show (B + 56 : Word) + signExtend13 (128 : BitVec 13) = B + 184 from by
        rw [show signExtend13 (128 : BitVec 13) = (128 : Word) from by decide]; bv_omega,
      show (B + 56 : Word) + 4 = B + 60 from by decide] at hbr14
  have hnt14 := cpsBranchWithin_ntakenStripPure2 hbr14 (fun _hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 hult_end)
  -- idx15 LBU x5,0(x8) @ B+60
  have hlbu := bytesRegion_lbu_within .x5 .x8 listBase v5 (B + 60) bs 0
    (by decide) h_align hlen_pos (by omega) (h_valid 0 hlen_pos)
  rw [show listBase + BitVec.ofNat 64 0 = listBase from by bv_omega] at hlbu
  have hlbu' := cpsTripleWithin_extend_code
    (mem_at 15 (.LBU .x5 .x8 (0 : BitVec 12)) (B + 60)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl)) hlbu
  rw [show (B + 60 : Word) + 4 = B + 64 from by decide] at hlbu'
  -- idx16 LI x6, 192 @ B+64
  have hli16 := cpsTripleWithin_extend_code
    (mem_at 16 (.LI .x6 (192 : Word)) (B + 64)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (li_spec_gen_within .x6 v6 (192 : Word) (B + 64) (by decide))
  rw [show (B + 64 : Word) + 4 = B + 68 from by decide] at hli16
  -- idx17 BLTU x5,x6,+116 @ B+68 — NOT taken (head ≥ 0xc0)
  have hbr17 := cpsBranchWithin_extend_code
    (mem_at 17 (.BLTU .x5 .x6 (116 : BitVec 13)) (B + 68)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (bltu_spec_gen_within .x5 .x6 (116 : BitVec 13)
      ((bs[0]'hlen_pos).zeroExtend 64) (192 : Word) (B + 68))
  rw [show (B + 68 : Word) + signExtend13 (116 : BitVec 13) = B + 184 from by
        rw [show signExtend13 (116 : BitVec 13) = (116 : Word) from by decide]; bv_omega,
      show (B + 68 : Word) + 4 = B + 72 from by decide] at hbr17
  have hnult17 : ¬ BitVec.ult ((bs[0]'hlen_pos).zeroExtend 64) (192 : Word) :=
    not_ult_zx_of_ge _ _ (by
      rw [show ((192 : Word)).toNat = 192 from by decide]; exact hlo)
  have hnt17 := cpsBranchWithin_ntakenStripPure2 hbr17 (fun _hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hnult17 ((sepConj_pure_right _).1 hQ).2)
  -- idx18 LI x6, 248 @ B+72
  have hli18 := cpsTripleWithin_extend_code
    (mem_at 18 (.LI .x6 (248 : Word)) (B + 72)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (li_spec_gen_within .x6 (192 : Word) (248 : Word) (B + 72) (by decide))
  rw [show (B + 72 : Word) + 4 = B + 76 from by decide] at hli18
  -- idx19 BLTU x5,x6,+40 @ B+76 — NOT taken (head ≥ 0xf8) → B+80
  have hbr19 := cpsBranchWithin_extend_code
    (mem_at 19 (.BLTU .x5 .x6 (40 : BitVec 13)) (B + 76)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (bltu_spec_gen_within .x5 .x6 (40 : BitVec 13)
      ((bs[0]'hlen_pos).zeroExtend 64) (248 : Word) (B + 76))
  rw [show (B + 76 : Word) + signExtend13 (40 : BitVec 13) = B + 116 from by
        rw [show signExtend13 (40 : BitVec 13) = (40 : Word) from by decide]; bv_omega,
      show (B + 76 : Word) + 4 = B + 80 from by decide] at hbr19
  have hnult19 : ¬ BitVec.ult ((bs[0]'hlen_pos).zeroExtend 64) (248 : Word) :=
    not_ult_zx_of_ge _ _ (by
      rw [show ((248 : Word)).toNat = 248 from by decide]; exact hge)
  have hnt19 := cpsBranchWithin_ntakenStripPure2 hbr19 (fun _hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hnult19 ((sepConj_pure_right _).1 hQ).2)
  -- idx20 LI x6, 247 @ B+80
  have hli20 := cpsTripleWithin_extend_code
    (mem_at 20 (.LI .x6 (247 : Word)) (B + 80)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (li_spec_gen_within .x6 (248 : Word) (247 : Word) (B + 80) (by decide))
  rw [show (B + 80 : Word) + 4 = B + 84 from by decide] at hli20
  -- idx21 SUB x7, x5, x6 @ B+84 — x7 = head - 0xF7 = lenlen
  have hsub21 := cpsTripleWithin_extend_code
    (mem_at 21 (.SUB .x7 .x5 .x6) (B + 84)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (sub_spec_gen_within .x7 .x5 .x6
      ((bs[0]'hlen_pos).zeroExtend 64) (247 : Word) v7 (B + 84) (by decide))
  rw [show (B + 84 : Word) + 4 = B + 88 from by decide] at hsub21
  -- idx22 ADDI x7, x7, 1 @ B+88 — x7 = 1 + lenlen = hdrLen
  have haddi22 := cpsTripleWithin_extend_code
    (mem_at 22 (.ADDI .x7 .x7 (1 : BitVec 12)) (B + 88)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (addi_spec_gen_same_within .x7
      (((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word)) (1 : BitVec 12)
      (B + 88) (by decide))
  rw [show (B + 88 : Word) + 4 = B + 92 from by decide] at haddi22
  -- idx23 ADD x21, x8, x7 @ B+92 — cursor = listBase + hdrLen
  have hadd23 := cpsTripleWithin_extend_code
    (mem_at 23 (.ADD .x21 .x8 .x7) (B + 92)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (add_spec_gen_within .x21 .x8 .x7 listBase
      ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12)) s5 (B + 92) (by decide))
  rw [show (B + 92 : Word) + 4 = B + 96 from by decide] at hadd23
  -- idx24 BGEU x21,x9,+88 @ B+96 — NOT taken → B+100
  have hbr24 := cpsBranchWithin_extend_code
    (mem_at 24 (.BGEU .x21 .x9 (88 : BitVec 13)) (B + 96)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (bgeu_spec_gen_within .x21 .x9 (88 : BitVec 13)
      (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12))) endPtr (B + 96))
  rw [show (B + 96 : Word) + signExtend13 (88 : BitVec 13) = B + 184 from by
        rw [show signExtend13 (88 : BitVec 13) = (88 : Word) from by decide]; bv_omega,
      show (B + 96 : Word) + 4 = B + 100 from by decide] at hbr24
  have hnt24 := cpsBranchWithin_ntakenStripPure2 hbr24 (fun _hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    have hcur_expr : BitVec.ult
        (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
          + signExtend12 (1 : BitVec 12))) endPtr := by
      rw [hcur]
      exact hult_cur0
    exact ((sepConj_pure_right _).1 hQ).2 hcur_expr)
  -- idx25 ADDI x7,x8,1 @ B+100 — x7 = listBase + 1
  have haddi25 := cpsTripleWithin_extend_code
    (mem_at 25 (.ADDI .x7 .x8 (1 : BitVec 12)) (B + 100)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (addi_spec_gen_within .x7 .x8
      ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12)) listBase (1 : BitVec 12)
      (B + 100) (by decide))
  rw [show (B + 100 : Word) + 4 = B + 104 from by decide] at haddi25
  -- idx26 LBU x7,x7,0 @ B+104 — first length byte is nonzero
  have hlbu26 := bytesRegion_lbu_same_reg_within .x7 listBase (B + 104) bs 1
    (by decide) h_align h1pos (by omega) (h_valid 1 h1pos)
  have hlbu26' := cpsTripleWithin_extend_code
    (mem_at 26 (.LBU .x7 .x7 (0 : BitVec 12)) (B + 104)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl)) hlbu26
  rw [show (B + 104 : Word) + 4 = B + 108 from by decide] at hlbu26'
  -- idx27 BEQ x7,x0,+76 @ B+108 — NOT taken (leading byte nonzero)
  have hbr27 := cpsBranchWithin_extend_code
    (mem_at 27 (.BEQ .x7 .x0 (76 : BitVec 13)) (B + 108)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (beq_spec_gen_within .x7 .x0 (76 : BitVec 13)
      ((bs[1]'h1pos).zeroExtend 64) (0 : Word) (B + 108))
  rw [show (B + 108 : Word) + signExtend13 (76 : BitVec 13) = B + 184 from by
        rw [show signExtend13 (76 : BitVec 13) = (76 : Word) from by decide]; bv_omega,
      show (B + 108 : Word) + 4 = B + 112 from by decide] at hbr27
  have hnt27 := cpsBranchWithin_ntakenStripPure2 hbr27 (fun _hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hbyte1_ne ((sepConj_pure_right _).1 hQ).2)
  -- idx28 JAL x0, +8 @ B+112 — skip the short arm → B+120
  have hjal28 := cpsTripleWithin_extend_code
    (mem_at 28 (.JAL .x0 (8 : BitVec 21)) (B + 112)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (jal_x0_spec_gen_within (8 : BitVec 21) (B + 112))
  rw [show (B + 112 : Word) + signExtend21 (8 : BitVec 21) = B + 120 from by
        rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega]
    at hjal28
  -- idx30 LI x22, 0 @ B+120
  have hli30 := cpsTripleWithin_extend_code
    (mem_at 30 (.LI .x22 (0 : Word)) (B + 120)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (li_spec_gen_within .x22 s6 (0 : Word) (B + 120) (by decide))
  rw [show (B + 120 : Word) + 4 = B + 124 from by decide] at hli30
  -- frames
  have f14 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hnt14
  have f15 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hlbu'
  have f16 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hli16
  have f17 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hnt17
  have f18 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hli18
  have f19 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hnt19
  have f20 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hli20
  have f21 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hsub21
  have f22 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) haddi22
  have f23 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hadd23
  have f24 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
     (.x7 ↦ᵣ ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12))) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hnt24
  have hptr1 : listBase + signExtend12 (1 : BitVec 12) =
      listBase + BitVec.ofNat 64 1 := by
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
    bv_omega
  rw [hptr1] at haddi25
  have f25 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12)))) ** (.x22 ↦ᵣ s6) **
     savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) haddi25
  have f26 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12)))) ** (.x22 ↦ᵣ s6) **
     savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
     (.x0 ↦ᵣ (0 : Word)) **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hlbu26'
  have f27 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12)))) ** (.x22 ↦ᵣ s6) **
     savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
     bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hnt27
  -- JAL x0 is emp/emp: frame the whole state, then strip the emp.
  have f28raw := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12)))) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
     (.x7 ↦ᵣ ((bs[1]'h1pos).zeroExtend 64)) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hjal28
  have f28 : cpsTripleWithin 1 (B + 112) (B + 120) spanCr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
       (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
       (.x21 ↦ᵣ (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
          + signExtend12 (1 : BitVec 12)))) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
       (.x7 ↦ᵣ ((bs[1]'h1pos).zeroExtend 64)) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz))
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
       (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
       (.x21 ↦ᵣ (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
          + signExtend12 (1 : BitVec 12)))) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
       (.x7 ↦ᵣ ((bs[1]'h1pos).zeroExtend 64)) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) :=
    cpsTripleWithin_weaken
      (fun _ hp => (sepConj_emp_left _).2 hp)
      (fun _ hq => (sepConj_emp_left _).1 hq)
      f28raw
  have f30 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12)))) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
     (.x7 ↦ᵣ ((bs[1]'h1pos).zeroExtend 64)) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hli30
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f14 f15
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 f16
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 f17
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 f18
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 f19
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 f20
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 f21
  have c08 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c07 f22
  have c09 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c08 f23
  have c10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c09 f24
  have c11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c10 f25
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c11 f26
  have c13 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 f27
  have c14 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c13 f28
  have c15 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c14 f30
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) c15
  -- Goal post is `inv` with regOwn x5/x6 and x7 carrying the first length byte.
  simp only [inv, amb]
  have hq1 :
      ((.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) **
       (.x6 ↦ᵣ (247 : Word)) **
       (.x2 ↦ᵣ newSp) ** savedFrame newSp saved **
       (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
       (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz) **
       (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
       (.x21 ↦ᵣ (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
          + signExtend12 (1 : BitVec 12)))) **
       (.x22 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ ((bs[1]'h1pos).zeroExtend 64)) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) h := by
    xperm_hyp hq
  rw [hcur, hk0] at hq1
  have hown :
      ((regOwn .x5) ** (regOwn .x6) **
       (.x2 ↦ᵣ newSp) ** savedFrame newSp saved **
       (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
       (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz) **
       (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
       (.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (listCursor items 0))) **
       (.x22 ↦ᵣ BitVec.ofNat 64 0) **
       (.x7 ↦ᵣ (longFirstLenByte items)) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) h := by
    have hlongbyte : longFirstLenByte items = (bs[1]'h1pos).zeroExtend 64 := by
      change (bs.getD 1 0).zeroExtend 64 = _
      rw [← hbyte1_getD]
    have hq1' := sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6) (fun _ hh => hh)) h hq1
    rw [hlongbyte]
    exact hq1'
  xperm_hyp hown


/-! ## Body: setup + long header + loop + exit stores -/

/-- Full body under a LONG outer header.  Identical to `body_spec` except
    for the header block, hence four extra steps (`42 + 19 * i` vs
    `34 + 19 * i`): the long path executes sixteen header instructions
    (the executed indices in 14..30, with the short-arm index 29 skipped)
    where the short path executes eight. -/
theorem body_spec_long
    (newSp listBase listLenW indexW outStart outSize st sz raVal : Word)
    (saved : Saved) (items : List RLPItem) (i : Nat)
    (v5 v6 v7 : Word)
    (hlong : 56 ≤ payloadLen items)
    (h_len : listLenW =
      BitVec.ofNat 64 (encode (.list items)).length)
    (h_align : listBase.toNat % 8 = 0)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (h_valid : ∀ j, j < (encode (.list items)).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 j) = true)
    (hi : i < items.length)
    (h_idx : indexW = BitVec.ofNat 64 i)
    (h_walk : WalkedSpanForm items i)
    (hra : saved.ra = raVal) :
    cpsTripleWithin (42 + 19 * i) (B + 36) (B + 188) spanCr
      ((.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
       (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) **
       (.x21 ↦ᵣ saved.s5) ** (.x22 ↦ᵣ saved.s6) **
       savedFrame newSp saved **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
       (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz))
      (bodyPost newSp listBase (listBase + listLenW) indexW outStart outSize
        (B + 164) saved items i hi) := by
  set bs := encode (.list items)
  set endPtr : Word := listBase + listLenW
  have h_end : endPtr =
      listBase + BitVec.ofNat 64 (encode (.list items)).length := by
    simp only [endPtr]; rw [h_len]
  have hlen_pos : 0 < bs.length := by
    simp only [bs]; exact encode_length_pos (.list items)
  let v7long : Word := longFirstLenByte items
  have hsetup0 := setup_spec newSp listBase listLenW indexW outStart outSize
    st sz raVal saved.s0 saved.s1 saved.s2 saved.s3 saved.s4 saved.s5 saved.s6
    v5 v6 v7 bs
  have hsetup' :
      cpsTripleWithin 5 (B + 36) (B + 56) spanCr
        ((.x2 ↦ᵣ newSp) **
         (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
         (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) **
         (.x21 ↦ᵣ saved.s5) ** (.x22 ↦ᵣ saved.s6) **
         savedFrame newSp saved **
         (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
         (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
         (outStart ↦ₘ st) ** (outSize ↦ₘ sz))
        ((.x2 ↦ᵣ newSp) **
         (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
         (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
         (.x21 ↦ᵣ saved.s5) ** (.x22 ↦ᵣ saved.s6) **
         savedFrame newSp saved **
         (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
         (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
         (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) := by
    have hsf :
        savedFrame newSp
            { ra := raVal, s0 := saved.s0, s1 := saved.s1, s2 := saved.s2,
              s3 := saved.s3, s4 := saved.s4, s5 := saved.s5, s6 := saved.s6 }
          = savedFrame newSp saved := by
      simp only [savedFrame, hra]
    simpa [hsf, endPtr] using hsetup0
  -- long header
  have hheader := header_to_loop_long newSp listBase endPtr indexW outStart outSize
    st sz raVal saved items v5 v6 v7 listBase listLenW indexW outStart outSize
    saved.s5 saved.s6 hlong h_end h_align h_over h_valid hlen_pos
  -- loop 0 → i, with x7 carrying the first length byte loaded by the guard
  have ⟨v10f, hloop⟩ :=
    loop_to_exit newSp listBase endPtr indexW outStart outSize st sz raVal
      saved items 0 i v7long
      listBase listLenW indexW outStart outSize
      h_end h_align h_over h_valid hi (Nat.zero_le _) h_idx h_walk
  -- exit
  have hexit :=
    exit_stores newSp listBase endPtr indexW outStart outSize st sz
      (loopExitRa i raVal) saved items i
      v7long v10f listLenW indexW outStart outSize
      h_end h_align h_over h_valid hi h_walk
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hsetup' hheader
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      set_option linter.unusedSimpArgs false in
        simp only [inv, amb, savedFrame, bs] at hp ⊢
      xperm_chunked hp)
    c01 hloop
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      set_option linter.unusedSimpArgs false in
        simp only [inv, amb, savedFrame, bodyPost, bs, Nat.sub_zero] at hp ⊢
      xperm_chunked hp)
    c02 hexit
  have hfuel :
      5 + 16 + (1 + 19 * (i - 0)) + 20 = 42 + 19 * i := by omega
  convert c03 using 1
  · exact hfuel.symm

/-! ## Whole-routine triples -/

/-- Shared ABI wrapper (prologue `ADDI sp` + 8 frame stores, body, 8 frame
    loads, `ADDI sp` back, `RET`).  Extracted so the long arm and the
    unified dispatch reuse one copy; the short arm's own wrapper predates
    this file and is left untouched in `RlpItemSpanBody.lean`. -/
theorem span_abi_wrap
    (sp0 ret listBase listLenW indexW outStart outSize st sz : Word)
    (s0 s1 s2 s3 s4 s5 s6 v5 v6 v7 : Word)
    (items : List RLPItem) (i : Nat) (nBody : Nat)
    (hi : i < items.length)
    (h_idx : indexW = BitVec.ofNat 64 i)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hb0 : cpsTripleWithin nBody (B + 36) (B + 188) spanCr
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-64 : BitVec 12))) **
       (.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
       (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
       (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
       savedFrame (sp0 + signExtend12 (-64 : BitVec 12))
         { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4,
           s5 := s5, s6 := s6 } **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
       (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz))
      (bodyPost (sp0 + signExtend12 (-64 : BitVec 12)) listBase
        (listBase + listLenW) indexW outStart outSize (B + 164)
        { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4,
          s5 := s5, s6 := s6 } items i hi)) :
    cpsTripleWithin
      (1 + spanFrame.length + nBody + spanFrame.length + 1 + 1)
      rlpItemSpanBase ret spanCr
      ((.x2 ↦ᵣ sp0) **
        regsAt spanFrame (spanVals ret s0 s1 s2 s3 s4 s5 s6) **
        frameSlotsOwn spanFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
         (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
         (outStart ↦ₘ st) ** (outSize ↦ₘ sz)))
      ((.x2 ↦ᵣ sp0) **
        regsAt spanFrame (spanVals ret s0 s1 s2 s3 s4 s5 s6) **
        frameSlotsSaved spanFrame (sp0 + signExtend12 (-64 : BitVec 12))
          (spanVals ret s0 s1 s2 s3 s4 s5 s6) **
        ((.x10 ↦ᵣ (0 : Word)) **
         (outStart ↦ₘ BitVec.ofNat 64 (listCursor items i)) **
         (outSize ↦ₘ BitVec.ofNat 64 (encode (items[i]'hi)).length) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14)) := by
  set saved : Saved :=
    { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4,
      s5 := s5, s6 := s6 }
  set newSp := sp0 + signExtend12 (-64 : BitVec 12)
  set endPtr := listBase + listLenW
  set vals := spanVals ret s0 s1 s2 s3 s4 s5 s6
  set vals' := spanVals' listBase endPtr indexW outStart outSize items i
  have hentry :
      rlpItemSpanBase + BitVec.ofNat 64 (4 * (1 + spanFrame.length))
        = B + 36 := by
    simp only [spanFrame_length, B]; decide
  have hexit :
      rlpItemSpanBase +
          BitVec.ofNat 64 (4 * (1 + spanFrame.length + spanBody.length))
        = B + 188 := by
    simp only [spanFrame_length, spanBody_length, B]; decide
  have hbody : cpsTripleWithin nBody
      (rlpItemSpanBase + BitVec.ofNat 64 (4 * (1 + spanFrame.length)))
      (rlpItemSpanBase + BitVec.ofNat 64 (4 * (1 + spanFrame.length + spanBody.length)))
      spanCr
      ((.x2 ↦ᵣ newSp) ** regsAt spanFrame vals **
        frameSlotsSaved spanFrame newSp vals **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
         (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
         (outStart ↦ₘ st) ** (outSize ↦ₘ sz)))
      ((.x2 ↦ᵣ newSp) ** regsAt spanFrame vals' **
        frameSlotsSaved spanFrame newSp vals **
        ((.x10 ↦ᵣ (0 : Word)) **
         (outStart ↦ₘ BitVec.ofNat 64 (listCursor items i)) **
         (outSize ↦ₘ BitVec.ofNat 64 (encode (items[i]'hi)).length) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14)) := by
    rw [hentry, hexit]
    have hvals : vals = savedVals saved := by
      simp only [vals, saved, spanVals_saved]
    have hslots :
        frameSlotsSaved spanFrame newSp vals = savedFrame newSp saved := by
      rw [hvals]; exact frameSlotsSaved_spanFrame newSp saved
    have hregs :
        regsAt spanFrame vals =
          ((.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
           (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
           (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6)) := by
      rw [hvals, regsAt_spanFrame]
    have hregs' :
        regsAt spanFrame vals' =
          ((.x1 ↦ᵣ (B + 164)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
           (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
           (.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (listCursor items i))) **
           (.x22 ↦ᵣ BitVec.ofNat 64 i)) := by
      simp only [vals', spanVals', regsAt, spanFrame, endPtr, h_idx,
        List.foldr_cons, List.foldr_nil, sepConj_emp_right']
    refine cpsTripleWithin_weaken ?pre ?post hb0
    · intro h hp
      rw [hregs, hslots] at hp
      simp only [saved] at hp ⊢
      xperm_chunked hp
    · intro h hq
      simp only [bodyPost, amb] at hq
      rw [hregs', hslots]
      simp only [saved, endPtr, h_idx] at hq ⊢
      xperm_chunked hq
  abi_frame (64 : BitVec 12) halign hbody

/-- **The long outer-header arm, whole routine.**  Same interface as
    `rlp_item_span_spec_within`, with `56 ≤ payloadLen items` in place of
    `payloadLen items ≤ 55`, and four more steps for the longer header
    block.  The post is form-agnostic: `listCursor` already carries the
    header length. -/
theorem rlp_item_span_long_spec_within
    (sp0 ret listBase listLenW indexW outStart outSize st sz : Word)
    (s0 s1 s2 s3 s4 s5 s6 v5 v6 v7 : Word)
    (items : List RLPItem) (i : Nat)
    (hlong : 56 ≤ payloadLen items)
    (h_len : listLenW =
      BitVec.ofNat 64 (encode (.list items)).length)
    (h_align : listBase.toNat % 8 = 0)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (h_valid : ∀ j, j < (encode (.list items)).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 j) = true)
    (hi : i < items.length)
    (h_idx : indexW = BitVec.ofNat 64 i)
    (h_walk : WalkedSpanForm items i)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      (1 + spanFrame.length + (42 + 19 * i) + spanFrame.length + 1 + 1)
      rlpItemSpanBase ret spanCr
      ((.x2 ↦ᵣ sp0) **
        regsAt spanFrame (spanVals ret s0 s1 s2 s3 s4 s5 s6) **
        frameSlotsOwn spanFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
         (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
         (outStart ↦ₘ st) ** (outSize ↦ₘ sz)))
      ((.x2 ↦ᵣ sp0) **
        regsAt spanFrame (spanVals ret s0 s1 s2 s3 s4 s5 s6) **
        frameSlotsSaved spanFrame (sp0 + signExtend12 (-64 : BitVec 12))
          (spanVals ret s0 s1 s2 s3 s4 s5 s6) **
        ((.x10 ↦ᵣ (0 : Word)) **
         (outStart ↦ₘ BitVec.ofNat 64 (listCursor items i)) **
         (outSize ↦ₘ BitVec.ofNat 64 (encode (items[i]'hi)).length) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14)) := by
  refine span_abi_wrap sp0 ret listBase listLenW indexW outStart outSize st sz
    s0 s1 s2 s3 s4 s5 s6 v5 v6 v7 items i (42 + 19 * i) hi h_idx halign ?_
  exact body_spec_long (sp0 + signExtend12 (-64 : BitVec 12)) listBase listLenW
    indexW outStart outSize st sz ret
    { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4,
      s5 := s5, s6 := s6 } items i v5 v6 v7
    hlong h_len h_align h_over h_valid hi h_idx h_walk (by rfl)

/-- **Total over outer header forms.**  Drops the header gate entirely: the
    two arms are dispatched on `payloadLen items ≤ 55`, which is decidable
    and exhaustive, so this triple holds for EVERY canonically encoded list.
    Stated at the long arm's step bound, which dominates the short arm's
    (`cpsTripleWithin` is an upper bound on steps). -/
theorem rlp_item_span_any_header_spec_within
    (sp0 ret listBase listLenW indexW outStart outSize st sz : Word)
    (s0 s1 s2 s3 s4 s5 s6 v5 v6 v7 : Word)
    (items : List RLPItem) (i : Nat)
    (h_len : listLenW =
      BitVec.ofNat 64 (encode (.list items)).length)
    (h_align : listBase.toNat % 8 = 0)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (h_valid : ∀ j, j < (encode (.list items)).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 j) = true)
    (hi : i < items.length)
    (h_idx : indexW = BitVec.ofNat 64 i)
    (h_walk : WalkedSpanForm items i)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      (1 + spanFrame.length + (42 + 19 * i) + spanFrame.length + 1 + 1)
      rlpItemSpanBase ret spanCr
      ((.x2 ↦ᵣ sp0) **
        regsAt spanFrame (spanVals ret s0 s1 s2 s3 s4 s5 s6) **
        frameSlotsOwn spanFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
         (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
         (outStart ↦ₘ st) ** (outSize ↦ₘ sz)))
      ((.x2 ↦ᵣ sp0) **
        regsAt spanFrame (spanVals ret s0 s1 s2 s3 s4 s5 s6) **
        frameSlotsSaved spanFrame (sp0 + signExtend12 (-64 : BitVec 12))
          (spanVals ret s0 s1 s2 s3 s4 s5 s6) **
        ((.x10 ↦ᵣ (0 : Word)) **
         (outStart ↦ₘ BitVec.ofNat 64 (listCursor items i)) **
         (outSize ↦ₘ BitVec.ofNat 64 (encode (items[i]'hi)).length) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14)) := by
  by_cases hshort : payloadLen items ≤ 55
  · refine cpsTripleWithin_mono_nSteps
      (show 1 + spanFrame.length + (34 + 19 * i) + spanFrame.length + 1 + 1
          ≤ 1 + spanFrame.length + (42 + 19 * i) + spanFrame.length + 1 + 1 by
        omega) ?_
    exact rlp_item_span_spec_within sp0 ret listBase listLenW indexW outStart
      outSize st sz s0 s1 s2 s3 s4 s5 s6 v5 v6 v7 items i
      hshort h_len h_align h_over h_valid hi h_idx h_walk halign
  · exact rlp_item_span_long_spec_within sp0 ret listBase listLenW indexW
      outStart outSize st sz s0 s1 s2 s3 s4 s5 s6 v5 v6 v7 items i
      (by omega) h_len h_align h_over h_valid hi h_idx h_walk halign

/-! ## Non-vacuity of the whole precondition bundle -/

/-- **Full-bundle non-vacuity.**  `rlp_item_span_long_precondition_reachable`
    satisfies the DOMAIN gate; this satisfies the domain gate AND every
    ABI/resource premise of `rlp_item_span_long_spec_within`
    simultaneously, at a concrete `listBase` and `ret`.  Checked rather
    than argued, because a bundled hypothesis nothing satisfies is a
    failure result, not a theorem.

    Witness: the 56-empty-string list of the coverRef (payload 56, so the
    outer header IS the long form `[0xF8, 0x38]` and the buffer is 58
    bytes) at `listBase = 0x1000` — 8-aligned and inside the legacy
    `MEM_START..MEM_END` zone for all 58 bytes. -/
theorem rlp_item_span_long_bundle_satisfiable :
    let items : List RLPItem := List.replicate 56 (.bytes [])
    let listBase : Word := BitVec.ofNat 64 0x1000
    let i : Nat := 3
    (encode (.list items)).length = 58
      ∧ 56 ≤ payloadLen items
      ∧ listBase.toNat % 8 = 0
      ∧ listBase.toNat + (encode (.list items)).length < 2 ^ 64
      ∧ (∀ j, j < (encode (.list items)).length →
          isValidByteAccess (listBase + BitVec.ofNat 64 j) = true)
      ∧ i < items.length
      ∧ WalkedSpanForm items i
      ∧ ((0 : Word) &&& ~~~(1 : Word)) = (0 : Word) := by
  obtain ⟨hpl, hi, hwalk, _hhdr, _hcur, henc⟩ :=
    rlp_item_span_long_precondition_reachable
  have hlen : (encode (.list (List.replicate 56 (RLPItem.bytes [])))).length = 58 := by
    rw [henc]; simp
  have hbase : (BitVec.ofNat 64 0x1000 : Word).toNat = 0x1000 := by decide
  refine ⟨hlen, hpl, by rw [hbase], by rw [hbase, hlen]; norm_num, ?_, hi, hwalk, by decide⟩
  intro j hj
  rw [hlen] at hj
  have haddr : ((BitVec.ofNat 64 0x1000 : Word) + BitVec.ofNat 64 j).toNat
      = 0x1000 + j := by
    have hj64 : j < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, hbase, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64]
    omega
  show isValidMemAddr _ = true
  unfold isValidMemAddr
  rw [haddr]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  refine Or.inl (Or.inl ⟨?_, ?_⟩)
  · unfold EvmAsm.Rv64.MEM_START; omega
  · unfold EvmAsm.Rv64.MEM_END; omega

end RlpItemSpanSpec
end EvmAsm.Codegen
