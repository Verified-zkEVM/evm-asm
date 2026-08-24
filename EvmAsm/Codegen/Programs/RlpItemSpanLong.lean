/-
  EvmAsm.Codegen.Programs.RlpItemSpanLong

  **The LONG outer-header arm of `rlp_item_span`** (#10780).

  `RlpItemSpanBody.lean` proves the routine under a SHORT outer list header
  (`payloadLen ≤ 55`, head byte `0xC0 + len`), which is the arm the guest
  reaches through `ADDI s5, s0, 1` (idx 25).  This file proves the other
  arm — head byte `0xF7 + lenlen` (`payloadLen ≥ 56`) — which the guest
  reaches through idx 20..24:

  ```
    idx19  BLTU x5, 0xF8, +24   -- NOT taken (head ≥ 0xF8)
    idx20  LI   x6, 247
    idx21  SUB  x7, x5, x6      -- x7 = head - 0xF7 = lenlen
    idx22  ADDI x7, x7, 1       -- x7 = 1 + lenlen
    idx23  ADD  x21, x8, x7     -- cursor = listBase + 1 + lenlen
    idx24  JAL  x0, +8          -- skip the short-form arm
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

  NOT covered (named cut): non-canonical long headers.  The guest computes
  `1 + (p - 0xF7)` without checking either canonicality condition the spec
  decoder enforces — `encoded_sequence[1] == 0` (leading zero in the length
  field, `rlp.py:436`) and `len_joined_encodings < 0x38` (long form used for
  a short length, `:441`).  Both hold by construction here because the
  domain is `bs = encode (.list items)`, i.e. a canonical encoding; this
  file therefore claims nothing about rejecting a malformed header.
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

/-! ## Header → loop, long form (idx 14..24, 26: B+56 → B+108) -/

/-- Long-list header path lands at `loopHdr` with `cursor = listBase + hdrLen`
    (`= listBase + 1 + lenlen`) and `k = 0`.  Twelve steps, versus the short
    arm's eight: `LI 247`, `SUB`, `ADDI`, `ADD`, `JAL` replace `ADDI s5,s0,1`. -/
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
    cpsTripleWithin 12 (B + 56) (B + 108) spanCr
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
         saved items 0 (BitVec.ofNat 64 (hdrLen items)) v10 v11 v12 v13 v14) := by
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
  have hlo : (192 : Nat) ≤ (bs[0]'hlen_pos).toNat := by omega
  have hge : (248 : Nat) ≤ (bs[0]'hlen_pos).toNat := by omega
  have hult_end : BitVec.ult listBase endPtr := by
    have hsum : (listBase + BitVec.ofNat 64 bs.length).toNat
        = listBase.toNat + bs.length := by
      have ha := listBase.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [h_end, BitVec.ult, decide_eq_true_eq, hsum]
    omega
  -- idx14 BGEU x8,x9,+112 @ B+56 — NOT taken → B+60
  have hbr14 := cpsBranchWithin_extend_code
    (mem_at 14 (.BGEU .x8 .x9 (112 : BitVec 13)) (B + 56)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (bgeu_spec_gen_within .x8 .x9 (112 : BitVec 13) listBase endPtr (B + 56))
  rw [show (B + 56 : Word) + signExtend13 (112 : BitVec 13) = B + 168 from by
        rw [show signExtend13 (112 : BitVec 13) = (112 : Word) from by decide]; bv_omega,
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
  -- idx17 BLTU x5,x6,+100 @ B+68 — NOT taken (head ≥ 0xc0)
  have hbr17 := cpsBranchWithin_extend_code
    (mem_at 17 (.BLTU .x5 .x6 (100 : BitVec 13)) (B + 68)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (bltu_spec_gen_within .x5 .x6 (100 : BitVec 13)
      ((bs[0]'hlen_pos).zeroExtend 64) (192 : Word) (B + 68))
  rw [show (B + 68 : Word) + signExtend13 (100 : BitVec 13) = B + 168 from by
        rw [show signExtend13 (100 : BitVec 13) = (100 : Word) from by decide]; bv_omega,
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
  -- idx19 BLTU x5,x6,+24 @ B+76 — NOT taken (head ≥ 0xf8) → B+80
  have hbr19 := cpsBranchWithin_extend_code
    (mem_at 19 (.BLTU .x5 .x6 (24 : BitVec 13)) (B + 76)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (bltu_spec_gen_within .x5 .x6 (24 : BitVec 13)
      ((bs[0]'hlen_pos).zeroExtend 64) (248 : Word) (B + 76))
  rw [show (B + 76 : Word) + signExtend13 (24 : BitVec 13) = B + 100 from by
        rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]; bv_omega,
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
  -- idx24 JAL x0, +8 @ B+96 — skip the short arm → B+104
  have hjal24 := cpsTripleWithin_extend_code
    (mem_at 24 (.JAL .x0 (8 : BitVec 21)) (B + 96)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (jal_x0_spec_gen_within (8 : BitVec 21) (B + 96))
  rw [show (B + 96 : Word) + signExtend21 (8 : BitVec 21) = B + 104 from by
        rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega]
    at hjal24
  -- idx26 LI x22, 0 @ B+104
  have hli26 := cpsTripleWithin_extend_code
    (mem_at 26 (.LI .x22 (0 : Word)) (B + 104)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (li_spec_gen_within .x22 s6 (0 : Word) (B + 104) (by decide))
  rw [show (B + 104 : Word) + 4 = B + 108 from by decide] at hli26
  -- x7's final value is `hdrLen`, and the cursor is item 0's `listCursor`.
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
  -- JAL x0 is emp/emp: frame the whole state, then strip the emp.
  have f24raw := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12)))) **
     (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
     (.x7 ↦ᵣ ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12))) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hjal24
  have f24 : cpsTripleWithin 1 (B + 96) (B + 104) spanCr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
       (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
       (.x21 ↦ᵣ (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
          + signExtend12 (1 : BitVec 12)))) **
       (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
       (.x7 ↦ᵣ ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
          + signExtend12 (1 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz))
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
       (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
       (.x21 ↦ᵣ (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
          + signExtend12 (1 : BitVec 12)))) **
       (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
       (.x7 ↦ᵣ ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
          + signExtend12 (1 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) :=
    cpsTripleWithin_weaken
      (fun _ hp => (sepConj_emp_left _).2 hp)
      (fun _ hq => (sepConj_emp_left _).1 hq)
      f24raw
  have f26 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ (listBase + ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12)))) **
     savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x6 ↦ᵣ (247 : Word)) **
     (.x7 ↦ᵣ ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
        + signExtend12 (1 : BitVec 12))) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hli26
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
  have c11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c10 f26
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) c11
  -- Goal post is `inv` with regOwn x5/x6 and x7 = ofNat hdrLen.
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
       (.x7 ↦ᵣ ((((bs[0]'hlen_pos).zeroExtend 64) - (247 : Word))
          + signExtend12 (1 : BitVec 12))) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) h := by
    xperm_hyp hq
  rw [hcur, hx7, hk0] at hq1
  have hown :
      ((regOwn .x5) ** (regOwn .x6) **
       (.x2 ↦ᵣ newSp) ** savedFrame newSp saved **
       (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
       (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz) **
       (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
       (.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (listCursor items 0))) **
       (.x22 ↦ᵣ BitVec.ofNat 64 0) **
       (.x7 ↦ᵣ BitVec.ofNat 64 (hdrLen items)) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) h :=
    sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6) (fun _ hh => hh)) h hq1
  xperm_hyp hown


/-! ## Body: setup + long header + loop + exit stores -/

/-- Full body under a LONG outer header.  Identical to `body_spec` except
    for the header block, hence four extra steps (`38 + 19 * i` vs
    `34 + 19 * i`): the long path executes twelve header instructions
    (idx 14..24, 26) where the short path executes eight. -/
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
    cpsTripleWithin (38 + 19 * i) (B + 36) (B + 172) spanCr
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
        (B + 148) saved items i hi) := by
  set bs := encode (.list items)
  set endPtr : Word := listBase + listLenW
  have h_end : endPtr =
      listBase + BitVec.ofNat 64 (encode (.list items)).length := by
    simp only [endPtr]; rw [h_len]
  have hlen_pos : 0 < bs.length := by
    simp only [bs]; exact encode_length_pos (.list items)
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
  -- loop 0 → i, with x7 carrying the header length the long path computed
  have ⟨v10f, hloop⟩ :=
    loop_to_exit newSp listBase endPtr indexW outStart outSize st sz raVal
      saved items 0 i (BitVec.ofNat 64 (hdrLen items))
      listBase listLenW indexW outStart outSize
      h_end h_align h_over h_valid hi (Nat.zero_le _) h_idx h_walk
  -- exit
  have hexit :=
    exit_stores newSp listBase endPtr indexW outStart outSize st sz
      (loopExitRa i raVal) saved items i
      (BitVec.ofNat 64 (hdrLen items)) v10f listLenW indexW outStart outSize
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
      5 + 12 + (1 + 19 * (i - 0)) + 20 = 38 + 19 * i := by omega
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
    (hb0 : cpsTripleWithin nBody (B + 36) (B + 172) spanCr
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
        (listBase + listLenW) indexW outStart outSize (B + 148)
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
        = B + 172 := by
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
          ((.x1 ↦ᵣ (B + 148)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
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
      (1 + spanFrame.length + (38 + 19 * i) + spanFrame.length + 1 + 1)
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
    s0 s1 s2 s3 s4 s5 s6 v5 v6 v7 items i (38 + 19 * i) hi h_idx halign ?_
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
      (1 + spanFrame.length + (38 + 19 * i) + spanFrame.length + 1 + 1)
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
          ≤ 1 + spanFrame.length + (38 + 19 * i) + spanFrame.length + 1 + 1 by
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
