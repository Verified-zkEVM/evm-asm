/-
  EvmAsm.Rv64.RLP.FlatListLoop

  EL.3 — foundations for the RV64 RLP flat-item list-decode loop closure: the
  `isFlatItem` predicate and the **stride-equivalence** linking the operational
  per-item stride to the pure encoding length.

  A flat item (singleByte / short byte-string / short list) is decoded by the
  loop body (`fll_body_spec_within`) in one pass, advancing the pointer by
  `itemTotalLen` of the item's first byte. `encode_head_eq_itemTotalLen` proves
  this stride equals `(encode item).length` — the bridge between the machine
  loop and the pure `encode`/`decodeItems` round-trip.

  On that foundation: `fll_loop_spec_within` is the **n-iteration closure**
  (structural induction over a list of flat items, threading the variable byte
  offset via `bs.drop O = encode.encodeItems items` and applying
  `fll_body_spec_within` per item with the decoder supplied as a ∀-hypothesis
  `decoderH`); `fll_loop_n_spec_within` is the offset-0 entry; and
  `fll_loop_bridge` conjoins the operational loop with the pure
  `decodeItems` round-trip (`decode_encode_mutual.2`). Uniform
  `15 * items.length` steps; only the per-item byte stride varies.
-/

import EvmAsm.Rv64.RLP.FlatListLoopBody
import EvmAsm.Rv64.RLP.SingleByteListLoop
import EvmAsm.EL.RLP.Properties
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.AddrNorm (se12_1)

/-- `(BitVec.ofNat 8 k).toNat = k` for a byte-sized `k`. -/
private theorem toNat_ofNat8 {k : Nat} (h : k < 256) : (BitVec.ofNat 8 k).toNat = k := by
  rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from rfl]; omega

-- ============================================================================
-- Flat items + the stride-equivalence
-- ============================================================================

/-- An RLP item whose encoding's first byte is a FLAT prefix
    (`singleByte`/`shortBytes`/`shortList`) — i.e. a short-form byte string
    (`≤ 55` bytes) or a short-form list (payload `≤ 55` bytes). -/
def isFlatItem : RLPItem → Prop
  | .bytes data => data.length ≤ 55
  | .list items => (encode.encodeItems items).length ≤ 55

/-- The head byte of `encode (.bytes data)` for a non-singleton short string. -/
private theorem encode_bytes_multi_head {b c : Byte} {rest : List Byte}
    (hlen : (b :: c :: rest).length ≤ 55) :
    (encode (.bytes (b :: c :: rest)))[0]'(encode_nonempty _)
      = BitVec.ofNat 8 (0x80 + (b :: c :: rest).length)
    ∧ (encode (.bytes (b :: c :: rest))).length = 1 + (b :: c :: rest).length := by
  have henc : encode (.bytes (b :: c :: rest))
      = [BitVec.ofNat 8 (0x80 + (b :: c :: rest).length)] ++ (b :: c :: rest) :=
    encodeBytes_short_of_length_ne_one _ hlen (by simp)
  exact ⟨by simp [henc], by simp [henc, Nat.add_comm]⟩

/-- The head byte of `encode (.list items)` for a short list. -/
private theorem encode_list_head {items : List RLPItem}
    (hflat : (encode.encodeItems items).length ≤ 55) :
    (encode (.list items))[0]'(encode_nonempty _)
      = BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)
    ∧ (encode (.list items)).length = 1 + (encode.encodeItems items).length := by
  have henc : encode (.list items)
      = [BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)] ++ encode.encodeItems items := by
    simp only [encode, hflat, if_true]
  exact ⟨by simp [henc], by simp [henc, Nat.add_comm]⟩

/-- The first byte of a flat item's encoding classifies as a flat prefix. -/
theorem classifyPrefix_encode_head_flat (item : RLPItem) (hflat : isFlatItem item) :
    classifyPrefix ((encode item)[0]'(encode_nonempty item)) = .singleByte
      ∨ classifyPrefix ((encode item)[0]'(encode_nonempty item)) = .shortBytes
      ∨ classifyPrefix ((encode item)[0]'(encode_nonempty item)) = .shortList := by
  cases item with
  | bytes data =>
    simp only [isFlatItem] at hflat
    cases data with
    | nil =>
      right; left
      have hh : (encode (.bytes ([] : List Byte)))[0]'(encode_nonempty _) = BitVec.ofNat 8 0x80 := by
        simp [encode, encodeBytes]
      rw [hh, classifyPrefix_shortBytes_iff, toNat_ofNat8 (by omega)]; omega
    | cons b tail =>
      cases tail with
      | nil =>
        by_cases hb : b.toNat < 0x80
        · left
          have hh : (encode (.bytes [b]))[0]'(encode_nonempty _) = b := by
            simp [encode, encodeBytes, hb]
          rw [hh, classifyPrefix_singleByte_iff]; exact hb
        · right; left
          have hh : (encode (.bytes [b]))[0]'(encode_nonempty _) = BitVec.ofNat 8 0x81 := by
            simp [encode, encodeBytes, hb]
          rw [hh, classifyPrefix_shortBytes_iff, toNat_ofNat8 (by omega)]; omega
      | cons c rest =>
        right; left
        obtain ⟨hh, _⟩ := encode_bytes_multi_head (b := b) (c := c) (rest := rest) hflat
        rw [hh, classifyPrefix_shortBytes_iff, toNat_ofNat8 (by simp only [List.length_cons] at hflat ⊢; omega)]
        simp only [List.length_cons] at hflat ⊢; omega
  | list items =>
    right; right
    simp only [isFlatItem] at hflat
    obtain ⟨hh, _⟩ := encode_list_head hflat
    rw [hh, classifyPrefix_shortList_iff, toNat_ofNat8 (by omega)]; omega

/-- **Stride-equivalence.** For a flat item, the operational per-item stride
    `itemTotalLen` of its encoding's first byte equals the encoding length. -/
theorem encode_head_eq_itemTotalLen (item : RLPItem) (hflat : isFlatItem item) :
    itemTotalLen ((encode item)[0]'(encode_nonempty item))
      = BitVec.ofNat 64 (encode item).length := by
  cases item with
  | bytes data =>
    simp only [isFlatItem] at hflat
    cases data with
    | nil =>
      have hh : (encode (.bytes ([] : List Byte)))[0]'(encode_nonempty _) = BitVec.ofNat 8 0x80 := by
        simp [encode, encodeBytes]
      have hl : (encode (.bytes ([] : List Byte))).length = 1 := by simp [encode, encodeBytes]
      have hk : (0x80 : Nat) < 256 := by omega
      have hcls : classifyPrefix (BitVec.ofNat 8 0x80) = .shortBytes := by
        rw [classifyPrefix_shortBytes_iff, toNat_ofNat8 hk]; omega
      rw [hh, hl]; simp only [itemTotalLen, hcls, rlpPrefixShortBytesPayloadLen, toNat_ofNat8 hk, se12_1]
      decide
    | cons b tail =>
      cases tail with
      | nil =>
        by_cases hb : b.toNat < 0x80
        · have hh : (encode (.bytes [b]))[0]'(encode_nonempty _) = b := by
            simp [encode, encodeBytes, hb]
          have hl : (encode (.bytes [b])).length = 1 := by simp [encode, encodeBytes, hb]
          rw [hh, hl]; simp only [itemTotalLen, (classifyPrefix_singleByte_iff b).mpr hb]; decide
        · have hh : (encode (.bytes [b]))[0]'(encode_nonempty _) = BitVec.ofNat 8 0x81 := by
            simp [encode, encodeBytes, hb]
          have hl : (encode (.bytes [b])).length = 2 := by simp [encode, encodeBytes, hb]
          have hk : (0x81 : Nat) < 256 := by omega
          have hcls : classifyPrefix (BitVec.ofNat 8 0x81) = .shortBytes := by
            rw [classifyPrefix_shortBytes_iff, toNat_ofNat8 hk]; omega
          rw [hh, hl]; simp only [itemTotalLen, hcls, rlpPrefixShortBytesPayloadLen, toNat_ofNat8 hk, se12_1]
          decide
      | cons c rest =>
        obtain ⟨hh, hl⟩ := encode_bytes_multi_head (b := b) (c := c) (rest := rest) hflat
        have hk : 0x80 + (b :: c :: rest).length < 256 := by
          simp only [List.length_cons] at hflat ⊢; omega
        have hcls : classifyPrefix (BitVec.ofNat 8 (0x80 + (b :: c :: rest).length)) = .shortBytes := by
          rw [classifyPrefix_shortBytes_iff, toNat_ofNat8 hk]; omega
        rw [hh, hl]
        simp only [itemTotalLen, hcls, rlpPrefixShortBytesPayloadLen, toNat_ofNat8 hk, se12_1]
        have hsub : (0x80 + (b :: c :: rest).length) - 0x80 = (b :: c :: rest).length := by omega
        rw [hsub]; bv_omega
  | list items =>
    simp only [isFlatItem] at hflat
    obtain ⟨hh, hl⟩ := encode_list_head hflat
    have hk : 0xC0 + (encode.encodeItems items).length < 256 := by omega
    have hcls : classifyPrefix (BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)) = .shortList := by
      rw [classifyPrefix_shortList_iff, toNat_ofNat8 hk]; omega
    rw [hh, hl]
    simp only [itemTotalLen, hcls, rlpPrefixShortListPayloadLen, toNat_ofNat8 hk, se12_1]
    have hsub : (0xC0 + (encode.encodeItems items).length) - 0xC0 = (encode.encodeItems items).length := by omega
    rw [hsub]; bv_omega

-- ============================================================================
-- N-iteration closure: decode a list of flat items
-- ============================================================================

/-- Bundled post for the whole flat list-loop: the scratch registers
    `x5/x10/x11` are abstracted to `regOwn` (their final values are irrelevant
    downstream), the pointer rests at `endPtr`, the counter is zeroed, and the
    byte region is intact. -/
@[irreducible]
def fll_loop_post (regionBase : Word) (bs : List (BitVec 8)) (endPtr : Word) : Assertion :=
  regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11 **
    (.x13 ↦ᵣ endPtr) ** (.x14 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs

theorem fll_loop_post_unfold (regionBase : Word) (bs : List (BitVec 8)) (endPtr : Word) :
    fll_loop_post regionBase bs endPtr =
    (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11 **
      (.x13 ↦ᵣ endPtr) ** (.x14 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) := by
  delta fll_loop_post; rfl

/-- `(regionBase + ofNat O) + ofNat L = regionBase + ofNat (O + L)` — the
    per-item pointer advance accumulates into a single offset. -/
private theorem region_ptr_add (regionBase : Word) (O L : Nat) :
    (regionBase + BitVec.ofNat 64 O) + BitVec.ofNat 64 L
      = regionBase + BitVec.ofNat 64 (O + L) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]

/-- The item count never exceeds the encoded byte length (each item is
    non-empty). Bounds the loop counter for the `≠ 0` guard. -/
private theorem length_le_encodeItems : ∀ (items : List RLPItem),
    items.length ≤ (encode.encodeItems items).length
  | [] => by simp [encode.encodeItems]
  | i :: is => by
    simp only [encode.encodeItems, List.length_append, List.length_cons]
    have := encode_nonempty i
    have := length_le_encodeItems is
    omega

/-- **N-iteration closure.** Decoding a non-empty list of FLAT items from the
    region suffix at offset `O` runs the loop body once per item — a uniform
    `15 * items.length` steps — advancing `x13` by the total encoded length and
    zeroing the counter. The flat single-item decoder is supplied abstractly as
    `decoderH` (∀ over the prefix byte and the live register values); each
    iteration discharges the body's opaque decoder hypothesis with it, and the
    stride-equivalence `encode_head_eq_itemTotalLen` re-indexes the pointer. -/
theorem fll_loop_spec_within
    (regionBase : Word) (lbase joinPC decoder_base : Word) (dcr : CodeReq) (back : BitVec 13)
    (bs : List (BitVec 8))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hdec_base : decoder_base = lbase + 4)
    (decoderH : ∀ (pfx : Byte) (w10 w11 w13 : Word),
       (classifyPrefix pfx = .singleByte ∨ classifyPrefix pfx = .shortBytes
         ∨ classifyPrefix pfx = .shortList) →
       cpsTripleWithin 11 decoder_base joinPC dcr
         ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ w10) **
          (.x11 ↦ᵣ w11) ** (.x13 ↦ᵣ w13))
         ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
          (.x13 ↦ᵣ itemPayloadPtr pfx w13)))
    (hback : (joinPC + 8) + signExtend13 back = lbase)
    (hne_lj : lbase ≠ joinPC) (hne_lj4 : lbase ≠ joinPC + 4) (hne_lj8 : lbase ≠ joinPC + 8)
    (hd_lbu_dec : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr)
    (hd_dec_add : dcr.Disjoint (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)))
    (hd_dec_addi : dcr.Disjoint (CodeReq.singleton (joinPC + 4) (.ADDI .x14 .x14 (-1))))
    (hd_dec_bne : dcr.Disjoint (CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back))) :
    ∀ (items : List RLPItem) (O : Nat) (v5Old v10 v11Old : Word),
      items ≠ [] →
      bs.drop O = encode.encodeItems items →
      (∀ item ∈ items, isFlatItem item) →
      (∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) →
      cpsTripleWithin (15 * items.length) lbase (joinPC + 12)
        (((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
            (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
            (CodeReq.singleton (joinPC + 4) (.ADDI .x14 .x14 (-1)))).union
            ((CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back)).union CodeReq.empty))
        ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
         (.x14 ↦ᵣ BitVec.ofNat 64 items.length) ** bytesRegion regionBase bs)
        (fll_loop_post regionBase bs
          (regionBase + BitVec.ofNat 64 (O + (encode.encodeItems items).length))) := by
  intro items
  induction items with
  | nil => intro O v5Old v10 v11Old hne _ _ _; exact absurd rfl hne
  | cons head tail ih =>
    intro O v5Old v10 v11Old _ hdrop hflat_all hwin
    -- The remaining encoding at offset `O` is `encode head ++ encode.encodeItems tail`.
    have hsplit : bs.drop O = encode head ++ encode.encodeItems tail := by
      rw [hdrop]; rfl
    -- `O < bs.length` (the suffix is non-empty since `encode head` is).
    have hO : O < bs.length := by
      have hlen : (bs.drop O).length = (encode head ++ encode.encodeItems tail).length := by
        rw [hsplit]
      rw [List.length_drop, List.length_append] at hlen
      have := encode_nonempty head; omega
    -- The current prefix byte is `(encode head)[0]`.
    have hbsO : bs[O]'hO = (encode head)[0]'(encode_nonempty head) := by
      have key : (bs.drop O)[0]'(by rw [List.length_drop]; omega)
          = (encode head)[0]'(encode_nonempty head) :=
        (List.getElem_of_eq hsplit _).trans (List.getElem_append_left (encode_nonempty head))
      rw [← key]; simp
    -- It classifies as a flat prefix.
    have hflat_O : classifyPrefix (bs[O]'hO) = .singleByte
        ∨ classifyPrefix (bs[O]'hO) = .shortBytes
        ∨ classifyPrefix (bs[O]'hO) = .shortList := by
      rw [hbsO]
      exact classifyPrefix_encode_head_flat head (hflat_all head (by simp))
    -- The stride equals the head's encoded length.
    have hstride : itemTotalLen (bs[O]'hO) = BitVec.ofNat 64 (encode head).length := by
      rw [hbsO]; exact encode_head_eq_itemTotalLen head (hflat_all head (by simp))
    -- The next-item pointer lands at offset `O + (encode head).length`.
    have hnext : itemNextPtr (bs[O]'hO) (regionBase + BitVec.ofNat 64 O)
        = regionBase + BitVec.ofNat 64 (O + (encode head).length) := by
      rw [itemNextPtr, hstride, region_ptr_add]
    have hoverO : regionBase.toNat + O < 2 ^ 64 := by omega
    have hvalidO : isValidByteAccess (regionBase + BitVec.ofNat 64 O) = true := hwin O hO
    cases tail with
    | nil =>
      -- One item: the body's BNE falls through (counter hits 0).
      have body := fll_body_spec_within regionBase v5Old v10 v11Old (BitVec.ofNat 64 1)
        lbase joinPC decoder_base dcr back bs O halign hO hoverO hvalidO hflat_O hdec_base
        (decoderH (bs[O]'hO) v10 v11Old (regionBase + BitVec.ofNat 64 O) hflat_O)
        hback hne_lj hne_lj4 hne_lj8 hd_lbu_dec hd_dec_add hd_dec_addi hd_dec_bne
      rw [show (BitVec.ofNat 64 1 : Word) = BitVec.ofNat 64 (0 + 1) from rfl,
        word_ofNat_succ_dec 0] at body
      have h_absurd : ∀ hp,
          fll_body_post regionBase bs (bs[O]'hO) (itemCascadeResidue (bs[O]'hO))
            (itemPayloadLen (bs[O]'hO)) (itemNextPtr (bs[O]'hO) (regionBase + BitVec.ofNat 64 O))
            (BitVec.ofNat 64 0) ((BitVec.ofNat 64 0 : Word) ≠ 0) hp → False :=
        fun hp hpost => (fll_body_post_pure hp hpost) (by decide)
      have tri := cpsBranchWithin_ntakenPath body h_absurd
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) tri
      simp only [fll_body_post_unfold] at hp
      rw [hnext] at hp
      rw [fll_loop_post_unfold,
        show (encode.encodeItems (head :: [])).length = (encode head).length from by
          simp only [encode.encodeItems, List.append_nil]]
      -- weaken the body post: scratch x5/x10/x11 → regOwn, drop the pure fact
      exact sepConj_mono (regIs_implies_regOwn _)
        (sepConj_mono_right
          (sepConj_mono (regIs_implies_regOwn _)
            (sepConj_mono (regIs_implies_regOwn _)
              (sepConj_mono_right
                (sepConj_mono_right
                  (fun h' hp' => ((sepConj_pure_right h').1 hp').1)))))) h hp
    | cons h2 t2 =>
      -- Two or more items: the body's BNE is taken; recurse on the tail.
      have hdrop' : bs.drop (O + (encode head).length) = encode.encodeItems (h2 :: t2) := by
        rw [← List.drop_drop, hsplit, List.drop_append_length]
      -- Counter bound for the loop guard.
      have hcnt_bound : t2.length + 1 < 18446744073709551616 := by
        have hcount := length_le_encodeItems (h2 :: t2)
        have e : (bs.drop (O + (encode head).length)).length
            = (encode.encodeItems (h2 :: t2)).length := by rw [hdrop']
        rw [List.length_drop] at e
        simp only [List.length_cons] at hcount
        omega
      have body := fll_body_spec_within regionBase v5Old v10 v11Old
        (BitVec.ofNat 64 ((h2 :: t2).length + 1))
        lbase joinPC decoder_base dcr back bs O halign hO hoverO hvalidO hflat_O hdec_base
        (decoderH (bs[O]'hO) v10 v11Old (regionBase + BitVec.ofNat 64 O) hflat_O)
        hback hne_lj hne_lj4 hne_lj8 hd_lbu_dec hd_dec_add hd_dec_addi hd_dec_bne
      rw [word_ofNat_succ_dec (h2 :: t2).length] at body
      have hne_cnt : (BitVec.ofNat 64 (h2 :: t2).length : Word) ≠ 0 :=
        word_ofNat_succ_ne_zero t2.length hcnt_bound
      have h_absurd : ∀ hp,
          fll_body_post regionBase bs (bs[O]'hO) (itemCascadeResidue (bs[O]'hO))
            (itemPayloadLen (bs[O]'hO)) (itemNextPtr (bs[O]'hO) (regionBase + BitVec.ofNat 64 O))
            (BitVec.ofNat 64 (h2 :: t2).length)
            ((BitVec.ofNat 64 (h2 :: t2).length : Word) = 0) hp → False :=
        fun hp hpost => absurd (fll_body_post_pure hp hpost) hne_cnt
      have tri1 := cpsBranchWithin_takenPath body h_absurd
      -- Weaken the body's taken post to the IH precondition (drop the pure fact,
      -- re-index the pointer by the stride).
      have tri1' : cpsTripleWithin 15 lbase lbase
          (((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
              (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
              (CodeReq.singleton (joinPC + 4) (.ADDI .x14 .x14 (-1)))).union
              ((CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back)).union CodeReq.empty))
          ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
           (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
           (.x14 ↦ᵣ BitVec.ofNat 64 ((h2 :: t2).length + 1)) ** bytesRegion regionBase bs)
          ((.x5 ↦ᵣ (bs[O]'hO).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
           (.x10 ↦ᵣ itemCascadeResidue (bs[O]'hO)) ** (.x11 ↦ᵣ itemPayloadLen (bs[O]'hO)) **
           (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode head).length))) **
           (.x14 ↦ᵣ BitVec.ofNat 64 (h2 :: t2).length) ** bytesRegion regionBase bs) := by
        refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) tri1
        simp only [fll_body_post_unfold] at hp
        rw [hnext] at hp
        exact (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (fun h' hp' => ((sepConj_pure_right h').1 hp').1))))))) h hp
      have ihspec := ih (O + (encode head).length) ((bs[O]'hO).zeroExtend 64)
        (itemCascadeResidue (bs[O]'hO)) (itemPayloadLen (bs[O]'hO))
        (by simp) hdrop'
        (fun item hitem => hflat_all item (List.mem_cons_of_mem _ hitem)) hwin
      have composed := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) tri1' ihspec
      rw [show 15 * (head :: h2 :: t2).length = 15 + 15 * (h2 :: t2).length from by
            simp only [List.length_cons]; ring,
          show O + (encode.encodeItems (head :: h2 :: t2)).length
              = (O + (encode head).length) + (encode.encodeItems (h2 :: t2)).length from by
            simp only [encode.encodeItems, List.length_append]; omega]
      exact composed

/-- **Loop entry (offset 0).** Running the loop over the whole region
    `bytesRegion regionBase (encode.encodeItems items)` decodes all `items` in
    `15 * items.length` steps, leaving the pointer at the region end. -/
theorem fll_loop_n_spec_within
    (regionBase : Word) (lbase joinPC decoder_base : Word) (dcr : CodeReq) (back : BitVec 13)
    (items : List RLPItem) (v5Old v10 v11Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + (encode.encodeItems items).length < 2 ^ 64)
    (hdec_base : decoder_base = lbase + 4)
    (decoderH : ∀ (pfx : Byte) (w10 w11 w13 : Word),
       (classifyPrefix pfx = .singleByte ∨ classifyPrefix pfx = .shortBytes
         ∨ classifyPrefix pfx = .shortList) →
       cpsTripleWithin 11 decoder_base joinPC dcr
         ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ w10) **
          (.x11 ↦ᵣ w11) ** (.x13 ↦ᵣ w13))
         ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
          (.x13 ↦ᵣ itemPayloadPtr pfx w13)))
    (hback : (joinPC + 8) + signExtend13 back = lbase)
    (hne_lj : lbase ≠ joinPC) (hne_lj4 : lbase ≠ joinPC + 4) (hne_lj8 : lbase ≠ joinPC + 8)
    (hd_lbu_dec : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr)
    (hd_dec_add : dcr.Disjoint (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)))
    (hd_dec_addi : dcr.Disjoint (CodeReq.singleton (joinPC + 4) (.ADDI .x14 .x14 (-1))))
    (hd_dec_bne : dcr.Disjoint (CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back)))
    (hne : items ≠ [])
    (hflat_all : ∀ item ∈ items, isFlatItem item)
    (hwin : ∀ i, i < (encode.encodeItems items).length →
       isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (15 * items.length) lbase (joinPC + 12)
      (((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
          (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
          (CodeReq.singleton (joinPC + 4) (.ADDI .x14 .x14 (-1)))).union
          ((CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back)).union CodeReq.empty))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ BitVec.ofNat 64 items.length) **
       bytesRegion regionBase (encode.encodeItems items))
      (fll_loop_post regionBase (encode.encodeItems items)
        (regionBase + BitVec.ofNat 64 (encode.encodeItems items).length)) := by
  have h := fll_loop_spec_within regionBase lbase joinPC decoder_base dcr back
    (encode.encodeItems items) halign hover hdec_base decoderH hback
    hne_lj hne_lj4 hne_lj8 hd_lbu_dec hd_dec_add hd_dec_addi hd_dec_bne
    items 0 v5Old v10 v11Old hne (by rw [List.drop_zero]) hflat_all hwin
  rw [show regionBase + BitVec.ofNat 64 0 = regionBase from by simp,
      show (0 : Nat) + (encode.encodeItems items).length
        = (encode.encodeItems items).length from Nat.zero_add _] at h
  exact h

/-- **Flat list-decode bridge.** The operational loop (left) decodes the region
    in `15 * items.length` steps; the pure decoder (right) recovers exactly
    `items`, consuming the whole list. The two halves share the region contents
    `encode.encodeItems items`. The pure depth is `2 * len + 1` (the round-trip
    `decode_encode_mutual` uses *strict* fuel `2 * len < nDepth`). -/
theorem fll_loop_bridge
    (regionBase : Word) (lbase joinPC decoder_base : Word) (dcr : CodeReq) (back : BitVec 13)
    (items : List RLPItem) (v5Old v10 v11Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + (encode.encodeItems items).length < 2 ^ 64)
    (hdec_base : decoder_base = lbase + 4)
    (decoderH : ∀ (pfx : Byte) (w10 w11 w13 : Word),
       (classifyPrefix pfx = .singleByte ∨ classifyPrefix pfx = .shortBytes
         ∨ classifyPrefix pfx = .shortList) →
       cpsTripleWithin 11 decoder_base joinPC dcr
         ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ w10) **
          (.x11 ↦ᵣ w11) ** (.x13 ↦ᵣ w13))
         ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
          (.x13 ↦ᵣ itemPayloadPtr pfx w13)))
    (hback : (joinPC + 8) + signExtend13 back = lbase)
    (hne_lj : lbase ≠ joinPC) (hne_lj4 : lbase ≠ joinPC + 4) (hne_lj8 : lbase ≠ joinPC + 8)
    (hd_lbu_dec : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr)
    (hd_dec_add : dcr.Disjoint (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)))
    (hd_dec_addi : dcr.Disjoint (CodeReq.singleton (joinPC + 4) (.ADDI .x14 .x14 (-1))))
    (hd_dec_bne : dcr.Disjoint (CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back)))
    (hne : items ≠ [])
    (hflat_all : ∀ item ∈ items, isFlatItem item)
    (hwin : ∀ i, i < (encode.encodeItems items).length →
       isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsize : (encode.encodeItems items).length < 256 ^ 8) :
    cpsTripleWithin (15 * items.length) lbase (joinPC + 12)
      (((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
          (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
          (CodeReq.singleton (joinPC + 4) (.ADDI .x14 .x14 (-1)))).union
          ((CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back)).union CodeReq.empty))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ BitVec.ofNat 64 items.length) **
       bytesRegion regionBase (encode.encodeItems items))
      (fll_loop_post regionBase (encode.encodeItems items)
        (regionBase + BitVec.ofNat 64 (encode.encodeItems items).length))
    ∧ decodeItems (2 * (encode.encodeItems items).length + 1) (encode.encodeItems items)
        = some (items, []) :=
  ⟨fll_loop_n_spec_within regionBase lbase joinPC decoder_base dcr back items v5Old v10 v11Old
      halign hover hdec_base decoderH hback hne_lj hne_lj4 hne_lj8 hd_lbu_dec hd_dec_add
      hd_dec_addi hd_dec_bne hne hflat_all hwin,
    (decode_encode_mutual (2 * (encode.encodeItems items).length + 1)).2 items hsize (by omega)⟩

-- Sanity: representative flat items, and the stride-equivalence instantiated.
example : isFlatItem (.bytes [(0x05 : Byte)]) := by simp [isFlatItem]
example : isFlatItem (.bytes [(0xAB : Byte)]) := by simp [isFlatItem]
example : isFlatItem (.list ([] : List RLPItem)) := by simp [isFlatItem, encode.encodeItems]
example :
    itemTotalLen ((encode (.bytes [(0x05 : Byte)]))[0]'(encode_nonempty _))
      = BitVec.ofNat 64 (encode (.bytes [(0x05 : Byte)])).length :=
  encode_head_eq_itemTotalLen _ (by simp [isFlatItem])

-- Cross-check the bridge's pure half on a concrete two-item flat list: the
-- decoder recovers both items at the canonical depth `2 * len + 1`.
example :
    decodeItems (2 * (encode.encodeItems [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]]).length + 1)
        (encode.encodeItems [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]])
      = some ([.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]], []) := by
  decide

end EvmAsm.Rv64.RLP
