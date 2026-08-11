/-
  EvmAsm.Rv64.RLP.WalkNextStrict

  The two-level RLP-decode model (#12033, phase 1).

  The emitted guest is two-level: a lenient single-item core
  (`rlp_walk_next_core`, 412 bytes — the converted `rlp_walk_next_prog`) and a
  strict recursive wrapper (`rlp_walk_next_shared` + `rlp_validate_payload`,
  which descends into list payloads and rejects malformed interiors with
  status 7, #11776).  The model collapsed both levels into one relation,
  `rlpItemDecode` (WalkNext.lean), whose list disjuncts are span-fit only —
  strictly weaker than the wrapper's acceptance set and than the reference
  `decodeAux`, which descends.  This module restores one relation per emitted
  level:

  * `rlpItemDecode` (unchanged) remains the CORE's contract — lenient,
    span-fit list arms, backed by the core's triples.
  * `rlpItemDecodeStrictW` (this file) is the WRAPPER's contract — the
    lenient relation plus the recursive payload condition: a list prefix is
    accepted only if `decodeAux` decodes the item as a `.list` consuming
    exactly the item's span.  The two relations coincide on non-list items.

  Phase 1 lands the structural split and both bridge directions:
  `decodeAux` acceptance implies the wrapper relation, and the wrapper
  relation (with its recursive list condition) implies `decodeAux` acceptance.
  The byte half of the forward direction is written per-arm as the reverse of
  `rlpItemDecode_of_decodeAux_bytes` (ItemDecodeForward.lean:370), using the
  canonical byte-prefix bridges.

  Machine-tying of the wrapper relation to the emitted wrapper symbols is a
  #12021 dependency: `rlp_walk_next_shared` (208 B) and
  `rlp_validate_payload` (92 B) have no transcribed Lean `Program` yet, so no
  machine triple can be stated against the wrapper until that transcription
  lands.  Nothing in this file touches the emitted guest; all 165 guest call
  sites already route through the strict wrapper (#12033 call-site census),
  so this is a model-side change only.
-/
import EvmAsm.Rv64.RLP.ItemDecodeForward

namespace EvmAsm.Rv64.RLP

open EvmAsm.EL.RLP

/-- The WRAPPER relation (#12033): the lenient single-item relation
    `rlpItemDecode` PLUS the recursive payload condition — if the prefix at
    `off` is a list prefix (`≥ 0xc0`), `decodeAux` at `floor` must decode the
    byte stream from `off` as a `.list` consuming exactly the item's span
    (residue `bytes.drop off'`).  Cursors are stated in the
    `rlpItemDecode_of_decodeAux_bytes` style: `cursor = base + off`,
    `endPtr = base + endOff`, `next = base + off'`; `len` is the reported
    length word (content length for strings, full span for lists). -/
def rlpItemDecodeStrictW (bytes : List (BitVec 8)) (base : Word)
    (off off' endOff : Nat) (len : Word) (floor : Nat) : Prop :=
  rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      (base + BitVec.ofNat 64 endOff) (base + BitVec.ofNat 64 off') len ∧
    ((∃ b : BitVec 8, bytes[off]? = some b ∧
        ¬ BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true) →
      ∃ inner : List RLPItem,
        decodeAux floor (bytes.drop off) = some (.list inner, bytes.drop off'))

/-- `decodeAux` accepting a `.bytes` item at `off` forces the prefix below
    `0xc0` (list prefixes would decode to a `.list` item instead). -/
private theorem prefix_lt_c0_of_decodeAux_bytes
    (bytes : List Byte) (off n : Nat) (p : List Byte) (rest : List Byte)
    (b : BitVec 8)
    (hdec : decodeAux (n + 1) (bytes.drop off) = some (.bytes p, rest))
    (hget : bytes[off]? = some b) :
    b.toNat < 0xc0 := by
  obtain ⟨b', hget', hdrop⟩ := exists_prefix_of_decodeAux hdec
  rw [hget] at hget'; cases hget'
  rw [hdrop] at hdec
  cases hclass : classifyPrefix b with
  | singleByte =>
      have hb := (classifyPrefix_singleByte_iff b).mp hclass
      omega
  | shortBytes =>
      have hb := (classifyPrefix_shortBytes_iff b).mp hclass
      omega
  | longBytes =>
      have hb := (classifyPrefix_longBytes_iff b).mp hclass
      omega
  | shortList =>
      rw [decodeAux_cons_shortList_of_classifyPrefix n b
        (bytes.drop (off + 1)) hclass] at hdec
      cases htake : takeBytes (bytes.drop (off + 1))
          (rlpPrefixShortListPayloadLen b) with
      | none => simp [htake] at hdec
      | some pr =>
          obtain ⟨payload, rest'⟩ := pr
          cases hitems : decodeItems n payload with
          | none => simp [htake, hitems] at hdec
          | some pr2 =>
              obtain ⟨items2, leftover⟩ := pr2
              cases leftover with
              | nil => simp [htake, hitems] at hdec
              | cons => simp [htake, hitems] at hdec
  | longList =>
      rw [decodeAux_cons_longList_of_classifyPrefix n b
        (bytes.drop (off + 1)) hclass] at hdec
      cases hrl : readLength (bytes.drop (off + 1))
          (rlpPrefixLongListLenOfLen b) with
      | none => simp [hrl] at hdec
      | some pr =>
          obtain ⟨lenVal, rest1⟩ := pr
          by_cases h55 : lenVal ≤ 55
          · simp [hrl, h55] at hdec
          · cases htake : takeBytes rest1 lenVal with
            | none => simp [hrl, h55, htake] at hdec
            | some pr2 =>
                obtain ⟨payload, outRest⟩ := pr2
                cases hitems : decodeItems n payload with
                | none => simp [hrl, h55, htake, hitems] at hdec
                | some pr3 =>
                    obtain ⟨items2, leftover⟩ := pr3
                    cases leftover with
                    | nil => simp [hrl, h55, htake, hitems] at hdec
                    | cons => simp [hrl, h55, htake, hitems] at hdec

/-- Reverse bridge, list arms: `decodeAux` accepting a `.list` at `off`
    establishes the weak `rlpItemDecode` relation with the full-span `len`
    word.  Mirrors the structure of `rlpItemDecode_of_decodeAux_bytes`
    (ItemDecodeForward.lean:370): the short-list arm contributes
    `off' = off + 1 + (p - 0xc0)` and the long-list arm
    `off' = off + 1 + lenLen + lenVal` with `lenVal ≥ 56` and no leading
    zero in the length field. -/
theorem rlpItemDecode_of_decodeAux_list
    (bytes : List Byte) (base : Word) (off off' endOff n : Nat)
    (inner : List RLPItem)
    (hdec : decodeAux (n + 1) (bytes.drop off) = some (.list inner, bytes.drop off'))
    (hoff' : off' ≤ endOff) (hendOff : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64) :
    rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      (base + BitVec.ofNat 64 endOff) (base + BitVec.ofNat 64 off')
      (BitVec.ofNat 64 (off' - off)) := by
  obtain ⟨b, hget, hdrop⟩ := exists_prefix_of_decodeAux hdec
  rw [hdrop] at hdec
  -- `decodeAux` accepting a `.list` forces the prefix to be a list prefix.
  have hc0 : 0xc0 ≤ b.toNat := by
    by_contra hlt0
    have hlt0' : b.toNat < 0xc0 := by omega
    have hclass0 : classifyPrefix b = .singleByte ∨ classifyPrefix b = .shortBytes ∨
        classifyPrefix b = .longBytes := by
      cases hclass : classifyPrefix b with
      | singleByte => exact Or.inl rfl
      | shortBytes => exact Or.inr (Or.inl rfl)
      | longBytes => exact Or.inr (Or.inr rfl)
      | shortList =>
          have hb := (classifyPrefix_shortList_iff b).mp hclass; omega
      | longList =>
          have hb := (classifyPrefix_longList_iff b).mp hclass; omega
    rcases hclass0 with hclass | hclass | hclass
    · rw [decodeAux_cons_singleByte_of_classifyPrefix n b
        (bytes.drop (off + 1)) hclass] at hdec
      simp at hdec
    · rw [decodeAux_cons_shortBytes_of_classifyPrefix n b
        (bytes.drop (off + 1)) hclass] at hdec
      cases htake : takeBytes (bytes.drop (off + 1))
          (rlpPrefixShortBytesPayloadLen b) with
      | none => simp [htake] at hdec
      | some pr =>
          obtain ⟨data, rest'⟩ := pr
          cases data with
          | nil => simp [htake] at hdec
          | cons hd tl =>
              cases tl with
              | nil =>
                  by_cases hb1 : hd.toNat < 0x80 <;> simp [htake, hb1] at hdec
              | cons => simp [htake] at hdec
    · rw [decodeAux_cons_longBytes_of_classifyPrefix n b
        (bytes.drop (off + 1)) hclass] at hdec
      cases hrl : readLength (bytes.drop (off + 1))
          (rlpPrefixLongBytesLenOfLen b) with
      | none => simp [hrl] at hdec
      | some pr =>
          obtain ⟨lenVal, rest1⟩ := pr
          by_cases h55 : lenVal ≤ 55
          · simp [hrl, h55] at hdec
          · cases htake : takeBytes rest1 lenVal with
            | none => simp [hrl, h55, htake] at hdec
            | some pr2 =>
                obtain ⟨data, rest2⟩ := pr2
                simp [hrl, h55, htake] at hdec
  -- Word/Nat arithmetic glue shared by both arms.
  have hnn64 : ∀ i j : Nat, i < 2 ^ 64 → j < 2 ^ 64 →
      (BitVec.ult (BitVec.ofNat 64 i) (BitVec.ofNat 64 j) = true ↔ i < j) := by
    intro i j hi hj
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
    omega
  have hofflt : off < bytes.length := by
    by_contra hc
    have he : bytes.drop off = [] := List.drop_eq_nil_of_le (by omega)
    rw [he] at hdrop; simp at hdrop
  have h192t : (0xc0 : Word).toNat = 192 := by decide
  have h248t : (0xf8 : Word).toNat = 248 := by decide
  have h247t : (0xf7 : Word).toNat = 247 := by decide
  have h56t : (56 : Word).toNat = 56 := by decide
  have h1t : (1 : Word).toNat = 1 := by decide
  by_cases hshort : b.toNat ≤ 0xf7
  · -- SHORT LIST ARM: prefix `0xc0 ≤ b ≤ 0xf7`, `off' = off + 1 + payload.length`.
    have hclass : classifyPrefix b = .shortList :=
      (classifyPrefix_shortList_iff b).mpr (by omega)
    have hout := (ListDecodeBridge.decodeAux_cons_shortList_eq_some_iff n b
      (bytes.drop (off + 1)) hclass inner (bytes.drop off')).mp hdec
    obtain ⟨payload, hsplice, hitems⟩ := hout
    obtain ⟨hcat, hplen⟩ := takeBytes_eq_some_imp hsplice
    have hplen' : payload.length = b.toNat - 0xc0 := by
      simpa [rlpPrefixShortListPayloadLen] using hplen
    have hlenDrop : (bytes.drop (off + 1)).length = bytes.length - (off + 1) :=
      List.length_drop ..
    have hlenDrop' : (bytes.drop off').length = bytes.length - off' :=
      List.length_drop ..
    have hoff_le : off + 1 + payload.length ≤ bytes.length := by
      have hl := congrArg List.length hcat
      rw [List.length_append, hlenDrop, hlenDrop'] at hl
      have hoff'le : off' ≤ bytes.length := Nat.le_trans hoff' hendOff
      omega
    have hrest : bytes.drop off' = bytes.drop (off + 1 + payload.length) := by
      have hdropEq : bytes.drop (off + 1 + payload.length)
          = (bytes.drop (off + 1)).drop payload.length := by
        rw [List.drop_drop]
      rw [hdropEq, hcat, List.drop_left]
    have hoffeq : off' = off + 1 + payload.length :=
      drop_inj_of_le (Nat.le_trans hoff' hendOff) hoff_le hrest
    -- disjunct fields
    have hrhs : (b.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12) =
        BitVec.ofNat 64 (payload.length + 1) := by
      rw [signExtend12_one]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_sub,
        BitVec.toNat_ofNat, hplen']
      omega
    have hlhs : (base + BitVec.ofNat 64 endOff) - (base + BitVec.ofNat 64 off) =
        BitVec.ofNat 64 (endOff - off) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hnextW : base + BitVec.ofNat 64 off' =
        base + BitVec.ofNat 64 off + BitVec.ofNat 64 (payload.length + 1) := by
      rw [hoffeq]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    refine ⟨b, hget, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩)))⟩
    · -- ¬ ult (b.zeroExtend 64) 0xc0
      simp only [BitVec.ult, decide_eq_true_eq, toNat_byte_zeroExtend, h192t]
      omega
    · -- ult (b.zeroExtend 64) 0xf8
      simp only [BitVec.ult, decide_eq_true_eq, toNat_byte_zeroExtend, h248t]
      omega
    · -- ¬ ult (endPtr - cursor) ((b.zeroExtend 64 - 0xc0) + 1)
      rw [hlhs, hrhs, hnn64 (endOff - off) (payload.length + 1) (by omega) (by omega)]
      omega
    · -- next
      rw [hnextW, hrhs]
    · -- len
      rw [hrhs]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, hoffeq]
      omega
  · -- LONG LIST ARM: prefix `b ≥ 0xf8`, `off' = off + 1 + k + lenVal`.
    have hclass : classifyPrefix b = .longList :=
      (classifyPrefix_longList_iff b).mpr (by omega)
    have hout := (ListDecodeBridge.decodeAux_cons_longList_eq_some_iff n b
      (bytes.drop (off + 1)) hclass inner (bytes.drop off')).mp hdec
    obtain ⟨lenVal, rest1, payload, hrl, h55, hsplice, hitems⟩ := hout
    have hk1 : 0 < rlpPrefixLongListLenOfLen b := by
      simp [rlpPrefixLongListLenOfLen]; omega
    obtain ⟨hklen, hlenVal, hrest1, ⟨c, hc0', hcz⟩⟩ := readLength_inv hk1 hrl
    obtain ⟨hcat0, hplen⟩ := takeBytes_eq_some_imp hsplice
    -- restate everything at index `k = b.toNat - 0xf7`
    set k := b.toNat - 0xf7 with hk_def
    have hk_eq : rlpPrefixLongListLenOfLen b = k := rfl
    have hcat : (bytes.drop (off + 1)).drop k = payload ++ bytes.drop off' := by
      rw [hk_eq] at hrest1
      exact hrest1.symm.trans hcat0
    have hplen' : payload.length = lenVal := hplen
    have hfb : Nat.fromBytesBE ((bytes.drop (off + 1)).take k) = lenVal := by
      rw [hk_eq] at hlenVal
      exact hlenVal.symm
    have hfb64 : lenVal < 2 ^ 64 := by
      have hbnd : lenVal < 256 ^ k := by
        have h1 := Nat.fromBytesBE_lt ((bytes.drop (off + 1)).take k)
        rw [hfb] at h1
        have htk : ((bytes.drop (off + 1)).take k).length = k := by
          rw [List.length_take]
          rw [hk_eq] at hklen
          omega
        rw [htk] at h1
        exact h1
      have hk8 : k ≤ 8 := by omega
      calc lenVal < 256 ^ k := hbnd
        _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hk8
        _ = 2 ^ 64 := by norm_num
    have hrest_eq : bytes.drop (off + 1 + k) = (bytes.drop (off + 1)).drop k := by
      rw [List.drop_drop]
    have hcat2 : bytes.drop (off + 1 + k) = payload ++ bytes.drop off' := by
      rw [hrest_eq]; exact hcat
    have hlenDrop : (bytes.drop (off + 1 + k)).length =
        bytes.length - (off + 1 + k) := List.length_drop ..
    have hlenDrop' : (bytes.drop off').length = bytes.length - off' :=
      List.length_drop ..
    have hoff_le : off + 1 + k + lenVal ≤ bytes.length := by
      have hl := congrArg List.length hcat2
      rw [List.length_append, hplen', hlenDrop, hlenDrop'] at hl
      have hoff'le : off' ≤ bytes.length := Nat.le_trans hoff' hendOff
      omega
    have hrest : bytes.drop off' = bytes.drop (off + 1 + k + lenVal) := by
      have hdropEq : bytes.drop (off + 1 + k + lenVal)
          = (bytes.drop (off + 1 + k)).drop lenVal := by
        rw [List.drop_drop]
      rw [hdropEq, hcat2, ← hplen', List.drop_left]
    have hoffeq : off' = off + 1 + k + lenVal :=
      drop_inj_of_le (Nat.le_trans hoff' hendOff) hoff_le hrest
    -- leading-zero byte
    have hrestNe : bytes.drop (off + 1) ≠ [] := by
      intro he
      rw [he] at hklen
      simp at hklen
      omega
    have hgetB1 : bytes[off + 1]? = some c := by
      have h0 : (bytes.drop (off + 1))[0]? = some c := hc0'
      rw [List.getElem?_drop] at h0
      exact h0
    -- disjunct fields
    have h_k : ((b.zeroExtend 64 - (0xf7 : Word))).toNat = k := by
      simp [BitVec.toNat_sub, BitVec.toNat_ofNat, hk_def]
      omega
    have h_ofsub : b.zeroExtend 64 - (0xf7 : Word) = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat]
      omega
    have h_dLen : BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop (off + 1)).take
        ((b.zeroExtend 64 - (0xf7 : Word)).toNat))) = BitVec.ofNat 64 lenVal := by
      rw [h_k, hfb]
    have hrhs : (b.zeroExtend 64 - (0xf7 : Word)) +
          BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop (off + 1)).take
            ((b.zeroExtend 64 - (0xf7 : Word)).toNat))) =
        BitVec.ofNat 64 k + BitVec.ofNat 64 lenVal := by
      rw [h_dLen, h_ofsub]
    have hlhs : (base + BitVec.ofNat 64 endOff) - (base + BitVec.ofNat 64 off) =
        BitVec.ofNat 64 (endOff - off) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hpre : base + BitVec.ofNat 64 off +
          ((b.zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)) =
        base + BitVec.ofNat 64 off + BitVec.ofNat 64 (k + 1) := by
      rw [signExtend12_one]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_sub,
        BitVec.toNat_ofNat]
      omega
    have hnextW : base + BitVec.ofNat 64 off' =
        (base + BitVec.ofNat 64 off + (BitVec.ofNat 64 k +
          BitVec.ofNat 64 lenVal)) + (1 : Word) := by
      rw [hoffeq]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    refine ⟨b, hget, Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))⟩
    · -- ¬ ult (b.zeroExtend 64) 0xf8
      simp only [BitVec.ult, decide_eq_true_eq, toNat_byte_zeroExtend, h248t]
      omega
    · -- leading zero
      refine ⟨c, hgetB1, ?_⟩
      intro hcz0
      have hct : c.toNat = 0 := by
        have h2 := congrArg BitVec.toNat hcz0
        rw [toNat_byte_zeroExtend] at h2
        simpa using h2
      by_cases hk1' : k = 1
      · -- k = 1: the length byte is `c` itself and `lenVal > 55` forces `c ≠ 0`
        have hsn : (bytes.drop (off + 1)).take k = [c] := by
          have h1 : (bytes.drop (off + 1))[0]? = some c := hc0'
          rw [hk1']
          cases hbs : bytes.drop (off + 1) with
          | nil => rw [hbs] at h1; simp at h1
          | cons x xs =>
              rw [hbs] at h1
              simp at h1
              rw [← h1]
              rfl
        have hc_eq : lenVal = c.toNat := by
          rw [← hfb, hsn]
          simp [Nat.fromBytesBE]
        omega
      · have h1k : 1 < k := by omega
        have := hcz h1k
        omega
    · -- ¬ ult (ofNat (fromBytesBE ...)) 56
      rw [h_dLen]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, h56t]
      omega
    · -- ¬ ult endPtr (cursor + ((b - 0xf7) + 1))
      have he1 : (base + BitVec.ofNat 64 endOff).ult
          (base + BitVec.ofNat 64 off +
            ((b.zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) =
          true ↔ endOff < off + (k + 1) := by
        rw [hpre]
        simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add,
          BitVec.toNat_ofNat]
        omega
      rw [he1]
      simp
      omega
    · -- ¬ ult (endPtr - (cursor + ((b - 0xf7) + 1))) (ofNat (fromBytesBE ...))
      have hstep : (base + BitVec.ofNat 64 endOff) -
          (base + BitVec.ofNat 64 off +
            ((b.zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) =
          BitVec.ofNat 64 (endOff - (off + k + 1)) := by
        rw [hpre]
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rw [hstep, h_dLen, hnn64 (endOff - (off + k + 1)) lenVal (by omega) hfb64]
      simp
      omega
    · -- next
      rw [hnextW]
      rw [h_dLen, h_ofsub, signExtend12_one]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · -- len
      rw [h_dLen, h_ofsub, signExtend12_one]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat, hoffeq]
      omega

private theorem rlpItemDecode_singleByte_to_decodeAux
    (bytes : List Byte) (base : Word) (off off' endOff n : Nat)
    (b : Byte) (hget : bytes[off]? = some b)
    (hform :
      BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult (base + BitVec.ofNat 64 off) (base + BitVec.ofNat 64 endOff) = true ∧
        base + BitVec.ofNat 64 off' =
          (base + BitVec.ofNat 64 off) + signExtend12 (1 : BitVec 12))
    (hoff' : off' ≤ endOff) (hendOff : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64) :
    decodeAux (n + 1) (bytes.drop off) = some (.bytes [b], bytes.drop off') := by
  rcases hform with ⟨hprefix, _, hnext⟩
  have hofflt : off < bytes.length := by
    exact (List.getElem?_eq_some_iff.mp hget).1
  have hsingle : b.toNat < 0x80 :=
    (ult_zeroExtend_iff (by norm_num)).mp hprefix
  have hclass : classifyPrefix b = .singleByte :=
    (classifyPrefix_singleByte_iff b).mpr hsingle
  have hoffeq : off' = off + 1 := by
    have hnext' := hnext
    rw [signExtend12_one, show (1 : Word) = BitVec.ofNat 64 1 from rfl,
      base_add_add_ofNat (bound := bytes.length) (by omega) hover] at hnext'
    have hn := congrArg BitVec.toNat hnext'
    rw [toNat_base_add_ofNat (bound := bytes.length) (by omega) hover,
      toNat_base_add_ofNat (bound := bytes.length) (by omega) hover] at hn
    omega
  have hdrop : bytes.drop off = b :: bytes.drop (off + 1) :=
    drop_eq_cons_of_getElem? hget
  rw [hdrop, hoffeq]
  exact (ByteStringDecodeBridge.decodeAux_cons_singleByte_eq_some_iff n b
    (bytes.drop (off + 1)) hclass [b] (bytes.drop (off + 1))).mpr ⟨rfl, rfl⟩

set_option maxRecDepth 8000 in
private theorem rlpItemDecode_shortBytes_to_decodeAux
    (bytes : List Byte) (base : Word) (off off' endOff n : Nat)
    (b : Byte) (hget : bytes[off]? = some b)
    (hform :
      ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true ∧
        (b.zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : Byte, bytes[off + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult (b.zeroExtend 64 - (0x80 : Word))
          (base + BitVec.ofNat 64 endOff - (base + BitVec.ofNat 64 off)) = true ∧
        base + BitVec.ofNat 64 off' =
          (base + BitVec.ofNat 64 off) + signExtend12 (1 : BitVec 12) +
            (b.zeroExtend 64 - (0x80 : Word)))
    (hoff : off ≤ endOff) (hoff' : off' ≤ endOff) (hendOff : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64) :
    decodeAux (n + 1) (bytes.drop off) =
      some (.bytes ((bytes.drop (off + 1)).take (b.toNat - 0x80)), bytes.drop off') := by
  rcases hform with ⟨hlo, hhi, hcanonW, hfit, hnext⟩
  have hofflt : off < bytes.length := by
    exact (List.getElem?_eq_some_iff.mp hget).1
  have hnot80 : ¬ b.toNat < 0x80 := by
    intro hlt
    apply hlo
    exact (ult_zeroExtend_iff (by norm_num)).mpr hlt
  have hlo' : 0x80 ≤ b.toNat := by
    omega
  have hhi' : b.toNat ≤ 0xb7 := by
    have hlt : b.toNat < 0xb8 :=
      (ult_zeroExtend_iff (b := b) (m := 0xb8) (by norm_num)).mp hhi
    omega
  have hplenW : b.zeroExtend 64 - (0x80 : Word) =
      BitVec.ofNat 64 (b.toNat - 0x80) := by
    exact zeroExtend_sub_eq_ofNat hlo' rfl (by norm_num)
  have hsub : (base + BitVec.ofNat 64 endOff) -
      (base + BitVec.ofNat 64 off) = BitVec.ofNat 64 (endOff - off) :=
    sub_base_add_ofNat hoff hendOff hover
  have hfit' := hfit
  rw [hsub, hplenW] at hfit'
  have hfitNat : b.toNat - 0x80 < endOff - off := by
    exact (ult_ofNat_iff (by omega) (by omega)).mp hfit'
  have hoffeq : off' = off + 1 + (b.toNat - 0x80) := by
    have hnext' := hnext
    rw [hplenW, signExtend12_one, show (1 : Word) = BitVec.ofNat 64 1 from rfl,
      base_add_add_ofNat (bound := bytes.length) (by omega) hover,
      base_add_add_ofNat (bound := bytes.length) (by omega) hover] at hnext'
    have hn := congrArg BitVec.toNat hnext'
    rw [toNat_base_add_ofNat (bound := bytes.length) (by omega) hover,
      toNat_base_add_ofNat (bound := bytes.length) (by omega) hover] at hn
    omega
  have hplen_fit : b.toNat - 0x80 ≤ (bytes.drop (off + 1)).length := by
    rw [List.length_drop]
    omega
  let payload := (bytes.drop (off + 1)).take (b.toNat - 0x80)
  have hpayload_len : payload.length = b.toNat - 0x80 := by
    simp only [payload, List.length_take]
    exact Nat.min_eq_left hplen_fit
  have htake : takeBytes (bytes.drop (off + 1)) (b.toNat - 0x80) =
      some (payload, bytes.drop off') := by
    rw [takeBytes_length_ge hplen_fit]
    simp only [payload]
    rw [List.drop_drop, hoffeq]
  let canonical : List Byte → Prop := fun q => match q with
      | [c] => ¬ c.toNat < 0x80
      | _ => True
  have hcanon : canonical payload := by
    by_cases hsingleton : ∃ c, payload = [c]
    · obtain ⟨c, hc⟩ := hsingleton
      rw [hc]
      change ¬ c.toNat < 0x80
      have hcontent : [c] =
          (bytes.drop (off + 1)).take ([c] : List Byte).length := by
        rw [← hc, hpayload_len]
      have hgetc : bytes[off + 1]? = some c :=
        getElem?_of_take_singleton hcontent rfl
      have hword : b.zeroExtend 64 - (0x80 : Word) = (1 : Word) := by
        rw [hplenW, ← hpayload_len, hc]
        rfl
      obtain ⟨c', hgetc', hcnz⟩ := hcanonW hword
      have hcc : c' = c := Option.some.inj (hgetc'.symm.trans hgetc)
      subst c'
      exact fun hlt => hcnz ((ult_zeroExtend_iff (by norm_num)).mpr hlt)
    · have hnot : ∀ c, payload ≠ [c] := by
        intro c hc
        exact hsingleton ⟨c, hc⟩
      have hmatch : ∀ q : List Byte, (∀ c, q ≠ [c]) → canonical q := by
        intro q hq
        cases q with
        | nil => trivial
        | cons c tl =>
            cases tl with
            | nil => exact False.elim (hq c rfl)
            | cons c' tl' => trivial
      exact hmatch payload hnot
  have hdrop : bytes.drop off = b :: bytes.drop (off + 1) :=
    drop_eq_cons_of_getElem? hget
  have hclass : classifyPrefix b = .shortBytes :=
    (classifyPrefix_shortBytes_iff b).mpr ⟨hlo', hhi'⟩
  rw [hdrop]
  exact (ByteStringDecodeBridge.decodeAux_cons_shortBytes_eq_some_iff n b
    (bytes.drop (off + 1)) hclass payload (bytes.drop off')).mpr
    ⟨payload, htake, rfl, by simpa only [canonical] using hcanon⟩

set_option maxRecDepth 8000 in
private theorem rlpItemDecode_longBytes_to_decodeAux
    (bytes : List Byte) (base : Word) (off off' endOff n : Nat)
    (b : Byte) (hget : bytes[off]? = some b)
    (hform :
      ¬ BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true ∧
        BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true ∧
        (∃ b1 : Byte, bytes[off + 1]? = some b1 ∧
          b1.zeroExtend 64 ≠ (0 : Word)) ∧
        ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
          ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xb7 : Word)).toNat)))
          (56 : Word) = true ∧
        ¬ BitVec.ult (base + BitVec.ofNat 64 endOff)
          (base + BitVec.ofNat 64 off +
            ((b.zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))) = true ∧
        ¬ BitVec.ult
          ((base + BitVec.ofNat 64 endOff) -
            (base + BitVec.ofNat 64 off +
              ((b.zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))))
          (BitVec.ofNat 64 (Nat.fromBytesBE
            ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xb7 : Word)).toNat))) = true ∧
        base + BitVec.ofNat 64 off' =
          (base + BitVec.ofNat 64 off +
            ((b.zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))) +
            BitVec.ofNat 64 (Nat.fromBytesBE
              ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xb7 : Word)).toNat)))
    (hoff : off ≤ endOff) (hoff' : off' ≤ endOff) (hendOff : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hnowrap : base.toNat + endOff + 9 < 2 ^ 64) :
    decodeAux (n + 1) (bytes.drop off) =
      some (.bytes
        ((bytes.drop (off + 1 + (b.toNat - 0xb7))).take
          (Nat.fromBytesBE
            ((bytes.drop (off + 1)).take (b.toNat - 0xb7)))),
        bytes.drop off') := by
  rcases hform with ⟨hlo, hhi, hnz, hlen, hheader, hfit, hnext⟩
  set k := b.toNat - 0xb7 with hk_def
  have hkpos : 0 < k := by
    dsimp [k]
    have hb := (ult_zeroExtend_iff (b := b) (m := 0xc0) (by norm_num)).mp hhi
    have hb0 : 0xb8 ≤ b.toNat := by
      have hnot : ¬ b.toNat < 0xb8 := by
        intro hh
        apply hlo
        exact (ult_zeroExtend_iff (b := b) (m := 0xb8) (by norm_num)).mpr hh
      omega
    omega
  have hk8 : k ≤ 8 := by
    dsimp [k]
    have hb := (ult_zeroExtend_iff (b := b) (m := 0xc0) (by norm_num)).mp hhi
    have hb0 : 0xb8 ≤ b.toNat := by
      have hnot : ¬ b.toNat < 0xb8 := by
        intro hh
        apply hlo
        exact (ult_zeroExtend_iff (b := b) (m := 0xb8) (by norm_num)).mpr hh
      omega
    omega
  have h_ofsub : b.zeroExtend 64 - (0xb7 : Word) = BitVec.ofNat 64 k := by
    have hnot : ¬ b.toNat < 0xb8 := by
      intro hh
      apply hlo
      exact (ult_zeroExtend_iff (b := b) (m := 0xb8) (by norm_num)).mpr hh
    have hge : 0xb7 ≤ b.toNat :=
      Nat.le_trans (by norm_num) (Nat.le_of_not_gt hnot)
    exact zeroExtend_sub_eq_ofNat hge hk_def (by norm_num)
  have h_k : (b.zeroExtend 64 - (0xb7 : Word)).toNat = k := by
    rw [h_ofsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpre : base + BitVec.ofNat 64 off +
        ((b.zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12)) =
      base + BitVec.ofNat 64 off + BitVec.ofNat 64 (k + 1) := by
    rw [h_ofsub, signExtend12_one, show (1 : Word) = BitVec.ofNat 64 1 from rfl,
      ofNat_add_ofNat (by omega)]
  have hheaderNat : off + k + 1 ≤ endOff := by
    rw [hpre] at hheader
    have hleft : (base + BitVec.ofNat 64 endOff).toNat = base.toNat + endOff :=
      toNat_base_add_ofNat hendOff hover
    have hsum : base.toNat + off + (k + 1) < 2 ^ 64 := by
      have hk1 : k + 1 ≤ 9 := by omega
      omega
    have hright : (base + BitVec.ofNat 64 off + BitVec.ofNat 64 (k + 1)).toNat =
        base.toNat + off + (k + 1) := by
      rw [BitVec.toNat_add, toNat_base_add_ofNat (le_trans hoff hendOff) hover,
        BitVec.toNat_ofNat]
      simp only [Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)]
      exact Nat.mod_eq_of_lt hsum
    simp only [BitVec.ult, decide_eq_true_eq, hleft, hright] at hheader
    omega
  let rest := bytes.drop (off + 1)
  let lenVal := Nat.fromBytesBE (rest.take k)
  have hlen_expr : Nat.fromBytesBE
      ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xb7 : Word)).toNat) = lenVal := by
    rw [h_k]
  have hrest_head : rest[0]? = some (Classical.choose hnz) := by
    dsimp [rest]
    rw [← (Classical.choose_spec hnz).1, List.getElem?_drop]
  have htake_len : takeBytes rest k = some (rest.take k, rest.drop k) := by
    exact takeBytes_length_ge (by
      dsimp [rest]
      rw [List.length_drop]
      omega)
  have hslice_nonempty : ∃ tail, rest.take k = Classical.choose hnz :: tail := by
    have hhead_take : (rest.take k).head? = some (Classical.choose hnz) := by
      rw [List.head?_take]
      simp only [if_neg (Nat.ne_of_gt hkpos)]
      simpa only [List.head?_eq_getElem?] using hrest_head
    cases hslice : rest.take k with
    | nil =>
        rw [hslice] at hhead_take
        simp at hhead_take
    | cons x xs =>
        rw [hslice] at hhead_take
        simp at hhead_take
        have hx : x = Classical.choose hnz := hhead_take
        subst x
        exact ⟨xs, rfl⟩
  have hchoose_ne : Classical.choose hnz ≠ (0 : Byte) := by
    intro hz
    apply (Classical.choose_spec hnz).2
    rw [hz]
    rfl
  have hread : readLength rest k = some (lenVal, rest.drop k) := by
    obtain ⟨tail, htail⟩ := hslice_nonempty
    have htake_nonzero : takeBytes rest k =
        some ((Classical.choose hnz :: tail), rest.drop k) := by
      simpa [htail] using htake_len
    have hread' := readLength_some_of_takeBytes_nonzero htake_nonzero hchoose_ne
    simpa [lenVal, htail] using hread'
  have hlenVal_bound : lenVal < 2 ^ 64 := by
    dsimp [lenVal]
    have hlt := Nat.fromBytesBE_lt (rest.take k)
    have htk : (rest.take k).length = k := by
      rw [List.length_take]
      exact Nat.min_eq_left (by
        dsimp [rest]
        rw [List.length_drop]
        omega)
    rw [htk] at hlt
    calc
      Nat.fromBytesBE (rest.take k) < 256 ^ k := hlt
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hk8
      _ = 2 ^ 64 := by norm_num
  have hlong : 55 < lenVal := by
    rw [hlen_expr] at hlen
    have hnot : ¬ lenVal < 56 := by
      intro hlt
      apply hlen
      exact (ult_ofNat_iff hlenVal_bound (by norm_num)).mpr hlt
    exact Nat.le_of_not_gt hnot
  have hheader_ptr : base + BitVec.ofNat 64 off + BitVec.ofNat 64 (k + 1) =
      base + BitVec.ofNat 64 (off + k + 1) := by
    exact base_add_add_ofNat (bound := bytes.length) (by omega) hover
  have hfit' := hfit
  rw [hpre, hheader_ptr, hlen_expr] at hfit'
  have hsub : (base + BitVec.ofNat 64 endOff) -
      (base + BitVec.ofNat 64 (off + k + 1)) =
      BitVec.ofNat 64 (endOff - (off + k + 1)) := by
    exact sub_base_add_ofNat hheaderNat hendOff hover
  rw [hsub] at hfit'
  have hfitNat : lenVal ≤ endOff - (off + k + 1) := by
    have hnot : ¬ endOff - (off + k + 1) < lenVal := by
      intro hlt
      apply hfit'
      exact (ult_ofNat_iff (by omega) hlenVal_bound).mpr hlt
    exact Nat.le_of_not_gt hnot
  have hpayload_fit : lenVal ≤ (rest.drop k).length := by
    have hlenrest : (rest.drop k).length = bytes.length - (off + 1 + k) := by
      dsimp [rest]
      rw [List.length_drop, List.length_drop]
      omega
    rw [hlenrest]
    omega
  have hoffeq : off' = off + 1 + k + lenVal := by
    have hnext' := hnext
    rw [hpre, hheader_ptr, hlen_expr] at hnext'
    have hcombine : (base + BitVec.ofNat 64 (off + k + 1)) +
        BitVec.ofNat 64 lenVal =
        base + BitVec.ofNat 64 (off + k + 1 + lenVal) :=
      base_add_add_ofNat (bound := bytes.length) (by omega) hover
    rw [hcombine] at hnext'
    have hn := congrArg BitVec.toNat hnext'
    rw [toNat_base_add_ofNat (le_trans hoff' hendOff) hover,
      toNat_base_add_ofNat (by omega) hover] at hn
    omega
  let payload := (rest.drop k).take lenVal
  have htake_payload : takeBytes (rest.drop k) lenVal =
      some (payload, bytes.drop off') := by
    rw [takeBytes_length_ge hpayload_fit]
    dsimp [payload]
    have hrem : (rest.drop k).drop lenVal = bytes.drop off' := by
      dsimp [rest]
      simp [List.drop_drop, hoffeq, Nat.add_assoc]
    rw [hrem]
  have hdrop : bytes.drop off = b :: rest := by
    dsimp [rest]
    exact drop_eq_cons_of_getElem? hget
  have hclass : classifyPrefix b = .longBytes := by
    apply (classifyPrefix_longBytes_iff b).mpr
    have hb0 : 0xb8 ≤ b.toNat := by
      have hnot : ¬ b.toNat < 0xb8 := by
        intro hh
        apply hlo
        exact (ult_zeroExtend_iff (b := b) (m := 0xb8) (by norm_num)).mpr hh
      omega
    have hb1 : b.toNat < 0xc0 :=
      (ult_zeroExtend_iff (b := b) (m := 0xc0) (by norm_num)).mp hhi
    exact ⟨hb0, by omega⟩
  rw [hdrop]
  have hdecode := (ByteStringDecodeBridge.decodeAux_cons_longBytes_eq_some_iff n b rest
    hclass payload (bytes.drop off')).mpr
    ⟨lenVal, rest.drop k, hread, hlong, htake_payload⟩
  simpa [payload, rest, lenVal, k, h_k] using hdecode

/-! ## Forward bridge: wrapper relation to model acceptance -/

/-- The forward half of the strict-wrapper bridge (#12033): once the weak walk
    relation is augmented with the wrapper's recursive list check, every
    accepted arm is an accepting `decodeAux` item.  The byte arms invert their
    corresponding canonical prefix bridge; the list arms use the recursive
    conjunct carried by `rlpItemDecodeStrictW` itself.  The caller supplies the
    in-window cursor bound and a nine-byte no-wrap margin for the long-header
    arithmetic; without that margin the word-level relation admits address
    wraparound and cannot imply a byte-window fit. -/
theorem rlpItemDecodeStrictW_to_decodeAux
    (bytes : List Byte) (base : Word) (off off' endOff n : Nat)
    (len : Word)
    (hstrict : rlpItemDecodeStrictW bytes base off off' endOff len (n + 1))
    (hoff : off ≤ endOff) (hoff' : off' ≤ endOff) (hendOff : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hnowrap : base.toNat + endOff + 9 < 2 ^ 64) :
    ∃ item, decodeAux (n + 1) (bytes.drop off) = some (item, bytes.drop off') := by
  rcases hstrict with ⟨hweak, hrecursive⟩
  rcases hweak with ⟨b, hget, harm⟩
  rcases harm with hsingle | hshort | hlong | hshortList | hlongList
  · refine ⟨.bytes [b], ?_⟩
    exact rlpItemDecode_singleByte_to_decodeAux bytes base off off' endOff n b hget
      ⟨hsingle.1, hsingle.2.1, hsingle.2.2.1⟩ hoff' hendOff hover
  · refine ⟨.bytes ((bytes.drop (off + 1)).take (b.toNat - 0x80)), ?_⟩
    exact rlpItemDecode_shortBytes_to_decodeAux bytes base off off' endOff n b hget
      ⟨hshort.1, hshort.2.1, hshort.2.2.1, hshort.2.2.2.1, hshort.2.2.2.2.1⟩
      hoff hoff' hendOff hover
  · refine ⟨.bytes ((bytes.drop (off + 1 + (b.toNat - 0xb7))).take
      (Nat.fromBytesBE ((bytes.drop (off + 1)).take (b.toNat - 0xb7)))), ?_⟩
    exact rlpItemDecode_longBytes_to_decodeAux bytes base off off' endOff n b hget
      (by
        rcases hlong with ⟨h1, h2, h3, h4, h5, h6, h7, _⟩
        exact ⟨h1, h2, h3, h4, h5, h6, h7⟩)
      hoff hoff' hendOff hover hnowrap
  · obtain ⟨inner, hdec⟩ := hrecursive ⟨b, hget, hshortList.1⟩
    exact ⟨.list inner, hdec⟩
  · have hge : ¬ BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true := by
      intro hc
      apply hlongList.1
      have hc' := (ult_zeroExtend_iff (b := b) (m := 0xc0) (by norm_num)).mp hc
      exact (ult_zeroExtend_iff (b := b) (m := 0xf8) (by norm_num)).mpr (by omega)
    obtain ⟨inner, hdec⟩ := hrecursive ⟨b, hget, hge⟩
    exact ⟨.list inner, hdec⟩

/-- Reverse bridge, complete (phase 1 of #12033): `decodeAux` acceptance at
    `off` implies the wrapper relation `rlpItemDecodeStrictW`.  The bytes arms
    reuse `rlpItemDecode_of_decodeAux_bytes` and satisfy the payload conjunct
    vacuously (a bytes item's prefix is `< 0xc0`); the list arms reuse
    `rlpItemDecode_of_decodeAux_list` and satisfy the payload conjunct
    definitionally from the acceptance hypothesis itself. -/
theorem rlpItemDecodeStrictW_of_decodeAux
    (bytes : List Byte) (base : Word) (off off' endOff n : Nat)
    (item : RLPItem)
    (hdec : decodeAux (n + 1) (bytes.drop off) = some (item, bytes.drop off'))
    (hoff' : off' ≤ endOff) (hendOff : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64) :
    ∃ len : Word,
      rlpItemDecodeStrictW bytes base off off' endOff len (n + 1) := by
  cases item with
  | bytes p =>
      refine ⟨BitVec.ofNat 64 p.length, ?_⟩
      refine ⟨rlpItemDecode_of_decodeAux_bytes bytes base off off' endOff n p
        hdec hoff' hendOff hover, ?_⟩
      intro ⟨b, hb, hge⟩
      exfalso
      have hlt := prefix_lt_c0_of_decodeAux_bytes bytes off n p
        (bytes.drop off') b hdec hb
      have hub : BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true := by
        rw [show (0xc0 : Word) = BitVec.ofNat 64 0xc0 from rfl]
        simp only [BitVec.ult, decide_eq_true_eq, toNat_byte_zeroExtend,
          BitVec.toNat_ofNat]
        omega
      exact hge hub
  | list inner =>
      refine ⟨BitVec.ofNat 64 (off' - off), ?_⟩
      refine ⟨rlpItemDecode_of_decodeAux_list bytes base off off' endOff n
        inner hdec hoff' hendOff hover, ?_⟩
      intro _
      exact ⟨inner, hdec⟩

end EvmAsm.Rv64.RLP
