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

  Phase 1 lands the structural split and the REVERSE bridge direction:
  `decodeAux` acceptance implies the wrapper relation, both arms
  (`rlpItemDecodeStrictW_of_decodeAux`).  The FORWARD direction
  (wrapper relation → `decodeAux` acceptance) is NOT attempted here: the
  byte half of that direction (weak `rlpItemDecode` bytes disjuncts →
  `EL.RLP.decode` acceptance) does not exist in any of WalkNext /
  ItemDecodeForward / WalkDecodeBridge / ListDecodeBridge and must be written
  per-arm as the reverse of `rlpItemDecode_of_decodeAux_bytes`
  (ItemDecodeForward.lean:370); that is the expensive half and is tracked
  separately.

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
