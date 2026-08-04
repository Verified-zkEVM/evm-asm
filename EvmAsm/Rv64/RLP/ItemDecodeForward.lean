/-
  EvmAsm.Rv64.RLP.ItemDecodeForward

  The **model → guest** direction of the item bridge: from a successful
  `decodeAux` of a *byte-string* item, construct the guest's `rlpItemDecode`
  relation at the corresponding offsets.

  This is the converse of `WalkDecodeBridge.lean`, and the restriction to
  `.bytes` items is essential rather than incidental.  The guest → model
  direction is **false** for the two list disjuncts: `rlpItemDecode` checks only
  that a child's declared span *fits* in the window, never its interior, so
  `[0xc3, 0xc2, 0x81, 0x00]` is accepted by the walk while `decodeAux` rejects
  the non-canonical nested `81 00`.  Restricting to byte strings removes exactly
  the disjuncts that carry that gap, which is why this direction is provable
  at all.

  Every RLP field of a block header is a byte string, so the restriction costs
  nothing for the header-extractor family.
-/

import EvmAsm.Rv64.RLP.WalkDecodeBridge
import EvmAsm.Rv64.RLP.WalkNext

namespace EvmAsm.Rv64.RLP

open EvmAsm.EL.RLP

/-! ## Offset arithmetic in the no-overflow regime

All cursors are `base + BitVec.ofNat 64 k` for `k ≤ bytes.length`, with the
whole buffer inside the address space.  These two lemmas discharge the
`toNat`/`ult` side conditions uniformly. -/

/-- In the no-overflow regime a cursor's `toNat` is its offset, unreduced. -/
theorem toNat_base_add_ofNat {base : Word} {k bound : Nat}
    (hk : k ≤ bound) (hover : base.toNat + bound < 2 ^ 64) :
    (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
  have hklt : k < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hklt,
    Nat.mod_eq_of_lt (by omega)]

/-- Cursor order mirrors offset order. -/
theorem ult_base_add_ofNat {base : Word} {i j bound : Nat}
    (hi : i ≤ bound) (hj : j ≤ bound) (hover : base.toNat + bound < 2 ^ 64) :
    BitVec.ult (base + BitVec.ofNat 64 i) (base + BitVec.ofNat 64 j) = true ↔ i < j := by
  simp only [BitVec.ult, decide_eq_true_eq,
    toNat_base_add_ofNat hi hover, toNat_base_add_ofNat hj hover]
  omega

/-- A cursor difference in the no-overflow regime is the offset difference. -/
theorem sub_base_add_ofNat {base : Word} {i j bound : Nat}
    (hij : i ≤ j) (hj : j ≤ bound) (hover : base.toNat + bound < 2 ^ 64) :
    (base + BitVec.ofNat 64 j) - (base + BitVec.ofNat 64 i)
      = BitVec.ofNat 64 (j - i) := by
  have hi : i ≤ bound := le_trans hij hj
  have hilt : i < 2 ^ 64 := by omega
  have hjlt : j < 2 ^ 64 := by omega
  have hdlt : j - i < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_base_add_ofNat hi hover, toNat_base_add_ofNat hj hover,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]
  have hsplit : 2 ^ 64 - (base.toNat + i) + (base.toNat + j)
      = 2 ^ 64 + (j - i) := by omega
  rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt hdlt]

/-- Recovering an offset from its cursor — the form `StrictNthItem.succ` needs,
    since it re-enters the chain at `(next - base).toNat`. -/
theorem sub_base_of_base_add {base : Word} {k bound : Nat}
    (hk : k ≤ bound) (hover : base.toNat + bound < 2 ^ 64) :
    ((base + BitVec.ofNat 64 k) - base).toNat = k := by
  have hklt : k < 2 ^ 64 := by omega
  rw [BitVec.toNat_sub, toNat_base_add_ofNat hk hover]
  have hsplit : 2 ^ 64 - base.toNat + (base.toNat + k) = 2 ^ 64 + k := by omega
  rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt hklt]

/-- `drop` is injective on offsets bounded by the length: the residues have
    different lengths otherwise.  This is what lets a `decodeAux` residue of the
    form `bytes.drop off'` pin `off'` itself. -/
theorem drop_inj_of_le {bytes : List Byte} {i j : Nat}
    (hi : i ≤ bytes.length) (hj : j ≤ bytes.length)
    (h : bytes.drop i = bytes.drop j) : i = j := by
  have := congrArg List.length h
  rw [List.length_drop, List.length_drop] at this
  omega

/-! ## The prefix byte -/

/-- A successful decode at `off` exposes the prefix byte there. -/
theorem exists_prefix_of_decodeAux {bytes : List Byte} {off : Nat}
    {item : RLPItem} {rest : List Byte} {n : Nat}
    (hdec : decodeAux (n + 1) (bytes.drop off) = some (item, rest)) :
    ∃ b, bytes[off]? = some b ∧ bytes.drop off = b :: bytes.drop (off + 1) := by
  cases hdrop : bytes.drop off with
  | nil => rw [hdrop] at hdec; simp [decodeAux] at hdec
  | cons b tl =>
      have hget : bytes[off]? = some b := by
        rw [← List.head?_drop, hdrop]
        rfl
      refine ⟨b, hget, ?_⟩
      rw [← hdrop]
      exact drop_eq_cons_of_getElem? hget

/-- A payload that is a `take` off a suffix and happens to be a singleton pins
    the byte at that suffix's head. -/
theorem getElem?_of_take_singleton {bytes : List Byte} {k : Nat} {p : List Byte}
    {c : Byte} (hcontent : p = (bytes.drop k).take p.length) (hp : p = [c]) :
    bytes[k]? = some c := by
  rw [hp] at hcontent
  simp only [List.length_cons, List.length_nil] at hcontent
  cases hdrop : bytes.drop k with
  | nil => rw [hdrop] at hcontent; simp at hcontent
  | cons x tl =>
      rw [hdrop] at hcontent
      simp only [List.take_succ_cons, List.take_zero] at hcontent
      have hx : x = c := (List.cons.inj hcontent).1.symm
      rw [← List.head?_drop, hdrop, hx]
      rfl

/-- `b - 0x80` as a word is the short-string payload length. -/
theorem toNat_byte_zeroExtend (b : Byte) : (b.zeroExtend 64).toNat = b.toNat := by
  have hlt : b.toNat < 2 ^ 64 := lt_trans b.isLt (by norm_num)
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt]

theorem zeroExtend_sub_eq_ofNat {b : Byte} {lo : Nat} {plen : Nat}
    (hlo : lo ≤ b.toNat) (hplen : plen = b.toNat - lo) (hlo256 : lo < 2 ^ 64) :
    b.zeroExtend 64 - BitVec.ofNat 64 lo = BitVec.ofNat 64 plen := by
  have hb256 : b.toNat < 256 := b.isLt
  have h1 : lo % 2 ^ 64 = lo := Nat.mod_eq_of_lt hlo256
  have h2 : plen % 2 ^ 64 = plen := Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_byte_zeroExtend, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1, h2]
  have hsplit : 2 ^ 64 - lo + b.toNat = 2 ^ 64 + plen := by omega
  rw [hsplit, Nat.add_mod_left, h2]

/-- `zeroExtend` of a byte compares as its numeral. -/
theorem ult_zeroExtend_iff {b : Byte} {m : Nat} (hm : m < 2 ^ 64) :
    BitVec.ult (b.zeroExtend 64) (BitVec.ofNat 64 m) = true ↔ b.toNat < m := by
  simp only [BitVec.ult, decide_eq_true_eq, toNat_byte_zeroExtend, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hm]

theorem signExtend12_one : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide

/-- Offsets compose inside the no-overflow window. -/
theorem base_add_add_ofNat {base : Word} {i j bound : Nat}
    (hij : i + j ≤ bound) (hover : base.toNat + bound < 2 ^ 64) :
    (base + BitVec.ofNat 64 i) + BitVec.ofNat 64 j = base + BitVec.ofNat 64 (i + j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add,
    toNat_base_add_ofNat (bound := bound) (by omega) hover,
    toNat_base_add_ofNat (bound := bound) (by omega) hover,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- Literal offsets add. -/
theorem ofNat_add_ofNat {i j : Nat} (hij : i + j < 2 ^ 64) :
    BitVec.ofNat 64 i + BitVec.ofNat 64 j = BitVec.ofNat 64 (i + j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt hij]

/-- Literal offsets compare. -/
theorem ult_ofNat_iff {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 i) (BitVec.ofNat 64 j) = true ↔ i < j := by
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]

/-! ## The three byte-string forms -/

/-- Single-byte item: the guest's first disjunct. -/
theorem rlpItemDecode_singleByte_forward
    (bytes : List Byte) (base : Word) (off endOff : Nat) (b : Byte)
    (hget : bytes[off]? = some b) (hsingle : b.toNat < 0x80)
    (hoff : off + 1 ≤ endOff) (hendOff : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64) :
    rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      (base + BitVec.ofNat 64 endOff) (base + BitVec.ofNat 64 (off + 1)) (1 : Word) := by
  refine ⟨b, hget, Or.inl ⟨?_, ?_, ?_, rfl⟩⟩
  · exact (ult_zeroExtend_iff (by norm_num)).mpr hsingle
  · exact (ult_base_add_ofNat (bound := bytes.length) (by omega) (by omega) hover).mpr
      (by omega)
  · have h1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [h1]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_base_add_ofNat (bound := bytes.length) (show off + 1 ≤ bytes.length by omega) hover,
      BitVec.toNat_add,
      toNat_base_add_ofNat (bound := bytes.length) (show off ≤ bytes.length by omega) hover,
      show BitVec.toNat (1 : Word) = 1 from by decide,
      Nat.mod_eq_of_lt (show base.toNat + off + 1 < 2 ^ 64 by omega)]
    omega

/-- Short byte string (`0x80..0xB7`): the guest's second disjunct. -/
theorem rlpItemDecode_shortBytes_forward
    (bytes : List Byte) (base : Word) (off endOff : Nat) (b : Byte) (p : List Byte)
    (hget : bytes[off]? = some b)
    (hlo : 0x80 ≤ b.toNat) (hhi : b.toNat ≤ 0xB7)
    (hplen : p.length = b.toNat - 0x80)
    (hcontent : p = (bytes.drop (off + 1)).take p.length)
    (hcanon : ∀ c, p = [c] → ¬ c.toNat < 0x80)
    (hoff : off + 1 + p.length ≤ endOff) (hendOff : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64) :
    rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      (base + BitVec.ofNat 64 endOff)
      (base + BitVec.ofNat 64 (off + 1 + p.length))
      (BitVec.ofNat 64 p.length) := by
  have hsub : b.zeroExtend 64 - (0x80 : Word) = BitVec.ofNat 64 p.length := by
    have : (0x80 : Word) = BitVec.ofNat 64 0x80 := by decide
    rw [this]
    exact zeroExtend_sub_eq_ofNat hlo hplen (by norm_num)
  have hplen_lt : p.length < 2 ^ 64 := by omega
  refine ⟨b, hget, Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_, hsub.symm⟩)⟩
  · rw [show (0x80 : Word) = BitVec.ofNat 64 0x80 from by decide]
    exact fun hc => absurd ((ult_zeroExtend_iff (by norm_num)).mp hc) (by omega)
  · rw [show (0xb8 : Word) = BitVec.ofNat 64 0xb8 from by decide]
    exact (ult_zeroExtend_iff (by norm_num)).mpr (by omega)
  · intro hone
    rw [hsub] at hone
    have hp1 : p.length = 1 := by
      have := congrArg BitVec.toNat hone
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplen_lt, show BitVec.toNat (1 : Word) = 1 from
        by decide] at this
    obtain ⟨c, hc⟩ : ∃ c, p = [c] := by
      match p, hp1 with
      | [c], _ => exact ⟨c, rfl⟩
    refine ⟨c, getElem?_of_take_singleton hcontent hc, ?_⟩
    rw [show (0x80 : Word) = BitVec.ofNat 64 0x80 from by decide]
    exact fun hlt => hcanon c hc ((ult_zeroExtend_iff (by norm_num)).mp hlt)
  · rw [hsub, sub_base_add_ofNat (bound := bytes.length) (by omega) (by omega) hover]
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hplen_lt, Nat.mod_eq_of_lt (show endOff - off < 2 ^ 64 by omega)]
    omega
  · rw [hsub]
    have h1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [h1]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_base_add_ofNat (bound := bytes.length) (by omega) hover,
      BitVec.toNat_add, BitVec.toNat_add,
      toNat_base_add_ofNat (bound := bytes.length) (by omega) hover,
      show BitVec.toNat (1 : Word) = 1 from by decide,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplen_lt,
      Nat.mod_eq_of_lt (show base.toNat + off + 1 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- Long byte string (`0xB8..0xBF`): the guest's third disjunct.  `lol` is the
    length-of-length byte count, so the header occupies `1 + lol` bytes. -/
theorem rlpItemDecode_longBytes_forward
    (bytes : List Byte) (base : Word) (off endOff lol : Nat) (b : Byte) (p : List Byte)
    (hget : bytes[off]? = some b)
    (hlo : 0xB8 ≤ b.toNat) (hhi : b.toNat ≤ 0xBF)
    (hlolDef : lol = b.toNat - 0xB7)
    (hlenval : Nat.fromBytesBE ((bytes.drop (off + 1)).take lol) = p.length)
    (hlong : 55 < p.length)
    (hnz : ∃ b1, bytes[off + 1]? = some b1 ∧ b1.toNat ≠ 0)
    (hoff : off + 1 + lol + p.length ≤ endOff)
    (hendOff : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64) :
    rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      (base + BitVec.ofNat 64 endOff)
      (base + BitVec.ofNat 64 (off + 1 + lol + p.length))
      (BitVec.ofNat 64 p.length) := by
  have hb256 : b.toNat < 256 := b.isLt
  have hlolW : b.zeroExtend 64 - (0xb7 : Word) = BitVec.ofNat 64 lol := by
    rw [show (0xb7 : Word) = BitVec.ofNat 64 0xb7 from by decide]
    exact zeroExtend_sub_eq_ofNat (by omega) hlolDef (by norm_num)
  have hlolNat : (b.zeroExtend 64 - (0xb7 : Word)).toNat = lol := by
    rw [hlolW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hplen_lt : p.length < 2 ^ 64 := by omega
  -- the decoded payload length, in the exact shape the guest predicate uses
  have hlenExpr : Nat.fromBytesBE
      ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xb7 : Word)).toNat) = p.length := by
    rw [hlolNat]; exact hlenval
  -- the header end (prefix byte + `lol` length bytes), as a cursor
  have hhdr : (base + BitVec.ofNat 64 off) +
      ((b.zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))
      = base + BitVec.ofNat 64 (off + 1 + lol) := by
    have harith : off + (lol + 1) = off + 1 + lol := by omega
    rw [hlolW, signExtend12_one, show (1 : Word) = BitVec.ofNat 64 1 from by decide,
      ofNat_add_ofNat (by omega),
      base_add_add_ofNat (bound := bytes.length) (by omega) hover, harith]
  refine ⟨b, hget, Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))⟩
  · rw [show (0xb8 : Word) = BitVec.ofNat 64 0xb8 from by decide]
    exact fun hc => absurd ((ult_zeroExtend_iff (by norm_num)).mp hc) (by omega)
  · rw [show (0xc0 : Word) = BitVec.ofNat 64 0xc0 from by decide]
    exact (ult_zeroExtend_iff (by norm_num)).mpr (by omega)
  · obtain ⟨b1, hb1get, hb1nz⟩ := hnz
    refine ⟨b1, hb1get, ?_⟩
    intro hzero
    exact hb1nz (by
      have := congrArg BitVec.toNat hzero
      rwa [toNat_byte_zeroExtend, show BitVec.toNat (0 : Word) = 0 from by decide] at this)
  · rw [hlenExpr, show (56 : Word) = BitVec.ofNat 64 56 from by decide]
    exact fun hc => absurd ((ult_ofNat_iff hplen_lt (by norm_num)).mp hc) (by omega)
  · rw [hhdr]
    exact fun hc => absurd
      ((ult_base_add_ofNat (bound := bytes.length) (by omega) (by omega) hover).mp hc) (by omega)
  · rw [hlenExpr, hhdr, sub_base_add_ofNat (bound := bytes.length) (by omega) (by omega) hover]
    exact fun hc => absurd
      ((ult_ofNat_iff (by omega) hplen_lt).mp hc) (by omega)
  · rw [hlenExpr, hhdr, base_add_add_ofNat (bound := bytes.length) (by omega) hover]
  · rw [hlenExpr]

/-! ## Inverting the model's length reader -/

/-- Inversion of `readLength` at a positive width: it consumes exactly `k`
    bytes, reads them big-endian, and (for `k > 1`) has rejected a leading
    zero. -/
theorem readLength_inv {bs : List Byte} {k lenVal : Nat} {rest' : List Byte}
    (hk : 0 < k) (h : readLength bs k = some (lenVal, rest')) :
    k ≤ bs.length ∧ lenVal = Nat.fromBytesBE (bs.take k) ∧ rest' = bs.drop k ∧
      ∃ c, bs[0]? = some c ∧ (1 < k → c.toNat ≠ 0) := by
  by_cases hle : k ≤ bs.length
  · cases hbs : bs with
    | nil => rw [hbs] at hle; simp at hle; omega
    | cons x xs =>
        subst hbs
        have hxs : k - 1 ≤ xs.length := by simp at hle; omega
        have htakeEq : (x :: xs).take k = x :: xs.take (k - 1) := by
          cases k with
          | zero => omega
          | succ k' => simp
        have htake : takeBytes (x :: xs) k
            = some (x :: xs.take (k - 1), (x :: xs).drop k) := by
          rw [takeBytes_length_ge hle, htakeEq]
        by_cases hx : x = (0 : Byte)
        · -- a leading zero is legal only at width one; there `1 < k → …` is vacuous
          subst hx
          have hk1 : k = 1 := by
            by_contra hne
            have hgt : 1 < k := by omega
            obtain ⟨y, ys, hys⟩ : ∃ y ys, xs.take (k - 1) = y :: ys := by
              cases hxt : xs.take (k - 1) with
              | nil =>
                  exfalso
                  have hl : (xs.take (k - 1)).length = k - 1 := by
                    rw [List.length_take]; omega
                  rw [hxt] at hl; simp at hl; omega
              | cons y ys => exact ⟨y, ys, rfl⟩
            rw [hys] at htake
            rw [readLength_none_of_takeBytes_leading_zero htake] at h
            simp at h
          subst hk1
          simp only [Nat.sub_self, List.take_zero] at htake
          rw [readLength_some_of_takeBytes_single htake] at h
          have hpair := Option.some.inj h
          have hval := congrArg Prod.fst hpair
          have hrest := congrArg Prod.snd hpair
          simp only at hval hrest
          refine ⟨hle, ?_, hrest.symm, (0 : Byte), rfl, fun hk => absurd hk (by omega)⟩
          rw [← hval, htakeEq]
          simp [Nat.fromBytesBE]
        · rw [readLength_some_of_takeBytes_nonzero htake hx] at h
          have hpair := Option.some.inj h
          have hval := congrArg Prod.fst hpair
          have hrest := congrArg Prod.snd hpair
          simp only at hval hrest
          refine ⟨hle, ?_, hrest.symm, x, rfl, fun _ hzero => hx ?_⟩
          · rw [← hval, htakeEq]
          · exact BitVec.eq_of_toNat_eq (by rw [hzero]; rfl)
  · rw [readLength_none_of_takeBytes_none (takeBytes_length_lt (by omega))] at h
    simp at h

/-! ## The dispatcher

From a successful model decode of a **byte-string** item at `off`, the guest's
`rlpItemDecode` holds at the corresponding cursors.  The residue is pinned as
`bytes.drop off'`, so `off'` is the model's advanced offset. -/

theorem rlpItemDecode_of_decodeAux_bytes
    (bytes : List Byte) (base : Word) (off off' endOff n : Nat) (p : List Byte)
    (hdec : decodeAux (n + 1) (bytes.drop off) = some (.bytes p, bytes.drop off'))
    (hoff' : off' ≤ endOff) (hendOff : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64) :
    rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      (base + BitVec.ofNat 64 endOff) (base + BitVec.ofNat 64 off')
      (BitVec.ofNat 64 p.length) := by
  obtain ⟨b, hget, hdrop⟩ := exists_prefix_of_decodeAux hdec
  have hofflt : off < bytes.length := by
    rw [List.getElem?_eq_some_iff] at hget; exact hget.1
  rw [hdrop] at hdec
  cases hclass : classifyPrefix b with
  | singleByte =>
      have hsingle : b.toNat < 0x80 := (classifyPrefix_singleByte_iff b).mp hclass
      obtain ⟨hp, hrest⟩ :=
        (ByteStringDecodeBridge.decodeAux_cons_singleByte_eq_some_iff n b
          (bytes.drop (off + 1)) hclass p (bytes.drop off')).mp hdec
      have hoffeq : off' = off + 1 :=
        drop_inj_of_le (by omega) (by omega) hrest.symm
      subst hoffeq
      rw [← hp]
      simpa using rlpItemDecode_singleByte_forward bytes base off endOff b hget hsingle
        (by omega) hendOff hover
  | shortBytes =>
      obtain ⟨hlo, hhi⟩ := (classifyPrefix_shortBytes_iff b).mp hclass
      obtain ⟨payload, htake, hpay, hcanon⟩ :=
        (ByteStringDecodeBridge.decodeAux_cons_shortBytes_eq_some_iff n b
          (bytes.drop (off + 1)) hclass p (bytes.drop off')).mp hdec
      subst hpay
      obtain ⟨hcat, hplen⟩ := takeBytes_eq_some_imp htake
      have hlenDrop : (bytes.drop (off + 1)).length = bytes.length - (off + 1) :=
        List.length_drop ..
      have hfits : off + 1 + payload.length ≤ bytes.length := by
        have := congrArg List.length hcat
        rw [List.length_append] at this
        omega
      have hcontent : payload = (bytes.drop (off + 1)).take payload.length := by
        rw [hcat, List.take_left]
      have hrest : bytes.drop off' = bytes.drop (off + 1 + payload.length) := by
        have hdropEq : bytes.drop (off + 1 + payload.length)
            = (bytes.drop (off + 1)).drop payload.length := by
          rw [List.drop_drop]
        rw [hdropEq, hcat, List.drop_left]
      have hoffeq : off' = off + 1 + payload.length :=
        drop_inj_of_le (by omega) (by omega) hrest
      subst hoffeq
      refine rlpItemDecode_shortBytes_forward bytes base off endOff b payload hget hlo hhi
        (by rw [hplen]; rfl) hcontent (fun c hc => ?_) (by omega) hendOff hover
      rw [hc] at hcanon
      exact hcanon
  | longBytes =>
      obtain ⟨hlo, hhi⟩ := (classifyPrefix_longBytes_iff b).mp hclass
      obtain ⟨lenVal, restLen, hread, hlong, htake⟩ :=
        (ByteStringDecodeBridge.decodeAux_cons_longBytes_eq_some_iff n b
          (bytes.drop (off + 1)) hclass p (bytes.drop off')).mp hdec
      have hlolpos : 0 < b.toNat - 0xB7 := by omega
      have hlolEq : rlpPrefixLongBytesLenOfLen b = b.toNat - 0xB7 := rfl
      rw [hlolEq] at hread
      obtain ⟨hklen, hlenVal, hrestLen, c, hc0, hcnz⟩ := readLength_inv hlolpos hread
      obtain ⟨hcat, hplen⟩ := takeBytes_eq_some_imp htake
      have hlenDrop : (bytes.drop (off + 1)).length = bytes.length - (off + 1) :=
        List.length_drop ..
      -- the length-bytes window sits at `off+1`, the payload right after it
      have hrestLenEq : restLen = bytes.drop (off + 1 + (b.toNat - 0xB7)) := by
        rw [hrestLen, List.drop_drop]
      have hfits : off + 1 + (b.toNat - 0xB7) + p.length ≤ bytes.length := by
        have := congrArg List.length hcat
        rw [List.length_append, hrestLenEq, List.length_drop] at this
        omega
      have hrest : bytes.drop off'
          = bytes.drop (off + 1 + (b.toNat - 0xB7) + p.length) := by
        have hdropEq : bytes.drop (off + 1 + (b.toNat - 0xB7) + p.length)
            = restLen.drop p.length := by
          rw [hrestLenEq, List.drop_drop]
        rw [hdropEq, hcat, List.drop_left]
      have hoffeq : off' = off + 1 + (b.toNat - 0xB7) + p.length :=
        drop_inj_of_le (by omega) (by omega) hrest
      subst hoffeq
      refine rlpItemDecode_longBytes_forward bytes base off endOff (b.toNat - 0xB7) b p
        hget (by omega) hhi rfl ?_ (by omega) ⟨c, ?_, ?_⟩ (by omega) hendOff hover
      · rw [← hlenVal, hplen]
      · rw [← hc0, List.getElem?_drop]
      · rcases Nat.lt_or_ge 1 (b.toNat - 0xB7) with hk | hk
        · exact hcnz hk
        · -- a single length byte: canonicality is forced by `lenVal > 55`
          have hk1 : b.toNat - 0xB7 = 1 := by omega
          intro hzero
          have hsingleton : (bytes.drop (off + 1)).take (b.toNat - 0xB7) = [c] := by
            rw [hk1]
            cases hbs : bytes.drop (off + 1) with
            | nil => rw [hbs] at hc0; simp at hc0
            | cons x xs =>
                rw [hbs] at hc0
                have : x = c := by
                  rw [List.getElem?_eq_getElem (by simp)] at hc0
                  exact Option.some.inj hc0
                rw [this]
                rfl
          rw [hsingleton] at hlenVal
          have : lenVal = c.toNat := by rw [hlenVal]; simp [Nat.fromBytesBE]
          omega
  | shortList =>
      exfalso
      rw [decodeAux_cons_shortList_of_classifyPrefix n b (bytes.drop (off + 1)) hclass] at hdec
      cases htake : takeBytes (bytes.drop (off + 1)) (rlpPrefixShortListPayloadLen b) with
      | none => simp [htake] at hdec
      | some pr =>
          obtain ⟨payload, rest'⟩ := pr
          cases hitems : decodeItems n payload with
          | none => simp [htake, hitems] at hdec
          | some ir =>
              obtain ⟨items, leftover⟩ := ir
              simp [htake, hitems] at hdec
  | longList =>
      exfalso
      rw [decodeAux_cons_longList_of_classifyPrefix n b (bytes.drop (off + 1)) hclass] at hdec
      cases hread : readLength (bytes.drop (off + 1)) (rlpPrefixLongListLenOfLen b) with
      | none => simp [hread] at hdec
      | some pr =>
          obtain ⟨lenVal, rest'⟩ := pr
          by_cases hshort : lenVal ≤ 55
          · simp [hread, hshort] at hdec
          · cases htake : takeBytes rest' lenVal with
            | none => simp [hread, hshort, htake] at hdec
            | some pr2 =>
                obtain ⟨payload, rest''⟩ := pr2
                cases hitems : decodeItems n payload with
                | none => simp [hread, hshort, htake, hitems] at hdec
                | some ir =>
                    obtain ⟨items, leftover⟩ := ir
                    simp [hread, hshort, htake, hitems] at hdec

/-! ## Residue shape, offset advance, and fuel independence

Three facts the chain layer needs, all read off the same prefix case split, so
it is performed once here and shared.  (#11441 derived only the advance fact
and did its own split; this generalises that proof rather than adding a second
copy — `decodeAux_bytes_advance` is now a two-line corollary.)

* the residue is itself `bytes.drop off'` for a **derived** `off'` — needed to
  turn `decodeItems`' arbitrary residues into `DecodeChain`'s offset-indexed
  ones;
* the decode strictly advances — the termination fact for the chain induction;
* the decode is **fuel-independent**, i.e. holds at every `m + 1`.  None of the
  three byte-string branches recurses, so their branch equations are already
  fuel-free; `DecodeChain` demands exactly this `∀ m` form.

⚠️ `off'` is *concluded*, not assumed, and the only bound produced is
`off' ≤ bytes.length` — deliberately **not** the window bound `off' ≤ endOff`
that `rlpItemDecode_of_decodeAux_bytes` takes.  The window bound is what the
chain induction is trying to establish, so assuming it here would be circular. -/

theorem decodeAux_bytes_residue
    (bytes : List Byte) (off n : Nat) (p r : List Byte)
    (hdec : decodeAux (n + 1) (bytes.drop off) = some (.bytes p, r)) :
    ∃ off', r = bytes.drop off' ∧ off < off' ∧ off' ≤ bytes.length ∧
      ∀ m, decodeAux (m + 1) (bytes.drop off) = some (.bytes p, bytes.drop off') := by
  obtain ⟨b, hget, hdrop⟩ := exists_prefix_of_decodeAux hdec
  have hofflt : off < bytes.length := by
    rw [List.getElem?_eq_some_iff] at hget; exact hget.1
  rw [hdrop] at hdec
  cases hclass : classifyPrefix b with
  | singleByte =>
      obtain ⟨hp, hrest⟩ :=
        (ByteStringDecodeBridge.decodeAux_cons_singleByte_eq_some_iff n b
          (bytes.drop (off + 1)) hclass p r).mp hdec
      refine ⟨off + 1, hrest.symm, by omega, by omega, fun m => ?_⟩
      rw [hdrop, decodeAux_cons_singleByte_of_classifyPrefix m b _ hclass, hp]
  | shortBytes =>
      obtain ⟨payload, htake, hpay, _⟩ :=
        (ByteStringDecodeBridge.decodeAux_cons_shortBytes_eq_some_iff n b
          (bytes.drop (off + 1)) hclass p r).mp hdec
      subst hpay
      obtain ⟨hcat, _⟩ := takeBytes_eq_some_imp htake
      have hfits : off + 1 + payload.length ≤ bytes.length := by
        have := congrArg List.length hcat
        rw [List.length_append, List.length_drop] at this
        omega
      have hres : r = bytes.drop (off + 1 + payload.length) := by
        have hdropEq : bytes.drop (off + 1 + payload.length)
            = (bytes.drop (off + 1)).drop payload.length := by
          rw [List.drop_drop]
        rw [hdropEq, hcat, List.drop_left]
      refine ⟨off + 1 + payload.length, hres, by omega, by omega, fun m => ?_⟩
      rw [hdrop, decodeAux_cons_shortBytes_of_classifyPrefix m b _ hclass,
        ← decodeAux_cons_shortBytes_of_classifyPrefix n b _ hclass, hdec, hres]
  | longBytes =>
      obtain ⟨hlo, hhi⟩ := (classifyPrefix_longBytes_iff b).mp hclass
      obtain ⟨lenVal, restLen, hread, _, htake⟩ :=
        (ByteStringDecodeBridge.decodeAux_cons_longBytes_eq_some_iff n b
          (bytes.drop (off + 1)) hclass p r).mp hdec
      have hlolEq : rlpPrefixLongBytesLenOfLen b = b.toNat - 0xB7 := rfl
      rw [hlolEq] at hread
      obtain ⟨hklen, _, hrestLen, _⟩ := readLength_inv (by omega) hread
      obtain ⟨hcat, _⟩ := takeBytes_eq_some_imp htake
      have hrestLenEq : restLen = bytes.drop (off + 1 + (b.toNat - 0xB7)) := by
        rw [hrestLen, List.drop_drop]
      have hfits : off + 1 + (b.toNat - 0xB7) + p.length ≤ bytes.length := by
        have := congrArg List.length hcat
        rw [List.length_append, hrestLenEq, List.length_drop] at this
        rw [List.length_drop] at hklen
        omega
      have hres : r = bytes.drop (off + 1 + (b.toNat - 0xB7) + p.length) := by
        have hdropEq : bytes.drop (off + 1 + (b.toNat - 0xB7) + p.length)
            = restLen.drop p.length := by
          rw [hrestLenEq, List.drop_drop]
        rw [hdropEq, hcat, List.drop_left]
      refine ⟨off + 1 + (b.toNat - 0xB7) + p.length, hres, by omega, by omega, fun m => ?_⟩
      rw [hdrop, decodeAux_cons_longBytes_of_classifyPrefix m b _ hclass,
        ← decodeAux_cons_longBytes_of_classifyPrefix n b _ hclass, hdec, hres]
  | shortList =>
      exfalso
      rw [decodeAux_cons_shortList_of_classifyPrefix n b (bytes.drop (off + 1)) hclass] at hdec
      cases htake : takeBytes (bytes.drop (off + 1)) (rlpPrefixShortListPayloadLen b) with
      | none => simp [htake] at hdec
      | some pr =>
          obtain ⟨payload, rest'⟩ := pr
          cases hitems : decodeItems n payload with
          | none => simp [htake, hitems] at hdec
          | some ir =>
              obtain ⟨items, leftover⟩ := ir
              simp [htake, hitems] at hdec
  | longList =>
      exfalso
      rw [decodeAux_cons_longList_of_classifyPrefix n b (bytes.drop (off + 1)) hclass] at hdec
      cases hread : readLength (bytes.drop (off + 1)) (rlpPrefixLongListLenOfLen b) with
      | none => simp [hread] at hdec
      | some pr =>
          obtain ⟨lenVal, rest'⟩ := pr
          by_cases hshort : lenVal ≤ 55
          · simp [hread, hshort] at hdec
          · cases htake : takeBytes rest' lenVal with
            | none => simp [hread, hshort, htake] at hdec
            | some pr2 =>
                obtain ⟨payload, rest''⟩ := pr2
                cases hitems : decodeItems n payload with
                | none => simp [hread, hshort, htake, hitems] at hdec
                | some ir =>
                    obtain ⟨items, leftover⟩ := ir
                    simp [hread, hshort, htake, hitems] at hdec

/-- Specialisation of `decodeAux_bytes_residue` to a residue already in offset
    form: the decode strictly advances. -/
theorem decodeAux_bytes_advance
    (bytes : List Byte) (off off' n : Nat) (p : List Byte)
    (hdec : decodeAux (n + 1) (bytes.drop off) = some (.bytes p, bytes.drop off'))
    (hoff'len : off' ≤ bytes.length) :
    off < off' := by
  obtain ⟨off'', hres, hlt, hle, _⟩ := decodeAux_bytes_residue bytes off n p _ hdec
  have : off' = off'' := drop_inj_of_le hoff'len hle hres
  omega

/-- A byte-string `DecodeChain` never runs past its own end offset.  Proved by
    induction on the item list: the tail bounds `off'`, and `decodeAux_bytes_advance`
    then bounds `off` below it. -/
theorem DecodeChain.le_of_bytes {bytes : List Byte} :
    ∀ (items : List RLPItem) (off offEnd : Nat),
      DecodeChain bytes off items offEnd → offEnd ≤ bytes.length →
      (∀ it ∈ items, ∃ q, it = RLPItem.bytes q) →
      off ≤ offEnd := by
  intro items
  induction items with
  | nil => intro off offEnd hchain _ _; exact le_of_eq hchain
  | cons item rest ih =>
      intro off offEnd hchain hend hbytes
      obtain ⟨off', hdec, hrest⟩ := hchain
      have hrestle : off' ≤ offEnd :=
        ih off' offEnd hrest hend (fun it hit => hbytes it (List.mem_cons_of_mem _ hit))
      obtain ⟨q, hq⟩ := hbytes item (List.mem_cons_self ..)
      subst hq
      have := decodeAux_bytes_advance bytes off off' 0 q (hdec 0) (by omega)
      omega

/-- Converse of `decodeItems_of_chain` (#11425): a model-side `decodeItems` that
    consumes its whole input yields the offset-indexed `DecodeChain`.  This is
    what turns `decodeFully`'s list payload into something the guest-side walk
    composition can consume. -/
theorem decodeItems_to_chain (bytes : List Byte) :
    ∀ (items : List RLPItem) (n off : Nat),
      decodeItems n (bytes.drop off) = some (items, []) →
      off ≤ bytes.length →
      (∀ it ∈ items, ∃ q, it = RLPItem.bytes q) →
      DecodeChain bytes off items bytes.length := by
  intro items
  induction items with
  | nil =>
      intro n off hdec hoff _
      have hnil : bytes.drop off = [] := by
        cases hbs : bytes.drop off with
        | nil => rfl
        | cons x xs =>
            exfalso
            rw [hbs] at hdec
            cases n with
            | zero => simp [decodeItems] at hdec
            | succ n' =>
                rw [decodeItems_succ_of_ne_nil n' _ (by simp)] at hdec
                rcases hd : decodeAux n' (x :: xs) with _ | ⟨i, r⟩
                · simp [hd] at hdec
                · simp only [hd, Option.bind_eq_bind, Option.bind_some] at hdec
                  rcases hr : decodeItems n' r with _ | ⟨is, r''⟩
                  · simp [hr] at hdec
                  · simp [hr] at hdec
      have hlen := congrArg List.length hnil
      rw [List.length_drop] at hlen
      simp only [List.length_nil] at hlen
      show off = bytes.length
      omega
  | cons item rest ih =>
      intro n off hdec hoff hbytes
      obtain ⟨q, hq⟩ := hbytes item (List.mem_cons_self ..)
      subst hq
      -- the input cannot be empty, so the fuel must be positive twice over
      cases hbs : bytes.drop off with
      | nil => rw [hbs] at hdec; simp [decodeItems] at hdec
      | cons x xs =>
          rw [hbs] at hdec
          cases n with
          | zero => simp [decodeItems] at hdec
          | succ n' =>
              obtain ⟨r, haux, hits⟩ :=
                decodeItems_cons_inv (x :: xs) _ rest [] n' (by simp) hdec
              cases n' with
              | zero => simp [decodeAux] at haux
              | succ n'' =>
                  rw [← hbs] at haux
                  obtain ⟨off', hres, hlt, hle, hall⟩ :=
                    decodeAux_bytes_residue bytes off n'' q r haux
                  refine ⟨off', hall, ?_⟩
                  refine ih (n'' + 1) off' ?_ hle
                    (fun it hit => hbytes it (List.mem_cons_of_mem _ hit))
                  rw [← hres]
                  exact hits

/-! ## Non-vacuity

Both checks instantiate the dispatcher on a concrete buffer, so the hypothesis
set is demonstrably satisfiable rather than merely consistent. -/

set_option maxRecDepth 8000 in
/-- A short string `0x83 01 02 03` decodes to a three-byte payload, and the
    guest relation holds with the cursor advanced by the full four-byte span. -/
example :
    rlpItemDecode [0x83, 0x01, 0x02, 0x03] 0
      ((0x1000 : Word) + BitVec.ofNat 64 0) ((0x1000 : Word) + BitVec.ofNat 64 4)
      ((0x1000 : Word) + BitVec.ofNat 64 4) (BitVec.ofNat 64 3) :=
  rlpItemDecode_of_decodeAux_bytes [0x83, 0x01, 0x02, 0x03] (0x1000 : Word) 0 4 4 8
    [0x01, 0x02, 0x03] rfl (by norm_num) (by norm_num) (by decide)

set_option maxRecDepth 8000 in
/-- A bare single byte `0x07` decodes to itself with a one-byte span. -/
example :
    rlpItemDecode [0x07] 0
      ((0x1000 : Word) + BitVec.ofNat 64 0) ((0x1000 : Word) + BitVec.ofNat 64 1)
      ((0x1000 : Word) + BitVec.ofNat 64 1) (BitVec.ofNat 64 1) :=
  rlpItemDecode_of_decodeAux_bytes [0x07] (0x1000 : Word) 0 1 1 8
    [0x07] rfl (by norm_num) (by norm_num) (by decide)

end EvmAsm.Rv64.RLP
