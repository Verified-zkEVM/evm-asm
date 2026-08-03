/-
  EvmAsm.Codegen.Programs.RlpEncodeBytesSAsm

  **Semantic specs for `rlp_encode_bytes`** (#10780 item 2) — the pure model
  layer, the guest layout, and the shared loop lemma.  The block theorems and
  the whole-routine composition follow in this module and its `…ComposeSAsm`
  sibling; `RlpRead.lean` holds only the string↔`Program` drift guard, which is
  why a per-file theorem count of *that* module reads as "unspecified".

  ## What the routine is, and why both sides of 55/56 matter

  `rlp_encode_bytes` is the generic RLP encoder for a raw byte string — the
  counterpart of `rlp_encode_uint_be`, which handles the *scalar* shape and
  strips leading zeros.  This one strips nothing and has the single-byte
  no-prefix short-cut.

  A spec that pinned only the short form would be worth little.  The **long
  form is the silent-failure case**: a long-form header carrying a
  non-canonical (leading-zero) length-of-length still parses, and still hashes
  differently from the reference.  So the length-of-length's canonicity is an
  explicit consequence here (§2's bridge), not an implementation detail.

  ## ABI (LP64)

  * `a0` — data pointer
  * `a1` — data byte length
  * `a2` — output pointer; caller must have `9 + len` bytes
  * `a3` — `u64` out pointer, receives the number of bytes written
  * `a0` on return — **always `0`**.  A total function: there is no failure
    path to specify, and no status code to case on.

  Two output locations, unlike `rlp_encode_uint_be`, which returned its length
  in `a0`.  The dword at `a3` is asserted with `↦ₘ`, following
  `RlpSpliceHelperSpec.lean`'s u64-out-param shape.

  ## Instruction map (76, three exits, all to `ra &&& ~~~1`)

  ```
  [0]-[4]    prologue; BNE x6,x28 -> [13]        (len ≠ 1)
  [5]-[7]    single-byte probe; BGEU -> [13]     (byte ≥ 0x80)
  [8]-[12]   raw-byte tail                            EXIT A
  [13]-[14]  short/long dispatch; BGEU -> [30]   (len ≥ 56)
  [15]-[18]  short header 0x80 + len
  [19]-[25]  payload copy loop                   7*len + 1
  [26]-[29]  short tail                               EXIT B
  [30]-[51]  bc ladder, seven BLTUs, all -> [52]
  [52]-[54]  long header 0xb7 + bc
  [55]-[62]  length-of-length loop                7*bc + 1
  [63]-[70]  payload copy loop                   7*len + 1
  [71]-[75]  long tail                                EXIT C
  ```

  `len = 0` needs no special case: it takes the short path, where the header
  is `0x80 + 0` and the copy loop runs zero times — exactly `encodeBytes []`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.RLP.ContentToU256Be
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Evm64.CallingConvention
import EvmAsm.EL.RLP.Properties
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpListEncodedSizeSAsm
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

namespace RlpEncodeBytesSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
-- `copyN` and the counter/pointer word lemmas are the verified core's, not
-- re-derived: both payload copy loops are the same six instructions as
-- `cu256_loop_spec_within`'s, register-renamed.
open EvmAsm.Rv64.RLP (copyN copyN_zero copyN_succ copyN_length copyN_eq_append
  word_ofNat_succ_dec word_ofNat_succ_ne_zero word_ofNat_add_one)
-- The byte-length model and its shift bridges are `rlp_bytes_encoded_size`'s,
-- reused as-is rather than restated (#10082 / #6agnq).
open EvmAsm.Codegen.RlpListEncodedSizeSAsm (u64ByteLen u64ByteLen_le
  u64ByteLen_shift_zero u64ByteLen_shift_ne)

/-! ## §1  Guest layout

    Stated at the `#guard`-tied symbolic `GuestAddrs.rlp_encode_bytes` base, the
    same convention as `reubBase` — so the spec is about the linked routine and
    not about a floating `∀ base` copy. -/

/-- Guest entry of `rlp_encode_bytes`. -/
def rebBase : Word := BitVec.ofNat 64 GuestAddrs.rlp_encode_bytes

/-- The `rlp_encode_bytes` body at its linked guest address. -/
abbrev rebCode : CodeReq := CodeReq.ofProg rebBase rlpEncodeBytes_prog

theorem reb_prog_length : rlpEncodeBytes_prog.length = 76 := by decide

/-- Code-membership for instruction `k`, addressed as `rebBase + OFF`. -/
local macro "rebmem" k:term:max : tactic =>
  `(tactic| exact CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr rebBase rlpEncodeBytes_prog $k _
        (by rw [reb_prog_length]; norm_num)
        (by rw [reb_prog_length]; norm_num) (by rfl)))

/-! ## §2  The length-of-length bridge

    **This is the linchpin of the long form.**  The machine computes its
    length-of-length byte count `bc` with the ladder at [30]-[51], which lands
    on `u64ByteLen`; the model states the long form over
    `(Nat.toBytesBE len).length` (`encodeBytes_long_of_length`).  Nothing in the
    tree connected those two, so without this lemma the machine half and the
    model half cannot meet.

    ⭐ It is also where **canonicity** comes from, and therefore where the
    maintainer's "pin both sides" requirement is discharged: because `bc` is
    *equal to* the minimal encoding's length rather than merely large enough,
    `Nat.toBytesBE_eq_cons_of_pos` gives a nonzero leading byte for free.  No
    no-leading-zero side condition has to be assumed — a long-form header with a
    padded length would make this equation false. -/

/-- The minimal big-endian encoding's own length always suffices to bound the
    value — the companion of `Nat.toBytesBE_length_le`, by the same division
    induction.  `length_le` bounds the length by a given width; this bounds the
    value by the length, which is the direction the squeeze below needs. -/
theorem toBytesBE_lt_pow : ∀ n : Nat, n < 256 ^ (Nat.toBytesBE n).length := by
  intro n
  induction n using Nat.toBytesBE.induct with
  | case1 => simp [Nat.toBytesBE]
  | case2 m _hlt ih =>
    rw [Nat.toBytesBE_succ, List.length_append, List.length_cons, List.length_nil]
    have hdiv : (m + 1) / 256 < 256 ^ (Nat.toBytesBE ((m + 1) / 256)).length := ih
    have hmod : (m + 1) % 256 < 256 := Nat.mod_lt _ (by omega)
    have hsplit : m + 1 = 256 * ((m + 1) / 256) + (m + 1) % 256 :=
      (Nat.div_add_mod (m + 1) 256).symm ▸ by omega
    rw [Nat.pow_succ]
    omega

/-- A nonvanishing right shift means the value reaches that power of two.  The
    public form of what `u64ByteLen_shift_ne` is really saying; the sibling
    module's `shift_zero_iff` is `private`. -/
theorem pow_le_of_shift_ne (v : Word) (s : Nat) (h : v >>> s ≠ (0 : Word)) :
    2 ^ s ≤ v.toNat := by
  by_contra hc
  apply h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, show (0 : Word).toNat = 0 from by decide,
      Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (by omega)

/-- **The bridge.**  The ladder's `bc` is exactly the model's
    length-of-length. -/
theorem u64ByteLen_eq_toBytesBE_length (v : Word) :
    u64ByteLen v = (Nat.toBytesBE v.toNat).length := by
  have hpow : ∀ k : Nat, (256 : Nat) ^ k = 2 ^ (8 * k) := by
    intro k
    rw [show (256 : Nat) = 2 ^ 8 from by norm_num, ← Nat.pow_mul]
  have hlt := v.isLt
  -- `≤`: the ladder's own upper bound feeds `Nat.toBytesBE_length_le`.
  have h1 : (Nat.toBytesBE v.toNat).length ≤ u64ByteLen v := by
    refine Nat.toBytesBE_length_le v.toNat (u64ByteLen v) ?_
    rw [hpow]
    unfold u64ByteLen
    split_ifs <;> (simp only [Nat.reduceMul]; omega)
  -- `≥`: `toBytesBE_lt_pow` bounds the value by its own length, and powers of
  -- two are strictly monotone, so a lower bound on the value transfers.
  have hlo : v.toNat < 2 ^ (8 * (Nat.toBytesBE v.toNat).length) := by
    have h := toBytesBE_lt_pow v.toNat
    rwa [hpow] at h
  have key : ∀ j : Nat, 2 ^ (8 * j) ≤ v.toNat → j < (Nat.toBytesBE v.toNat).length := by
    intro j hj
    have hmono : (2 : Nat) ^ (8 * j) < 2 ^ (8 * (Nat.toBytesBE v.toNat).length) :=
      Nat.lt_of_le_of_lt hj hlo
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hmono
    omega
  have h2 : u64ByteLen v ≤ (Nat.toBytesBE v.toNat).length := by
    unfold u64ByteLen
    split_ifs
    · omega
    · exact key 0 (by simp only [Nat.reduceMul]; omega)
    · exact key 1 (by simp only [Nat.reduceMul]; omega)
    · exact key 2 (by simp only [Nat.reduceMul]; omega)
    · exact key 3 (by simp only [Nat.reduceMul]; omega)
    · exact key 4 (by simp only [Nat.reduceMul]; omega)
    · exact key 5 (by simp only [Nat.reduceMul]; omega)
    · exact key 6 (by simp only [Nat.reduceMul]; omega)
    · exact key 7 (by simp only [Nat.reduceMul]; omega)
  omega

/-- The length-of-length is in `[1, 8]` for any long-form payload, which is the
    decoder's accepted range.  `u64ByteLen_le` gives the upper bound; the lower
    needs only that a `≥ 56` length is positive. -/
theorem toBytesBE_length_mem_range (v : Word) (h : 56 ≤ v.toNat) :
    1 ≤ (Nat.toBytesBE v.toNat).length ∧ (Nat.toBytesBE v.toNat).length ≤ 8 := by
  rw [← u64ByteLen_eq_toBytesBE_length]
  refine ⟨?_, u64ByteLen_le v⟩
  unfold u64ByteLen
  split_ifs <;> omega

/-- **Canonicity, as a consequence rather than an assumption.**  The header
    the machine writes records the *minimal* encoding's length, so the
    length-of-length it then emits has a nonzero leading byte.  A padded
    length-of-length would falsify `u64ByteLen_eq_toBytesBE_length`. -/
theorem toBytesBE_no_leading_zero (v : Word) (h : 56 ≤ v.toNat) :
    ∃ b tl, Nat.toBytesBE v.toNat = b :: tl ∧ b ≠ (0 : Byte) :=
  Nat.toBytesBE_eq_cons_of_pos v.toNat (by omega)

/-! ## §3  The short-form model target

    `encodeBytes_nil`, `encodeBytes_single_large` and
    `encodeBytes_short_of_length_ne_one` are the *same* statement on the machine
    path that runs: `0x80 + 0 = 0x80` and `0x80 + 1 = 0x81`.  Unifying them here
    keeps the composition free of a sub-case on the byte value above the
    dispatch that actually branches on it — the trick that made
    `rlp_encode_uint_be`'s header path one chain instead of two. -/

/-- **The short path's model, all three degenerate cases folded in.**  The
    hypothesis is exactly the machine's dispatch: anything that is not "one byte
    below `0x80`" and is shorter than 56 bytes takes the `0x80 + len` header. -/
theorem rebOut_short_form (data : List Byte) (hhi : data.length < 56)
    (hnot_raw : ∀ b, data = [b] → ¬ b.toNat < 0x80) :
    encodeBytes data = BitVec.ofNat 8 (0x80 + data.length) :: data := by
  by_cases h1 : data.length = 1
  · obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 h1
    rw [hb, encodeBytes_single_large b (hnot_raw b hb)]
    rfl
  · -- `encodeBytes_short_of_length_ne_one` already covers `data = []`, so the
    -- `0x80 + 0` degenerate case needs no branch of its own.
    rw [encodeBytes_short_of_length_ne_one data (by omega) h1]
    rfl

/-- The single-byte short-cut's model: below `0x80` a one-byte string is its own
    encoding, with no prefix. -/
theorem rebOut_raw_byte (data : List Byte) (b : Byte) (hb : data = [b])
    (hsmall : b.toNat < 0x80) : encodeBytes data = [b] := by
  rw [hb, encodeBytes_single_small b hsmall]

/-- Written length in the short and raw paths. -/
theorem rebOut_short_length (data : List Byte) (hhi : data.length < 56)
    (hnot_raw : ∀ b, data = [b] → ¬ b.toNat < 0x80) :
    (encodeBytes data).length = data.length + 1 := by
  rw [rebOut_short_form data hhi hnot_raw, List.length_cons]

/-! ## §4  The length-of-length loop's contents

    `u64ByteLen_eq_toBytesBE_length` (§2) gives the length-of-length's *count*.
    That is not enough for the long form: the spec also has to say *which bytes*
    the loop at [55]-[62] writes.  Two separate facts, and the plan for this
    routine initially conflated them.

    The loop stores, for `i = bc-1` down to `0`, the byte `(len >>> 8i) & 0xff`.
    ⭐ Defining that sequence by peeling the **least** significant byte makes it
    structurally identical to `Nat.toBytesBE`'s own division recursion, which
    collapses the bridge to a four-line induction.  An earlier attempt stated it
    as an indexed `List.range … |>.reverse.map` and needed a `List.ext_getElem`
    argument plus tail-peeling of `range` — same theorem, much worse proof. -/

/-- The byte sequence the length-of-length loop emits: `k` bytes of `v`, most
    significant first.  Defined by peeling the *least* significant byte, which is
    the recursion `Nat.toBytesBE` itself uses — that alignment is what makes the
    bridge below a short induction rather than an indexed argument. -/
def beShift (v : Nat) : Nat → List Byte
  | 0 => []
  | k + 1 => beShift (v / 256) k ++ [BitVec.ofNat 8 (v % 256)]

theorem beShift_length : ∀ (k v : Nat), (beShift v k).length = k := by
  intro k
  induction k with
  | zero => intro v; rfl
  | succ k ih =>
    intro v
    rw [beShift, List.length_append, ih, List.length_cons, List.length_nil]

/-- **At its own length, `beShift` IS the minimal big-endian encoding.** -/
theorem beShift_eq_toBytesBE : ∀ n : Nat,
    beShift n (Nat.toBytesBE n).length = Nat.toBytesBE n := by
  intro n
  induction n using Nat.toBytesBE.induct with
  | case1 => simp [Nat.toBytesBE, beShift]
  | case2 m _hlt ih =>
    rw [Nat.toBytesBE_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.add_zero, beShift, ih]

/-- Element `j` is `v` shifted right by `k-1-j` bytes — the form the machine loop
    needs, since at iteration `i` it stores `(len >>> 8i) & 0xff`, which lands at
    index `k-1-i`.  Stated with `getElem?` rather than `getElem`: the dependent
    index proof blocks `rw` on `beShift` itself. -/
theorem beShift_getElem? : ∀ (k v j : Nat), j < k →
    (beShift v k)[j]? = some (BitVec.ofNat 8 (v / 256 ^ (k - 1 - j) % 256)) := by
  intro k
  induction k with
  | zero => intro v j hj; omega
  | succ k ih =>
    intro v j hj
    have hlenA : (beShift (v / 256) k).length = k := beShift_length k _
    show ((beShift (v / 256) k ++ [BitVec.ofNat 8 (v % 256)])[j]?) = _
    by_cases hjk : j < k
    · rw [List.getElem?_append_left (by rw [hlenA]; exact hjk), ih (v / 256) j hjk]
      -- one shift of the *value* is one more byte of the *exponent*
      have hd : (v / 256) / 256 ^ (k - 1 - j) = v / 256 ^ (k + 1 - 1 - j) := by
        rw [Nat.div_div_eq_div_mul]
        congr 1
        rw [show k + 1 - 1 - j = (k - 1 - j) + 1 from by omega, Nat.pow_succ]
        ring
      rw [hd]
    · have hje : j = k := by omega
      subst hje
      rw [List.getElem?_append_right (by rw [hlenA]), hlenA, Nat.sub_self]
      simp

-- non-vacuity: the bridge is an equation between things that actually compute
#guard beShift 56 1 == [0x38]
#guard beShift 65536 3 == [0x01, 0x00, 0x00]
#guard beShift 65536 3 == Nat.toBytesBE 65536
#guard beShift 255 1 == Nat.toBytesBE 255
#guard beShift 256 2 == Nat.toBytesBE 256
#guard (beShift 65536 3)[1]? == some 0x00
#guard (beShift 65536 3)[0]? == some 0x01
#guard beShift 0 0 == Nat.toBytesBE 0

-- non-vacuity: the bridge relates things that actually compute
#guard beShift 56 1 == [0x38]
#guard beShift 65536 3 == [0x01, 0x00, 0x00]
#guard beShift 65536 3 == Nat.toBytesBE 65536
#guard beShift 255 1 == Nat.toBytesBE 255
#guard beShift 256 2 == Nat.toBytesBE 256
#guard beShift 0 0 == Nat.toBytesBE 0

/-- `beShift`'s **most-significant-first** view.  The definition peels the least
    significant byte, which is what aligns it with `Nat.toBytesBE`; the machine
    loop writes in the opposite order, so it needs the head instead. -/
theorem beShift_cons : ∀ (m v : Nat),
    beShift v (m + 1) = BitVec.ofNat 8 (v / 256 ^ m % 256) :: beShift v m := by
  intro m
  induction m with
  | zero => intro v; simp [beShift]
  | succ m ih =>
    intro v
    show beShift (v / 256) (m + 1) ++ _ = _
    have hd : (v / 256) / 256 ^ m = v / 256 ^ (m + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      congr 1
      ring
    rw [ih (v / 256), List.cons_append, hd]
    rfl

/-- The region update the length-of-length loop performs: `m` bytes of `v`,
    most significant first, starting at index `di`.  Mirrors `copyN`'s
    repeated-`List.set` shape so the same append lemma is available. -/
def writeShift (dst : List Byte) (di v : Nat) : Nat → List Byte
  | 0 => dst
  | m + 1 => writeShift (dst.set di (BitVec.ofNat 8 (v / 256 ^ m % 256))) (di + 1) v m

theorem writeShift_length (dst : List Byte) (di v m : Nat) :
    (writeShift dst di v m).length = dst.length := by
  induction m generalizing dst di with
  | zero => rfl
  | succ m ih => rw [writeShift, ih, List.length_set]

/-- The analogue of `copyN_eq_append`: the write overwrites exactly the window
    `[di, di + m)` with `beShift v m`. -/
theorem writeShift_eq_append : ∀ (m : Nat) (dst : List Byte) (di v : Nat),
    di + m ≤ dst.length →
    writeShift dst di v m = dst.take di ++ (beShift v m ++ dst.drop (di + m)) := by
  intro m
  induction m with
  | zero => intro dst di v _; simp [writeShift, beShift]
  | succ m ih =>
    intro dst di v h
    have hdi : di < dst.length := by omega
    rw [writeShift,
      ih (dst.set di (BitVec.ofNat 8 (v / 256 ^ m % 256))) (di + 1) v
        (by rw [List.length_set]; omega),
      beShift_cons m v]
    have hlt : (dst.take di).length = di := by rw [List.length_take]; omega
    rw [List.set_eq_take_cons_drop _ hdi]
    have hT1 : (dst.take di ++ BitVec.ofNat 8 (v / 256 ^ m % 256) :: dst.drop (di + 1)).take (di + 1)
        = dst.take di ++ [BitVec.ofNat 8 (v / 256 ^ m % 256)] := by
      rw [List.take_append, hlt, List.take_of_length_le (by rw [hlt]; omega),
        show di + 1 - di = 1 from by omega, List.take_succ_cons, List.take_zero]
    have hT3 : (dst.take di ++ BitVec.ofNat 8 (v / 256 ^ m % 256) :: dst.drop (di + 1)).drop (di + 1 + m)
        = dst.drop (di + 1 + m) := by
      rw [List.drop_append, hlt, List.drop_eq_nil_of_le (by rw [hlt]; omega),
        show di + 1 + m - di = m + 1 from by omega, List.drop_succ_cons,
        List.drop_drop, List.nil_append,
        show di + 1 + m = m + (di + 1) from by omega]
    rw [hT1, hT3, show di + (m + 1) = di + 1 + m from by omega]
    simp [List.append_assoc]

-- the region update: 3 bytes of 65536 written at index 1, the rest untouched
#guard writeShift [0,0,0,0,0] 1 65536 3 == [0, 1, 0, 0, 0]
#guard writeShift [9,9,9,9] 0 56 1 == [0x38, 9, 9, 9]

/-! ## §5  Machine-side bridges for the length-of-length loop

    Three small facts the loop at [55]-[62] needs, kept here with the rest of the
    model layer so the loop proof itself is pure plumbing. -/

/-- The byte the loop actually stores at iteration `i`, in the model's form.
    `SB` truncates to 8 bits, and `256 ^ i = 2 ^ (8*i)`. -/
theorem truncate_shift_eq (v : Word) (i : Nat) :
    (v >>> (8 * i)).truncate 8 = BitVec.ofNat 8 (v.toNat / 256 ^ i % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow,
      show (256 : Nat) ^ i = 2 ^ (8 * i) from by
        rw [show (256 : Nat) = 2 ^ 8 from by norm_num, ← Nat.pow_mul]]
  omega

/-- The loop's guard is **signed** (`BLT`), and the counter runs down to `-1`.
    At `-1` the branch fires. -/
theorem slt_neg_one : BitVec.slt (-1 : Word) (0 : Word) = true := by decide

/-- ...and does not fire while the counter is a small non-negative value.  The
    counter never exceeds `bc - 1 ≤ 7`. -/
theorem slt_small_false (i : Nat) (h : i < 8) :
    BitVec.slt (BitVec.ofNat 64 i) (0 : Word) = false := by
  -- `i ≤ 7` is the truth of the situation: the counter starts at `bc - 1` and
  -- `bc ≤ 8`.  Stating the tight bound and discharging the eight concrete values
  -- beats asserting `i < 2 ^ 63`, which `omega`/`bv_omega` cannot reach anyway
  -- (`slt` normalises through `Int.bmod`, which they treat opaquely).
  interval_cases i <;> decide

/-- Counter bookkeeping: `ofNat (m+1) - 1 = ofNat m`, so the invariant's
    `ofNat m - 1` form steps cleanly.

    **Unconditional** — `mod 2 ^ 64` absorbs the reduction, so no `m + 1 < 2 ^ 64`
    side condition is needed.  Same as `word_128_add` in `rlp_encode_uint_be`:
    keeping a range bound here would misplace a domain restriction as an
    arithmetic fact. -/
theorem ofNat_succ_sub_one (m : Nat) :
    BitVec.ofNat 64 (m + 1) - 1 = BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (1 : Word).toNat = 1 from by decide]
  omega

/-! ## §6  Non-vacuity checks on the model layer

    The lemmas above are conditional equations; these pin them at concrete data
    so a later edit cannot make them true by making them unreachable.  The
    boundary pair is the point of this module: `55` takes the short header
    `0x80 + 55 = 0xb7`, and `56` takes the long header `0xb7 + 1 = 0xb8`
    followed by the one-byte length `0x38`.  **`0xb7` is both the largest short
    header and the base of the long-form header** — the two forms meet exactly
    there, which is why pinning one side would say so little. -/

-- the four short-path shapes
#guard encodeBytes [] == [0x80]
#guard encodeBytes [0x2a] == [0x2a]
#guard encodeBytes [0x81] == [0x81, 0x81]
#guard encodeBytes [0x01, 0x02] == [0x82, 0x01, 0x02]
-- the boundary, both sides
#guard (encodeBytes (List.replicate 55 (0x11 : Byte))).take 1 == [0xb7]
#guard (encodeBytes (List.replicate 55 (0x11 : Byte))).length == 56
#guard (encodeBytes (List.replicate 56 (0x11 : Byte))).take 2 == [0xb8, 0x38]
#guard (encodeBytes (List.replicate 56 (0x11 : Byte))).length == 58
-- the bridge at the boundary and at each ladder step it can reach
#guard u64ByteLen (BitVec.ofNat 64 55) == (Nat.toBytesBE 55).length
#guard u64ByteLen (BitVec.ofNat 64 56) == (Nat.toBytesBE 56).length
#guard u64ByteLen (BitVec.ofNat 64 255) == (Nat.toBytesBE 255).length
#guard u64ByteLen (BitVec.ofNat 64 256) == (Nat.toBytesBE 256).length
#guard u64ByteLen (BitVec.ofNat 64 65536) == (Nat.toBytesBE 65536).length
-- ...and that it is not the constant function: the ladder really does step
#guard u64ByteLen (BitVec.ofNat 64 255) == 1
#guard u64ByteLen (BitVec.ofNat 64 256) == 2
#guard u64ByteLen (BitVec.ofNat 64 65536) == 3
-- canonicity: the length-of-length the long form emits leads with a nonzero byte
#guard Nat.toBytesBE 65536 == [0x01, 0x00, 0x00]
#guard (Nat.toBytesBE 65536).head? == some 0x01

end RlpEncodeBytesSAsm

end EvmAsm.Codegen
