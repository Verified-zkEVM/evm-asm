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

/-! ## §4  Non-vacuity checks on the model layer

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
