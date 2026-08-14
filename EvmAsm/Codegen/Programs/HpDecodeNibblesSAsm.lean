/-
  Verified byte-transparent port of `hp_decode_nibbles` (bead
  evm-asm-4ch8f.16.3, unblocking .16.3.1's two capability gaps with the
  landed `AbiFrame` (PR #9982) and `UpLoop` (this PR) machinery).

  The routine (`EvmAsm/Codegen/Programs/Mpt.lean`, PR-K23) decodes the
  hex-prefix compact path of a leaf/extension MPT node into one-nibble
  bytes, writing the nibble count and the is-leaf flag to caller cells:

    a0 src ptr, a1 len, a2 nibble buf, a3 count cell, a4 is_leaf cell
    → a0 = 0 success / 1 parse failure.

  Shape: a C-ABI saved-register frame (`abiFrameProg`, byte-transparent —
  no re-emit), a validation prefix whose failure branches jump straight to
  a shared `li a0,1` fail tail, an odd/even parity split, and an
  up-counting nibble loop (`bgeu i, len` top guard — `upLoop_spec`).

  The genuine post is stated against `hdnRes`, the guest-exact decode
  mirror, which (post bead evm-asm-3umhl) IS `EvmAsm.Evm64.hpDecode`
  (`MptAssertions.lean`), so `hdnRes_eq_hpDecode` is a total definitional
  agreement and `hdnRes_hpEncode` the round-trip on every hex-prefix
  encoding.

  ## What that agreement is NOT (GH #10528)

  `hpDecode` is a **guest mirror**, not the SpecRef port. The proved chain
  is `guest -> hdnRes -> hpDecode`; the further link
  `hpDecode -> SpecRef.compact_to_nibbles` is **still not stated as a
  theorem**, but as of GH #10528 it is no longer FALSE. `hpDecode` used to
  reject a head nibble `>= 4` while `compact_to_nibbles`
  (`SpecRef/IncrementalMpt.lean:76-86`, mirroring
  `amsterdam/incremental_mpt.py:878-889`) masks bits 2-3 away and accepts,
  making the guest STRICTER than the spec -- a false-reject shape. Both
  sides now mask: `hpDecode` matches on `(b0.toNat / 16) % 4`, and
  `compact_to_nibbles` reads only `first_nibble &&& 0x02` (is-leaf) and
  `&&& 0x01` (odd), so bits 2-3 are dead on both sides. The head-nibble
  divergence is GONE rather than pinned; the `#guard`s below now record
  the masked results (`hdnRes [0x4a] = some (false, [])`, and so on
  through `0xfa`).

  What `evm-asm-3umhl` relaxed was the EVEN-PATH PADDING NIBBLE; #10528
  relaxed the head nibble. Both divergences are now closed, and what
  remains owed is the THEOREM linking `hpDecode` to `compact_to_nibbles`
  -- the behaviour agrees, the proof does not exist yet.
-/

import EvmAsm.Codegen.Programs.BytesToNibblesSAsm
import EvmAsm.Evm64.MptAssertions
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.UpLoop
import EvmAsm.Rv64.MemRegionStore

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace HpDecodeNibblesSAsm

open BytesToNibblesSAsm (highNibble lowNibble nibblePair nibblePrefix
  length_nibblePrefix)

/-! ## The byte-transparent frame split -/

/-- The saved-register frame `hp_decode_nibbles` allocates:
    `ra` at 0, then `s0/s1/s2/s3/s4` = `x8/x9/x18/x19/x20`. -/
def hdnFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]

/-- The body slice of the emitted routine (between the frame prologue and
    the shared epilogue): argument moves, validation with branches into
    the shared `li a0,1` fail tail, the parity split, the up-counting
    nibble loop, and the success tail. -/
def hdnBody : List Instr :=
  [ .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .BEQ .x9 .x0 (120 : BitVec 13),   -- GH #10528: -8, the deleted reject pair
    .LBU .x5 .x8 (0 : BitVec 12),
    .SRLI .x6 .x5 (4 : BitVec 6),
    .ANDI .x7 .x5 (15 : BitVec 12),
    .ANDI .x28 .x6 (2 : BitVec 12),
    .SRLI .x28 .x28 (1 : BitVec 6),
    .SD .x20 .x28 (0 : BitVec 12),
    .ANDI .x6 .x6 (1 : BitVec 12),
    .BEQ .x6 .x0 (20 : BitVec 13),
    .SB .x18 .x7 (0 : BitVec 12),
    .LI .x30 (1 : Word),
    .ADDI .x31 .x18 (1 : BitVec 12),
    .JAL .x0 (12 : BitVec 21),
    .LI .x30 (0 : Word),
    .MV .x31 .x18,
    .LI .x5 (1 : Word),
    .BGEU .x5 .x9 (44 : BitVec 13),
    .ADD .x6 .x8 .x5,
    .LBU .x7 .x6 (0 : BitVec 12),
    .SRLI .x28 .x7 (4 : BitVec 6),
    .ANDI .x29 .x7 (15 : BitVec 12),
    .SB .x31 .x28 (0 : BitVec 12),
    .SB .x31 .x29 (1 : BitVec 12),
    .ADDI .x31 .x31 (2 : BitVec 12),
    .ADDI .x30 .x30 (2 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-40 : BitVec 21),
    .SD .x19 .x30 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word) ]

/-- **Byte transparency**: the emitted routine is EXACTLY the ABI-frame
    flatten of `hdnFrame` around `hdnBody` — no re-emission, the verified
    triple is over the guest's own bytes. -/
theorem hdnProg_eq :
    abiFrameProg (-48 : BitVec 12) (48 : BitVec 12) hdnFrame hdnBody
      = hpDecodeNibbles_prog := rfl

#guard abiFrameProg (-48 : BitVec 12) (48 : BitVec 12) hdnFrame hdnBody
  = hpDecodeNibbles_prog

#guard hdnBody.length = 36

/-! ## The guest-exact decode model -/

/-- The guest-exact hex-prefix decode. Post bead `evm-asm-3umhl` the
    guest is LENIENT on the even-path padding nibble (it ignores the low
    nibble of the head byte, exactly like execution-specs
    `compact_to_nibbles`), so the guest-exact model IS the spec-side
    `hpDecode`. -/
def hdnRes (bs : List (BitVec 8)) : Option (Bool × List (BitVec 8)) :=
  EvmAsm.Evm64.hpDecode bs

/-- **Total agreement with `hpDecode`** (`MptAssertions.lean`) —
    definitional after `evm-asm-3umhl`.

    `hpDecode` is the GUEST MIRROR, not the SpecRef port: this says nothing
    about `SpecRef.compact_to_nibbles`, which accepts head nibbles the guest
    rejects. See the module docstring and GH #10528. -/
theorem hdnRes_eq_hpDecode (bs : List (BitVec 8)) :
    hdnRes bs = EvmAsm.Evm64.hpDecode bs := rfl

/-- **Round-trip against the spec encoder**: on every hex-prefix encoding
    of a well-formed nibble path the guest decode succeeds with exactly
    the flag and path. -/
theorem hdnRes_hpEncode (isLeaf : Bool) (nibs : List (BitVec 8))
    (hn : ∀ n ∈ nibs, n.toNat < 16) :
    hdnRes (EvmAsm.Evm64.hpEncode isLeaf nibs) = some (isLeaf, nibs) :=
  EvmAsm.Evm64.hpDecode_hpEncode isLeaf nibs hn

/-! ## Machine-value bridges -/

/-- `highNibble`/`lowNibble` (the machine's `srli 4` / `andi 15` on the
    zero-extended byte, truncated back by `sb`) are the spec's nibble
    arithmetic. -/
theorem highNibble_eq (b : BitVec 8) :
    highNibble b = BitVec.ofNat 8 (b.toNat / 16) := by
  revert b; decide

theorem lowNibble_eq (b : BitVec 8) :
    lowNibble b = BitVec.ofNat 8 (b.toNat % 16) := by
  revert b; decide

/-- The machine loop's pair sequence is `hpUnpackPairs` over the consumed
    bytes. -/
theorem nibblePrefix_eq_hpUnpackPairs (bs : List (BitVec 8)) :
    ∀ i, i ≤ bs.length →
      nibblePrefix bs i = EvmAsm.Evm64.hpUnpackPairs (bs.take i) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ k ih =>
    intro hle
    have hk : k < bs.length := by omega
    rw [show nibblePrefix bs (k + 1)
          = nibblePrefix bs k ++ nibblePair (bs.getD k 0) from rfl,
        ih (by omega),
        show bs.take (k + 1) = bs.take k ++ [bs[k]'hk] from by
          rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl]
    unfold EvmAsm.Evm64.hpUnpackPairs
    rw [List.flatMap_append]
    congr 1
    show nibblePair (bs.getD k 0) = [_, _] ++ []
    rw [List.append_nil,
      show bs.getD k 0 = bs[k]'hk from by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl]
    show [highNibble _, lowNibble _] = _
    rw [highNibble_eq, lowNibble_eq]

/-! ## The result pieces the post is stated with -/

/-- Head byte (meaningful only when `bs ≠ []`). -/
def hdnB0 (bs : List (BitVec 8)) : BitVec 8 := bs.getD 0 0

/-- Parity of the compact path (1 = odd, carries a nibble in byte 0). -/
def hdnOdd (bs : List (BitVec 8)) : Bool := (hdnB0 bs).toNat / 16 % 2 = 1

/-- The is-leaf machine word `(hi & 2) >> 1` the routine stores. -/
def hdnIsLeafW (bs : List (BitVec 8)) : Word :=
  BitVec.ofNat 64 ((hdnB0 bs).toNat / 16 / 2 % 2)

/-- Whether the is-leaf cell is written at all: the store sits after the
    `len = 0` and `hi ≥ 4` rejects, so it executes iff the head byte
    exists and has a valid flag. -/
def hdnIslWritten (bs : List (BitVec 8)) : Bool :=
  !bs.isEmpty

/-- The decoded nibble list (empty on failure). -/
def hdnNibs (bs : List (BitVec 8)) : List (BitVec 8) :=
  ((hdnRes bs).map Prod.snd).getD []

/-- Success flag as the returned status word (0 success / 1 failure). -/
def hdnStatusW (bs : List (BitVec 8)) : Word :=
  if (hdnRes bs).isSome then 0 else 1

/-- Final nibble-buffer contents: the decoded nibbles spliced over the
    original buffer (nothing is written on failure — `hdnNibs = []`). -/
def hdnBufFinal (bs orig : List (BitVec 8)) : List (BitVec 8) :=
  setBytes orig 0 (hdnNibs bs)

/-- Final count cell: the nibble count on success, untouched otherwise. -/
def hdnCntFinal (bs : List (BitVec 8)) (old : Word) : Word :=
  if (hdnRes bs).isSome then BitVec.ofNat 64 (hdnNibs bs).length else old

/-- Final is-leaf cell. -/
def hdnIslFinal (bs : List (BitVec 8)) (old : Word) : Word :=
  if hdnIslWritten bs then hdnIsLeafW bs else old

-- Executable cross-checks of the model against the spec round-trip.
#guard hdnRes (EvmAsm.Evm64.hpEncode true [1, 2, 3]) = some (true, [1, 2, 3])
#guard hdnRes (EvmAsm.Evm64.hpEncode false [0xa, 0xb]) = some (false, [0xa, 0xb])
#guard hdnRes [] = none
-- Head nibble ≥ 4: bits 2-3 are IGNORED, exactly as `compact_to_nibbles`
-- masks them (GH #10528).  These used to be rejected.
#guard hdnRes [0x4a] = some (false, [])       -- 4 % 4 = 0 -> extension, even
#guard hdnRes [0x5a] = some (false, [0x0a])   -- 5 % 4 = 1 -> extension, odd
#guard hdnRes [0x6a] = some (true, [])        -- 6 % 4 = 2 -> leaf, even
#guard hdnRes [0x7a] = some (true, [0x0a])    -- 7 % 4 = 3 -> leaf, odd
#guard hdnRes [0xfa] = some (true, [0x0a])    -- top of the range
-- Lenient even-path padding nibble (evm-asm-3umhl): these DECODE now,
-- exactly like execution-specs `compact_to_nibbles`.
#guard hdnRes [0x2a] = some (true, [])
#guard hdnRes [0x01, 0xab] = some (false, [0x0a, 0x0b])

/-- `bytesRegion` is pc-free (instance form, for `runBlock`'s automatic
    framing). -/
instance (b : Word) (bs : List (BitVec 8)) :
    EvmAsm.Rv64.Assertion.PCFree (bytesRegion b bs) :=
  ⟨bytesRegion_pcFree b bs⟩

/-! ## Machine addressing and code membership (symbolic base) -/

/-- The routine `CodeReq` at a symbolic guest base. -/
def hdnCr (base : Word) : CodeReq := CodeReq.ofProg base hpDecodeNibbles_prog

/-- Address of body instruction `k` (the prologue is 7 instructions). -/
def bAt (base : Word) (k : Nat) : Word := base + BitVec.ofNat 64 (4 * (7 + k))

private theorem memAt (base : Word) (k : Nat) (instr : Instr)
    (hk : 7 + k < hpDecodeNibbles_prog.length)
    (hget : hpDecodeNibbles_prog.get ⟨7 + k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton (bAt base k) instr a = some i → hdnCr base a = some i := by
  have m := CodeReq.ofProg_lookup_addr base hpDecodeNibbles_prog (7 + k) (bAt base k)
    hk (by decide) rfl
  rw [hget] at m
  exact CodeReq.singleton_mono m

/-- Lift a segment triple over its own contiguous `ofProg` slice into the
    routine `CodeReq` (body index `k`). -/
private theorem liftSeg (base : Word) {n : Nat} {B : Word} {seg : List Instr}
    {P Q : Assertion} (k : Nat)
    (hslice : (hpDecodeNibbles_prog.drop (7 + k)).take seg.length = seg)
    (hrange : 7 + k + seg.length ≤ hpDecodeNibbles_prog.length)
    (h : cpsTripleWithin n (bAt base k) B (CodeReq.ofProg (bAt base k) seg) P Q) :
    cpsTripleWithin n (bAt base k) B (hdnCr base) P Q :=
  cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (bAt base k) hpDecodeNibbles_prog seg (7 + k)
      rfl hslice hrange (by decide)) h

private theorem ofNat_add' (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

private theorem bAt_add (base : Word) (k j : Nat) :
    bAt base k + BitVec.ofNat 64 (4 * j) = bAt base (k + j) := by
  unfold bAt
  rw [BitVec.add_assoc, ofNat_add']
  congr 2
  omega

private theorem bAt_succ (base : Word) (k : Nat) : bAt base k + 4 = bAt base (k + 1) := by
  have := bAt_add base k 1
  rwa [show BitVec.ofNat 64 (4 * 1) = (4 : Word) from rfl] at this

/-- Forward branch/jump landing: `bAt k + ofs = bAt (k + ofs/4)` for the
    emitted positive immediates. -/
private theorem bAt_br (base : Word) (k j : Nat) (ofs : BitVec 13)
    (h : signExtend13 ofs = BitVec.ofNat 64 (4 * j)) :
    bAt base k + signExtend13 ofs = bAt base (k + j) := by
  rw [h]; exact bAt_add base k j

private theorem bAt_jal (base : Word) (k j : Nat) (ofs : BitVec 21)
    (h : signExtend21 ofs = BitVec.ofNat 64 (4 * j)) :
    bAt base k + signExtend21 ofs = bAt base (k + j) := by
  rw [h]; exact bAt_add base k j

/-- Backward jump: the loop back-edge `jal x0, -40` from body 33 to body 23. -/
private theorem bAt_jal_back40 (base : Word) :
    bAt base 31 + signExtend21 (-40 : BitVec 21) = bAt base 21 := by
  unfold bAt
  rw [BitVec.add_assoc]
  congr 1

/-! ## Value bridges (machine words ↔ nibble arithmetic) -/

private theorem hi_word_eq (b : BitVec 8) :
    (b.zeroExtend 64 : Word) >>> (4 : BitVec 6).toNat
      = BitVec.ofNat 64 (b.toNat / 16) := by
  revert b; decide

private theorem lo_word_eq (b : BitVec 8) :
    (b.zeroExtend 64 : Word) &&& signExtend12 (15 : BitVec 12)
      = BitVec.ofNat 64 (b.toNat % 16) := by
  revert b; decide

private theorem isleaf_word_eq (b : BitVec 8) :
    (BitVec.ofNat 64 (b.toNat / 16) &&& signExtend12 (2 : BitVec 12))
        >>> (1 : BitVec 6).toNat
      = BitVec.ofNat 64 (b.toNat / 16 / 2 % 2) := by
  revert b; decide

private theorem parity_word_eq (b : BitVec 8) :
    BitVec.ofNat 64 (b.toNat / 16) &&& signExtend12 (1 : BitVec 12)
      = BitVec.ofNat 64 (b.toNat / 16 % 2) := by
  revert b; decide

private theorem hi_truncate_eq (b : BitVec 8) :
    ((b.zeroExtend 64 : Word) >>> (4 : BitVec 6).toNat).truncate 8 = highNibble b := rfl

private theorem lo_truncate_eq (b : BitVec 8) :
    ((b.zeroExtend 64 : Word) &&& signExtend12 (15 : BitVec 12)).truncate 8
      = lowNibble b := rfl

private theorem hi_lt4_iff (b : BitVec 8) :
    BitVec.ult (BitVec.ofNat 64 (b.toNat / 16)) (4 : Word) ↔ b.toNat / 16 < 4 := by
  revert b; decide

private theorem nib_word_eq_zero {n : Nat} (h : BitVec.ofNat 64 n = 0)
    (hlt : n < 2 ^ 64) : n = 0 := by
  have h2 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h2
  simpa using h2

private theorem nib_word_ne_zero_iff (n : Nat) (h : n < 16) :
    BitVec.ofNat 64 n ≠ (0 : Word) ↔ n ≠ 0 := by
  constructor
  · intro hne h0; exact hne (by rw [h0]; rfl)
  · intro hne heq
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact hne (by simpa using this)

/-! ## SB at instruction offset 1 (the loop's second nibble store) -/

/-- `bytesRegion_sb_within` sibling for `.SB rs1 rs2 1`: with `rs1` at
    region index `i`, the store writes index `i + 1`. -/
theorem bytesRegion_sb1_within (rs1 rs2 : Reg) (regionBase v_data : Word) (base : Word)
    (bs : List (BitVec 8)) (i : Nat)
    (halign : regionBase.toNat % 8 = 0) (hi : i + 1 < bs.length)
    (hover : regionBase.toNat + (i + 1) < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 (i + 1)) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SB rs1 rs2 1))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (rs2 ↦ᵣ v_data)
        ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (rs2 ↦ᵣ v_data) **
       bytesRegion regionBase (bs.set (i + 1) (v_data.truncate 8))) := by
  have hsb := bytesRegion_sb_within rs1 rs2 regionBase v_data base bs (i + 1)
    halign hi hover hvalid
  -- Transport the offset-0 lemma along `rs1 = (regionBase + i+1) - 1`:
  -- redo it directly instead, since the instruction differs.  We inline the
  -- same skeleton via the generic store spec.
  clear hsb
  have hr : (i + 1) % 8 < 8 := Nat.mod_lt _ (by norm_num)
  obtain ⟨front, rest, hf, hrst, heq, heqset⟩ :=
    bytesRegion_dword_at_set regionBase bs ((i + 1) / 8) ((i + 1) % 8)
      (v_data.truncate 8) hr (by omega)
  rw [Nat.div_add_mod (i + 1) 8] at heqset
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * ((i + 1) / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * ((i + 1) / 8))).take 8) with hwv
  have hptr_eq : (regionBase + BitVec.ofNat 64 i) + signExtend12 (1 : BitVec 12)
      = regionBase + BitVec.ofNat 64 (i + 1) := by
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, Nat.add_mod]
  have halign' :
      alignToDword ((regionBase + BitVec.ofNat 64 i) + signExtend12 (1 : BitVec 12))
        = dwordAddr := by
    rw [hptr_eq]; exact alignToDword_add_ofNat_of_aligned halign hover
  have hvalid' :
      isValidByteAccess ((regionBase + BitVec.ofNat 64 i) + signExtend12 (1 : BitVec 12))
        = true := by
    rw [hptr_eq]; exact hvalid
  have sb := generic_sb_spec_within rs1 rs2 (regionBase + BitVec.ofNat 64 i) v_data 1 base
    dwordAddr wordVal halign' hvalid'
  have hbo : byteOffset (regionBase + BitVec.ofNat 64 (i + 1)) = (i + 1) % 8 :=
    byteOffset_add_ofNat_of_aligned halign hover
  rw [hptr_eq, hbo, hwv,
    packBytes_set _ ((i + 1) % 8) (v_data.truncate 8) hr
      (by rw [List.length_take, List.length_drop]; omega)] at sb
  rw [heq, heqset]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hrst) sb)

/-! ## The buffer window -/

/-- Initial-count nibbles (the odd path's first nibble). -/
def hdnC0 (bs : List (BitVec 8)) : Nat := if hdnOdd bs then 1 else 0

def hdnInitNibs (bs : List (BitVec 8)) : List (BitVec 8) :=
  if hdnOdd bs then [lowNibble (hdnB0 bs)] else []

@[simp] theorem hdnInitNibs_length (bs : List (BitVec 8)) :
    (hdnInitNibs bs).length = hdnC0 bs := by
  unfold hdnInitNibs hdnC0
  split <;> rfl

/-- The nibble buffer after the loop has consumed `j` tail bytes. -/
def hdnWin (bs orig : List (BitVec 8)) (j : Nat) : List (BitVec 8) :=
  setBytes orig 0 (hdnInitNibs bs ++ nibblePrefix (bs.drop 1) j)

private theorem setBytes_append (bs : List (BitVec 8)) (i : Nat)
    (xs ys : List (BitVec 8)) :
    setBytes bs i (xs ++ ys) = setBytes (setBytes bs i xs) (i + xs.length) ys := by
  induction xs generalizing bs i with
  | nil => simp
  | cons x xt ih =>
    rw [List.cons_append, setBytes_cons, setBytes_cons, ih]
    congr 1
    simp; omega

/-- One loop iteration extends the window by the byte's nibble pair. -/
theorem hdnWin_step (bs orig : List (BitVec 8)) (j : Nat) :
    ((hdnWin bs orig j).set (hdnC0 bs + 2 * j)
        (highNibble ((bs.drop 1).getD j 0))).set (hdnC0 bs + 2 * j + 1)
        (lowNibble ((bs.drop 1).getD j 0))
      = hdnWin bs orig (j + 1) := by
  unfold hdnWin
  rw [show nibblePrefix (bs.drop 1) (j + 1)
        = nibblePrefix (bs.drop 1) j ++ nibblePair ((bs.drop 1).getD j 0) from rfl,
    ← List.append_assoc]
  have hlen : (hdnInitNibs bs ++ nibblePrefix (bs.drop 1) j).length
      = hdnC0 bs + 2 * j := by
    rw [List.length_append, hdnInitNibs_length, length_nibblePrefix]
  conv_rhs => rw [setBytes_append, hlen]
  rw [Nat.zero_add]
  simp only [BytesToNibblesSAsm.nibblePair, setBytes_cons, setBytes_nil]

@[simp] theorem hdnWin_zero_length (bs orig : List (BitVec 8)) (j : Nat) :
    (hdnWin bs orig j).length = orig.length := by
  unfold hdnWin
  exact length_setBytes _ _ _

/-! ## Segment triples -/

private def seg0Prog : List Instr :=
  [ .MV .x8 .x10, .MV .x9 .x11, .MV .x18 .x12, .MV .x19 .x13, .MV .x20 .x14 ]

/-- Body 0–4: move the five arguments into the saved `s`-registers. -/
theorem seg0_spec (base src lenW dst cnt isl s8 s9 s18 s19 s20 : Word) :
    cpsTripleWithin 5 (bAt base 0) (bAt base 5) (hdnCr base)
      ((.x10 ↦ᵣ src) ** (.x8 ↦ᵣ s8) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ s9)
        ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ s18) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ s19)
        ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ s20))
      ((.x10 ↦ᵣ src) ** (.x8 ↦ᵣ src) ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW)
        ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
        ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)) := by
  have hexit : base + BitVec.ofNat 64 28 + 4 + 4 + 4 + 4 + 4 = bAt base 5 := by
    simp only [bAt, BitVec.add_assoc]
    congr 1
  refine liftSeg base 0 (seg := seg0Prog) (by rfl) (by decide) ?_
  show cpsTripleWithin 5 (base + BitVec.ofNat 64 28) (bAt base 5)
    (CodeReq.ofProg (base + BitVec.ofNat 64 28) seg0Prog) _ _
  rw [← hexit]
  simp only [seg0Prog, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]
  have h0 := mv_spec_gen_within .x8 .x10 src s8
    (base + BitVec.ofNat 64 28) (by decide)
  have h1 := mv_spec_gen_within .x9 .x11 lenW s9
    (base + BitVec.ofNat 64 28 + 4) (by decide)
  have h2 := mv_spec_gen_within .x18 .x12 dst s18
    (base + BitVec.ofNat 64 28 + 4 + 4) (by decide)
  have h3 := mv_spec_gen_within .x19 .x13 cnt s19
    (base + BitVec.ofNat 64 28 + 4 + 4 + 4) (by decide)
  have h4 := mv_spec_gen_within .x20 .x14 isl s20
    (base + BitVec.ofNat 64 28 + 4 + 4 + 4 + 4) (by decide)
  runBlock h0 h1 h2 h3 h4

private theorem add_sext0 (x : Word) : x + signExtend12 (0 : BitVec 12) = x := by
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  exact BitVec.add_zero x

theorem add_ofNat_zero (x : Word) : x + BitVec.ofNat 64 0 = x := by
  rw [show BitVec.ofNat 64 0 = (0 : Word) from rfl]
  exact BitVec.add_zero x

/-- Numeral truncate bridge for the odd path's first-nibble store. -/
private theorem lo64_truncate_eq (b : BitVec 8) :
    (BitVec.ofNat 64 (b.toNat % 16)).truncate 8 = lowNibble b := by
  revert b; decide


private def seg1Prog : List Instr :=
  [ .LBU .x5 .x8 (0 : BitVec 12), .SRLI .x6 .x5 (4 : BitVec 6),
    .ANDI .x7 .x5 (15 : BitVec 12) ]

private def seg2Prog : List Instr :=
  [ .ANDI .x28 .x6 (2 : BitVec 12), .SRLI .x28 .x28 (1 : BitVec 6),
    .SD .x20 .x28 (0 : BitVec 12), .ANDI .x6 .x6 (1 : BitVec 12) ]

private def seg3oddProg : List Instr :=
  [ .SB .x18 .x7 (0 : BitVec 12), .LI .x30 (1 : Word),
    .ADDI .x31 .x18 (1 : BitVec 12) ]

private def seg4evenProg : List Instr :=
  [ .LI .x30 (0 : Word), .MV .x31 .x18 ]

/-- Body 5 (`beq s1, x0, +120`), taken: `len = 0` → fail tail. -/
theorem br1_taken (base : Word) (v : Word) (hv : v = 0) :
    cpsTripleWithin 1 (bAt base 5) (bAt base 35) (hdnCr base)
      ((.x9 ↦ᵣ v) ** (Reg.x0 ↦ᵣ (0 : Word)))
      ((.x9 ↦ᵣ v) ** (Reg.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x9 .x0 (120 : BitVec 13) v 0 (bAt base 5)
  rw [show bAt base 5 + signExtend13 (120 : BitVec 13) = bAt base 35 from by
    simp only [bAt, BitVec.add_assoc]; congr 1] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (memAt base 5 (.BEQ .x9 .x0 (120 : BitVec 13)) (by decide) (by rfl)) hbeq)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hv)

/-- Body 5, not taken: `len ≠ 0`. -/
theorem br1_ntaken (base : Word) (v : Word) (hv : v ≠ 0) :
    cpsTripleWithin 1 (bAt base 5) (bAt base 6) (hdnCr base)
      ((.x9 ↦ᵣ v) ** (Reg.x0 ↦ᵣ (0 : Word)))
      ((.x9 ↦ᵣ v) ** (Reg.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x9 .x0 (120 : BitVec 13) v 0 (bAt base 5)
  rw [bAt_succ base 5] at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (memAt base 5 (.BEQ .x9 .x0 (120 : BitVec 13)) (by decide) (by rfl)) hbeq)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hv ((sepConj_pure_right _).1 hBP).2)

/-- `seg1Prog` core at a free entry address. -/
private theorem seg1_core (A src : Word) (srcBytes : List (BitVec 8))
    (v5 v6 v7 v28 : Word)
    (hne : 0 < srcBytes.length) (halign : src.toNat % 8 = 0)
    (_hover : src.toNat + srcBytes.length < 2 ^ 64)
    (hvalid : isValidByteAccess (src + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 3 A (A + 4 + 4 + 4) (CodeReq.ofProg A seg1Prog)
      ((.x8 ↦ᵣ src) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7)
        ** (.x28 ↦ᵣ v28) ** bytesRegion src srcBytes)
      ((.x8 ↦ᵣ src) ** (.x5 ↦ᵣ ((srcBytes.getD 0 0).zeroExtend 64))
        ** (.x6 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16))
        ** (.x7 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16))
        ** (.x28 ↦ᵣ v28) ** bytesRegion src srcBytes) := by
  have hb0 : srcBytes.getD 0 0 = srcBytes[0]'hne := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hne]; rfl
  simp only [seg1Prog, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]
  have h0 := bytesRegion_lbu_within .x5 .x8 src v5 A srcBytes 0
    (by decide) halign hne (by omega) hvalid
  rw [add_ofNat_zero src] at h0
  have h1 := srli_spec_gen_within .x6 .x5 v6 ((srcBytes[0]'hne).zeroExtend 64)
    (4 : BitVec 6) (A + 4) (by decide)
  have h2 := andi_spec_gen_within .x7 .x5 v7 ((srcBytes[0]'hne).zeroExtend 64)
    (15 : BitVec 12) (A + 4 + 4) (by decide)
  rw [hi_word_eq] at h1
  rw [lo_word_eq] at h2
  rw [hb0]
  runBlock h0 h1 h2

/-- Body 6–9: load byte 0 and split it into the high/low nibbles; stage the
    flag bound. -/
theorem seg1_spec (base src : Word) (srcBytes : List (BitVec 8))
    (v5 v6 v7 v28 : Word)
    (hne : 0 < srcBytes.length) (halign : src.toNat % 8 = 0)
    (hover : src.toNat + srcBytes.length < 2 ^ 64)
    (hvalid : isValidByteAccess (src + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 3 (bAt base 6) (bAt base 9) (hdnCr base)
      ((.x8 ↦ᵣ src) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7)
        ** (.x28 ↦ᵣ v28) ** bytesRegion src srcBytes)
      ((.x8 ↦ᵣ src) ** (.x5 ↦ᵣ ((srcBytes.getD 0 0).zeroExtend 64))
        ** (.x6 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16))
        ** (.x7 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16))
        ** (.x28 ↦ᵣ v28) ** bytesRegion src srcBytes) := by
  have hexit : bAt base 6 + 4 + 4 + 4 = bAt base 9 := by
    simp only [bAt, BitVec.add_assoc]
    congr 1
  have hc := seg1_core (bAt base 6) src srcBytes v5 v6 v7 v28 hne halign hover hvalid
  rw [hexit] at hc
  exact liftSeg base 6 (seg := seg1Prog) (by rfl) (by decide) hc

/-- `seg2Prog` core at a free entry address. -/
private theorem seg2_core (A isl oldIsl : Word) (b0 : BitVec 8) (v28 : Word) :
    cpsTripleWithin 4 A (A + 4 + 4 + 4 + 4) (CodeReq.ofProg A seg2Prog)
      ((.x6 ↦ᵣ BitVec.ofNat 64 (b0.toNat / 16)) ** (.x28 ↦ᵣ v28)
        ** (.x20 ↦ᵣ isl) ** (isl ↦ₘ oldIsl))
      ((.x6 ↦ᵣ BitVec.ofNat 64 (b0.toNat / 16 % 2))
        ** (.x28 ↦ᵣ BitVec.ofNat 64 (b0.toNat / 16 / 2 % 2))
        ** (.x20 ↦ᵣ isl) ** (isl ↦ₘ BitVec.ofNat 64 (b0.toNat / 16 / 2 % 2))) := by
  simp only [seg2Prog, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]
  have h0 := andi_spec_gen_within .x28 .x6 v28 (BitVec.ofNat 64 (b0.toNat / 16))
    (2 : BitVec 12) A (by decide)
  have h1 := srli_spec_gen_same_within .x28
    (BitVec.ofNat 64 (b0.toNat / 16) &&& signExtend12 (2 : BitVec 12))
    (1 : BitVec 6) (A + 4) (by decide)
  rw [isleaf_word_eq] at h1
  have h2 := sd_spec_gen_within .x20 .x28 isl
    (BitVec.ofNat 64 (b0.toNat / 16 / 2 % 2)) oldIsl (0 : BitVec 12) (A + 4 + 4)
  rw [add_sext0 isl] at h2
  have h3 := andi_spec_gen_same_within .x6 (BitVec.ofNat 64 (b0.toNat / 16))
    (1 : BitVec 12) (A + 4 + 4 + 4) (by decide)
  rw [parity_word_eq] at h3
  runBlock h0 h1 h2 h3

/-- Body 11–14: compute + store the is-leaf flag, reduce `x6` to the
    parity bit. -/
theorem seg2_spec (base isl oldIsl : Word) (b0 : BitVec 8) (v28 : Word) :
    cpsTripleWithin 4 (bAt base 9) (bAt base 13) (hdnCr base)
      ((.x6 ↦ᵣ BitVec.ofNat 64 (b0.toNat / 16)) ** (.x28 ↦ᵣ v28)
        ** (.x20 ↦ᵣ isl) ** (isl ↦ₘ oldIsl))
      ((.x6 ↦ᵣ BitVec.ofNat 64 (b0.toNat / 16 % 2))
        ** (.x28 ↦ᵣ BitVec.ofNat 64 (b0.toNat / 16 / 2 % 2))
        ** (.x20 ↦ᵣ isl) ** (isl ↦ₘ BitVec.ofNat 64 (b0.toNat / 16 / 2 % 2))) := by
  have hexit : bAt base 9 + 4 + 4 + 4 + 4 = bAt base 13 := by
    simp only [bAt, BitVec.add_assoc]
    congr 1
  have hc := seg2_core (bAt base 9) isl oldIsl b0 v28
  rw [hexit] at hc
  exact liftSeg base 9 (seg := seg2Prog) (by rfl) (by decide) hc

/-- Body 15 (`beq parity, x0, +20`), taken: even path. -/
theorem br3_taken (base : Word) (b0 : BitVec 8)
    (hv : b0.toNat / 16 % 2 = 0) :
    cpsTripleWithin 1 (bAt base 13) (bAt base 18) (hdnCr base)
      ((.x6 ↦ᵣ BitVec.ofNat 64 (b0.toNat / 16 % 2)) ** (Reg.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ BitVec.ofNat 64 (b0.toNat / 16 % 2)) ** (Reg.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x6 .x0 (20 : BitVec 13)
    (BitVec.ofNat 64 (b0.toNat / 16 % 2)) 0 (bAt base 13)
  rw [show bAt base 13 + signExtend13 (20 : BitVec 13) = bAt base 18 from by
    simp only [bAt, BitVec.add_assoc]; congr 1] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (memAt base 13 (.BEQ .x6 .x0 (20 : BitVec 13)) (by decide) (by rfl)) hbeq)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 (by rw [hv]; rfl))

/-- Body 15, not taken: odd path. -/
theorem br3_ntaken (base : Word) (b0 : BitVec 8)
    (hv : b0.toNat / 16 % 2 ≠ 0) :
    cpsTripleWithin 1 (bAt base 13) (bAt base 14) (hdnCr base)
      ((.x6 ↦ᵣ BitVec.ofNat 64 (b0.toNat / 16 % 2)) ** (Reg.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ BitVec.ofNat 64 (b0.toNat / 16 % 2)) ** (Reg.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x6 .x0 (20 : BitVec 13)
    (BitVec.ofNat 64 (b0.toNat / 16 % 2)) 0 (bAt base 13)
  rw [bAt_succ base 13] at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (memAt base 13 (.BEQ .x6 .x0 (20 : BitVec 13)) (by decide) (by rfl)) hbeq)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hv (nib_word_eq_zero ((sepConj_pure_right _).1 hBP).2 (by omega)))

/-- `seg3oddProg` core at a free entry address. -/
private theorem seg3odd_core (A dst : Word) (b0 : BitVec 8)
    (bufOrig : List (BitVec 8)) (v30 v31 : Word)
    (hlen : 0 < bufOrig.length) (halign : dst.toNat % 8 = 0)
    (_hover : dst.toNat + bufOrig.length < 2 ^ 64)
    (hvalid : isValidByteAccess (dst + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 3 A (A + 4 + 4 + 4) (CodeReq.ofProg A seg3oddProg)
      ((.x18 ↦ᵣ dst) ** (.x7 ↦ᵣ BitVec.ofNat 64 (b0.toNat % 16))
        ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** bytesRegion dst bufOrig)
      ((.x18 ↦ᵣ dst) ** (.x7 ↦ᵣ BitVec.ofNat 64 (b0.toNat % 16))
        ** (.x30 ↦ᵣ (1 : Word)) ** (.x31 ↦ᵣ (dst + BitVec.ofNat 64 1))
        ** bytesRegion dst (bufOrig.set 0 (lowNibble b0))) := by
  simp only [seg3oddProg, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]
  have h0 := bytesRegion_sb_within .x18 .x7 dst
    (BitVec.ofNat 64 (b0.toNat % 16)) A bufOrig 0 halign hlen (by omega) hvalid
  rw [add_ofNat_zero dst, lo64_truncate_eq] at h0
  have h1 := li_spec_gen_within .x30 v30 (1 : Word) (A + 4) (by decide)
  have h2 := addi_spec_gen_within .x31 .x18 v31 dst (1 : BitVec 12)
    (A + 4 + 4) (by decide)
  rw [show dst + signExtend12 (1 : BitVec 12) = dst + BitVec.ofNat 64 1 from by
    congr 1] at h2
  runBlock h0 h1 h2

/-- Body 16–18 (odd path): store the head nibble at `dst[0]`, count 1,
    cursor `dst + 1`. -/
theorem seg3odd_spec (base dst : Word) (b0 : BitVec 8)
    (bufOrig : List (BitVec 8)) (v30 v31 : Word)
    (hlen : 0 < bufOrig.length) (halign : dst.toNat % 8 = 0)
    (hover : dst.toNat + bufOrig.length < 2 ^ 64)
    (hvalid : isValidByteAccess (dst + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 3 (bAt base 14) (bAt base 17) (hdnCr base)
      ((.x18 ↦ᵣ dst) ** (.x7 ↦ᵣ BitVec.ofNat 64 (b0.toNat % 16))
        ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** bytesRegion dst bufOrig)
      ((.x18 ↦ᵣ dst) ** (.x7 ↦ᵣ BitVec.ofNat 64 (b0.toNat % 16))
        ** (.x30 ↦ᵣ (1 : Word)) ** (.x31 ↦ᵣ (dst + BitVec.ofNat 64 1))
        ** bytesRegion dst (bufOrig.set 0 (lowNibble b0))) := by
  have hexit : bAt base 14 + 4 + 4 + 4 = bAt base 17 := by
    simp only [bAt, BitVec.add_assoc]
    congr 1
  have hc := seg3odd_core (bAt base 14) dst b0 bufOrig v30 v31 hlen halign hover hvalid
  rw [hexit] at hc
  exact liftSeg base 14 (seg := seg3oddProg) (by rfl) (by decide) hc

/-- Body 19: the odd path's `jal x0, +12` over the even block into the
    loop init. -/
theorem jal19_spec (base : Word) {P : Assertion} (hP : P.pcFree) :
    cpsTripleWithin 1 (bAt base 17) (bAt base 20) (hdnCr base) P P := by
  have h := jal0_spec_pcFree (12 : BitVec 21) (bAt base 17) hP
  rw [show bAt base 17 + signExtend21 (12 : BitVec 21) = bAt base 20 from by
    simp only [bAt, BitVec.add_assoc]; congr 1] at h
  exact cpsTripleWithin_extend_code
    (memAt base 17 (.JAL .x0 (12 : BitVec 21)) (by decide) (by rfl)) h

/-- `seg4evenProg` core at a free entry address. -/
private theorem seg4even_core (A dst : Word) (v30 v31 : Word) :
    cpsTripleWithin 2 A (A + 4 + 4) (CodeReq.ofProg A seg4evenProg)
      ((.x18 ↦ᵣ dst) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
      ((.x18 ↦ᵣ dst) ** (.x30 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ dst)) := by
  simp only [seg4evenProg, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]
  have h0 := li_spec_gen_within .x30 v30 (0 : Word) A (by decide)
  have h1 := mv_spec_gen_within .x31 .x18 dst v31 (A + 4) (by decide)
  runBlock h0 h1

/-- Body 20–21 (even path): count 0, cursor `dst`. -/
theorem seg4even_spec (base dst : Word) (v30 v31 : Word) :
    cpsTripleWithin 2 (bAt base 18) (bAt base 20) (hdnCr base)
      ((.x18 ↦ᵣ dst) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
      ((.x18 ↦ᵣ dst) ** (.x30 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ dst)) := by
  have hexit : bAt base 18 + 4 + 4 = bAt base 20 := by
    simp only [bAt, BitVec.add_assoc]
    congr 1
  have hc := seg4even_core (bAt base 18) dst v30 v31
  rw [hexit] at hc
  exact liftSeg base 18 (seg := seg4evenProg) (by rfl) (by decide) hc

/-- Body 22: loop-cursor init `li t0, 1`. -/
theorem seg5_spec (base : Word) (v5 : Word) :
    cpsTripleWithin 1 (bAt base 20) (bAt base 21) (hdnCr base)
      (.x5 ↦ᵣ v5) (.x5 ↦ᵣ (1 : Word)) := by
  have h := li_spec_gen_within .x5 v5 (1 : Word) (bAt base 20) (by decide)
  rw [bAt_succ base 20] at h
  exact cpsTripleWithin_extend_code
    (memAt base 20 (.LI .x5 (1 : Word)) (by decide) (by rfl)) h

/-- Body 34–36: store the nibble count, status 0, jump to the body exit. -/
theorem seg6_spec (base cnt oldCnt : Word) (v30 v10 : Word) :
    cpsTripleWithin 3 (bAt base 32) (bAt base 36) (hdnCr base)
      ((.x19 ↦ᵣ cnt) ** (.x30 ↦ᵣ v30) ** (.x10 ↦ᵣ v10) ** (cnt ↦ₘ oldCnt))
      ((.x19 ↦ᵣ cnt) ** (.x30 ↦ᵣ v30) ** (.x10 ↦ᵣ (0 : Word)) ** (cnt ↦ₘ v30)) := by
  -- SD, then LI, then the jump — the jump is handled separately since
  -- `runBlock` chains fall-through exits only.
  have h0 := sd_spec_gen_within .x19 .x30 cnt v30 oldCnt (0 : BitVec 12) (bAt base 32)
  rw [add_sext0 cnt, bAt_succ base 32] at h0
  have h1 := li_spec_gen_within .x10 v10 (0 : Word) (bAt base 33) (by decide)
  rw [bAt_succ base 33] at h1
  have h2 := jal0_spec_pcFree (8 : BitVec 21) (bAt base 34)
    (P := (.x19 ↦ᵣ cnt) ** (.x30 ↦ᵣ v30) ** (.x10 ↦ᵣ (0 : Word)) ** (cnt ↦ₘ v30))
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs pcFree_memIs)))
  rw [show bAt base 34 + signExtend21 (8 : BitVec 21) = bAt base 36 from by
    simp only [bAt, BitVec.add_assoc]; congr 1] at h2
  have m0 := cpsTripleWithin_extend_code
    (memAt base 32 (.SD .x19 .x30 (0 : BitVec 12)) (by decide) (by rfl)) h0
  have m1 := cpsTripleWithin_extend_code
    (memAt base 33 (.LI .x10 (0 : Word)) (by decide) (by rfl)) h1
  have m2 := cpsTripleWithin_extend_code
    (memAt base 34 (.JAL .x0 (8 : BitVec 21)) (by decide) (by rfl)) h2
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (.x10 ↦ᵣ v10) pcFree_regIs m0)
    (cpsTripleWithin_frameR ((.x19 ↦ᵣ cnt) ** (cnt ↦ₘ v30)) (pcFree_sepConj
      pcFree_regIs pcFree_memIs) (cpsTripleWithin_frameR (.x30 ↦ᵣ v30)
        pcFree_regIs m1))
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 m2
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) s2

/-- Body 37: the shared fail tail `li a0, 1`, falling into the epilogue. -/
theorem fail38_spec (base : Word) (v10 : Word) :
    cpsTripleWithin 1 (bAt base 35) (bAt base 36) (hdnCr base)
      (.x10 ↦ᵣ v10) (.x10 ↦ᵣ (1 : Word)) := by
  have h := li_spec_gen_within .x10 v10 (1 : Word) (bAt base 35) (by decide)
  rw [bAt_succ base 35] at h
  exact cpsTripleWithin_extend_code
    (memAt base 35 (.LI .x10 (1 : Word)) (by decide) (by rfl)) h


/-! ## The nibble loop -/

private def loopProg : List Instr :=
  [ .ADD .x6 .x8 .x5,
    .LBU .x7 .x6 (0 : BitVec 12),
    .SRLI .x28 .x7 (4 : BitVec 6),
    .ANDI .x29 .x7 (15 : BitVec 12),
    .SB .x31 .x28 (0 : BitVec 12),
    .SB .x31 .x29 (1 : BitVec 12),
    .ADDI .x31 .x31 (2 : BitVec 12),
    .ADDI .x30 .x30 (2 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12) ]

private theorem hi64_truncate_eq (b : BitVec 8) :
    (BitVec.ofNat 64 (b.toNat / 16)).truncate 8 = highNibble b := by
  revert b; decide

private theorem getD_drop1 (bs : List (BitVec 8)) (i : Nat) (hi : 1 ≤ i) :
    (bs.drop 1).getD (i - 1) 0 = bs.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2
  omega

private theorem add_ofNat_sext2 (x : Word) (a : Nat) :
    x + BitVec.ofNat 64 a + signExtend12 (2 : BitVec 12) = x + BitVec.ofNat 64 (a + 2) := by
  rw [show signExtend12 (2 : BitVec 12) = BitVec.ofNat 64 2 from by decide,
    BitVec.add_assoc, ofNat_add']

private theorem ofNat_sext2 (a : Nat) :
    BitVec.ofNat 64 a + signExtend12 (2 : BitVec 12) = BitVec.ofNat 64 (a + 2) := by
  rw [show signExtend12 (2 : BitVec 12) = BitVec.ofNat 64 2 from by decide, ofNat_add']

private theorem ofNat_sext1 (a : Nat) :
    BitVec.ofNat 64 a + signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 (a + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide, ofNat_add']

/-- One loop iteration's straight-line core (body 25–33) at a free entry
    address: read byte `i`, write its nibble pair at the cursor, bump
    cursor/count/index.  `W` is the current buffer window. -/
private theorem loopCore (A src dst : Word) (bs W : List (BitVec 8)) (i p : Nat)
    (w6 w7 w28 w29 : Word)
    (hi : i < bs.length) (hsalign : src.toNat % 8 = 0)
    (hsover : src.toNat + bs.length < 2 ^ 64)
    (hsvalid : isValidByteAccess (src + BitVec.ofNat 64 i) = true)
    (hp : p + 1 < W.length) (hdalign : dst.toNat % 8 = 0)
    (hdover : dst.toNat + W.length < 2 ^ 64)
    (hdvalid0 : isValidByteAccess (dst + BitVec.ofNat 64 p) = true)
    (hdvalid1 : isValidByteAccess (dst + BitVec.ofNat 64 (p + 1)) = true) :
    cpsTripleWithin 9 A (A + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4)
      (CodeReq.ofProg A loopProg)
      ((.x5 ↦ᵣ BitVec.ofNat 64 i) ** (.x8 ↦ᵣ src) ** (.x6 ↦ᵣ w6)
        ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29)
        ** (.x30 ↦ᵣ BitVec.ofNat 64 p) ** (.x31 ↦ᵣ (dst + BitVec.ofNat 64 p))
        ** bytesRegion src bs ** bytesRegion dst W)
      ((.x5 ↦ᵣ BitVec.ofNat 64 (i + 1)) ** (.x8 ↦ᵣ src)
        ** (.x6 ↦ᵣ (src + BitVec.ofNat 64 i))
        ** (.x7 ↦ᵣ ((bs.getD i 0).zeroExtend 64))
        ** (.x28 ↦ᵣ BitVec.ofNat 64 ((bs.getD i 0).toNat / 16))
        ** (.x29 ↦ᵣ BitVec.ofNat 64 ((bs.getD i 0).toNat % 16))
        ** (.x30 ↦ᵣ BitVec.ofNat 64 (p + 2))
        ** (.x31 ↦ᵣ (dst + BitVec.ofNat 64 (p + 2)))
        ** bytesRegion src bs
        ** bytesRegion dst
            ((W.set p (highNibble (bs.getD i 0))).set (p + 1)
              (lowNibble (bs.getD i 0)))) := by
  have hbi : bs.getD i 0 = bs[i]'hi := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  simp only [loopProg, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]
  have h0 := add_spec_gen_within .x6 .x8 .x5 src (BitVec.ofNat 64 i) w6 A (by decide)
  have h1 := bytesRegion_lbu_within .x7 .x6 src w7 (A + 4) bs i
    (by decide) hsalign hi (by omega) hsvalid
  have h2 := srli_spec_gen_within .x28 .x7 w28 ((bs[i]'hi).zeroExtend 64)
    (4 : BitVec 6) (A + 4 + 4) (by decide)
  rw [hi_word_eq] at h2
  have h3 := andi_spec_gen_within .x29 .x7 w29 ((bs[i]'hi).zeroExtend 64)
    (15 : BitVec 12) (A + 4 + 4 + 4) (by decide)
  rw [lo_word_eq] at h3
  have h4 := bytesRegion_sb_within .x31 .x28 dst
    (BitVec.ofNat 64 ((bs[i]'hi).toNat / 16)) (A + 4 + 4 + 4 + 4) W p
    hdalign (by omega) (by omega) hdvalid0
  rw [hi64_truncate_eq] at h4
  have h5 := bytesRegion_sb1_within .x31 .x29 dst
    (BitVec.ofNat 64 ((bs[i]'hi).toNat % 16)) (A + 4 + 4 + 4 + 4 + 4)
    (W.set p (highNibble (bs[i]'hi))) p
    hdalign (by rw [List.length_set]; omega) (by omega) hdvalid1
  rw [lo64_truncate_eq] at h5
  have h6 := addi_spec_gen_same_within .x31 (dst + BitVec.ofNat 64 p)
    (2 : BitVec 12) (A + 4 + 4 + 4 + 4 + 4 + 4) (by decide)
  rw [add_ofNat_sext2] at h6
  have h7 := addi_spec_gen_same_within .x30 (BitVec.ofNat 64 p)
    (2 : BitVec 12) (A + 4 + 4 + 4 + 4 + 4 + 4 + 4) (by decide)
  rw [ofNat_sext2] at h7
  have h8 := addi_spec_gen_same_within .x5 (BitVec.ofNat 64 i)
    (1 : BitVec 12) (A + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) (by decide)
  rw [ofNat_sext1] at h8
  rw [hbi]
  runBlock h0 h1 h2 h3 h4 h5 h6 h7 h8

/-- The loop invariant at cursor `i` (`1 ≤ i`): the first `i - 1` tail
    bytes have been unpacked into the window, count and cursor are at
    `c0 + 2 * (i - 1)`, and the scratch registers hold the entry values
    (`i = 1`) or the previous iteration's values. -/
def hdnInv (src dst : Word) (bs orig : List (BitVec 8))
    (e6 e7 e28 e29 : Word) (i : Nat) : Assertion :=
  (.x8 ↦ᵣ src) **
  (.x6 ↦ᵣ (if i ≤ 1 then e6 else src + BitVec.ofNat 64 (i - 1))) **
  (.x7 ↦ᵣ (if i ≤ 1 then e7 else (bs.getD (i - 1) 0).zeroExtend 64)) **
  (.x28 ↦ᵣ (if i ≤ 1 then e28
    else BitVec.ofNat 64 ((bs.getD (i - 1) 0).toNat / 16))) **
  (.x29 ↦ᵣ (if i ≤ 1 then e29
    else BitVec.ofNat 64 ((bs.getD (i - 1) 0).toNat % 16))) **
  (.x30 ↦ᵣ BitVec.ofNat 64 (hdnC0 bs + 2 * (i - 1))) **
  (.x31 ↦ᵣ (dst + BitVec.ofNat 64 (hdnC0 bs + 2 * (i - 1)))) **
  bytesRegion src bs ** bytesRegion dst (hdnWin bs orig (i - 1))

private theorem pcFree_hdnInv (src dst : Word) (bs orig : List (BitVec 8))
    (e6 e7 e28 e29 : Word) (i : Nat) :
    (hdnInv src dst bs orig e6 e7 e28 e29 i).pcFree := by
  unfold hdnInv
  exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj
          (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _))))))))

/-- The per-iteration body triple `upLoop_spec` consumes: fall-through
    (body 25) back to the header (body 24). -/
private theorem loopBody_spec (base src dst : Word) (bs orig : List (BitVec 8))
    (e6 e7 e28 e29 : Word) (i : Nat)
    (h1i : 1 ≤ i) (hi : i < bs.length)
    (hsalign : src.toNat % 8 = 0) (hsover : src.toNat + bs.length < 2 ^ 64)
    (hsvalid : ∀ j, j < bs.length → isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (hbuf : hdnC0 bs + 2 * (bs.length - 1) ≤ orig.length)
    (hdalign : dst.toNat % 8 = 0) (hdover : dst.toNat + orig.length < 2 ^ 64)
    (hdvalid : ∀ j, j < orig.length → isValidByteAccess (dst + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 10 (bAt base 22) (bAt base 21) (hdnCr base)
      ((.x5 ↦ᵣ BitVec.ofNat 64 i) ** (.x9 ↦ᵣ BitVec.ofNat 64 bs.length)
        ** hdnInv src dst bs orig e6 e7 e28 e29 i)
      ((.x5 ↦ᵣ BitVec.ofNat 64 (i + 1)) ** (.x9 ↦ᵣ BitVec.ofNat 64 bs.length)
        ** hdnInv src dst bs orig e6 e7 e28 e29 (i + 1)) := by
  have hc0 : hdnC0 bs ≤ 1 := by unfold hdnC0; split <;> omega
  have hplen : hdnC0 bs + 2 * (i - 1) + 1 < orig.length := by omega
  have hwinlen : (hdnWin bs orig (i - 1)).length = orig.length :=
    hdnWin_zero_length bs orig (i - 1)
  -- The straight-line core over the real bytes.
  have hcore := loopCore (bAt base 22) src dst bs (hdnWin bs orig (i - 1)) i
    (hdnC0 bs + 2 * (i - 1))
    (if i ≤ 1 then e6 else src + BitVec.ofNat 64 (i - 1))
    (if i ≤ 1 then e7 else (bs.getD (i - 1) 0).zeroExtend 64)
    (if i ≤ 1 then e28 else BitVec.ofNat 64 ((bs.getD (i - 1) 0).toNat / 16))
    (if i ≤ 1 then e29 else BitVec.ofNat 64 ((bs.getD (i - 1) 0).toNat % 16))
    hi hsalign hsover (hsvalid i hi)
    (by rw [hwinlen]; omega) hdalign (by rw [hwinlen]; omega)
    (hdvalid _ (by omega)) (hdvalid _ (by omega))
  -- Rewrite the window step and the tail-byte bridge.
  have hstep := hdnWin_step bs orig (i - 1)
  rw [getD_drop1 bs i h1i] at hstep
  rw [show i - 1 + 1 = i from by omega] at hstep
  rw [hstep] at hcore
  -- Lift into the routine CodeReq.
  have hexit : bAt base 22 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = bAt base 31 := by
    simp only [bAt, BitVec.add_assoc]
    congr 1
  rw [hexit] at hcore
  have hlift := liftSeg base 22 (seg := loopProg) (by rfl) (by decide) hcore
  -- The back-edge.
  have hjal := jal0_spec_pcFree (-40 : BitVec 21) (bAt base 31)
    (P := (.x5 ↦ᵣ BitVec.ofNat 64 (i + 1)) ** (.x8 ↦ᵣ src)
      ** (.x6 ↦ᵣ (src + BitVec.ofNat 64 i))
      ** (.x7 ↦ᵣ ((bs.getD i 0).zeroExtend 64))
      ** (.x28 ↦ᵣ BitVec.ofNat 64 ((bs.getD i 0).toNat / 16))
      ** (.x29 ↦ᵣ BitVec.ofNat 64 ((bs.getD i 0).toNat % 16))
      ** (.x30 ↦ᵣ BitVec.ofNat 64 (hdnC0 bs + 2 * (i - 1) + 2))
      ** (.x31 ↦ᵣ (dst + BitVec.ofNat 64 (hdnC0 bs + 2 * (i - 1) + 2)))
      ** bytesRegion src bs ** bytesRegion dst (hdnWin bs orig i))
    (hP := pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj (bytesRegion_pcFree _ _)
              (bytesRegion_pcFree _ _))))))))))
  rw [bAt_jal_back40 base] at hjal
  have hjal' := cpsTripleWithin_extend_code
    (memAt base 31 (.JAL .x0 (-40 : BitVec 21)) (by decide) (by rfl)) hjal
  -- core ; jal, then frame x9 and reshape into the invariant.
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hlift hjal'
  have hframed := cpsTripleWithin_frameR (.x9 ↦ᵣ BitVec.ofNat 64 bs.length)
    pcFree_regIs hseq
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hframed
  · unfold hdnInv at hp
    xperm_hyp hp
  · unfold hdnInv
    rw [if_neg (by omega : ¬ i + 1 ≤ 1), if_neg (by omega : ¬ i + 1 ≤ 1),
      if_neg (by omega : ¬ i + 1 ≤ 1), if_neg (by omega : ¬ i + 1 ≤ 1),
      show i + 1 - 1 = i from by omega,
      show hdnC0 bs + 2 * i = hdnC0 bs + 2 * (i - 1) + 2 from by omega]
    xperm_hyp hq

/-- The whole nibble loop, from the header at cursor 1 to the exit at
    cursor `len` (`upLoop_spec` instance on the emitted `bgeu`/back-edge). -/
theorem loop_spec (base src dst : Word) (bs orig : List (BitVec 8))
    (e6 e7 e28 e29 : Word)
    (hlen1 : 1 ≤ bs.length)
    (hsalign : src.toNat % 8 = 0) (hsover : src.toNat + bs.length < 2 ^ 64)
    (hsvalid : ∀ j, j < bs.length → isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (hbuf : hdnC0 bs + 2 * (bs.length - 1) ≤ orig.length)
    (hdalign : dst.toNat % 8 = 0) (hdover : dst.toNat + orig.length < 2 ^ 64)
    (hdvalid : ∀ j, j < orig.length → isValidByteAccess (dst + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin ((bs.length - 1) * 11 + 1) (bAt base 21) (bAt base 32)
      (hdnCr base)
      ((.x5 ↦ᵣ BitVec.ofNat 64 1) ** (.x9 ↦ᵣ BitVec.ofNat 64 bs.length)
        ** hdnInv src dst bs orig e6 e7 e28 e29 1)
      ((.x5 ↦ᵣ BitVec.ofNat 64 bs.length) ** (.x9 ↦ᵣ BitVec.ofNat 64 bs.length)
        ** hdnInv src dst bs orig e6 e7 e28 e29 bs.length) := by
  have h := upLoop_spec (hdnCr base) (bAt base 21) (bAt base 32) .x5 .x9
    (44 : BitVec 13) 10 bs.length
    (hdnInv src dst bs orig e6 e7 e28 e29)
    (by omega)
    (by
      show bAt base 21 + signExtend13 (44 : BitVec 13) = bAt base 32
      simp only [bAt, BitVec.add_assoc]
      congr 1)
    (fun n => pcFree_hdnInv src dst bs orig e6 e7 e28 e29 n)
    (memAt base 21 (.BGEU .x5 .x9 (44 : BitVec 13)) (by decide) (by rfl))
    1 hlen1
    (fun i h1i hi => by
      have h := loopBody_spec base src dst bs orig e6 e7 e28 e29 i h1i hi
        hsalign hsover hsvalid hbuf hdalign hdover hdvalid
      rw [← bAt_succ base 21] at h
      exact h)
  exact cpsTripleWithin_mono_nSteps (by omega) h


end HpDecodeNibblesSAsm

end EvmAsm.Codegen
