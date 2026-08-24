import EvmAsm.Codegen.Programs.RlpEncodeBytesComposeSAsm

namespace EvmAsm.Codegen

namespace RlpEncodeBytesSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
open EvmAsm.Rv64.RLP (copyN copyN_eq_append word_ofNat_add_one)
open EvmAsm.Codegen.RlpListEncodedSizeSAsm (u64ByteLen u64ByteLen_le)

set_option maxRecDepth 8000 in
/-- **`rlp_encode_bytes` over an arena window.**  This is the producer-facing
    whole-routine contract: the logical output pointer is `arenaPtr + off`,
    while the complete aligned arena is framed before and after the call. -/
theorem reb_spec_arena_within (srcPtr arenaPtr cellPtr raVal cellOld : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) (data arenaBytes : List Byte)
    (off n : Nat) (hn : data.length = n) (hn64 : n < 2 ^ 64)
    (hfit : off + n + 9 ≤ arenaBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hbase_align : arenaPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64)
    (hover : arenaPtr.toNat + (off + n + 9) < 2 ^ 64)
    (hsvalid : ∀ k, k < n →
      isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hvalid : ∀ k, k < n + 9 →
      isValidByteAccess (arenaPtr + BitVec.ofNat 64 (off + k)) = true) :
    cpsTripleWithin (19 + 10 * u64ByteLen (BitVec.ofNat 64 n) + 7 * n)
      rebBase (raVal &&& ~~~1) rebCode
      (rebAbiArenaPre srcPtr arenaPtr cellPtr raVal cellOld data arenaBytes off n
        v5 v6 v7 v28 v29 v30 v31)
      (rebAbiArenaPost srcPtr arenaPtr cellPtr raVal data arenaBytes off) := by
  have hbc8 : u64ByteLen (BitVec.ofNat 64 n) ≤ 8 := u64ByteLen_le _
  by_cases hraw : ∃ b : Byte, data = [b] ∧ b.toNat < 128
  · obtain ⟨b, hdata, hsmall⟩ := hraw
    have hn1 : n = 1 := by rw [← hn, hdata]; rfl
    have hfit1 : off + 1 ≤ arenaBytes.length := by omega
    have hover1 : arenaPtr.toNat + off < 2 ^ 64 := by omega
    have hsteps : 13 ≤ 19 + 10 * u64ByteLen (BitVec.ofNat 64 n) + 7 * n := by
      rw [hn1]
      decide
    exact cpsTripleWithin_mono_nSteps hsteps
      (show cpsTripleWithin 13 rebBase (raVal &&& ~~~1) rebCode
          (rebAbiArenaPre srcPtr arenaPtr cellPtr raVal cellOld data arenaBytes off n
            v5 v6 v7 v28 v29 v30 v31)
          (rebAbiArenaPost srcPtr arenaPtr cellPtr raVal data arenaBytes off) from by
        simpa [hn1] using
          (reb_spec_raw_arena srcPtr arenaPtr cellPtr raVal cellOld
            v5 v6 v7 v28 v29 v30 v31 data arenaBytes off b hdata hsmall
            hfit1 hsalign hbase_align (by omega) hover1
            (by simpa [hdata] using hsvalid 0 (by omega))
            (hvalid 0 (by omega))))
  · have hnot_raw : ∀ b : Byte, data = [b] → ¬ b.toNat < 128 := by
      intro b hdata hsmall
      exact hraw ⟨b, hdata, hsmall⟩
    by_cases h56 : n < 56
    · exact cpsTripleWithin_mono_nSteps (by omega)
        (reb_spec_short_arena srcPtr arenaPtr cellPtr raVal cellOld
          v5 v6 v7 v28 v29 v30 v31 data arenaBytes off n hn h56 hn64 hnot_raw
          (by omega) hsalign hbase_align hsover (by omega) hsvalid
          (fun k hk => hvalid k (by omega)))
    · exact cpsTripleWithin_mono_nSteps (by omega)
        (reb_spec_long_arena srcPtr arenaPtr cellPtr raVal cellOld
          v5 v6 v7 v28 v29 v30 v31 data arenaBytes off n hn (by omega) hn64
          (by omega) hsalign hbase_align hsover (by omega) hsvalid
          (fun k hk => hvalid k (by omega)))

set_option maxRecDepth 8000 in
/-- **Whole routine, long form** (`len ≥ 56`): `rebBase → ra &&& ~~~1` in
    `19 + 10*bc + 7*n` steps, writing `0xb7 + bc`, the canonical
    length-of-length, and the payload. -/
theorem reb_spec_long (srcPtr outPtr cellPtr raVal cellOld : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) (data outBytes : List Byte) (n : Nat)
    (hn : data.length = n) (hn56 : 56 ≤ n) (hn64 : n < 2 ^ 64)
    (holen : (1 + u64ByteLen (BitVec.ofNat 64 n)) + n ≤ outBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64)
    (hoover : outPtr.toNat + ((1 + u64ByteLen (BitVec.ofNat 64 n)) + n) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < (1 + u64ByteLen (BitVec.ofNat 64 n)) + n →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (19 + 10 * u64ByteLen (BitVec.ofNat 64 n) + 7 * n)
      rebBase (raVal &&& ~~~1) rebCode
      (rebAbiPre srcPtr outPtr cellPtr raVal cellOld data outBytes n
        v5 v6 v7 v28 v29 v30 v31)
      (rebAbiPost srcPtr outPtr cellPtr raVal data outBytes n) := by
  set bc := u64ByteLen (BitVec.ofNat 64 n) with hbc
  have hlenN : (BitVec.ofNat 64 n).toNat = n := ofNat_toNat_eq n hn64
  have hbc8 : bc ≤ 8 := u64ByteLen_le _
  have hbc_len : bc = (Nat.toBytesBE n).length := by
    rw [hbc, u64ByteLen_eq_toBytesBE_length, hlenN]
  -- ### the model side
  have henc : encodeBytes data
      = [BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE n).length)]
          ++ Nat.toBytesBE n ++ data := by
    have h := encodeBytes_long_of_length data (by omega)
    rwa [hn] at h
  have hlen : (encodeBytes data).length = (1 + bc) + n := by
    rw [henc]
    simp only [List.length_append, List.length_cons, List.length_nil, hn,
      ← hbc_len]
  -- ### the region: header byte, then the length-of-length, then the payload
  have hregion :
      copyN (writeShift (outBytes.set 0 (BitVec.ofNat 8 (183 + bc))) 1 n bc)
          data (1 + bc) 0 n
        = encodeBytes data ++ outBytes.drop (encodeBytes data).length := by
    have hset_len : (outBytes.set 0 (BitVec.ofNat 8 (183 + bc))).length
        = outBytes.length := List.length_set ..
    have hbs : beShift n bc = Nat.toBytesBE n := by
      rw [hbc_len]; exact beShift_eq_toBytesBE n
    have hpre_len : ([BitVec.ofNat 8 (183 + bc)] ++ Nat.toBytesBE n).length
        = 1 + bc := by
      simp [← hbc_len]
      omega
    -- the length-of-length write, regrouped with the header as one prefix
    have step1 : writeShift (outBytes.set 0 (BitVec.ofNat 8 (183 + bc))) 1 n bc
        = ([BitVec.ofNat 8 (183 + bc)] ++ Nat.toBytesBE n)
            ++ outBytes.drop (1 + bc) := by
      rw [writeShift_eq_append bc _ 1 n (by rw [hset_len]; omega),
          take_one_set_zero _ _ (by omega), drop_set_zero _ _ _ (by omega), hbs]
      simp
    -- the payload copy lands immediately after that prefix
    have step2 : (([BitVec.ofNat 8 (183 + bc)] ++ Nat.toBytesBE n)
          ++ outBytes.drop (1 + bc)).drop ((1 + bc) + n)
        = outBytes.drop ((1 + bc) + n) := by
      rw [← List.drop_drop, List.drop_left' hpre_len, List.drop_drop]
    rw [step1, copyN_eq_append _ _ _ _ _
        (by simp only [List.length_append, hpre_len, List.length_drop]; omega)
        (by omega),
      List.drop_zero, List.take_left' hpre_len,
      List.take_of_length_le (by omega), step2, hlen, henc, ← hbc_len]
    simp [List.append_assoc]
  -- ### the machine side
  -- front: [0]-[4], [13]-[14], [30]-[51]
  have hpro := rebPrologueNe1 srcPtr outPtr (BitVec.ofNat 64 n) v5 v6 v7 v28
    (ofNat_ne_one n (by omega) hn64)
  have hproF := cpsTripleWithin_frameR
    (((.x13 : Reg) ↦ᵣ cellPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     bytesRegion srcPtr data ** bytesRegion outPtr outBytes **
     (cellPtr ↦ₘ cellOld)) (by pcFree) hpro
  have hdisp := rebDispatchLong (BitVec.ofNat 64 n) (1 : Word)
    (by rw [hlenN]; exact hn56)
  have hdispF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
     ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x5 : Reg) ↦ᵣ srcPtr) ** ((.x7 : Reg) ↦ᵣ outPtr) **
     ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) **
     bytesRegion srcPtr data ** bytesRegion outPtr outBytes **
     (cellPtr ↦ₘ cellOld)) (by pcFree) hdisp
  have hlad := rebLadder (BitVec.ofNat 64 n) (56 : Word) v29
    (by rw [hlenN]; exact hn56)
  have hladF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
     ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x5 : Reg) ↦ᵣ srcPtr) ** ((.x7 : Reg) ↦ᵣ outPtr) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     bytesRegion srcPtr data ** bytesRegion outPtr outBytes **
     (cellPtr ↦ₘ cellOld)) (by pcFree) hlad
  have f1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hproF hdispF
  have f2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    f1 hladF
  -- middle: [52]-[63], for any x29 the ladder leaves behind
  have hmid := cpsTripleWithin_of_forall_regIs_to_regOwn (fun w29 =>
    reb_long_mid srcPtr outPtr cellPtr raVal cellOld w29 v30 v31 data outBytes n
      hn64 (by omega) hoalign (by omega)
      (fun k hk => hovalid k (by omega)))
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    f2 hmid
  -- tail: [64]-[75], for any x30 the loops leave behind
  have hdst_len : (writeShift (outBytes.set 0 (BitVec.ofNat 8 (183 + bc))) 1 n bc).length
      = outBytes.length := by
    rw [writeShift_length, List.length_set]
  have htl := cpsTripleWithin_of_forall_regIs_to_regOwn (fun w30 =>
    reb_long_tail2 srcPtr outPtr cellPtr raVal cellOld w30 data
      (writeShift (outBytes.set 0 (BitVec.ofNat 8 (183 + bc))) 1 n bc) n bc
      hn hn64 (by rw [hdst_len]; omega) hsalign hoalign hsover (by omega)
      hsvalid (fun k hk => hovalid ((1 + bc) + k) (by omega)))
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    c1 htl
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) c2)
  · unfold rebAbiPre at hp
    xperm_hyp hp
  · unfold rebAbiPost
    rw [← hregion, hlen]
    -- normalise hp's written-length words to match the post, leaving its
    -- cursor atoms untouched
    rw [long_cell_word bc n,
        show bc + 1 + n = (1 + bc) + n from by omega] at hp
    refine scratch7 (0 : Word) (BitVec.ofNat 64 n) outPtr cellPtr raVal
      (BitVec.ofNat 64 ((1 + bc) + n)) srcPtr data _
      ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n))
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n)
      ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 ((1 + bc) + n)))
      ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 bc)
      ((.x29 : Reg) ↦ᵣ (0 : Word))
      ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 ((1 + bc) + n))
      (regOwn .x31)
      (regIs_implies_regOwn .x5) (regIs_implies_regOwn .x6)
      (regIs_implies_regOwn .x7) (regIs_implies_regOwn .x28)
      (regIs_implies_regOwn .x29) (regIs_implies_regOwn .x30)
      (fun _ x => x) h ?_
    xperm_hyp hp

/-! ## §7  The whole-routine triple

    One `cpsTripleWithin` for `rlp_encode_bytes`, from `rebBase` to
    `ra &&& ~~~1`, covering **every** input: the routine is total, so unlike
    `rlp_encode_uint_be` there is no input-domain restriction — `n < 56` and
    `n ≥ 56` are both inside the claim, which is what "pin both sides of the
    55/56 boundary" demands.

    The preconditions are the ABI's documented ones: `n + 9` bytes of output
    capacity (`9 = 1 + 8`, the header plus the widest length-of-length),
    dword-aligned pointers, in-range windows, and the `a3` cell owned. -/

set_option maxRecDepth 8000 in
/-- **`rlp_encode_bytes` computes RLP.**  On any input, the routine returns
    status `a0 = 0`, leaves `encodeBytes data` at the front of the output
    buffer with the rest untouched, and writes the encoding's length to the
    `a3` cell — in at most `19 + 10*bc + 7*n` steps. -/
theorem reb_spec_within (srcPtr outPtr cellPtr raVal cellOld : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) (data outBytes : List Byte) (n : Nat)
    (hn : data.length = n) (hn64 : n < 2 ^ 64)
    (holen : n + 9 ≤ outBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64)
    (hoover : outPtr.toNat + (n + 9) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < n + 9 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (19 + 10 * u64ByteLen (BitVec.ofNat 64 n) + 7 * n)
      rebBase (raVal &&& ~~~1) rebCode
      (rebAbiPre srcPtr outPtr cellPtr raVal cellOld data outBytes n
        v5 v6 v7 v28 v29 v30 v31)
      (rebAbiPost srcPtr outPtr cellPtr raVal data outBytes n) := by
  have hbc8 : u64ByteLen (BitVec.ofNat 64 n) ≤ 8 := u64ByteLen_le _
  by_cases hraw : ∃ b : Byte, data = [b] ∧ b.toNat < 128
  · -- path A
    obtain ⟨b, hb, hsm⟩ := hraw
    have hn1 : n = 1 := by rw [← hn, hb]; rfl
    subst hn1
    exact cpsTripleWithin_mono_nSteps (by omega)
      (reb_spec_raw srcPtr outPtr cellPtr raVal cellOld v5 v6 v7 v28 v29 v30 v31
        data outBytes b hb hsm (by omega) hsalign hoalign (by omega) (by omega)
        (by have := hsvalid 0 (by omega)
            rwa [show srcPtr + BitVec.ofNat 64 0 = srcPtr from by bv_omega] at this)
        (by have := hovalid 0 (by omega)
            rwa [show outPtr + BitVec.ofNat 64 0 = outPtr from by bv_omega] at this))
  · have hnot_raw : ∀ b : Byte, data = [b] → ¬ b.toNat < 128 := by
      intro b hb hlt
      exact hraw ⟨b, hb, hlt⟩
    by_cases h56 : n < 56
    · -- path B
      exact cpsTripleWithin_mono_nSteps (by omega)
        (reb_spec_short srcPtr outPtr cellPtr raVal cellOld v5 v6 v7 v28 v29 v30 v31
          data outBytes n hn h56 hn64 hnot_raw (by omega) hsalign hoalign hsover
          (by omega) hsvalid (fun k hk => hovalid k (by omega)))
    · -- path C
      exact cpsTripleWithin_mono_nSteps (by omega)
        (reb_spec_long srcPtr outPtr cellPtr raVal cellOld v5 v6 v7 v28 v29 v30 v31
          data outBytes n hn (by omega) hn64 (by omega) hsalign hoalign hsover
          (by omega) hsvalid (fun k hk => hovalid k (by omega)))

/-! ## §8  The SpecRef-facing corollary

    `encodeBytes` is not merely "this repo's Lean port": it is **the function
    `SpecRef` itself calls** — `SpecRef/IncrementalMptWrite.lean` defines
    `encR i := EvmAsm.EL.RLP.encode i`, and `encode (.bytes d) = encodeBytes d`
    holds definitionally.  So the residual audit gap is `EL.RLP` versus the
    pinned Python, not this spec versus `SpecRef`.

    `rlpItemRegionFrom` states the output region over an `RLPItem` — the shared
    vocabulary — so a caller encoding a `SpecRef` struct field composes with
    this triple directly.  Deliberately **not** over a `SpecRef.Account` or
    similar: this routine encodes whatever bytes it is handed, and an assertion
    claiming the region "represents" a structure it never saw would be false. -/

/-- The region holds the RLP encoding of `item`, then `tailBytes`. -/
def rlpItemRegionFrom (base : Word) (item : RLPItem) (tailBytes : List Byte) :
    Assertion :=
  bytesRegion base (EvmAsm.EL.RLP.encode item ++ tailBytes)

/-- **The same claim over `RLPItem`** — `encode (.bytes data)` is
    `encodeBytes data` definitionally, so this is `reb_spec_within` with the
    output region phrased in the vocabulary `SpecRef`'s encoders use. -/
theorem reb_spec_rlpItem_within (srcPtr outPtr cellPtr raVal cellOld : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) (data outBytes : List Byte) (n : Nat)
    (hn : data.length = n) (hn64 : n < 2 ^ 64)
    (holen : n + 9 ≤ outBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64)
    (hoover : outPtr.toNat + (n + 9) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < n + 9 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (19 + 10 * u64ByteLen (BitVec.ofNat 64 n) + 7 * n)
      rebBase (raVal &&& ~~~1) rebCode
      (rebAbiPre srcPtr outPtr cellPtr raVal cellOld data outBytes n
        v5 v6 v7 v28 v29 v30 v31)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
       ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       bytesRegion srcPtr data **
       rlpItemRegionFrom outPtr (.bytes data)
         (outBytes.drop (EvmAsm.EL.RLP.encode (.bytes data)).length) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (EvmAsm.EL.RLP.encode (.bytes data)).length)) :=
  reb_spec_within srcPtr outPtr cellPtr raVal cellOld v5 v6 v7 v28 v29 v30 v31
    data outBytes n hn hn64 holen hsalign hoalign hsover hoover hsvalid hovalid

/-! ## §9  Path coverage

    Each `example`'s post names the **output bytes and the written length as
    literals** — not `encodeBytes data` — so it typechecks only if the composed
    triple really puts those bytes in the region and that length in the cell.
    A literal step bound proves nothing about which path ran (the #11040
    review's finding); content does.

    The boundary pair is the point: 55 bytes take the short header
    `0x80 + 55 = 0xb7`, and 56 take the long header `0xb8` with the one-byte
    length-of-length `0x38`.  `0xb7` is both the largest short header and the
    long-form base, so an off-by-one at the boundary produces a well-formed
    header of the *other* kind — which is why both sides are pinned.

    Checked with a negative control rather than assumed: swapping the `len=56`
    example's `0xb8` for `0xb7` fails to elaborate. -/

/-- `rebAbiPost` with the outputs as literals. -/
private def rebLiteralPost (srcPtr outPtr cellPtr raVal : Word)
    (data outBytes outLit : List Byte) (n cellLit : Nat) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
  ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
  ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  bytesRegion srcPtr data **
  bytesRegion outPtr (outLit ++ outBytes.drop outLit.length) **
  (cellPtr ↦ₘ BitVec.ofNat 64 cellLit)

/-- Convert the ABI post to a literal post from two `decide`-able equations —
    the boundary examples cannot go by definitional unfolding (reducing
    `encodeBytes` through a 55-element list exhausts the elaborator's fuel,
    and raising that budget is off-limits), but the kernel evaluates the
    equations instantly. -/
private theorem literal_of_abi (srcPtr outPtr cellPtr raVal : Word)
    (data outBytes outLit : List Byte) (n cellLit : Nat)
    (h1 : encodeBytes data = outLit) (h2 : outLit.length = cellLit) :
    rebAbiPost srcPtr outPtr cellPtr raVal data outBytes n
      = rebLiteralPost srcPtr outPtr cellPtr raVal data outBytes outLit n cellLit := by
  unfold rebAbiPost rebLiteralPost
  rw [h1, h2]

section PathCoverage

variable {srcPtr outPtr cellPtr raVal cellOld : Word}
  {v5 v6 v7 v28 v29 v30 v31 : Word} {outBytes : List Byte}

/-- Path A fires: a raw byte is its own encoding, one byte written. -/
example (holen : 1 + 9 ≤ outBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + 1 < 2 ^ 64)
    (hoover : outPtr.toNat + (1 + 9) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < 1 → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < 1 + 9 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 36 rebBase (raVal &&& ~~~1) rebCode
      (rebAbiPre srcPtr outPtr cellPtr raVal cellOld [0x2a] outBytes 1
        v5 v6 v7 v28 v29 v30 v31)
      (rebLiteralPost srcPtr outPtr cellPtr raVal [0x2a] outBytes [0x2a] 1 1) :=
  reb_spec_within srcPtr outPtr cellPtr raVal cellOld v5 v6 v7 v28 v29 v30 v31
    [0x2a] outBytes 1 (by decide) (by decide) holen hsalign hoalign hsover hoover
    hsvalid hovalid

/-- Path B fires at `len = 1` with a byte `≥ 0x80`: the `0x81` short header. -/
example (holen : 1 + 9 ≤ outBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + 1 < 2 ^ 64)
    (hoover : outPtr.toNat + (1 + 9) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < 1 → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < 1 + 9 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 36 rebBase (raVal &&& ~~~1) rebCode
      (rebAbiPre srcPtr outPtr cellPtr raVal cellOld [0x81] outBytes 1
        v5 v6 v7 v28 v29 v30 v31)
      (rebLiteralPost srcPtr outPtr cellPtr raVal [0x81] outBytes [0x81, 0x81] 1 2) :=
  reb_spec_within srcPtr outPtr cellPtr raVal cellOld v5 v6 v7 v28 v29 v30 v31
    [0x81] outBytes 1 (by decide) (by decide) holen hsalign hoalign hsover hoover
    hsvalid hovalid

/-- Path B fires at the boundary's short side: 55 bytes take header `0xb7`,
    56 bytes written. -/
example (holen : 55 + 9 ≤ outBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + 55 < 2 ^ 64)
    (hoover : outPtr.toNat + (55 + 9) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < 55 → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < 55 + 9 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 414 rebBase (raVal &&& ~~~1) rebCode
      (rebAbiPre srcPtr outPtr cellPtr raVal cellOld
        (List.replicate 55 (0x11 : Byte)) outBytes 55 v5 v6 v7 v28 v29 v30 v31)
      (rebLiteralPost srcPtr outPtr cellPtr raVal
        (List.replicate 55 (0x11 : Byte)) outBytes
        (0xb7 :: List.replicate 55 (0x11 : Byte)) 55 56) := by
  rw [← literal_of_abi srcPtr outPtr cellPtr raVal _ outBytes _ 55 56
    (by decide) (by decide)]
  exact reb_spec_within srcPtr outPtr cellPtr raVal cellOld v5 v6 v7 v28 v29 v30 v31
    (List.replicate 55 (0x11 : Byte)) outBytes 55 (by decide) (by decide)
    holen hsalign hoalign hsover hoover hsvalid hovalid

/-- Path C fires at the boundary's long side: 56 bytes take header `0xb8`,
    then the canonical one-byte length-of-length `0x38`, 58 bytes written. -/
example (holen : 56 + 9 ≤ outBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + 56 < 2 ^ 64)
    (hoover : outPtr.toNat + (56 + 9) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < 56 → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < 56 + 9 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 421 rebBase (raVal &&& ~~~1) rebCode
      (rebAbiPre srcPtr outPtr cellPtr raVal cellOld
        (List.replicate 56 (0x11 : Byte)) outBytes 56 v5 v6 v7 v28 v29 v30 v31)
      (rebLiteralPost srcPtr outPtr cellPtr raVal
        (List.replicate 56 (0x11 : Byte)) outBytes
        (0xb8 :: 0x38 :: List.replicate 56 (0x11 : Byte)) 56 58) := by
  -- `decide` cannot reduce `Nat.toBytesBE` (well-founded recursion), so the
  -- long form's literal goes through the equation lemmas instead
  have htb56 : Nat.toBytesBE 56 = [0x38] := by
    rw [show (56 : Nat) = 55 + 1 from rfl, Nat.toBytesBE_succ,
        show (55 + 1) / 256 = 0 from by norm_num, Nat.toBytesBE_zero]
    rfl
  have h1 : encodeBytes (List.replicate 56 (0x11 : Byte))
      = 0xb8 :: 0x38 :: List.replicate 56 (0x11 : Byte) := by
    rw [encodeBytes_long_of_length _ (by simp),
        show (List.replicate 56 (0x11 : Byte)).length = 56 from by simp, htb56]
    rfl
  rw [← literal_of_abi srcPtr outPtr cellPtr raVal _ outBytes _ 56 58
    h1 (by decide)]
  exact reb_spec_within srcPtr outPtr cellPtr raVal cellOld v5 v6 v7 v28 v29 v30 v31
    (List.replicate 56 (0x11 : Byte)) outBytes 56 (by decide) (by decide)
    holen hsalign hoalign hsover hoover hsvalid hovalid

end PathCoverage

end RlpEncodeBytesSAsm

end EvmAsm.Codegen
