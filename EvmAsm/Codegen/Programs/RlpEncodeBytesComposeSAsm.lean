/-
  EvmAsm.Codegen.Programs.RlpEncodeBytesComposeSAsm

  **The whole-routine triple for `rlp_encode_bytes`** (#10780 item 2, stage 3):
  the composition of the block theorems in `RlpEncodeBytesBlocksSAsm.lean` /
  `RlpEncodeBytesLadderSAsm.lean` into a single
  `cpsTripleWithin … rebBase (ra &&& ~~~1)`, and with it the first statement
  that the routine *computes RLP* rather than that its blocks do sixteen
  things.

  ## Both sides of 55/56, in one theorem

  The routine is **total** — `a0 = 0` always — and the composed triple covers
  every input length: the raw single byte, the `0x80 + len` short form for
  `len < 56`, and the `0xb7 + bc` long form for `len ≥ 56` with a canonical
  (minimal, no leading zero) length-of-length.  There is **no input-domain
  restriction**, unlike `rlp_encode_uint_be`'s `≤ 55` bound: covering the
  boundary from both sides is the point of the exercise.

  ## The three machine paths

  All three exit at `ra &&& ~~~1`, so the composition is a triple, not a
  branch.  Which one runs is decided by the data, so the proof splits on
  `data` *before* touching the machine:

  | path | condition | exit | steps |
  |---|---|---|---|
  | A | `data = [b]`, `b < 0x80` | [12] | 13 |
  | B | `len < 56`, not A | [29] | `16 + 7·len` (+3 if `len = 1`) |
  | C | `len ≥ 56` | [75] | `19 + 10·bc + 7·len` |

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.RlpEncodeBytesBlocksSAsm

namespace EvmAsm.Codegen

namespace RlpEncodeBytesSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
open EvmAsm.Rv64.RLP (copyN copyN_eq_append word_ofNat_add_one)
open EvmAsm.Codegen.RlpListEncodedSizeSAsm (u64ByteLen u64ByteLen_le)

/-! ## §1  The ABI-level pre and post

    Scratch registers are explicit values on the way in (matching the block
    theorems) and `regOwn` on the way out, because the three paths leave them
    holding different things.  Both outputs are in the post: the byte region at
    `a2` holds the encoding at the front with the remainder untouched, and the
    dword at `a3` holds the written length. -/

/-- Entry state: `a0` data ptr, `a1` length, `a2` out ptr, `a3` the u64-out
    cell, plus the seven registers the routine clobbers. -/
def rebAbiPre (srcPtr outPtr cellPtr raVal cellOld : Word)
    (data outBytes : List Byte) (n : Nat)
    (v5 v6 v7 v28 v29 v30 v31 : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
  ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
  ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
  ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
  ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
  bytesRegion srcPtr data ** bytesRegion outPtr outBytes **
  (cellPtr ↦ₘ cellOld)

/-- Exit state: status `a0 = 0` (total function), the output region beginning
    with `encodeBytes data` and otherwise untouched, the written length in the
    `a3` cell, and the source region unchanged. -/
def rebAbiPost (srcPtr outPtr cellPtr raVal : Word)
    (data outBytes : List Byte) (n : Nat) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
  ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
  ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  bytesRegion srcPtr data **
  bytesRegion outPtr (encodeBytes data ++ outBytes.drop (encodeBytes data).length) **
  (cellPtr ↦ₘ BitVec.ofNat 64 (encodeBytes data).length)

/-! ## §2  List bookkeeping (ports of item 1's compose lemmas) -/

/-- Writing one byte at the front of a nonempty buffer is `[b] ++ tail`. -/
private theorem set_zero_eq_append (out : List Byte) (b : Byte) (h : 0 < out.length) :
    out.set 0 b = [b] ++ out.drop 1 := by
  cases out with
  | nil => simp at h
  | cons a t => simp

/-- The header byte is the whole of the first cell after the set. -/
private theorem take_one_set_zero (out : List Byte) (b : Byte) (h : 0 < out.length) :
    (out.set 0 b).take 1 = [b] := by
  cases out with
  | nil => simp at h
  | cons a t => simp

/-- Everything from index 1 on survives the header write. -/
private theorem drop_set_zero (out : List Byte) (b : Byte) (k : Nat) (hk : 1 ≤ k) :
    (out.set 0 b).drop k = out.drop k := by
  cases out with
  | nil => simp
  | cons a t =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp

/-! ## §3  The scratch discharge, shared by all paths

    Each path exits with the seven clobbered registers in different states —
    some concrete, some already `regOwn` from a loop post — so the discharge is
    generic in an implication per register. -/

private theorem scratch7 (a0 nW outPtr cellPtr raVal cellVal : Word)
    (srcPtr : Word) (data newOut : List Byte)
    (A5 A6 A7 A28 A29 A30 A31 : Assertion)
    (h5 : ∀ h, A5 h → regOwn .x5 h) (h6 : ∀ h, A6 h → regOwn .x6 h)
    (h7 : ∀ h, A7 h → regOwn .x7 h) (h28 : ∀ h, A28 h → regOwn .x28 h)
    (h29 : ∀ h, A29 h → regOwn .x29 h) (h30 : ∀ h, A30 h → regOwn .x30 h)
    (h31 : ∀ h, A31 h → regOwn .x31 h) :
    ∀ h, (((.x10 : Reg) ↦ᵣ a0) ** ((.x11 : Reg) ↦ᵣ nW) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
      ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      A5 ** A6 ** A7 ** A28 ** A29 ** A30 ** A31 **
      bytesRegion srcPtr data ** bytesRegion outPtr newOut **
      (cellPtr ↦ₘ cellVal)) h →
    (((.x10 : Reg) ↦ᵣ a0) ** ((.x11 : Reg) ↦ᵣ nW) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
      ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion srcPtr data ** bytesRegion outPtr newOut **
      (cellPtr ↦ₘ cellVal)) h := by
  intro h hp
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono h5 (sepConj_mono h6 (sepConj_mono h7 (sepConj_mono h28
        (sepConj_mono h29 (sepConj_mono h30 (sepConj_mono h31
          (fun _ x => x))))))))))))) h hp

/-! ## §4  Path A — the raw single byte (`data = [b]`, `b < 0x80`) -/

set_option maxRecDepth 8000 in
/-- **Whole routine, raw byte**: `rebBase → ra &&& ~~~1` in 13 steps
    (prologue 5, probe 3, tail 5).  The byte is its own encoding. -/
theorem reb_spec_raw (srcPtr outPtr cellPtr raVal cellOld : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) (data outBytes : List Byte) (b : Byte)
    (hdata : data = [b]) (hsmall : b.toNat < 128)
    (holen : 0 < outBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat < 2 ^ 64) (hoover : outPtr.toNat < 2 ^ 64)
    (hsvalid : isValidByteAccess srcPtr = true)
    (hovalid : isValidByteAccess outPtr = true) :
    cpsTripleWithin 13 rebBase (raVal &&& ~~~1) rebCode
      (rebAbiPre srcPtr outPtr cellPtr raVal cellOld data outBytes 1
        v5 v6 v7 v28 v29 v30 v31)
      (rebAbiPost srcPtr outPtr cellPtr raVal data outBytes 1) := by
  subst hdata
  have henc : encodeBytes [b] = [b] := encodeBytes_single_small b hsmall
  have h0 : 0 < ([b] : List Byte).length := by simp
  have hb0 : ([b] : List Byte)[0]'h0 = b := rfl
  -- [0]-[4], len = 1
  have hpro := rebPrologueEq1 srcPtr outPtr (BitVec.ofNat 64 1) v5 v6 v7 v28
    (by decide)
  have hproF := cpsTripleWithin_frameR
    (((.x13 : Reg) ↦ᵣ cellPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     bytesRegion srcPtr [b] ** bytesRegion outPtr outBytes **
     (cellPtr ↦ₘ cellOld)) (by pcFree) hpro
  -- [5]-[7], byte below 0x80
  have hprobe := rebRawProbeSmall srcPtr v29 v30 [b] h0
    (by rw [hb0]; exact hsmall) hsalign hsover hsvalid
  rw [hb0] at hprobe
  have hprobeF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 1) **
     ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
     ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 1) ** ((.x7 : Reg) ↦ᵣ outPtr) **
     ((.x28 : Reg) ↦ᵣ (1 : Word)) ** ((.x31 : Reg) ↦ᵣ v31) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld)) (by pcFree) hprobe
  -- [8]-[12], the tail (x10 still holds srcPtr on entry)
  have htail := rebRawTail outPtr cellPtr raVal cellOld v31 srcPtr b outBytes
    holen hoalign hoover hovalid
  have htailF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 1) ** ((.x12 : Reg) ↦ᵣ outPtr) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ srcPtr) **
     ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 1) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x30 : Reg) ↦ᵣ (128 : Word)) ** bytesRegion srcPtr [b])
    (by pcFree) htail
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hproF hprobeF
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    s12 htailF
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) s123
  · unfold rebAbiPre at hp
    xperm_hyp hp
  · unfold rebAbiPost
    rw [henc, show ([b] : List Byte).length = 1 from rfl,
        ← set_zero_eq_append outBytes b holen,
        show BitVec.ofNat 64 1 = (1 : Word) from by decide]
    refine scratch7 (0 : Word) (BitVec.ofNat 64 1) outPtr cellPtr raVal (1 : Word)
      srcPtr [b] (outBytes.set 0 b)
      ((.x5 : Reg) ↦ᵣ srcPtr) ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 1)
      ((.x7 : Reg) ↦ᵣ outPtr) ((.x28 : Reg) ↦ᵣ (1 : Word))
      ((.x29 : Reg) ↦ᵣ b.zeroExtend 64) ((.x30 : Reg) ↦ᵣ (128 : Word))
      ((.x31 : Reg) ↦ᵣ (1 : Word))
      (regIs_implies_regOwn .x5) (regIs_implies_regOwn .x6)
      (regIs_implies_regOwn .x7) (regIs_implies_regOwn .x28)
      (regIs_implies_regOwn .x29) (regIs_implies_regOwn .x30)
      (regIs_implies_regOwn .x31) h ?_
    xperm_hyp hp

/-! ## §5  Path B — the short form (`len < 56`, not path A)

    Two routes reach the dispatch at `+52`: the `len ≠ 1` prologue exit, and the
    `len = 1, byte ≥ 0x80` probe exit.  They differ only in `x29`/`x30`, both
    overwritten downstream, so the tail from `+52` is proved once, universally
    quantified over those two registers, and each route instantiates it —
    item 1's technique.  This is sound because `rebAbiPost` returns the scratch
    registers as `regOwn`: no caller may rely on them, so the routes' different
    values need never be reconciled. -/

/-- Word-level bridges for the short path. -/
private theorem ofNat_toNat_eq (n : Nat) (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  omega

/-- The short header byte, tied to the model's `0x80 + len` form.
    Unconditional: `mod 2 ^ 64` and `mod 2 ^ 8` absorb the reductions. -/
private theorem short_hdr_byte (n : Nat) :
    (BitVec.ofNat 64 n + 128).truncate 8 = BitVec.ofNat 8 (128 + n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, show (128 : Word).toNat = 128 from by decide]
  omega

/-- `BNE`'s taken side needs the word form of `n ≠ 1`. -/
private theorem ofNat_ne_one (n : Nat) (hne : n ≠ 1) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ (1 : Word) := by
  intro hc
  have := congrArg BitVec.toNat hc
  rw [ofNat_toNat_eq n h, show (1 : Word).toNat = 1 from by decide] at this
  exact hne this

set_option maxRecDepth 8000 in
/-- The shared short-path tail: dispatch, header, copy loop, tail —
    `rebBase+52 → ra &&& ~~~1` in `11 + 7*n` steps, for any `x29`/`x30`. -/
private theorem reb_short_rest (srcPtr outPtr cellPtr raVal cellOld : Word)
    (w29 w30 v31 : Word) (data outBytes : List Byte) (n : Nat)
    (hn : data.length = n) (hn56 : n < 56) (hn64 : n < 2 ^ 64)
    (hnot_raw : ∀ b, data = [b] → ¬ b.toNat < 0x80)
    (holen : n + 1 ≤ outBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64)
    (hoover : outPtr.toNat + (n + 1) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < n + 1 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (11 + 7 * n) (rebBase + 52) (raVal &&& ~~~1) rebCode
      (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
       ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ srcPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x7 : Reg) ↦ᵣ outPtr) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
       ((.x29 : Reg) ↦ᵣ w29) ** ((.x30 : Reg) ↦ᵣ w30) **
       ((.x31 : Reg) ↦ᵣ v31) **
       bytesRegion srcPtr data ** bytesRegion outPtr outBytes **
       (cellPtr ↦ₘ cellOld))
      (rebAbiPost srcPtr outPtr cellPtr raVal data outBytes n) := by
  have hlenN : (BitVec.ofNat 64 n).toNat = n := ofNat_toNat_eq n hn64
  have haddr0 : srcPtr + BitVec.ofNat 64 0 = srcPtr := by bv_omega
  -- the model side
  have hout : encodeBytes data = BitVec.ofNat 8 (128 + n) :: data := by
    have h := rebOut_short_form data (by omega) hnot_raw
    rwa [hn] at h
  have hlen : (encodeBytes data).length = n + 1 := by
    rw [hout, List.length_cons, hn]
  -- the region the copy loop produces IS the encoding at the front
  have hregion : copyN (outBytes.set 0 (BitVec.ofNat 8 (128 + n))) data 1 0 n
      = encodeBytes data ++ outBytes.drop (encodeBytes data).length := by
    rw [copyN_eq_append _ _ _ _ _ (by rw [List.length_set]; omega) (by omega),
        take_one_set_zero _ _ (by omega), drop_set_zero _ _ _ (by omega),
        List.drop_zero, List.take_of_length_le (by omega), hlen, hout,
        show 1 + n = n + 1 from by omega]
    rfl
  -- [13]-[14]
  have hdisp := rebDispatchShort (BitVec.ofNat 64 n) (1 : Word) (by omega)
  have hdispF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
     ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x5 : Reg) ↦ᵣ srcPtr) ** ((.x7 : Reg) ↦ᵣ outPtr) **
     ((.x29 : Reg) ↦ᵣ w29) ** ((.x30 : Reg) ↦ᵣ w30) **
     ((.x31 : Reg) ↦ᵣ v31) **
     bytesRegion srcPtr data ** bytesRegion outPtr outBytes **
     (cellPtr ↦ₘ cellOld)) (by pcFree) hdisp
  -- [15]-[18]
  have hhdr := rebShortHeader outPtr (BitVec.ofNat 64 n) w29 outBytes
    (by omega) hoalign (by omega)
    (by have := hovalid 0 (by omega)
        rwa [show outPtr + BitVec.ofNat 64 0 = outPtr from by bv_omega] at this)
  rw [short_hdr_byte n] at hhdr
  have hhdrF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
     ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x5 : Reg) ↦ᵣ srcPtr) ** ((.x30 : Reg) ↦ᵣ w30) **
     ((.x31 : Reg) ↦ᵣ v31) **
     bytesRegion srcPtr data ** (cellPtr ↦ₘ cellOld)) (by pcFree) hhdr
  -- [19]-[25]
  have hloop := rebShortCopyLoop srcPtr outPtr ((BitVec.ofNat 64 n) + 128)
    data (outBytes.set 0 (BitVec.ofNat 8 (128 + n))) 0 1 n
    hsalign hoalign (by omega) (by rw [List.length_set]; omega)
    (by omega) (by omega) hn64
    (fun k hk => by have := hsvalid k hk; simpa using this)
    (fun k hk => by have := hovalid (1 + k) (by omega); simpa using this)
  rw [haddr0] at hloop
  simp only [Nat.zero_add] at hloop
  have hloopF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
     ((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x30 : Reg) ↦ᵣ w30) ** ((.x31 : Reg) ↦ᵣ v31) **
     (cellPtr ↦ₘ cellOld)) (by pcFree) hloop
  -- [26]-[29]
  have htail := rebShortTail cellPtr raVal cellOld (BitVec.ofNat 64 n) v31 srcPtr
  have htailF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x12 : Reg) ↦ᵣ outPtr) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
     ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 (1 + n))) **
     ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ w30) ** regOwn .x28 **
     bytesRegion srcPtr data **
     bytesRegion outPtr (copyN (outBytes.set 0 (BitVec.ofNat 8 (128 + n))) data 1 0 n))
    (by pcFree) htail
  -- chain and close
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hdispF hhdrF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    s1 hloopF
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    s2 htailF
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) s3)
  · xperm_hyp hp
  · unfold rebAbiPost
    rw [← hregion, hlen]
    refine scratch7 (0 : Word) (BitVec.ofNat 64 n) outPtr cellPtr raVal
      (BitVec.ofNat 64 (n + 1)) srcPtr data _
      ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n))
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n)
      ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 (1 + n)))
      (regOwn .x28)
      ((.x29 : Reg) ↦ᵣ (0 : Word)) ((.x30 : Reg) ↦ᵣ w30)
      ((.x31 : Reg) ↦ᵣ (BitVec.ofNat 64 (n + 1)))
      (regIs_implies_regOwn .x5) (regIs_implies_regOwn .x6)
      (regIs_implies_regOwn .x7) (fun _ x => x)
      (regIs_implies_regOwn .x29) (regIs_implies_regOwn .x30)
      (regIs_implies_regOwn .x31) h ?_
    rw [word_ofNat_add_one n]
    xperm_hyp hp

set_option maxRecDepth 8000 in
/-- **Whole routine, short form** (`len < 56`, not the raw-byte case):
    `rebBase → ra &&& ~~~1` in at most `19 + 7*n` steps.  The `len ≠ 1` route
    costs `16 + 7n`; the `len = 1, byte ≥ 0x80` route costs three more for the
    probe.  Both land in `reb_short_rest`. -/
theorem reb_spec_short (srcPtr outPtr cellPtr raVal cellOld : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) (data outBytes : List Byte) (n : Nat)
    (hn : data.length = n) (hn56 : n < 56) (hn64 : n < 2 ^ 64)
    (hnot_raw : ∀ b, data = [b] → ¬ b.toNat < 0x80)
    (holen : n + 1 ≤ outBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64)
    (hoover : outPtr.toNat + (n + 1) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < n + 1 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (19 + 7 * n) rebBase (raVal &&& ~~~1) rebCode
      (rebAbiPre srcPtr outPtr cellPtr raVal cellOld data outBytes n
        v5 v6 v7 v28 v29 v30 v31)
      (rebAbiPost srcPtr outPtr cellPtr raVal data outBytes n) := by
  have hrest := fun w29 w30 => reb_short_rest srcPtr outPtr cellPtr raVal cellOld
    w29 w30 v31 data outBytes n hn hn56 hn64 hnot_raw holen
    hsalign hoalign hsover hoover hsvalid hovalid
  by_cases h1 : n = 1
  · -- the `len = 1, byte ≥ 0x80` route: prologue falls through, probe jumps
    subst h1
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hn
    subst hb
    have h0 : 0 < ([b] : List Byte).length := by simp
    have hb0 : ([b] : List Byte)[0]'h0 = b := rfl
    have hpro := rebPrologueEq1 srcPtr outPtr (BitVec.ofNat 64 1) v5 v6 v7 v28
      (by decide)
    have hproF := cpsTripleWithin_frameR
      (((.x13 : Reg) ↦ᵣ cellPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       bytesRegion srcPtr [b] ** bytesRegion outPtr outBytes **
       (cellPtr ↦ₘ cellOld)) (by pcFree) hpro
    have hprobe := rebRawProbeLarge srcPtr v29 v30 [b] h0
      (by rw [hb0]; have := hnot_raw b rfl; omega)
      hsalign (by omega) (by
        have := hsvalid 0 (by omega)
        rwa [show srcPtr + BitVec.ofNat 64 0 = srcPtr from by bv_omega] at this)
    rw [hb0] at hprobe
    have hprobeF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 1) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
       ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 1) ** ((.x7 : Reg) ↦ᵣ outPtr) **
       ((.x28 : Reg) ↦ᵣ (1 : Word)) ** ((.x31 : Reg) ↦ᵣ v31) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld)) (by pcFree) hprobe
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
      hproF hprobeF
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
      s1 (hrest (b.zeroExtend 64) (128 : Word))
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) s2)
    unfold rebAbiPre at hp
    xperm_hyp hp
  · -- the `len ≠ 1` route: prologue jumps straight to the dispatch
    have hpro := rebPrologueNe1 srcPtr outPtr (BitVec.ofNat 64 n) v5 v6 v7 v28
      (ofNat_ne_one n h1 hn64)
    have hproF := cpsTripleWithin_frameR
      (((.x13 : Reg) ↦ᵣ cellPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       bytesRegion srcPtr data ** bytesRegion outPtr outBytes **
       (cellPtr ↦ₘ cellOld)) (by pcFree) hpro
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
      hproF (hrest v29 v30)
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) s1)
    unfold rebAbiPre at hp
    xperm_hyp hp

/-! ## §6  Path C — the long form (`len ≥ 56`)

    The longest chain: prologue, dispatch, the `bc` ladder, the long header,
    the length-of-length loop, the payload copy, the tail.  Three loop posts
    return a register as `regOwn` that the next block needs concrete, so the
    chain has three `∀ w` seams joined by
    `cpsTripleWithin_of_forall_regIs_to_regOwn` — each pre shaped with the
    quantified register as the OUTERMOST right factor, which is all that
    combinator can see. -/

/-- The long header byte, tied to the model's `0xb7 + lenlen` form.
    Unconditional. -/
private theorem long_hdr_byte (bc : Nat) :
    (BitVec.ofNat 64 bc + 183).truncate 8 = BitVec.ofNat 8 (183 + bc) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
    show (183 : Word).toNat = 183 from by decide]
  omega

/-- The written length in word form.  Unconditional. -/
private theorem long_cell_word (bc n : Nat) :
    BitVec.ofNat 64 bc + 1 + BitVec.ofNat 64 n = BitVec.ofNat 64 (bc + 1 + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    show (1 : Word).toNat = 1 from by decide]
  omega

set_option maxRecDepth 8000 in
/-- The long path from the copy loop on ([64]-[75]): `rebBase+256 → ra &&& ~~~1`
    in `7*n + 6` steps, for any incoming `x30`. -/
private theorem reb_long_tail2 (srcPtr outPtr cellPtr raVal cellOld w30 : Word)
    (data dst : List Byte) (n bc : Nat)
    (hn : data.length = n) (hn64 : n < 2 ^ 64)
    (hdlen : (1 + bc) + n ≤ dst.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64)
    (hoover : outPtr.toNat + ((1 + bc) + n) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < n → isValidByteAccess (outPtr + BitVec.ofNat 64 ((1 + bc) + k)) = true) :
    cpsTripleWithin (7 * n + 6) (rebBase + 256) (raVal &&& ~~~1) rebCode
      ((((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
        ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ srcPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 (1 + bc))) **
        ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 bc) **
        ((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** regOwn .x31 **
        bytesRegion srcPtr data ** bytesRegion outPtr dst **
        (cellPtr ↦ₘ cellOld)) ** ((.x30 : Reg) ↦ᵣ w30))
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
       ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
       ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 ((1 + bc) + n))) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 bc) ** ((.x29 : Reg) ↦ᵣ (0 : Word)) **
       ((.x30 : Reg) ↦ᵣ (BitVec.ofNat 64 bc + 1 + BitVec.ofNat 64 n)) **
       regOwn .x31 **
       bytesRegion srcPtr data **
       bytesRegion outPtr (copyN dst data (1 + bc) 0 n) **
       (cellPtr ↦ₘ (BitVec.ofNat 64 bc + 1 + BitVec.ofNat 64 n))) := by
  have haddr0 : srcPtr + BitVec.ofNat 64 0 = srcPtr := by bv_omega
  -- [64]-[70]
  have hloop := rebLongCopyLoop srcPtr outPtr w30 data dst 0 (1 + bc) n
    hsalign hoalign (by omega) hdlen (by omega) (by omega) hn64
    (fun k hk => by have := hsvalid k hk; simpa using this)
    (fun k hk => hovalid k hk)
  rw [haddr0] at hloop
  simp only [Nat.zero_add] at hloop
  have hloopF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
     ((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 bc) ** regOwn .x31 **
     (cellPtr ↦ₘ cellOld)) (by pcFree) hloop
  -- [71]-[75], for any x30 the copy loop leaves behind.  The instance type is
  -- stated in full: with it inferred, `xperm` runs against a metavariable and
  -- reports "LHS has 1 atom".
  have htail3i : ∀ w30' : Word, cpsTripleWithin 5 (rebBase + 284) (raVal &&& ~~~1)
      rebCode
      ((((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
        ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 ((1 + bc) + n))) **
        ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 bc) ** ((.x29 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x31 ** bytesRegion srcPtr data **
        bytesRegion outPtr (copyN dst data (1 + bc) 0 n) **
        (cellPtr ↦ₘ cellOld)) ** ((.x30 : Reg) ↦ᵣ w30'))
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
       ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
       ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 ((1 + bc) + n))) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 bc) ** ((.x29 : Reg) ↦ᵣ (0 : Word)) **
       ((.x30 : Reg) ↦ᵣ (BitVec.ofNat 64 bc + 1 + BitVec.ofNat 64 n)) **
       regOwn .x31 ** bytesRegion srcPtr data **
       bytesRegion outPtr (copyN dst data (1 + bc) 0 n) **
       (cellPtr ↦ₘ (BitVec.ofNat 64 bc + 1 + BitVec.ofNat 64 n))) := by
    intro w30'
    have ht := rebLongTail cellPtr raVal cellOld (BitVec.ofNat 64 bc)
      (BitVec.ofNat 64 n) w30' srcPtr
    have htF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x12 : Reg) ↦ᵣ outPtr) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
       ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 ((1 + bc) + n))) **
       ((.x29 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x31 **
       bytesRegion srcPtr data **
       bytesRegion outPtr (copyN dst data (1 + bc) 0 n)) (by pcFree) ht
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) htF
  have htail3 := cpsTripleWithin_of_forall_regIs_to_regOwn htail3i
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp1 := sepConj_mono_right (fun h' hp' => hp') h hp
      xperm_hyp hp1) hloopF htail3
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) s1
  · xperm_hyp hp
  · xperm_hyp hp

set_option maxRecDepth 8000 in
/-- The long path's middle: header, length-of-length loop, copy setup —
    `rebBase+208 → rebBase+256` in `7*bc + 6` steps, for any incoming `x29`. -/
private theorem reb_long_mid (srcPtr outPtr cellPtr raVal cellOld w29 v30 v31 : Word)
    (data outBytes : List Byte) (n : Nat)
    (hn64 : n < 2 ^ 64)
    (holen : 1 + u64ByteLen (BitVec.ofNat 64 n) ≤ outBytes.length)
    (hoalign : outPtr.toNat % 8 = 0)
    (hoover : outPtr.toNat + (1 + u64ByteLen (BitVec.ofNat 64 n)) ≤ 2 ^ 64)
    (hovalid : ∀ k, k < 1 + u64ByteLen (BitVec.ofNat 64 n) →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * u64ByteLen (BitVec.ofNat 64 n) + 6)
      (rebBase + 208) (rebBase + 256) rebCode
      ((((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
        ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ srcPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        ((.x7 : Reg) ↦ᵣ outPtr) **
        ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen (BitVec.ofNat 64 n))) **
        ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
        bytesRegion srcPtr data ** bytesRegion outPtr outBytes **
        (cellPtr ↦ₘ cellOld)) ** ((.x29 : Reg) ↦ᵣ w29))
      (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
       ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ srcPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 (1 + u64ByteLen (BitVec.ofNat 64 n)))) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen (BitVec.ofNat 64 n))) **
       ((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** regOwn .x30 ** regOwn .x31 **
       bytesRegion srcPtr data **
       bytesRegion outPtr
         (writeShift
           (outBytes.set 0 (BitVec.ofNat 8 (183 + u64ByteLen (BitVec.ofNat 64 n))))
           1 n (u64ByteLen (BitVec.ofNat 64 n))) **
       (cellPtr ↦ₘ cellOld)) := by
  set bc := u64ByteLen (BitVec.ofNat 64 n) with hbc
  have hlenN : (BitVec.ofNat 64 n).toNat = n := ofNat_toNat_eq n hn64
  -- [52]-[55]
  have hhdr := rebLongHeader outPtr (BitVec.ofNat 64 bc) w29 outBytes
    (by omega) hoalign (by omega)
    (by have := hovalid 0 (by omega)
        rwa [show outPtr + BitVec.ofNat 64 0 = outPtr from by bv_omega] at this)
  rw [long_hdr_byte bc] at hhdr
  have hhdrF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
     ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x5 : Reg) ↦ᵣ srcPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     bytesRegion srcPtr data ** (cellPtr ↦ₘ cellOld)) (by pcFree) hhdr
  -- [56]-[62]
  have hlol := rebLolLoop outPtr v30 v31 (BitVec.ofNat 64 n)
    (outBytes.set 0 (BitVec.ofNat 8 (183 + bc))) 1 bc
    (u64ByteLen_le _) hoalign (by rw [List.length_set]; omega) (by omega)
    (fun k hk => by have := hovalid (1 + k) (by omega); simpa using this)
  rw [hlenN] at hlol
  have hlolF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
     ((.x1 : Reg) ↦ᵣ raVal) **
     ((.x5 : Reg) ↦ᵣ srcPtr) **
     ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 bc) **
     bytesRegion srcPtr data ** (cellPtr ↦ₘ cellOld)) (by pcFree) hlol
  -- [63]
  have hsetup := rebLongCopySetup (BitVec.ofNat 64 n) (-1 : Word)
  have hsetupF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
     ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x5 : Reg) ↦ᵣ srcPtr) **
     ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 (1 + bc))) **
     ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 bc) ** regOwn .x30 ** regOwn .x31 **
     bytesRegion srcPtr data **
     bytesRegion outPtr
       (writeShift (outBytes.set 0 (BitVec.ofNat 8 (183 + bc))) 1 n bc) **
     (cellPtr ↦ₘ cellOld)) (by pcFree) hsetup
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hhdrF hlolF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    s1 hsetupF
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) s2)
  · xperm_hyp hp
  · xperm_hyp hp

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
