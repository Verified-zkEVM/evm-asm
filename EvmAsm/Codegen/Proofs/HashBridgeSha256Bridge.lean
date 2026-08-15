/-
  EvmAsm.Codegen.Proofs.HashBridgeSha256Bridge

  Pure bridge: operational `sha256BodyDigest` (guest Merkle–Damgård post of
  `zkvm_sha256_spec_within`) equals SpecRef `sha256`.

  Statement domain matches the machine triple:
    `input.length = 64 * N + rem` with `rem < 64`
  (both rem&lt;56 single final block and rem≥56 two-block pad arms).

  No machine edits. No Accel CSRS — pure byte/list/SHA algebra only.
  Reuses `chunkBytes` infrastructure from `HashBridgeKeccakBridge`.
-/

import EvmAsm.Codegen.Proofs.HashBridgeSha256Body
import EvmAsm.Codegen.Proofs.HashBridgeSha256OuterBody
import EvmAsm.Codegen.Proofs.HashBridgeSha256Rem
import EvmAsm.Codegen.Proofs.HashBridgeSha256Final
import EvmAsm.Codegen.Proofs.HashBridgeSha256Squeeze
import EvmAsm.Codegen.Proofs.HashBridgeKeccakBridge
import EvmAsm.Codegen.Proofs.HashBridgeKeccakPure
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Rv64.SAsm.RwSubwindow
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Stateless.SpecRef.Crypto
import EvmAsm.Evm64.EvmWord
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8000

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Accel
open EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef

private abbrev sha256BridgeBlockBytes : Nat := 64

/-! ## SpecRef block list for the first `k` full input blocks -/

def sha256AbsorbBlocks (input : List (BitVec 8)) (k : Nat) : List (List (BitVec 8)) :=
  chunkBytes sha256BridgeBlockBytes (input.take (sha256BridgeBlockBytes * k))

/-! ## u32 state ↔ 32-byte wire image -/

/-- Spec-side hash state as the eight u32 words stored in LE dwords. -/
def sha256StateWords (st : List (BitVec 8)) : List (BitVec 32) :=
  dwordsToU32s ((List.range 4).map fun i =>
    packBytes (st.drop (8 * i) |>.take 8))

/-- Pack u32 hash state to the 32-byte guest wire layout. -/
def sha256StateBytes (hs : List (BitVec 32)) : List (BitVec 8) :=
  (u32sToDwords hs).flatMap dwordBytes

theorem sha256StateBytes_sha256IV :
    sha256StateBytes sha256IV = sha256IvBytes := by
  simp only [sha256StateBytes, sha256IvBytes, sha256IV]

theorem sha256StateBytes_length (hs : List (BitVec 32)) (h8 : hs.length = 8) :
    (sha256StateBytes hs).length = 32 := by
  simp only [sha256StateBytes, length_flatMap_dwordBytes, length_u32sToDwords, h8]

private theorem sha256StateWords_eq_wsDwords (st : List (BitVec 8)) (hst : st.length = 32) :
    sha256StateWords st = dwordsToU32s (wsDwords 4 st 0) := by
  unfold sha256StateWords wsDwords wsDword
  simp only [Nat.zero_add]

theorem sha256StateWords_stateBytes (hs : List (BitVec 32)) (h8 : hs.length = 8) :
    sha256StateWords (sha256StateBytes hs) = hs := by
  have hst : (sha256StateBytes hs).length = 32 := sha256StateBytes_length hs h8
  rw [sha256StateWords_eq_wsDwords _ hst]
  unfold sha256StateBytes
  have hlen_u : (u32sToDwords hs).length = 4 := by rw [length_u32sToDwords, h8]
  have hws : wsDwords 4 ((u32sToDwords hs).flatMap dwordBytes) 0 = u32sToDwords hs := by
    have hfit : 0 + 8 * (u32sToDwords hs).length ≤
        ((u32sToDwords hs).flatMap dwordBytes).length := by
      rw [length_flatMap_dwordBytes]; omega
    have h := wsDwords_setBytes_flatMap (bs := (u32sToDwords hs).flatMap dwordBytes)
      (j := 0) (payload := u32sToDwords hs) hfit
    -- `setBytes bs 0 (payload.flatMap dwordBytes)` is `setBytes bs 0 bs`.
    simpa [hlen_u, setBytes_self] using h
  rw [hws, Accel.dwordsToU32s_u32sToDwords hs (by omega)]

/-! ## Block words: SpecRef `sha256BlockWords` ↔ machine BE dwords -/

def sha256BlockDwords (blk : List (BitVec 8)) : List Word :=
  (List.range 8).map fun i => packBytes (blk.drop (8 * i) |>.take 8)

def sha256BlockWordsMachine (blk : List (BitVec 8)) : List (BitVec 32) :=
  dwordsToU32sBE (sha256BlockDwords blk)

private theorem sha256BlockDwords_length (blk : List (BitVec 8)) (h : blk.length = 64) :
    (sha256BlockDwords blk).length = 8 := by
  simp [sha256BlockDwords, List.length_map, List.length_range, h]

private theorem sha256BlockWordsMachine_length (blk : List (BitVec 8)) (h : blk.length = 64) :
    (sha256BlockWordsMachine blk).length = 16 := by
  unfold sha256BlockWordsMachine sha256BlockDwords dwordsToU32sBE
  rw [length_dwordsToU32s]
  simp only [List.length_map, List.length_range, h]

private theorem bytesLEtoNat_four (b0 b1 b2 b3 : BitVec 8) :
    bytesLEtoNat [b0, b1, b2, b3] =
      b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat := by
  simp [bytesLEtoNat]; ring

private theorem bytesBEtoNat_four (b0 b1 b2 b3 : BitVec 8) :
    bytesBEtoNat [b0, b1, b2, b3] =
      b0.toNat * 256 ^ 3 + b1.toNat * 256 ^ 2 + b2.toNat * 256 + b3.toNat := by
  simp [bytesBEtoNat, EvmAsm.EL.RLP.Nat.fromBytesBE]; ring

private theorem bytesLEtoNat_four_mod256 (b0 b1 b2 b3 : BitVec 8) :
    (b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat) % 256 = b0.toNat := by
  have := b0.isLt; omega

private theorem bytesLEtoNat_four_div256_mod256 (b0 b1 b2 b3 : BitVec 8) :
    (b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat) / 256 % 256 = b1.toNat := by
  have := b0.isLt; have := b1.isLt; omega

private theorem bytesLEtoNat_four_div2562_mod256 (b0 b1 b2 b3 : BitVec 8) :
    (b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat) / 256 ^ 2 % 256 = b2.toNat := by
  have := b0.isLt; have := b1.isLt; have := b2.isLt; omega

private theorem bytesLEtoNat_four_div2563_mod256 (b0 b1 b2 b3 : BitVec 8) :
    (b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat) / 256 ^ 3 % 256 = b3.toNat := by
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt; omega

private theorem bytesLEtoNat_cons_expand (b0 b1 b2 b3 : BitVec 8)
    (rest : List (BitVec 8)) :
    bytesLEtoNat (b0 :: b1 :: b2 :: b3 :: rest) =
      bytesLEtoNat [b0, b1, b2, b3] + 256 ^ 4 * bytesLEtoNat rest := by
  simp [bytesLEtoNat_four, bytesLEtoNat]; ring

private theorem bytesLEtoNat_mod_pow4 (b0 b1 b2 b3 : BitVec 8)
    (rest : List (BitVec 8)) :
    bytesLEtoNat (b0 :: b1 :: b2 :: b3 :: rest) % 256 ^ 4 =
      bytesLEtoNat [b0, b1, b2, b3] := by
  have hb0 : b0.toNat < 256 := b0.isLt
  have hb1 : b1.toNat < 256 := b1.isLt
  have hb2 : b2.toNat < 256 := b2.isLt
  have hb3 : b3.toNat < 256 := b3.isLt
  rw [bytesLEtoNat_cons_expand, Nat.add_mul_mod_self_left]
  have hlt : bytesLEtoNat [b0, b1, b2, b3] < 256 ^ 4 := by
    rw [bytesLEtoNat_four]; omega
  exact Nat.mod_eq_of_lt hlt

private theorem list_length_eq_8_cases {α : Type _} (bs : List α) (h : bs.length = 8) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, bs = [a0, a1, a2, a3, a4, a5, a6, a7] := by
  revert h
  cases bs with
  | nil => intro h; simp at h
  | cons a0 bs1 =>
    cases bs1 with
    | nil => intro h; simp at h
    | cons a1 bs2 =>
      cases bs2 with
      | nil => intro h; simp at h
      | cons a2 bs3 =>
        cases bs3 with
        | nil => intro h; simp at h
        | cons a3 bs4 =>
          cases bs4 with
          | nil => intro h; simp at h
          | cons a4 bs5 =>
            cases bs5 with
            | nil => intro h; simp at h
            | cons a5 bs6 =>
              cases bs6 with
              | nil => intro h; simp at h
              | cons a6 bs7 =>
                cases bs7 with
                | nil => intro h; simp at h
                | cons a7 bs8 =>
                  cases bs8 with
                  | nil =>
                    intro h
                    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩
                  | cons _ _ =>
                    intro h
                    simp at h

private theorem setWidth32_packBytes_take4 (bs : List (BitVec 8)) (h : bs.length = 8) :
    ((packBytes bs).setWidth 32).toNat = bytesLEtoNat (bs.take 4) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := list_length_eq_8_cases bs h
  rw [BitVec.toNat_setWidth]
  have hpack := packBytes_toNat_of_length_8 [a0, a1, a2, a3, a4, a5, a6, a7] (by simp)
  have hlo : bytesLEtoNat [a0, a1, a2, a3] < 256 ^ 4 := by
    rw [bytesLEtoNat_four]; omega
  have h32 : bytesLEtoNat [a0, a1, a2, a3] < 2 ^ 32 := by omega
  rw [hpack, bytesLEtoNat_cons_expand, show 256 ^ 4 = 2 ^ 32 from by decide,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h32]
  simp only [List.take, bytesLEtoNat_four]

private theorem ushift32_packBytes_drop4 (bs : List (BitVec 8)) (h : bs.length = 8) :
    (((packBytes bs) >>> 32).setWidth 32).toNat = bytesLEtoNat (bs.drop 4) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := list_length_eq_8_cases bs h
  have hpack := packBytes_toNat_of_length_8 [a0, a1, a2, a3, a4, a5, a6, a7] (by simp)
  have hlo : bytesLEtoNat [a0, a1, a2, a3] < 2 ^ 32 := by rw [bytesLEtoNat_four]; omega
  have hhi : bytesLEtoNat [a4, a5, a6, a7] < 2 ^ 32 := by rw [bytesLEtoNat_four]; omega
  have hm : 0 < 2 ^ 32 := by decide
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hpack]
  rw [bytesLEtoNat_cons_expand, show 256 ^ 4 = 2 ^ 32 from by decide,
    Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hlo, Nat.zero_add, Nat.mod_eq_of_lt hhi]
  simp only [List.drop]

private theorem or_and_disjoint32 (a b c : BitVec 32) (h1 : a &&& c = 0#32) (h2 : b &&& c = 0#32) :
    (a ||| b) &&& c = 0#32 := by
  rw [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]

private theorem toNat_shift32_u32 (b : BitVec 32) (n : Nat) (hn : n + 8 ≤ 32) (hb : b.toNat < 256) :
    (b <<< n).toNat = b.toNat * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (by
    calc b.toNat * 2 ^ n < 256 * 2 ^ n := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos n)
      _ = 2 ^ (8 + n) := by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add]
      _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 8 + n ≤ 32))

private theorem shift32_disjoint (b c : BitVec 32) (mb mc : Nat)
    (hb : b.toNat < 256) (hc : c.toNat < 256) (hsep : mb + 8 ≤ mc) :
    (b <<< mc) &&& (c <<< mb) = 0#32 := by
  ext i
  have hi : i < 32 := by assumption
  simp only [BitVec.getElem_and, BitVec.getElem_zero, Bool.and_eq_false_iff]
  by_cases hmb : i < mb
  · exact Or.inr (by simp [BitVec.getElem_shiftLeft, hmb])
  · by_cases hmc : i < mc
    · exact Or.inl (by simp [BitVec.getElem_shiftLeft, hmc])
    · exact Or.inr (by
        simp only [BitVec.getElem_shiftLeft, hmb]
        rw [BitVec.getElem_eq_testBit_toNat]
        have hge : 8 ≤ i - mb := by omega
        have hbit : c.toNat < 2 ^ (i - mb) :=
          Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hge)
        exact Nat.testBit_lt_two_pow hbit)

private theorem toNat_or_shift32_u32 (x z : BitVec 32) (m : Nat)
    (hdisj : x &&& (z <<< m) = 0#32) (hsum : x.toNat + z.toNat * 2 ^ m < 2 ^ 32) :
    (x ||| (z <<< m)).toNat = x.toNat + z.toNat * 2 ^ m := by
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, BitVec.toNat_add_of_and_eq_zero hdisj]
  congr 1
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (by omega : z.toNat * 2 ^ m < 2 ^ 32)

private theorem byteSwap32_toNat_and_ff (x : BitVec 32) :
    ((x &&& (0x000000ff : BitVec 32)).toNat) = x.toNat % 256 := by
  rw [BitVec.toNat_and, show ((0x000000ff : BitVec 32)).toNat = 255 from by decide,
    show (255 : Nat) = 2 ^ 8 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]

private theorem byteSwap32_toNat_shift_byte (x : BitVec 32) (k : Nat) (hk : k < 4) :
    (((x >>> (8 * k)) &&& (0x000000ff : BitVec 32)).toNat) = x.toNat / 256 ^ k % 256 := by
  rcases Nat.eq_zero_or_pos k with rfl | _
  · rw [BitVec.ushiftRight_zero, Nat.pow_zero, Nat.div_one]
    exact byteSwap32_toNat_and_ff x
  · have hpow : 2 ^ (8 * k) = 256 ^ k := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show ((0x000000ff : BitVec 32)).toNat = 255 from by decide,
      show (255 : Nat) = 2 ^ 8 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod, hpow]

private theorem toNat_ushift8_and_ff_mod (x : BitVec 32) :
    (x.toNat >>> 8 &&& 255) = x.toNat / 256 % 256 := by
  rw [← BitVec.toNat_ushiftRight, show (255 : Nat) = ((0x000000ff : BitVec 32)).toNat from by decide,
    ← BitVec.toNat_and]
  simpa [Nat.pow_one] using byteSwap32_toNat_shift_byte x 1 (by decide)

private theorem toNat_ushift16_and_ff_mod (x : BitVec 32) :
    (x.toNat >>> 16 &&& 255) = x.toNat / 256 ^ 2 % 256 := by
  rw [← BitVec.toNat_ushiftRight, show (255 : Nat) = ((0x000000ff : BitVec 32)).toNat from by decide,
    ← BitVec.toNat_and]
  exact byteSwap32_toNat_shift_byte x 2 (by decide)

private theorem toNat_ushift24_and_ff_mod (x : BitVec 32) :
    (x.toNat >>> 24 &&& 255) = x.toNat / 256 ^ 3 % 256 := by
  rw [← BitVec.toNat_ushiftRight, show (255 : Nat) = ((0x000000ff : BitVec 32)).toNat from by decide,
    ← BitVec.toNat_and]
  exact byteSwap32_toNat_shift_byte x 3 (by decide)

private theorem byteSwap32_shl16_ushr8 (b : BitVec 32) (hb : b.toNat < 256) :
    ((b <<< 16) >>> 8) = (b <<< 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have h16 : b.toNat * 2 ^ 16 < 2 ^ 32 := by
    calc b.toNat * 2 ^ 16 < 256 * 2 ^ 16 := Nat.mul_lt_mul_of_pos_right hb (by decide)
      _ = 2 ^ 24 := by decide
      _ < 2 ^ 32 := by decide
  have h8 : b.toNat * 2 ^ 8 < 2 ^ 32 := by
    calc b.toNat * 2 ^ 8 < 256 * 2 ^ 8 := Nat.mul_lt_mul_of_pos_right hb (by decide)
      _ = 2 ^ 16 := by decide
      _ < 2 ^ 32 := by decide
  rw [Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt h8]
  omega

private theorem byteSwap32_shl24_ushr24 (b : BitVec 32) (hb : b.toNat < 256) :
    ((b <<< 24) >>> 24) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hlt : b.toNat * 2 ^ 24 < 2 ^ 32 := by
    have hstrict : b.toNat * 2 ^ 24 < 256 * 2 ^ 24 :=
      Nat.mul_lt_mul_of_pos_right hb (by decide)
    simpa [show (256 : Nat) * 2 ^ 24 = 2 ^ 32 from by decide] using hstrict
  rw [Nat.mod_eq_of_lt hlt]
  omega

private theorem byteSwap32_mask_ff00_eq (x : BitVec 32) :
    (x &&& (0x0000ff00 : BitVec 32)) = (((x >>> 8) &&& (0x000000ff : BitVec 32)) <<< 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i
  all_goals simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]

private theorem byteSwap32_mask_ff0000_eq (x : BitVec 32) :
    (x &&& (0x00ff0000 : BitVec 32)) = (((x >>> 16) &&& (0x000000ff : BitVec 32)) <<< 16) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i
  all_goals simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]

private theorem byteSwap32_mask_ff000000_eq (x : BitVec 32) :
    (x &&& (0xff000000 : BitVec 32)) = (((x >>> 24) &&& (0x000000ff : BitVec 32)) <<< 24) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i
  all_goals simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]

private theorem byteSwap32_mask_ff00_shl8 (x : BitVec 32) :
    ((x &&& (0x0000ff00 : BitVec 32)) <<< 8) = (((x >>> 8) &&& (0x000000ff : BitVec 32)) <<< 16) := by
  rw [byteSwap32_mask_ff00_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i
  all_goals simp [BitVec.getLsbD_shiftLeft]

private theorem byteSwap32_mask_ff0000_ushr8 (x : BitVec 32) :
    ((x &&& (0x00ff0000 : BitVec 32)) >>> 8) = (((x >>> 16) &&& (0x000000ff : BitVec 32)) <<< 8) := by
  have hb : (((x >>> 16) &&& (0x000000ff : BitVec 32)).toNat) < 256 := by
    rw [byteSwap32_toNat_shift_byte x 2 (by decide)]; exact Nat.mod_lt _ (by decide)
  calc ((x &&& (0x00ff0000 : BitVec 32)) >>> 8)
      = (((x >>> 16) &&& (0x000000ff : BitVec 32)) <<< 16) >>> 8 := by rw [byteSwap32_mask_ff0000_eq]
    _ = (((x >>> 16) &&& (0x000000ff : BitVec 32)) <<< 8) :=
      byteSwap32_shl16_ushr8 _ hb

private theorem byteSwap32_mask_ff000000_ushr24 (x : BitVec 32) :
    ((x &&& (0xff000000 : BitVec 32)) >>> 24) = ((x >>> 24) &&& (0x000000ff : BitVec 32)) := by
  have hb : (((x >>> 24) &&& (0x000000ff : BitVec 32)).toNat) < 256 := by
    rw [byteSwap32_toNat_shift_byte x 3 (by decide)]; exact Nat.mod_lt _ (by decide)
  calc ((x &&& (0xff000000 : BitVec 32)) >>> 24)
      = (((x >>> 24) &&& (0x000000ff : BitVec 32)) <<< 24) >>> 24 := by rw [byteSwap32_mask_ff000000_eq]
    _ = ((x >>> 24) &&& (0x000000ff : BitVec 32)) := byteSwap32_shl24_ushr24 _ hb

private theorem byteSwap32_toNat_or01 (b0 b1 : BitVec 32) (hb0 : b0.toNat < 256) (hb1 : b1.toNat < 256) :
    ((b0 <<< 24) ||| (b1 <<< 16)).toNat =
      b0.toNat * 256 ^ 3 + b1.toNat * 256 ^ 2 := by
  have hd : (b0 <<< 24) &&& (b1 <<< 16) = 0#32 :=
    shift32_disjoint b0 b1 16 24 hb0 hb1 (by decide)
  rw [toNat_or_shift32_u32 (b0 <<< 24) b1 16 hd (by
    rw [toNat_shift32_u32 b0 24 (by decide) hb0]; omega)]
  rw [toNat_shift32_u32 b0 24 (by decide) hb0]
  simp only [show (256 : Nat) ^ 3 = 2 ^ 24 from by decide, show (256 : Nat) ^ 2 = 2 ^ 16 from by decide]

private theorem byteSwap32_toNat_or012 (b0 b1 b2 : BitVec 32)
    (hb0 : b0.toNat < 256) (hb1 : b1.toNat < 256) (hb2 : b2.toNat < 256) :
    ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8)).toNat =
      b0.toNat * 256 ^ 3 + b1.toNat * 256 ^ 2 + b2.toNat * 256 := by
  have ht01 := byteSwap32_toNat_or01 b0 b1 hb0 hb1
  have hd : ((b0 <<< 24) ||| (b1 <<< 16)) &&& (b2 <<< 8) = 0#32 :=
    or_and_disjoint32 (b0 <<< 24) (b1 <<< 16) (b2 <<< 8)
      (shift32_disjoint b0 b2 8 24 hb0 hb2 (by decide))
      (shift32_disjoint b1 b2 8 16 hb1 hb2 (by decide))
  rw [toNat_or_shift32_u32 ((b0 <<< 24) ||| (b1 <<< 16)) b2 8 hd (by rw [ht01]; omega)]
  rw [ht01]
  simp only [show (256 : Nat) ^ 3 = 2 ^ 24 from by decide, show (256 : Nat) ^ 2 = 2 ^ 16 from by decide,
    show (256 : Nat) = 2 ^ 8 from by decide]

private theorem shift32_disjoint_zero (b c : BitVec 32) (mc : Nat)
    (hb : b.toNat < 256) (hc : c.toNat < 256) (hsep : 8 ≤ mc) :
    (b <<< mc) &&& c = 0#32 := by
  simpa [BitVec.shiftLeft_zero] using shift32_disjoint b c 0 mc hb hc hsep

private theorem byteSwap32_hd3_left (b0 b1 b3 : BitVec 32)
    (hlt0 : b0.toNat < 256) (hlt1 : b1.toNat < 256) (hlt3 : b3.toNat < 256) :
    ((b0 <<< 24) ||| (b1 <<< 16)) &&& b3 = 0#32 :=
  or_and_disjoint32 (b0 <<< 24) (b1 <<< 16) b3
    (shift32_disjoint_zero b0 b3 24 hlt0 hlt3 (by decide))
    (shift32_disjoint_zero b1 b3 16 hlt1 hlt3 (by decide))

private theorem byteSwap32_hd3 (b0 b1 b2 b3 : BitVec 32)
    (hlt0 : b0.toNat < 256) (hlt1 : b1.toNat < 256) (hlt2 : b2.toNat < 256) (hlt3 : b3.toNat < 256) :
    ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8)) &&& b3 = 0#32 :=
  or_and_disjoint32 ((b0 <<< 24) ||| (b1 <<< 16)) (b2 <<< 8) b3
    (byteSwap32_hd3_left b0 b1 b3 hlt0 hlt1 hlt3)
    (shift32_disjoint_zero b2 b3 8 hlt2 hlt3 (by decide))

private theorem byteSwap32_toNat (x : BitVec 32) :
    (byteSwap32 x).toNat =
      x.toNat % 256 * 256 ^ 3 + (x.toNat / 256) % 256 * 256 ^ 2 +
        (x.toNat / 256 ^ 2) % 256 * 256 + x.toNat / 256 ^ 3 % 256 := by
  unfold byteSwap32
  set b0 := ((x >>> 0) &&& (0x000000ff : BitVec 32)) with hb0
  set b1 := ((x >>> 8) &&& (0x000000ff : BitVec 32)) with hb1
  set b2 := ((x >>> 16) &&& (0x000000ff : BitVec 32)) with hb2
  set b3 := ((x >>> 24) &&& (0x000000ff : BitVec 32)) with hb3
  have hb0' : b0.toNat = x.toNat % 256 := by
    rw [hb0, byteSwap32_toNat_shift_byte x 0 (by decide), Nat.pow_zero, Nat.div_one]
  have hb1' : b1.toNat = x.toNat / 256 % 256 := by
    rw [hb1, byteSwap32_toNat_shift_byte x 1 (by decide), Nat.pow_one]
  have hb2' : b2.toNat = x.toNat / 256 ^ 2 % 256 := by rw [hb2, byteSwap32_toNat_shift_byte x 2 (by decide)]
  have hb3' : b3.toNat = x.toNat / 256 ^ 3 % 256 := by rw [hb3, byteSwap32_toNat_shift_byte x 3 (by decide)]
  have hlt0 : b0.toNat < 256 := by rw [hb0']; exact Nat.mod_lt _ (by decide)
  have hlt1 : b1.toNat < 256 := by rw [hb1']; exact Nat.mod_lt _ (by decide)
  have hlt2 : b2.toNat < 256 := by rw [hb2']; exact Nat.mod_lt _ (by decide)
  have hlt3 : b3.toNat < 256 := by rw [hb3']; exact Nat.mod_lt _ (by decide)
  rw [byteSwap32_mask_ff00_shl8, byteSwap32_mask_ff0000_ushr8, byteSwap32_mask_ff000000_ushr24]
  rw [show (x &&& 255) = b0 from by rw [hb0, BitVec.ushiftRight_zero x],
    show (x >>> 8 &&& 255) = b1 from by rw [← hb1],
    show (x >>> 16 &&& 255) = b2 from by rw [← hb2],
    show (x >>> 24 &&& 255) = b3 from by rw [← hb3]]
  have ht012 := byteSwap32_toNat_or012 b0 b1 b2 hlt0 hlt1 hlt2
  have hd3 := byteSwap32_hd3 b0 b1 b2 b3 hlt0 hlt1 hlt2 hlt3
  have hd3' : ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8)) &&& (b3 <<< 0) = 0#32 := by
    rw [BitVec.shiftLeft_zero]; exact hd3
  have hor : (b0 <<< 24 ||| b1 <<< 16 ||| b2 <<< 8 ||| b3) =
      ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8)) ||| (b3 <<< 0) := by
    simp [BitVec.shiftLeft_zero]
  rw [hor, toNat_or_shift32_u32 ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8)) b3 0 hd3'
      (by rw [ht012, hb3']; omega),
    ht012, hb0', hb1', hb2', hb3']
  ring

/-- Critical: `byteSwap32` of an LE-packed 4-byte Nat equals the BE word. -/
private theorem byteSwap32_of_bytesLE_eq_bytesBE (b0 b1 b2 b3 : BitVec 8) :
    byteSwap32 (BitVec.ofNat 32 (bytesLEtoNat [b0, b1, b2, b3])) =
      BitVec.ofNat 32 (bytesBEtoNat [b0, b1, b2, b3]) := by
  apply BitVec.eq_of_toNat_eq
  rw [byteSwap32_toNat, bytesLEtoNat_four, BitVec.toNat_ofNat]
  have hlt : bytesLEtoNat [b0, b1, b2, b3] < 2 ^ 32 := by rw [bytesLEtoNat_four]; omega
  have hlt' : b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat < 2 ^ 32 := by
    rw [← bytesLEtoNat_four]; exact hlt
  rw [Nat.mod_eq_of_lt hlt']
  rw [bytesLEtoNat_four_mod256, bytesLEtoNat_four_div256_mod256,
    bytesLEtoNat_four_div2562_mod256, bytesLEtoNat_four_div2563_mod256, bytesBEtoNat_four]
  have hbe : b0.toNat * 256 ^ 3 + b1.toNat * 256 ^ 2 + b2.toNat * 256 + b3.toNat < 2 ^ 32 := by
    have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt; omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbe]

private theorem byteSwap32_packBytes_lo (bs : List (BitVec 8)) (h : bs.length = 8) :
    byteSwap32 ((packBytes bs).setWidth 32) =
      BitVec.ofNat 32 (bytesBEtoNat (bs.take 4)) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := list_length_eq_8_cases bs h
  have h8 : ([a0, a1, a2, a3, a4, a5, a6, a7] : List (BitVec 8)).length = 8 := by simp
  have heq : (packBytes [a0, a1, a2, a3, a4, a5, a6, a7]).setWidth 32 =
      BitVec.ofNat 32 (bytesLEtoNat [a0, a1, a2, a3]) := by
    apply BitVec.eq_of_toNat_eq
    rw [setWidth32_packBytes_take4 _ h8, BitVec.toNat_ofNat]
    have hlt : bytesLEtoNat [a0, a1, a2, a3] < 2 ^ 32 := by rw [bytesLEtoNat_four]; omega
    simp only [Nat.mod_eq_of_lt hlt, List.take]
  rw [heq, byteSwap32_of_bytesLE_eq_bytesBE a0 a1 a2 a3]
  simp only [List.take]

private theorem byteSwap32_packBytes_hi (bs : List (BitVec 8)) (h : bs.length = 8) :
    byteSwap32 (((packBytes bs) >>> 32).setWidth 32) =
      BitVec.ofNat 32 (bytesBEtoNat ((bs.drop 4).take 4)) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := list_length_eq_8_cases bs h
  have h8 : ([a0, a1, a2, a3, a4, a5, a6, a7] : List (BitVec 8)).length = 8 := by simp
  have heq : ((packBytes [a0, a1, a2, a3, a4, a5, a6, a7]) >>> 32).setWidth 32 =
      BitVec.ofNat 32 (bytesLEtoNat [a4, a5, a6, a7]) := by
    apply BitVec.eq_of_toNat_eq
    rw [ushift32_packBytes_drop4 _ h8, BitVec.toNat_ofNat]
    have hlt : bytesLEtoNat [a4, a5, a6, a7] < 2 ^ 32 := by rw [bytesLEtoNat_four]; omega
    simp only [Nat.mod_eq_of_lt hlt, List.drop]
  rw [heq, byteSwap32_of_bytesLE_eq_bytesBE a4 a5 a6 a7]
  simp only [List.drop, List.take]

private theorem dwordBE_setWidth_lo (w : Word) :
    (dwordBE w).setWidth 32 = byteSwap32 (w.truncate 32) := by
  unfold dwordBE
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hnge := Nat.not_le_of_gt hi
  simp [BitVec.getLsbD_setWidth, hi, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.zeroExtend_eq_setWidth, hnge]

private theorem dwordBE_ushift_hi (w : Word) :
    ((dwordBE w) >>> 32).setWidth 32 = byteSwap32 ((w >>> 32).truncate 32) := by
  unfold dwordBE
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hlt : 32 + i < 64 := by omega
  have hnge : ¬(32 + i < 32) := by omega
  have hi64 : i < 64 := by omega
  simp [BitVec.getLsbD_setWidth, hi, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.zeroExtend_eq_setWidth, hlt, hnge, hi64]

private theorem dwordsToU32s_dwordBE_packBytes (bs : List (BitVec 8)) (hbs : bs.length = 8) :
    dwordsToU32s [dwordBE (packBytes bs)] =
      [BitVec.ofNat 32 (bytesBEtoNat (bs.take 4)),
       BitVec.ofNat 32 (bytesBEtoNat ((bs.drop 4).take 4))] := by
  show [((dwordBE (packBytes bs)).setWidth 32),
      (((dwordBE (packBytes bs)) >>> 32).setWidth 32)] = _
  rw [dwordBE_setWidth_lo, dwordBE_ushift_hi, byteSwap32_packBytes_lo bs hbs,
    byteSwap32_packBytes_hi bs hbs]

private theorem dwordsToU32s_cons (w : Word) (ws : List Word) :
    dwordsToU32s (w :: ws) = w.setWidth 32 :: (w >>> 32).setWidth 32 :: dwordsToU32s ws := by
  simp [dwordsToU32s]

private theorem dwordsToU32s_getElem (ws : List Word) (k : Nat) (hk : k < 2 * ws.length) :
    (dwordsToU32s ws)[k]'(by rw [length_dwordsToU32s]; exact hk) =
      if k % 2 = 0 then (ws[k / 2]'(by omega)).setWidth 32
      else ((ws[k / 2]'(by omega)) >>> 32).setWidth 32 := by
  induction ws generalizing k with
  | nil => simp at hk
  | cons w rest ih =>
    simp only [dwordsToU32s_cons]
    match k, hk with
    | 0, _ => simp
    | 1, _ => simp
    | (k+2), hk =>
      have hk' : k < 2 * rest.length := by simp [List.length_cons] at hk; omega
      have heq := ih k hk'
      have e1 : (k + 2) / 2 = k / 2 + 1 := by omega
      have e2 : (k + 2) % 2 = k % 2 := by omega
      simp only [List.getElem_cons_succ, e1, e2]
      exact heq

private theorem sha256BlockDwords_getElem (blk : List (BitVec 8)) (h : blk.length = 64)
    (i : Nat) (hi : i < 8) :
    (sha256BlockDwords blk)[i]'(by rw [sha256BlockDwords_length blk h]; exact hi) =
      packBytes (blk.drop (8 * i) |>.take 8) := by
  unfold sha256BlockDwords
  simp only [List.getElem_map, List.getElem_range]

private theorem sha256BlockWordsMachine_getElem (blk : List (BitVec 8)) (h : blk.length = 64)
    (j : Nat) (hj : j < 16) :
    (sha256BlockWordsMachine blk)[j]'(sha256BlockWordsMachine_length blk h ▸ hj) =
      BitVec.ofNat 32 (bytesBEtoNat ((blk.drop (4 * j)).take 4)) := by
  unfold sha256BlockWordsMachine dwordsToU32sBE
  have hlen8 : ((sha256BlockDwords blk).map dwordBE).length = 8 := by
    rw [List.length_map, sha256BlockDwords_length blk h]
  have hi8 : j / 2 < 8 := by omega
  have hk : j < 2 * ((sha256BlockDwords blk).map dwordBE).length := by rw [hlen8]; omega
  rw [dwordsToU32s_getElem _ j hk]
  have hmap : ((sha256BlockDwords blk).map dwordBE)[j / 2]'(by rw [hlen8]; exact hi8) =
      dwordBE ((sha256BlockDwords blk)[j / 2]'(by
        rw [sha256BlockDwords_length blk h]; exact hi8)) := by
    rw [List.getElem_map]
  have hbs : (sha256BlockDwords blk)[j / 2]'(by rw [sha256BlockDwords_length blk h]; exact hi8) =
      packBytes (blk.drop (8 * (j / 2)) |>.take 8) :=
    sha256BlockDwords_getElem blk h (j / 2) hi8
  have hblen : (blk.drop (8 * (j / 2)) |>.take 8).length = 8 := by
    simp only [List.length_take, List.length_drop, h]; omega
  by_cases hpar : j % 2 = 0
  · simp only [hpar, if_true, hmap, hbs]
    have hidx : 8 * (j / 2) = 4 * j := by omega
    rw [dwordBE_setWidth_lo, byteSwap32_packBytes_lo _ hblen, List.take_take, hidx,
      show min 4 8 = 4 from by decide]
  · simp only [hpar, if_false, hmap, hbs]
    have hidx : 8 * (j / 2) + 4 = 4 * j := by omega
    rw [dwordBE_ushift_hi, byteSwap32_packBytes_hi _ hblen, List.drop_take, List.drop_drop,
      show (8:Nat) - 4 = 4 from by decide, hidx, List.take_take,
      show min 4 4 = 4 from by decide]

/-- Machine block u32 view matches SpecRef big-endian 32-bit word extraction. -/
theorem sha256BlockWords_eq_machine (blk : List (BitVec 8)) (h : blk.length = 64) :
    sha256BlockWords blk = sha256BlockWordsMachine blk := by
  unfold sha256BlockWords
  apply List.ext_getElem
  · rw [sha256BlockWordsMachine_length blk h]; simp [List.length_map, List.length_range]
  · intro j hj _; simp only [List.getElem_map, List.getElem_range]
    rw [sha256BlockWordsMachine_getElem blk h j hj]

/-! ## One compression step -/

theorem sha256CompressBytes_eq_stateBytes
    (hs : List (BitVec 32)) (blk : List (BitVec 8))
    (h8 : hs.length = 8) (hblk : blk.length = 64) :
    sha256CompressBytes (sha256StateBytes hs) blk =
      sha256StateBytes (sha256Compress hs (sha256BlockWords blk)) := by
  have hst32 : (sha256StateBytes hs).length = 32 := sha256StateBytes_length hs h8
  have hhs : dwordsToU32s (wsDwords 4 (sha256StateBytes hs) 0) = hs := by
    rw [← sha256StateWords_eq_wsDwords _ hst32, sha256StateWords_stateBytes hs h8]
  have hw : dwordsToU32sBE (sha256BlockDwords blk) = sha256BlockWords blk := by
    simpa using (sha256BlockWords_eq_machine blk hblk).symm
  rw [sha256CompressBytes_eq_payload]
  suffices h :
      sha256CompressPayload (sha256StateBytes hs) blk =
        u32sToDwords (sha256Compress hs (sha256BlockWords blk)) by
    rw [h, sha256StateBytes]
  unfold sha256CompressPayload
  have hstD : (List.range 4).map (fun i =>
      packBytes ((sha256StateBytes hs).drop (8 * i) |>.take 8)) =
      wsDwords 4 (sha256StateBytes hs) 0 := by
    unfold wsDwords wsDword; simp [Nat.zero_add]
  have hblkD : (List.range 8).map (fun i =>
      packBytes (List.take 8 (List.drop (8 * i) blk))) = sha256BlockDwords blk := by
    unfold sha256BlockDwords; rfl
  simp only [hstD, hblkD, hhs, hw]

private theorem sha256Compress'_snoc (hs : List (BitVec 32)) (blk : List (BitVec 8))
    (rest : List (List (BitVec 8))) :
    sha256Compress' hs (blk :: rest) =
      sha256Compress' (sha256Compress hs (sha256BlockWords blk)) rest := rfl

private theorem sha256Compress'_nil (hs : List (BitVec 32)) :
    sha256Compress' hs [] = hs := rfl

private theorem sha256Compress'_append_singleton (hs : List (BitVec 32))
    (bs : List (List (BitVec 8))) (blk : List (BitVec 8)) :
    sha256Compress' hs (bs ++ [blk]) =
      sha256Compress (sha256Compress' hs bs) (sha256BlockWords blk) := by
  induction bs generalizing hs with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.cons_append, sha256Compress', ih]

private theorem sha256IV_length : sha256IV.length = 8 := by
  simp [sha256IV]

private theorem sha256Compress'_length (hs : List (BitVec 32)) (bs : List (List (BitVec 8)))
    (h8 : hs.length = 8) :
    (sha256Compress' hs bs).length = 8 := by
  induction bs generalizing hs with
  | nil => simpa [sha256Compress'] using h8
  | cons b rest ih =>
    simp only [sha256Compress']
    exact ih _ (sha256Compress_length hs (sha256BlockWords b) (by omega))

/-! ## N-block absorb prefix -/

/-- `chunkBytes n ys = [ys]` when `ys.length = n > 0`. -/
private theorem chunkBytes_singleton64 (ys : List (BitVec 8)) (hys : ys.length = 64) :
    chunkBytes 64 ys = [ys] := by
  have h := chunkBytes_cons 64 ys (by omega) (by omega)
  rw [h, List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega),
    chunkBytes_nil]

/-- Append one full 64-byte block onto an exact multiple-of-64 prefix. -/
private theorem chunkBytes_append_block64 (k : Nat) (xs ys : List (BitVec 8))
    (hxs : xs.length = 64 * k) (hys : ys.length = 64) :
    chunkBytes 64 (xs ++ ys) = chunkBytes 64 xs ++ [ys] := by
  induction k generalizing xs with
  | zero =>
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp only [List.nil_append, chunkBytes_nil]
    exact chunkBytes_singleton64 ys hys
  | succ k ih =>
    have hge : 64 ≤ xs.length := by omega
    have hcons := chunkBytes_cons 64 (xs ++ ys) (by omega) (by
      simp only [List.length_append, hxs, hys]; omega)
    rw [hcons, List.take_append_of_le_length hge, List.drop_append_of_le_length hge]
    have hrest : (xs.drop 64).length = 64 * k := by
      rw [List.length_drop, hxs]; omega
    rw [ih (xs.drop 64) hrest, chunkBytes_cons 64 xs (by omega) hge, List.cons_append]

private theorem sha256AbsorbBlocks_succ (input : List (BitVec 8)) (k : Nat)
    (hfit : 64 * (k + 1) ≤ input.length) :
    sha256AbsorbBlocks input (k + 1) =
      sha256AbsorbBlocks input k ++
        [(input.drop (64 * k)).take 64] := by
  unfold sha256AbsorbBlocks
  have hsplit : input.take (64 * (k + 1)) =
      input.take (64 * k) ++ (input.drop (64 * k)).take 64 := by
    have hsum : 64 * k + 64 = 64 * (k + 1) := by omega
    rw [← hsum, List.take_add]
  rw [hsplit]
  refine chunkBytes_append_block64 k (input.take (64 * k))
    ((input.drop (64 * k)).take 64) ?_ ?_
  · rw [List.length_take]; omega
  · rw [List.length_take, List.length_drop]; omega

theorem sha256AbsorbedState_eq_compress' (input : List (BitVec 8)) (N : Nat)
    (hfit : sha256BridgeBlockBytes * N ≤ input.length) :
    sha256AbsorbedState sha256IvBytes input N =
      sha256StateBytes
        (sha256Compress' sha256IV (sha256AbsorbBlocks input N)) := by
  induction N with
  | zero =>
    simp only [sha256AbsorbedState, sha256AbsorbBlocks]
    exact sha256StateBytes_sha256IV.symm
  | succ k ih =>
    have hfitk : 64 * k ≤ input.length := by
      simp only [sha256BridgeBlockBytes] at hfit ⊢; omega
    have hfit' : 64 * (k + 1) ≤ input.length := by
      simp only [sha256BridgeBlockBytes] at hfit; omega
    set blk := (input.drop (64 * k)).take 64
    have hblk : blk.length = 64 := by
      simp only [blk, List.length_take, List.length_drop]; omega
    have hsucc :
        sha256AbsorbedState sha256IvBytes input (k + 1) =
          sha256CompressBytes (sha256AbsorbedState sha256IvBytes input k)
            ((input.drop (64 * k)).take 64) :=
      sha256AbsorbedState_succ sha256IvBytes input k
    rw [hsucc, ih hfitk]
    have h8 : (sha256Compress' sha256IV (sha256AbsorbBlocks input k)).length = 8 :=
      sha256Compress'_length sha256IV _ sha256IV_length
    rw [sha256CompressBytes_eq_stateBytes _ blk h8 hblk]
    congr 1
    rw [sha256AbsorbBlocks_succ input k hfit']
    exact (sha256Compress'_append_singleton sha256IV (sha256AbsorbBlocks input k) blk).symm

/-! ## Pad suffix / final block(s) -/

private theorem length_mod_block (N rem : Nat) (hrem : rem < 64) :
    (64 * N + rem) % 64 = rem := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem]

private theorem sha256Pad_zeros_lt56 (N rem : Nat) (hrem : rem < 56) :
    (64 - ((64 * N + rem + 9) % 64)) % 64 = 64 - rem - 9 := by
  omega

private theorem natToBytesBE_length (width x : Nat) :
    (natToBytesBE width x).length = width := by
  simp [natToBytesBE]

private theorem sha256Residual_length (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) :
    (input.drop (64 * N)).length = rem := by
  rw [List.length_drop, hlen]; omega

private theorem sha256PadScratch_lt56_len (res : List (BitVec 8)) (rem : Nat)
    (hres : res.length = rem) (hrem : rem < 64) :
    (sha256PadScratch_lt56 res sha256ZeroScratch rem).length = 64 :=
  length_sha256PadScratch_lt56 res sha256ZeroScratch rem sha256ZeroScratch_length
    hrem (by rw [hres])

private theorem sha256PadScratch_lt56_getElem (res : List (BitVec 8)) (rem i : Nat)
    (hres : res.length = rem) (hrem : rem < 64) (hi : i < 64) :
    (sha256PadScratch_lt56 res sha256ZeroScratch rem)[i]'(by
        rw [sha256PadScratch_lt56_len res rem hres hrem]; exact hi) =
      if h : i < rem then res[i]'(by rw [hres]; exact h)
      else if h' : i = rem then (128 : BitVec 8)
      else (0 : BitVec 8) := by
  unfold sha256PadScratch_lt56 sha256RemPrefix
  simp only [sha256PadZeroed_eq_replicate sha256ZeroScratch sha256ZeroScratch_length]
  have htakeLen : (res.take rem).length = rem := by simp [List.length_take, hres]
  simp only [List.getElem_set]
  by_cases hset : rem = i
  · have hi_eq : i = rem := hset.symm
    simp [hi_eq]
  · by_cases hlt : i < rem
    · have hlt' : i < (res.take rem).length := by omega
      simp only [hset, ↓reduceIte, hlt, ↓reduceDIte]
      rw [List.getElem_append_left hlt', List.getElem_take]
    · have hge : (res.take rem).length ≤ i := by omega
      have hne : i ≠ rem := fun h => hset h.symm
      simp only [hset, ↓reduceIte, hlt, ↓reduceDIte, hne]
      rw [List.getElem_append_right hge]
      have hiDrop : i - (res.take rem).length < ((List.replicate 64 (0 : BitVec 8)).drop rem).length := by
        simp [List.length_drop, List.length_replicate, htakeLen]; omega
      rw [List.getElem_drop (xs := List.replicate 64 (0 : BitVec 8)) (i := rem)
          (j := i - (res.take rem).length) (h := hiDrop)]
      convert List.getElem_replicate (a := (0 : BitVec 8)) (n := 64) (i := i) hi
      · rw [htakeLen]; exact Nat.add_sub_of_le (Nat.le_of_not_gt hlt)

private theorem sha256BitlenBE_getElem_lt56 (scratch : List (BitVec 8)) (bitLen : Word)
    (i : Nat) (h : scratch.length = 64) (hi : i < 56) :
    (sha256BitlenBE scratch bitLen)[i]'(by
        rw [length_sha256BitlenBE scratch bitLen h]; omega) = scratch[i]'(by omega) := by
  unfold sha256BitlenBE
  interval_cases i <;> simp [List.getElem_set, h]

private theorem sha256BitlenBE_getElem_ge56 (scratch : List (BitVec 8)) (bitLen : Word)
    (i : Nat) (h : scratch.length = 64) (hi : 56 ≤ i) (hi' : i < 64) :
    (sha256BitlenBE scratch bitLen)[i]'(by
        rw [length_sha256BitlenBE scratch bitLen h]; exact hi') =
      ((bitLen >>> (8 * (63 - i))).truncate 8) := by
  unfold sha256BitlenBE
  interval_cases i <;> simp [List.getElem_set, h, ne_eq, BitVec.ushiftRight_eq]

private theorem natToBytesBE8_getElem (x k : Nat) (hk : k < 8) :
    (natToBytesBE 8 x)[k]'(by rw [natToBytesBE_length]; exact hk) =
      BitVec.ofNat 8 (x >>> (8 * (7 - k))) := by
  simp only [natToBytesBE, List.getElem_map, List.getElem_reverse, List.length_range,
    List.getElem_range]

private theorem sha256Pad_drop_suffix_lt56 (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : rem < 56) :
    (sha256Pad input).drop (64 * N) =
      (input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
        List.replicate (64 - rem - 9) (0 : BitVec 8) ++
          natToBytesBE 8 ((64 * N + rem) * 8) := by
  unfold sha256Pad
  simp only [hlen]
  rw [sha256Pad_zeros_lt56 N rem hrem]
  have happ :
      input ++ [(0x80 : BitVec 8)] ++ List.replicate (64 - rem - 9) (0 : BitVec 8) ++
          natToBytesBE 8 ((64 * N + rem) * 8) =
        input ++ ([(0x80 : BitVec 8)] ++ List.replicate (64 - rem - 9) (0 : BitVec 8) ++
          natToBytesBE 8 ((64 * N + rem) * 8)) := by
    simp only [List.append_assoc]
  rw [happ, List.drop_append_of_le_length (by omega)]
  simp only [List.append_assoc]

private theorem natToBytesBE8_shift_mod (x k : Nat) (hk : k < 8) :
    BitVec.ofNat 8 (x >>> (8 * (7 - k))) =
      BitVec.ofNat 8 ((x % 2 ^ 64) >>> (8 * (7 - k))) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  interval_cases k <;> omega

/-- SpecRef final 64-byte block for rem &lt; 56 (pad + bitlen in one block). -/
def sha256LastBlock_lt56 (input : List (BitVec 8)) (N rem : Nat) (bitLen : Word) :
    List (BitVec 8) :=
  sha256FinalBlock_lt56 (input.drop (64 * N)) rem bitLen

/-- SpecRef penultimate block for rem ≥ 56 (partial pad, no bitlen). -/
def sha256PenultimateBlock_ge56 (input : List (BitVec 8)) (N rem : Nat) :
    List (BitVec 8) :=
  sha256PadScratch_lt56 (input.drop (64 * N)) sha256ZeroScratch rem

/-- SpecRef final block for rem ≥ 56 (zeroed scratch + bitlen). -/
def sha256LastBlock_ge56 (input : List (BitVec 8)) (N rem : Nat) (bitLen : Word) :
    List (BitVec 8) :=
  sha256FinalBlock_ge56 (input.drop (64 * N)) rem bitLen

theorem sha256LastBlock_lt56_length (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : rem < 56) :
    (sha256LastBlock_lt56 input N rem (sha256BitLenW N rem)).length = 64 := by
  simp only [sha256LastBlock_lt56, sha256FinalBlock_lt56]
  exact length_sha256BitlenBE _ _ (length_sha256PadScratch_lt56 _ _ rem
    sha256ZeroScratch_length (by omega) (by rw [List.length_drop, hlen]; omega))

private theorem sha256LastBlock_lt56_getElem (input : List (BitVec 8)) (N rem i : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : rem < 56) (hi : i < 64) :
    (sha256LastBlock_lt56 input N rem (sha256BitLenW N rem))[i]'(by
        rw [sha256LastBlock_lt56_length input N rem hlen hrem]; exact hi) =
      if h : i < rem then (input.drop (64 * N))[i]'(by
          rw [sha256Residual_length input N rem hlen]; exact h)
      else if h' : i = rem then (0x80 : BitVec 8)
      else if hi56 : i < 56 then (0 : BitVec 8)
      else (natToBytesBE 8 ((64 * N + rem) * 8))[i - 56]'(by
          rw [natToBytesBE_length]; omega) := by
  unfold sha256LastBlock_lt56 sha256FinalBlock_lt56
  have hres : (input.drop (64 * N)).length = rem :=
    sha256Residual_length input N rem hlen
  have hscratch :
      (sha256PadScratch_lt56 (input.drop (64 * N)) sha256ZeroScratch rem).length = 64 :=
    sha256PadScratch_lt56_len _ rem hres (by omega)
  by_cases hi56 : i < 56
  · refine Eq.trans (sha256BitlenBE_getElem_lt56 _ (sha256BitLenW N rem) i hscratch hi56) ?_
    refine Eq.trans (sha256PadScratch_lt56_getElem _ rem i hres (by omega) hi) ?_
    by_cases h : i < rem
    · simp [h]
    · by_cases h' : i = rem
      · simp [h, h']
      · simp [h, h', hi56]
  · have hiGe : 56 ≤ i := Nat.le_of_not_gt hi56
    refine Eq.trans (sha256BitlenBE_getElem_ge56 _ (sha256BitLenW N rem) i hscratch hiGe hi) ?_
    have hj : i - 56 < 8 := by omega
    have hshift : 8 * (63 - i) = 8 * (7 - (i - 56)) := by omega
    simp only [hshift]
    refine Eq.trans (sha256BitLenW_shift_byte N rem (i - 56) hj) ?_
    refine Eq.trans (natToBytesBE8_shift_mod ((64 * N + rem) * 8) (i - 56) hj).symm ?_
    refine Eq.trans (natToBytesBE8_getElem ((64 * N + rem) * 8) (i - 56) hj).symm ?_
    have hrem_lt : ¬ i < rem := by omega
    have hne : i ≠ rem := by omega
    simp [hrem_lt, hne, hi56]

private theorem sha256PadSuffix_lt56_getElem (input : List (BitVec 8)) (N rem i : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : rem < 56) (hi : i < 64) :
    ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
        List.replicate (64 - rem - 9) (0 : BitVec 8) ++
          natToBytesBE 8 ((64 * N + rem) * 8))[i]'(by
        rw [List.length_append, List.length_append, List.length_append, List.length_singleton,
          sha256Residual_length input N rem hlen, List.length_replicate, natToBytesBE_length]
        omega) =
      if h : i < rem then (input.drop (64 * N))[i]'(by
          rw [sha256Residual_length input N rem hlen]; exact h)
      else if h' : i = rem then (0x80 : BitVec 8)
      else if hi56 : i < 56 then (0 : BitVec 8)
      else (natToBytesBE 8 ((64 * N + rem) * 8))[i - 56]'(by
          rw [natToBytesBE_length]; omega) := by
  have hres : (input.drop (64 * N)).length = rem :=
    sha256Residual_length input N rem hlen
  have hmid : ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]).length = rem + 1 := by
    simp [List.length_append, List.length_singleton, hres]
  have hpre :
      (((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]) ++
        List.replicate (64 - rem - 9) (0 : BitVec 8)).length = 56 := by
    simp [List.length_append, List.length_singleton, List.length_replicate, hres]; omega
  by_cases h : i < rem
  · have h1 : i < (((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]) ++
        List.replicate (64 - rem - 9) (0 : BitVec 8)).length := by omega
    have h2 : i < ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]).length := by omega
    have h3 : i < (input.drop (64 * N)).length := by omega
    simp only [h, ↓reduceDIte]
    rw [List.getElem_append_left h1, List.getElem_append_left h2, List.getElem_append_left h3]
  · by_cases h' : i = rem
    · have h1 : i < (((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]) ++
          List.replicate (64 - rem - 9) (0 : BitVec 8)).length := by omega
      have h2 : i < ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]).length := by omega
      have hge : (input.drop (64 * N)).length ≤ i := by omega
      have hRHS :
          (if h : i < rem then (input.drop (64 * N))[i]'(by rw [hres]; exact h)
            else if h' : i = rem then (0x80 : BitVec 8)
            else if hi56 : i < 56 then (0 : BitVec 8)
            else (natToBytesBE 8 ((64 * N + rem) * 8))[i - 56]'(by
                rw [natToBytesBE_length]; omega)) = (0x80 : BitVec 8) := by
        simp [h, h']
      rw [hRHS]
      rw [List.getElem_append_left h1, List.getElem_append_left h2, List.getElem_append_right hge]
      have hidx : i - (input.drop (64 * N)).length = 0 := by omega
      simp [hidx, List.getElem_singleton]
    · by_cases hi56 : i < 56
      · have h1 : i < (((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]) ++
            List.replicate (64 - rem - 9) (0 : BitVec 8)).length := by omega
        have hge : ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]).length ≤ i := by omega
        simp only [h, ↓reduceDIte, h', ↓reduceDIte, hi56, ↓reduceDIte]
        rw [List.getElem_append_left h1, List.getElem_append_right hge]
        simp only [hmid]
        have hz : i - (rem + 1) < (List.replicate (64 - rem - 9) (0 : BitVec 8)).length := by
          simp [List.length_replicate]; omega
        exact List.getElem_replicate (a := (0 : BitVec 8)) (n := 64 - rem - 9)
          (i := i - (rem + 1)) hz
      · have hge :
            (((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]) ++
              List.replicate (64 - rem - 9) (0 : BitVec 8)).length ≤ i := by omega
        simp only [h, ↓reduceDIte, h', ↓reduceDIte, hi56]
        rw [List.getElem_append_right hge]
        simp only [hpre]

theorem sha256PenultimateBlock_ge56_length (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    (sha256PenultimateBlock_ge56 input N rem).length = 64 := by
  simp only [sha256PenultimateBlock_ge56]
  exact length_sha256PadScratch_lt56 _ sha256ZeroScratch rem sha256ZeroScratch_length
    hrem64 (by rw [List.length_drop, hlen]; omega)

theorem sha256LastBlock_ge56_length (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    (sha256LastBlock_ge56 input N rem (sha256BitLenW N rem)).length = 64 := by
  simp only [sha256LastBlock_ge56, sha256FinalBlock_ge56]
  exact length_sha256BitlenBE _ _ (length_sha256PadScratch_ge56 _ sha256ZeroScratch rem
    sha256ZeroScratch_length hrem64 (by rw [List.length_drop, hlen]; omega))

theorem sha256LastBlock_lt56_eq_pad_drop (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : rem < 56) :
    (sha256Pad input).drop (64 * N) =
      sha256LastBlock_lt56 input N rem (sha256BitLenW N rem) := by
  rw [sha256Pad_drop_suffix_lt56 input N rem hlen hrem]
  refine List.ext_getElem ?_ ?_
  · have hL := sha256LastBlock_lt56_length input N rem hlen hrem
    rw [List.length_append, List.length_append, List.length_append, List.length_singleton,
      sha256Residual_length input N rem hlen, List.length_replicate, natToBytesBE_length, hL]
    omega
  · intro i h₁ h₂
    have hi : i < 64 := by
      rw [sha256LastBlock_lt56_length input N rem hlen hrem] at h₂; exact h₂
    rw [sha256PadSuffix_lt56_getElem input N rem i hlen hrem hi,
      sha256LastBlock_lt56_getElem input N rem i hlen hrem hi]

theorem sha256Pad_chunks_split_lt56 (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : rem < 56) :
    chunkBytes 64 (sha256Pad input) =
      sha256AbsorbBlocks input N ++
        [sha256LastBlock_lt56 input N rem (sha256BitLenW N rem)] := by
  have htake : (sha256Pad input).take (64 * N) = input.take (64 * N) := by
    have hle : 64 * N ≤ input.length := by rw [hlen]; omega
    simp only [sha256Pad, hlen]
    have happ :
        input ++ [(0x80 : BitVec 8)] ++
            List.replicate ((64 - ((64 * N + rem + 9) % 64)) % 64) (0 : BitVec 8) ++
              natToBytesBE 8 ((64 * N + rem) * 8) =
          input ++ ([(0x80 : BitVec 8)] ++
            List.replicate ((64 - ((64 * N + rem + 9) % 64)) % 64) (0 : BitVec 8) ++
              natToBytesBE 8 ((64 * N + rem) * 8)) := by
      simp only [List.append_assoc]
    rw [happ]
    exact List.take_append_of_le_length hle
  have hdrop := sha256LastBlock_lt56_eq_pad_drop input N rem hlen hrem
  have hsplit : sha256Pad input =
      (sha256Pad input).take (64 * N) ++
        (sha256Pad input).drop (64 * N) :=
    (List.take_append_drop (64 * N) (sha256Pad input)).symm
  conv_lhs => rw [hsplit, htake, hdrop]
  unfold sha256AbsorbBlocks
  simp only [sha256BridgeBlockBytes]
  refine chunkBytes_append_block64 N (input.take (64 * N))
    (sha256LastBlock_lt56 input N rem (sha256BitLenW N rem)) ?_ ?_
  · rw [List.length_take, hlen, min_eq_left (by omega)]
  · exact sha256LastBlock_lt56_length input N rem hlen hrem

private theorem sha256Pad_zeros_ge56 (N rem : Nat) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    (64 - ((64 * N + rem + 9) % 64)) % 64 = 119 - rem := by
  have hlt : rem + 9 - 64 < 64 := by omega
  have hmod : (64 * N + rem + 9) % 64 = rem + 9 - 64 := by
    have hrew : 64 * N + rem + 9 = (rem + 9 - 64) + 64 * (N + 1) := by omega
    rw [hrew]
    -- (r + 64 * k) % 64 = r % 64  via add_mul_mod_self_left (a:=r) (b:=64) (n:=k)
    have hmod' := Nat.add_mul_mod_self_left (rem + 9 - 64) 64 (N + 1)
    rw [hmod', Nat.mod_eq_of_lt hlt]
  rw [hmod]
  have : 64 - (rem + 9 - 64) = 119 - rem := by omega
  rw [this, Nat.mod_eq_of_lt (by omega)]

private theorem sha256Pad_drop_suffix_ge56 (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    (sha256Pad input).drop (64 * N) =
      (input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
        List.replicate (119 - rem) (0 : BitVec 8) ++
          natToBytesBE 8 ((64 * N + rem) * 8) := by
  unfold sha256Pad
  simp only [hlen]
  rw [sha256Pad_zeros_ge56 N rem hrem hrem64]
  have happ :
      input ++ [(0x80 : BitVec 8)] ++ List.replicate (119 - rem) (0 : BitVec 8) ++
          natToBytesBE 8 ((64 * N + rem) * 8) =
        input ++ ([(0x80 : BitVec 8)] ++ List.replicate (119 - rem) (0 : BitVec 8) ++
          natToBytesBE 8 ((64 * N + rem) * 8)) := by
    simp only [List.append_assoc]
  rw [happ, List.drop_append_of_le_length (by omega)]
  simp only [List.append_assoc]

/-- SpecRef first pad block as residual ‖ 0x80 ‖ zeros (no bitlen). -/
private theorem sha256Penultimate_as_prefix (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
        List.replicate (119 - rem) (0 : BitVec 8) ++
          natToBytesBE 8 ((64 * N + rem) * 8)).take 64 =
      (input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
        List.replicate (64 - rem - 1) (0 : BitVec 8) := by
  have hres : (input.drop (64 * N)).length = rem :=
    sha256Residual_length input N rem hlen
  have hz : List.replicate (119 - rem) (0 : BitVec 8) =
      List.replicate (64 - rem - 1) (0 : BitVec 8) ++
        List.replicate 56 (0 : BitVec 8) := by
    have hsum : (64 - rem - 1) + 56 = 119 - rem := by omega
    rw [← hsum, List.replicate_append_replicate]
  rw [hz]
  change
    ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
        (List.replicate (64 - rem - 1) (0 : BitVec 8) ++
          List.replicate 56 (0 : BitVec 8)) ++
          natToBytesBE 8 ((64 * N + rem) * 8)).take 64 =
      (input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
        List.replicate (64 - rem - 1) (0 : BitVec 8)
  have hassoc :
      (input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
          (List.replicate (64 - rem - 1) (0 : BitVec 8) ++
            List.replicate 56 (0 : BitVec 8)) ++
            natToBytesBE 8 ((64 * N + rem) * 8) =
        ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
            List.replicate (64 - rem - 1) (0 : BitVec 8)) ++
          (List.replicate 56 (0 : BitVec 8) ++
            natToBytesBE 8 ((64 * N + rem) * 8)) := by
    simp only [List.append_assoc]
  rw [hassoc, List.take_append_of_le_length]
  · exact List.take_of_length_le (by
      simp [List.length_append, List.length_singleton, hres, List.length_replicate]; omega)
  · simp [List.length_append, List.length_singleton, hres, List.length_replicate]; omega

private theorem sha256Last_as_suffix (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
        List.replicate (119 - rem) (0 : BitVec 8) ++
          natToBytesBE 8 ((64 * N + rem) * 8)).drop 64 =
      List.replicate 56 (0 : BitVec 8) ++
        natToBytesBE 8 ((64 * N + rem) * 8) := by
  have hres : (input.drop (64 * N)).length = rem :=
    sha256Residual_length input N rem hlen
  have hz : List.replicate (119 - rem) (0 : BitVec 8) =
      List.replicate (64 - rem - 1) (0 : BitVec 8) ++
        List.replicate 56 (0 : BitVec 8) := by
    have hsum : (64 - rem - 1) + 56 = 119 - rem := by omega
    rw [← hsum, List.replicate_append_replicate]
  rw [hz]
  change
    ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
        (List.replicate (64 - rem - 1) (0 : BitVec 8) ++
          List.replicate 56 (0 : BitVec 8)) ++
          natToBytesBE 8 ((64 * N + rem) * 8)).drop 64 =
      List.replicate 56 (0 : BitVec 8) ++
        natToBytesBE 8 ((64 * N + rem) * 8)
  have hassoc :
      (input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
          (List.replicate (64 - rem - 1) (0 : BitVec 8) ++
            List.replicate 56 (0 : BitVec 8)) ++
            natToBytesBE 8 ((64 * N + rem) * 8) =
        ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
            List.replicate (64 - rem - 1) (0 : BitVec 8)) ++
          (List.replicate 56 (0 : BitVec 8) ++
            natToBytesBE 8 ((64 * N + rem) * 8)) := by
    simp only [List.append_assoc]
  rw [hassoc, List.drop_append_of_le_length, List.drop_eq_nil_of_le, List.nil_append]
  · simp [List.length_append, List.length_singleton, hres, List.length_replicate]; omega
  · simp [List.length_append, List.length_singleton, hres, List.length_replicate]; omega

/-- Penultimate machine block = SpecRef first pad block. -/
private theorem sha256PenultimateBlock_ge56_eq_prefix
    (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    sha256PenultimateBlock_ge56 input N rem =
      (input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
        List.replicate (64 - rem - 1) (0 : BitVec 8) := by
  refine List.ext_getElem ?_ ?_
  · have hL := sha256PenultimateBlock_ge56_length input N rem hlen hrem hrem64
    simp [List.length_append, List.length_singleton, sha256Residual_length input N rem hlen,
      List.length_replicate, hL]
    omega
  · intro i h₁ h₂
    have hi : i < 64 := by
      rw [sha256PenultimateBlock_ge56_length input N rem hlen hrem hrem64] at h₁; exact h₁
    have hres : (input.drop (64 * N)).length = rem :=
      sha256Residual_length input N rem hlen
    have hpen := sha256PadScratch_lt56_getElem (input.drop (64 * N)) rem i hres hrem64 hi
    simp only [sha256PenultimateBlock_ge56]
    rw [hpen]
    by_cases h : i < rem
    · -- into residual prefix of ((res ++ [0x80]) ++ zeros)
      rw [dif_pos h]
      have hmid : i < ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]).length := by
        simp only [List.length_append, List.length_singleton, hres]; omega
      have htail : i <
          (((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]) ++
            List.replicate (64 - rem - 1) (0 : BitVec 8)).length := by
        simp only [List.length_append, List.length_singleton, hres, List.length_replicate]; omega
      -- Normalize pretty-printed `a ++ b ++ c` to explicit left-assoc for getElem_append.
      change _ = (((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]) ++
          List.replicate (64 - rem - 1) (0 : BitVec 8))[i]
      rw [List.getElem_append_left hmid]
      have h1 : i < (input.drop (64 * N)).length := by omega
      rw [List.getElem_append_left h1]
    · by_cases h' : i = rem
      · rw [dif_neg h, dif_pos h']
        change 128 = (((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]) ++
            List.replicate (64 - rem - 1) (0 : BitVec 8))[i]
        have hmid : i < ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]).length := by
          simp only [List.length_append, List.length_singleton, hres]; omega
        rw [List.getElem_append_left hmid]
        have hge : (input.drop (64 * N)).length ≤ i := by omega
        rw [List.getElem_append_right hge]
        have hidx : i - (input.drop (64 * N)).length = 0 := by omega
        simp only [hidx, List.getElem_singleton]
      · rw [dif_neg h, dif_neg h']
        change 0 = (((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]) ++
            List.replicate (64 - rem - 1) (0 : BitVec 8))[i]
        have hge : ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]).length ≤ i := by
          simp only [List.length_append, List.length_singleton, hres]; omega
        rw [List.getElem_append_right hge]
        have hlenF : ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)]).length = rem + 1 := by
          simp only [List.length_append, List.length_singleton, hres]
        simp only [hlenF]
        have hz : i - (rem + 1) < (List.replicate (64 - rem - 1) (0 : BitVec 8)).length := by
          rw [List.length_replicate]; omega
        exact (List.getElem_replicate (a := (0 : BitVec 8)) (n := 64 - rem - 1)
          (i := i - (rem + 1)) hz).symm

/-- Last machine block = 56 zero bytes ‖ BE bit-length. -/
private theorem sha256LastBlock_ge56_eq_zerosBitlen
    (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    sha256LastBlock_ge56 input N rem (sha256BitLenW N rem) =
      List.replicate 56 (0 : BitVec 8) ++
        natToBytesBE 8 ((64 * N + rem) * 8) := by
  have hres : (input.drop (64 * N)).length = rem :=
    sha256Residual_length input N rem hlen
  have hlenZ : (List.replicate 64 (0 : BitVec 8)).length = 64 := List.length_replicate
  have hzero :
      sha256PadZeroed (sha256PadScratch_lt56 (input.drop (64 * N)) sha256ZeroScratch rem) =
        List.replicate 64 (0 : BitVec 8) := by
    have hmid := length_sha256PadScratch_lt56 (input.drop (64 * N)) sha256ZeroScratch rem
      sha256ZeroScratch_length hrem64 (by rw [hres])
    exact sha256PadZeroed_eq_replicate _ hmid
  have hbit :
      sha256BitlenBE (List.replicate 64 (0 : BitVec 8)) (sha256BitLenW N rem) =
        List.replicate 56 (0 : BitVec 8) ++
          natToBytesBE 8 ((64 * N + rem) * 8) := by
    refine List.ext_getElem ?_ ?_
    · rw [length_sha256BitlenBE _ _ hlenZ, List.length_append, List.length_replicate,
        natToBytesBE_length]
    · intro i h₁ h₂
      have hi : i < 64 := by
        rw [length_sha256BitlenBE _ _ hlenZ] at h₁; exact h₁
      by_cases hi56 : i < 56
      · have hb := sha256BitlenBE_getElem_lt56 (List.replicate 64 (0 : BitVec 8))
          (sha256BitLenW N rem) i hlenZ hi56
        rw [hb, List.getElem_replicate]
        have hL : i < (List.replicate 56 (0 : BitVec 8)).length := by
          rw [List.length_replicate]; exact hi56
        rw [List.getElem_append_left hL, List.getElem_replicate]
      · have hiGe : 56 ≤ i := Nat.le_of_not_gt hi56
        have hb := sha256BitlenBE_getElem_ge56 (List.replicate 64 (0 : BitVec 8))
          (sha256BitLenW N rem) i hlenZ hiGe hi
        rw [hb]
        have hj : i - 56 < 8 := by omega
        have hshift : 8 * (63 - i) = 8 * (7 - (i - 56)) := by omega
        simp only [hshift]
        refine Eq.trans (sha256BitLenW_shift_byte N rem (i - 56) hj) ?_
        refine Eq.trans (natToBytesBE8_shift_mod ((64 * N + rem) * 8) (i - 56) hj).symm ?_
        refine Eq.trans (natToBytesBE8_getElem ((64 * N + rem) * 8) (i - 56) hj).symm ?_
        have hge : (List.replicate 56 (0 : BitVec 8)).length ≤ i := by
          rw [List.length_replicate]; exact hiGe
        rw [List.getElem_append_right hge]
        simp only [List.length_replicate]
  simp only [sha256LastBlock_ge56, sha256FinalBlock_ge56, sha256PadScratch_ge56, hzero, hbit]

theorem sha256Pad_drop_eq_two_blocks_ge56 (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    (sha256Pad input).drop (64 * N) =
      sha256PenultimateBlock_ge56 input N rem ++
        sha256LastBlock_ge56 input N rem (sha256BitLenW N rem) := by
  rw [sha256Pad_drop_suffix_ge56 input N rem hlen hrem hrem64]
  have hsplit :=
    (List.take_append_drop 64
      ((input.drop (64 * N)) ++ [(0x80 : BitVec 8)] ++
        List.replicate (119 - rem) (0 : BitVec 8) ++
          natToBytesBE 8 ((64 * N + rem) * 8))).symm
  rw [hsplit, sha256Penultimate_as_prefix input N rem hlen hrem hrem64,
    sha256Last_as_suffix input N rem hlen hrem hrem64,
    ← sha256PenultimateBlock_ge56_eq_prefix input N rem hlen hrem hrem64,
    ← sha256LastBlock_ge56_eq_zerosBitlen input N rem hlen hrem hrem64]

theorem sha256Pad_chunks_split_ge56 (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    chunkBytes 64 (sha256Pad input) =
      sha256AbsorbBlocks input N ++
        [sha256PenultimateBlock_ge56 input N rem,
         sha256LastBlock_ge56 input N rem (sha256BitLenW N rem)] := by
  have htake : (sha256Pad input).take (64 * N) = input.take (64 * N) := by
    have hle : 64 * N ≤ input.length := by rw [hlen]; omega
    simp only [sha256Pad, hlen]
    have happ :
        input ++ [(0x80 : BitVec 8)] ++
            List.replicate ((64 - ((64 * N + rem + 9) % 64)) % 64) (0 : BitVec 8) ++
              natToBytesBE 8 ((64 * N + rem) * 8) =
          input ++ ([(0x80 : BitVec 8)] ++
            List.replicate ((64 - ((64 * N + rem + 9) % 64)) % 64) (0 : BitVec 8) ++
              natToBytesBE 8 ((64 * N + rem) * 8)) := by
      simp only [List.append_assoc]
    rw [happ]
    exact List.take_append_of_le_length hle
  have hdrop := sha256Pad_drop_eq_two_blocks_ge56 input N rem hlen hrem hrem64
  have hsplit : sha256Pad input =
      (sha256Pad input).take (64 * N) ++
        (sha256Pad input).drop (64 * N) :=
    (List.take_append_drop (64 * N) (sha256Pad input)).symm
  conv_lhs => rw [hsplit, htake, hdrop]
  unfold sha256AbsorbBlocks
  simp only [sha256BridgeBlockBytes]
  set penult := sha256PenultimateBlock_ge56 input N rem
  set last := sha256LastBlock_ge56 input N rem (sha256BitLenW N rem)
  have hpen : penult.length = 64 :=
    sha256PenultimateBlock_ge56_length input N rem hlen hrem hrem64
  have hlast : last.length = 64 :=
    sha256LastBlock_ge56_length input N rem hlen hrem hrem64
  have hxs : (input.take (64 * N)).length = 64 * N := by
    rw [List.length_take, hlen, min_eq_left (by omega)]
  rw [← List.append_assoc]
  have hmid := chunkBytes_append_block64 N (input.take (64 * N)) penult hxs hpen
  have h2 := chunkBytes_append_block64 (N + 1) (input.take (64 * N) ++ penult) last
    (by simp [List.length_append, hxs, hpen]; omega) hlast
  rw [h2, hmid]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-! ## Body final state = full SpecRef compress chain -/

private theorem sha256Residual_eq_drop (input : List (BitVec 8)) (N : Nat) :
    sha256Residual input N = input.drop (64 * N) := by
  simp only [sha256Residual]

private theorem sha256FinalBlock_lt56_eq_last (input : List (BitVec 8)) (N rem : Nat) :
    sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem) =
      sha256LastBlock_lt56 input N rem (sha256BitLenW N rem) := by
  simp only [sha256LastBlock_lt56, sha256Residual_eq_drop]

private theorem sha256BodyFinalState_eq_compress'_lt56 (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : rem < 56) :
    sha256BodyFinalState input N rem =
      sha256StateBytes
        (sha256Compress' sha256IV (chunkBytes 64 (sha256Pad input))) := by
  have hfit : sha256BridgeBlockBytes * N ≤ input.length := by
    simp only [sha256BridgeBlockBytes, hlen]; omega
  simp only [sha256BodyFinalState, hrem, ↓reduceIte]
  rw [sha256AbsorbedState_eq_compress' input N hfit,
    sha256FinalBlock_lt56_eq_last]
  have h8 : (sha256Compress' sha256IV (sha256AbsorbBlocks input N)).length = 8 :=
    sha256Compress'_length sha256IV _ sha256IV_length
  have hblk := sha256LastBlock_lt56_length input N rem hlen hrem
  rw [sha256CompressBytes_eq_stateBytes _ _ h8 hblk]
  congr 1
  rw [← sha256Compress'_append_singleton,
    ← sha256Pad_chunks_split_lt56 input N rem hlen hrem]

/-- SpecRef Compress' over absorb ‖ two rem≥56 pad blocks. -/
private theorem sha256_compress'_pad_two_blocks_ge56
    (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    sha256Compress
      (sha256Compress (sha256Compress' sha256IV (sha256AbsorbBlocks input N))
        (sha256BlockWords (sha256PenultimateBlock_ge56 input N rem)))
      (sha256BlockWords (sha256LastBlock_ge56 input N rem (sha256BitLenW N rem))) =
      sha256Compress' sha256IV (chunkBytes 64 (sha256Pad input)) := by
  rw [sha256Pad_chunks_split_ge56 input N rem hlen hrem hrem64]
  have hpair :
      sha256AbsorbBlocks input N ++
          [sha256PenultimateBlock_ge56 input N rem,
           sha256LastBlock_ge56 input N rem (sha256BitLenW N rem)] =
        (sha256AbsorbBlocks input N ++ [sha256PenultimateBlock_ge56 input N rem]) ++
          [sha256LastBlock_ge56 input N rem (sha256BitLenW N rem)] := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hpair, sha256Compress'_append_singleton, sha256Compress'_append_singleton]

/-- Double pad-path compress (rem≥56) equals SpecRef Compress' over the full pad chunks. -/
private theorem sha256_double_compressBytes_eq_compress'_ge56
    (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    sha256CompressBytes
      (sha256CompressBytes
        (sha256StateBytes (sha256Compress' sha256IV (sha256AbsorbBlocks input N)))
        (sha256PenultimateBlock_ge56 input N rem))
      (sha256LastBlock_ge56 input N rem (sha256BitLenW N rem)) =
      sha256StateBytes
        (sha256Compress' sha256IV (chunkBytes 64 (sha256Pad input))) := by
  have h8 : (sha256Compress' sha256IV (sha256AbsorbBlocks input N)).length = 8 :=
    sha256Compress'_length sha256IV _ sha256IV_length
  have hpenLen := sha256PenultimateBlock_ge56_length input N rem hlen hrem hrem64
  have hlastLen := sha256LastBlock_ge56_length input N rem hlen hrem hrem64
  have h1 := sha256CompressBytes_eq_stateBytes
    (sha256Compress' sha256IV (sha256AbsorbBlocks input N))
    (sha256PenultimateBlock_ge56 input N rem) h8 hpenLen
  rw [h1]
  have h8mid :
      (sha256Compress (sha256Compress' sha256IV (sha256AbsorbBlocks input N))
        (sha256BlockWords (sha256PenultimateBlock_ge56 input N rem))).length = 8 :=
    sha256Compress_length _ _ (by omega)
  have h2 := sha256CompressBytes_eq_stateBytes
    (sha256Compress (sha256Compress' sha256IV (sha256AbsorbBlocks input N))
      (sha256BlockWords (sha256PenultimateBlock_ge56 input N rem)))
    (sha256LastBlock_ge56 input N rem (sha256BitLenW N rem)) h8mid hlastLen
  rw [h2, sha256_compress'_pad_two_blocks_ge56 input N rem hlen hrem hrem64]

private theorem sha256BodyFinalState_eq_compress'_ge56 (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    sha256BodyFinalState input N rem =
      sha256StateBytes
        (sha256Compress' sha256IV (chunkBytes 64 (sha256Pad input))) := by
  have hfit : sha256BridgeBlockBytes * N ≤ input.length := by
    simp only [sha256BridgeBlockBytes, hlen]; omega
  have hge : ¬ rem < 56 := Nat.not_lt.mpr hrem
  unfold sha256BodyFinalState
  simp only [hge, ↓reduceIte]
  rw [sha256Residual_eq_drop, sha256AbsorbedState_eq_compress' input N hfit]
  -- PadScratch_lt56 / FinalBlock_ge56 are the SpecRef block defs.
  simpa [sha256PenultimateBlock_ge56, sha256LastBlock_ge56] using
    sha256_double_compressBytes_eq_compress'_ge56 input N rem hlen hrem hrem64

private theorem sha256BodyFinalState_eq_compress' (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : rem < 64) :
    sha256BodyFinalState input N rem =
      sha256StateBytes
        (sha256Compress' sha256IV (chunkBytes 64 (sha256Pad input))) := by
  by_cases hlt : rem < 56
  · exact sha256BodyFinalState_eq_compress'_lt56 input N rem hlen hlt
  · exact sha256BodyFinalState_eq_compress'_ge56 input N rem hlen (Nat.le_of_not_gt hlt) hrem

/-! ## BE squeeze = SpecRef digest bytes -/

private theorem natToBytesBE4_getElem (x k : Nat) (hk : k < 4) :
    (natToBytesBE 4 x)[k]'(by rw [natToBytesBE_length]; exact hk) =
      BitVec.ofNat 8 (x >>> (8 * (3 - k))) := by
  simp only [natToBytesBE, List.getElem_map, List.getElem_reverse, List.length_range,
    List.getElem_range]

private theorem length_flatMap_const {α β : Type _} (ws : List α) (f : α → List β)
    (n : Nat) (hf : ∀ a, (f a).length = n) :
    (ws.flatMap f).length = ws.length * n := by
  induction ws with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hf, ih, Nat.succ_mul]
    omega

private theorem flatMap_constLen_getElem {α β : Type _} (ws : List α) (f : α → List β)
    (n : Nat) (hf : ∀ a, (f a).length = n) (hn : 0 < n)
    (i : Nat) (hi : i < ws.length * n) :
    (ws.flatMap f)[i]'(by rw [length_flatMap_const ws f n hf]; exact hi) =
      (f (ws[i / n]'(by
        apply (Nat.div_lt_iff_lt_mul hn).2; exact hi)))[i % n]'(by
        simpa [hf] using Nat.mod_lt i hn) := by
  induction ws generalizing i with
  | nil =>
    simp at hi
  | cons a rest ih =>
    have hlenA : (f a).length = n := hf a
    simp only [List.flatMap_cons, List.length_cons, Nat.succ_mul] at hi ⊢
    by_cases hlt : i < n
    · have hdiv : i / n = 0 := Nat.div_eq_of_lt hlt
      have hmod : i % n = i := Nat.mod_eq_of_lt hlt
      simp only [hdiv, hmod, List.getElem_cons_zero]
      rw [List.getElem_append_left (by rw [hlenA]; exact hlt)]
    · have hge : n ≤ i := Nat.le_of_not_gt hlt
      have hi' : i - n < rest.length * n := by omega
      have hdiv : i / n = (i - n) / n + 1 := by
        rw [Nat.div_eq_sub_div hn hge]
      have hmod : i % n = (i - n) % n := Nat.mod_eq_sub_mod hge
      rw [List.getElem_append_right (by rw [hlenA]; exact hge)]
      simp only [hlenA, hdiv, hmod, List.getElem_cons_succ]
      exact ih (i - n) hi'

private theorem length_flatMap_natToBytesBE4 (hs : List (BitVec 32)) (h8 : hs.length = 8) :
    (hs.flatMap (fun w => natToBytesBE 4 w.toNat)).length = 32 := by
  rw [length_flatMap_const _ _ 4 (fun _ => natToBytesBE_length 4 _), h8]

private theorem xor3_mod4 (r : Nat) (hr : r < 4) : r ^^^ 3 = 3 - r := by
  interval_cases r <;> decide

/-- `i ^^^ 3` on a byte index `4*q + r` (r &lt; 4) selects the BE twin of LE lane `r`. -/
private theorem xor3_add_mul4 (q r : Nat) (hr : r < 4) :
    (4 * q + r) ^^^ 3 = 4 * q + (3 - r) := by
  rw [← xor3_mod4 r hr]
  apply Nat.eq_of_testBit_eq
  intro j
  have h4 : 4 * q = 2 ^ 2 * q := by omega
  have hr3 : r ^^^ 3 < 4 := by interval_cases r <;> decide
  have hL := Nat.testBit_two_pow_mul_add q (b := r) (i := 2) hr j
  have hR := Nat.testBit_two_pow_mul_add q (b := r ^^^ 3) (i := 2) hr3 j
  rw [← h4] at hL hR
  simp only [Nat.testBit_xor, hL, hR]
  by_cases hj : j < 2
  · simp only [hj, ↓reduceIte]
  · simp only [hj, ↓reduceIte]
    have h3f : Nat.testBit 3 j = false :=
      Nat.testBit_lt_two_pow (x := 3) (i := j) (by
        have : 2 ≤ j := Nat.le_of_not_gt hj
        have : 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide : 0 < 2) this
        omega)
    simp [h3f]

private theorem extractByte_pack_lo (lo hi : BitVec 32) (r : Nat) (hr : r < 4) :
    extractByte ((hi.setWidth 64 <<< 32) ||| lo.setWidth 64) r =
      (lo >>> (8 * r)).truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have hlt32 : r * 8 + i < 32 := by omega
  have hlt64 : r * 8 + i < 64 := by omega
  have h8eq : 8 * r + i = r * 8 + i := by omega
  simp only [hi, h8eq, decide_eq_true hlt32, decide_eq_true hlt64,
    Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_or, Bool.true_and]

private theorem extractByte_pack_hi (lo hi : BitVec 32) (r : Nat) (hr : r < 4) :
    extractByte ((hi.setWidth 64 <<< 32) ||| lo.setWidth 64) (r + 4) =
      (hi >>> (8 * r)).truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have hge32 : ¬ ((r + 4) * 8 + i < 32) := by omega
  have hlt64 : (r + 4) * 8 + i < 64 := by omega
  have hidx : (r + 4) * 8 + i - 32 = 8 * r + i := by omega
  have hloF : lo.getLsbD ((r + 4) * 8 + i) = false :=
    BitVec.getLsbD_of_ge lo ((r + 4) * 8 + i) (by omega)
  have hlt : 8 * r + i < 64 := by omega
  simp only [hi, decide_eq_false hge32, decide_eq_true hlt64,
    Bool.not_false, Bool.and_true, Bool.true_and, hidx, hloF,
    Bool.or_false, decide_eq_true hlt]

private theorem dwordBytes_getElem_extract (w : Word) (j : Nat) (hj : j < 8) :
    (dwordBytes w)[j]'(by simp [length_dwordBytes]; exact hj) = extractByte w j := by
  simp only [dwordBytes]
  interval_cases j <;> rfl

private theorem truncate8_eq_ofNat_shift (w : BitVec 32) (r : Nat) (_hr : r < 4) :
    (w >>> (8 * r)).truncate 8 = BitVec.ofNat 8 (w.toNat >>> (8 * r)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat]

/-- Right-nested append shape matches `List.flatMap_cons` unfolding. -/
private theorem flatMap4_dwordBytes_getElem (d0 d1 d2 d3 : Word) (i : Nat) (hi : i < 32) :
    (dwordBytes d0 ++ (dwordBytes d1 ++ (dwordBytes d2 ++ dwordBytes d3)))[i]'(by
        simp [List.length_append, length_dwordBytes]; omega) =
      (dwordBytes ([d0, d1, d2, d3][i / 8]'(by simp; omega)))[i % 8]'(by
        exact Nat.mod_lt i (by decide)) := by
  have hflat :
      dwordBytes d0 ++ (dwordBytes d1 ++ (dwordBytes d2 ++ dwordBytes d3)) =
        [d0, d1, d2, d3].flatMap dwordBytes := by
    simp [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [hflat]
  have hi' : i < [d0, d1, d2, d3].length * 8 := by simp; omega
  simpa using flatMap_constLen_getElem [d0, d1, d2, d3] dwordBytes 8
    (fun _ => length_dwordBytes _) (by decide) i hi'

private theorem sha256StateBytes_getElem_le
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32) (q r : Nat)
    (hq : q < 8) (hr : r < 4) :
    (sha256StateBytes [w0, w1, w2, w3, w4, w5, w6, w7])[4 * q + r]'(by
        rw [sha256StateBytes_length _ (by simp)]; omega) =
      (([w0, w1, w2, w3, w4, w5, w6, w7][q]'(hq)) >>> (8 * r)).truncate 8 := by
  simp only [sha256StateBytes]
  have hu :
      u32sToDwords [w0, w1, w2, w3, w4, w5, w6, w7] =
        [((w1.setWidth 64 <<< 32) ||| w0.setWidth 64),
         ((w3.setWidth 64 <<< 32) ||| w2.setWidth 64),
         ((w5.setWidth 64 <<< 32) ||| w4.setWidth 64),
         ((w7.setWidth 64 <<< 32) ||| w6.setWidth 64)] := by
    simp [u32sToDwords]
  simp only [hu, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hi : 4 * q + r < 32 := by omega
  rw [flatMap4_dwordBytes_getElem _ _ _ _ _ hi]
  interval_cases q
  · have hmod : (4 * 0 + r) % 8 = r := by omega
    have hdiv : (4 * 0 + r) / 8 = 0 := by omega
    have hd : [((w1.setWidth 64 <<< 32) ||| w0.setWidth 64),
         ((w3.setWidth 64 <<< 32) ||| w2.setWidth 64),
         ((w5.setWidth 64 <<< 32) ||| w4.setWidth 64),
         ((w7.setWidth 64 <<< 32) ||| w6.setWidth 64)][0]'(by simp) =
        ((w1.setWidth 64 <<< 32) ||| w0.setWidth 64) := rfl
    simp only [hmod, hdiv, hd]
    rw [dwordBytes_getElem_extract _ _ (by omega), extractByte_pack_lo w0 w1 r hr]
    simp
  · have hmod : (4 * 1 + r) % 8 = r + 4 := by omega
    have hdiv : (4 * 1 + r) / 8 = 0 := by omega
    have hd : [((w1.setWidth 64 <<< 32) ||| w0.setWidth 64),
         ((w3.setWidth 64 <<< 32) ||| w2.setWidth 64),
         ((w5.setWidth 64 <<< 32) ||| w4.setWidth 64),
         ((w7.setWidth 64 <<< 32) ||| w6.setWidth 64)][0]'(by simp) =
        ((w1.setWidth 64 <<< 32) ||| w0.setWidth 64) := rfl
    simp only [hmod, hdiv, hd]
    rw [dwordBytes_getElem_extract _ _ (by omega), extractByte_pack_hi w0 w1 r hr]
    simp
  · have hmod : (4 * 2 + r) % 8 = r := by omega
    have hdiv : (4 * 2 + r) / 8 = 1 := by omega
    have hd : [((w1.setWidth 64 <<< 32) ||| w0.setWidth 64),
         ((w3.setWidth 64 <<< 32) ||| w2.setWidth 64),
         ((w5.setWidth 64 <<< 32) ||| w4.setWidth 64),
         ((w7.setWidth 64 <<< 32) ||| w6.setWidth 64)][1]'(by simp) =
        ((w3.setWidth 64 <<< 32) ||| w2.setWidth 64) := rfl
    simp only [hmod, hdiv, hd]
    rw [dwordBytes_getElem_extract _ _ (by omega), extractByte_pack_lo w2 w3 r hr]
    simp
  · have hmod : (4 * 3 + r) % 8 = r + 4 := by omega
    have hdiv : (4 * 3 + r) / 8 = 1 := by omega
    have hd : [((w1.setWidth 64 <<< 32) ||| w0.setWidth 64),
         ((w3.setWidth 64 <<< 32) ||| w2.setWidth 64),
         ((w5.setWidth 64 <<< 32) ||| w4.setWidth 64),
         ((w7.setWidth 64 <<< 32) ||| w6.setWidth 64)][1]'(by simp) =
        ((w3.setWidth 64 <<< 32) ||| w2.setWidth 64) := rfl
    simp only [hmod, hdiv, hd]
    rw [dwordBytes_getElem_extract _ _ (by omega), extractByte_pack_hi w2 w3 r hr]
    simp
  · have hmod : (4 * 4 + r) % 8 = r := by omega
    have hdiv : (4 * 4 + r) / 8 = 2 := by omega
    have hd : [((w1.setWidth 64 <<< 32) ||| w0.setWidth 64),
         ((w3.setWidth 64 <<< 32) ||| w2.setWidth 64),
         ((w5.setWidth 64 <<< 32) ||| w4.setWidth 64),
         ((w7.setWidth 64 <<< 32) ||| w6.setWidth 64)][2]'(by simp) =
        ((w5.setWidth 64 <<< 32) ||| w4.setWidth 64) := rfl
    simp only [hmod, hdiv, hd]
    rw [dwordBytes_getElem_extract _ _ (by omega), extractByte_pack_lo w4 w5 r hr]
    simp
  · have hmod : (4 * 5 + r) % 8 = r + 4 := by omega
    have hdiv : (4 * 5 + r) / 8 = 2 := by omega
    have hd : [((w1.setWidth 64 <<< 32) ||| w0.setWidth 64),
         ((w3.setWidth 64 <<< 32) ||| w2.setWidth 64),
         ((w5.setWidth 64 <<< 32) ||| w4.setWidth 64),
         ((w7.setWidth 64 <<< 32) ||| w6.setWidth 64)][2]'(by simp) =
        ((w5.setWidth 64 <<< 32) ||| w4.setWidth 64) := rfl
    simp only [hmod, hdiv, hd]
    rw [dwordBytes_getElem_extract _ _ (by omega), extractByte_pack_hi w4 w5 r hr]
    simp
  · have hmod : (4 * 6 + r) % 8 = r := by omega
    have hdiv : (4 * 6 + r) / 8 = 3 := by omega
    have hd : [((w1.setWidth 64 <<< 32) ||| w0.setWidth 64),
         ((w3.setWidth 64 <<< 32) ||| w2.setWidth 64),
         ((w5.setWidth 64 <<< 32) ||| w4.setWidth 64),
         ((w7.setWidth 64 <<< 32) ||| w6.setWidth 64)][3]'(by simp) =
        ((w7.setWidth 64 <<< 32) ||| w6.setWidth 64) := rfl
    simp only [hmod, hdiv, hd]
    rw [dwordBytes_getElem_extract _ _ (by omega), extractByte_pack_lo w6 w7 r hr]
    simp
  · have hmod : (4 * 7 + r) % 8 = r + 4 := by omega
    have hdiv : (4 * 7 + r) / 8 = 3 := by omega
    have hd : [((w1.setWidth 64 <<< 32) ||| w0.setWidth 64),
         ((w3.setWidth 64 <<< 32) ||| w2.setWidth 64),
         ((w5.setWidth 64 <<< 32) ||| w4.setWidth 64),
         ((w7.setWidth 64 <<< 32) ||| w6.setWidth 64)][3]'(by simp) =
        ((w7.setWidth 64 <<< 32) ||| w6.setWidth 64) := rfl
    simp only [hmod, hdiv, hd]
    rw [dwordBytes_getElem_extract _ _ (by omega), extractByte_pack_hi w6 w7 r hr]
    simp

private theorem flatMap8_natToBytesBE4_getElem
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32) (i : Nat) (hi : i < 32) :
    ([w0, w1, w2, w3, w4, w5, w6, w7].flatMap (fun w => natToBytesBE 4 w.toNat))[i]'(by
        rw [length_flatMap_const _ _ 4 (fun _ => natToBytesBE_length 4 _)]; simp; omega) =
      (natToBytesBE 4
        (([w0, w1, w2, w3, w4, w5, w6, w7][i / 4]'(by simp; omega)).toNat))[i % 4]'(by
        exact Nat.mod_lt i (by decide)) := by
  have hi' : i < [w0, w1, w2, w3, w4, w5, w6, w7].length * 4 := by simp; omega
  simpa using flatMap_constLen_getElem [w0, w1, w2, w3, w4, w5, w6, w7]
    (fun w => natToBytesBE 4 w.toNat) 4 (fun _ => natToBytesBE_length 4 _)
    (by decide) i hi'

theorem sha256SqueezeBE_eq_spec (hs : List (BitVec 32)) (h8 : hs.length = 8) :
    sha256SqueezeBE (sha256StateBytes hs) =
      hs.flatMap (fun w => natToBytesBE 4 w.toNat) := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩ := list_length_eq_8_cases hs h8
  refine List.ext_getElem ?_ ?_
  · have hlen := length_flatMap_natToBytesBE4 [w0, w1, w2, w3, w4, w5, w6, w7] (by simp)
    simpa [sha256SqueezeBE_length] using hlen.symm
  · intro i h₁ h₂
    have hi : i < 32 := by simpa [sha256SqueezeBE_length] using h₁
    simp only [sha256SqueezeBE, List.getElem_map, List.getElem_range]
    have hx : i ^^^ 3 < 32 := xor3_lt_32 i hi
    have hst : (sha256StateBytes [w0, w1, w2, w3, w4, w5, w6, w7]).length = 32 :=
      sha256StateBytes_length _ (by simp)
    rw [List.getD_eq_getElem _ _ (hn := by omega)]
    have hq : i / 4 < 8 := by omega
    have hr : i % 4 < 4 := Nat.mod_lt i (by decide)
    have hi_eq : i = 4 * (i / 4) + i % 4 := (Nat.div_add_mod i 4).symm
    have hxor : i ^^^ 3 = 4 * (i / 4) + (3 - i % 4) := by
      conv => lhs; rw [hi_eq]
      exact xor3_add_mul4 (i / 4) (i % 4) hr
    simp only [hxor]
    rw [sha256StateBytes_getElem_le w0 w1 w2 w3 w4 w5 w6 w7 (i / 4) (3 - i % 4) hq (by omega)]
    rw [flatMap8_natToBytesBE4_getElem w0 w1 w2 w3 w4 w5 w6 w7 i hi]
    rw [truncate8_eq_ofNat_shift _ (3 - i % 4) (by omega)]
    exact (natToBytesBE4_getElem
      (([w0, w1, w2, w3, w4, w5, w6, w7][i / 4]'(by omega)).toNat) (i % 4) hr).symm

/-- Named bridge (#12018): operational machine digest = SpecRef. -/
theorem sha256BodyDigest_eq_specref (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 64 * N + rem) (hrem : rem < 64) :
    sha256BodyDigest input N rem = sha256 input := by
  unfold sha256BodyDigest sha256
  rw [sha256BodyFinalState_eq_compress' input N rem hlen hrem]
  rw [sha256SqueezeBE_eq_spec _
    (sha256Compress'_length sha256IV _ sha256IV_length)]

end EvmAsm.Codegen.Proofs
