/-
  Structured SAsm port scaffold for `ssz_pack_bytes` (PR-S8).

  The emitted routine copies `len` bytes, zero-pads the final 32-byte chunk,
  and returns `ceil(len / 32)`.  This file deliberately keeps the semantic
  postcondition explicit; the full `vcgen` proof is added only once both loop
  invariants discharge under the strict Region/RwRegion model.
-/

import EvmAsm.Codegen.Programs.Ssz
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Codegen.Programs.SgMemcpySAsm
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace SszPackBytesSAsm

open SgMemcpySAsm

def padLen (len : Nat) : Nat :=
  if len % 32 = 0 then 0 else 32 - len % 32

def outLen (len : Nat) : Nat := len + padLen len

def chunkCount (len : Nat) : Nat := (len + 31) / 32

def packedBytes (srcBytes : List (BitVec 8)) (len : Nat) : List (BitVec 8) :=
  srcBytes.take len ++ List.replicate (padLen len) (0 : BitVec 8)

def copyWin (srcBytes orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  srcBytes.take i ++ orig.drop i

def padWin (srcBytes orig : List (BitVec 8)) (len k : Nat) : List (BitVec 8) :=
    srcBytes.take len ++ List.replicate k (0 : BitVec 8) ++ orig.drop (len + k)

theorem len_le_outLen (len : Nat) : len ≤ outLen len := by
  simp only [outLen]
  omega

theorem toNat_and_31 (i : Nat) :
    ((BitVec.ofNat 64 i) &&& (31 : Word)).toNat = i % 32 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  show (i % 2 ^ 64) &&& (2 ^ 5 - 1) = i % 32
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem toNat_ushiftRight_five {i : Nat} (hi : i < 2 ^ 64) :
    ((BitVec.ofNat 64 i) >>> (5 : Nat)).toNat = i / 32 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  omega

theorem copyWin_zero (srcBytes orig : List (BitVec 8)) :
    copyWin srcBytes orig 0 = orig := by simp [copyWin]

theorem copyWin_step (srcBytes orig : List (BitVec 8)) (len i : Nat)
    (hsrc : len ≤ srcBytes.length) (horig : orig.length = outLen len)
    (hi : i < len) :
    setBytes (copyWin srcBytes orig i) i [srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrc)] =
      copyWin srcBytes orig (i + 1) := by
  rw [setBytes_singleton]
  have hpre : (srcBytes.take i).length = i := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_trans (Nat.le_of_lt hi) hsrc)]
  have hiout : i < orig.length := by
    rw [horig]
    exact Nat.lt_of_lt_of_le hi (len_le_outLen len)
  have hdrop : orig.drop i = orig[i] :: orig.drop (i + 1) :=
    List.drop_eq_getElem_cons hiout
  unfold copyWin
  simp only [hpre, List.set_append_right, Nat.le_refl, Nat.sub_self]
  rw [hdrop]
  rw [List.set_cons_zero]
  rw [show srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrc) :: orig.drop (i + 1) =
      [srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrc)] ++ orig.drop (i + 1) by rfl]
  rw [← List.append_assoc]
  have htake : srcBytes.take i ++
      [srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrc)] = srcBytes.take (i + 1) := by
    have hfirst : (srcBytes.drop i).take 1 =
        [srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrc)] := by
      exact List.take_one_drop_eq_of_lt_length
        (Nat.lt_of_lt_of_le hi hsrc)
    rw [← hfirst, ← List.take_add]
  rw [htake]

theorem padWin_zero (srcBytes orig : List (BitVec 8)) (len : Nat) :
    padWin srcBytes orig len 0 = srcBytes.take len ++ orig.drop len := by
  simp [padWin]

theorem padWin_step (srcBytes orig : List (BitVec 8)) (len rem k : Nat)
    (hsrc : len ≤ srcBytes.length) (horig : orig.length = outLen len)
    (hrem : len + rem = outLen len) (hk : k < rem) :
    setBytes (padWin srcBytes orig len k) (len + k) [0] =
      padWin srcBytes orig len (k + 1) := by
  rw [setBytes_singleton]
  have htake : (srcBytes.take len).length = len := by
    rw [List.length_take, Nat.min_eq_left hsrc]
  have hdrop : orig.drop (len + k) =
      orig[len + k] :: orig.drop (len + k + 1) := by
    apply List.drop_eq_getElem_cons
  simp only [padWin]
  rw [hdrop]
  change ((srcBytes.take len ++ List.replicate k (0 : BitVec 8)) ++
      (orig[len + k] :: orig.drop (len + k + 1))).set (len + k) 0 = _
  rw [List.set_append_right (h := by simp [htake])]
  simp only [List.length_append, List.length_replicate, htake, Nat.sub_self]
  rw [List.set_cons_zero]
  rw [show (0 : BitVec 8) :: orig.drop (len + k + 1) =
      [0] ++ orig.drop (len + k + 1) by rfl]
  have hrep : List.replicate k (0 : BitVec 8) ++ [0] =
      List.replicate (k + 1) (0 : BitVec 8) := by
    rw [show [0] = List.replicate 1 (0 : BitVec 8) by simp,
      List.replicate_append_replicate]
  have hassoc2 : List.replicate k (0 : BitVec 8) ++
      ([0] ++ orig.drop (len + k + 1)) =
      (List.replicate k (0 : BitVec 8) ++ [0]) ++
        orig.drop (len + k + 1) := by simp [List.append_assoc]
  simp only [List.append_assoc]
  rw [hassoc2, hrep]
  simp [Nat.add_assoc]

def copyStepBlock : List Instr :=
  [.LBU .x28 .x5 (0 : BitVec 12),
   .SB .x6 .x28 (0 : BitVec 12),
   .ADDI .x5 .x5 (1 : BitVec 12),
   .ADDI .x6 .x6 (1 : BitVec 12),
   .ADDI .x7 .x7 (-1 : BitVec 12)]

def copyStepRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r1 := rf.set .x28 (b.zeroExtend 64)
  let r2 := r1.set .x5 (r1.get .x5 + signExtend12 (1 : BitVec 12))
  let r3 := r2.set .x6 (r2.get .x6 + signExtend12 (1 : BitVec 12))
  r3.set .x7 (r3.get .x7 + signExtend12 (-1 : BitVec 12))

theorem copyStepRf_get_x5 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x5 = rf.get .x5 + signExtend12 (1 : BitVec 12) := by
  unfold copyStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
    RegFile.get_set_self _ _ _ (by decide : Reg.x5 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28)]

theorem copyStepRf_get_x6 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x6 = rf.get .x6 + signExtend12 (1 : BitVec 12) := by
  unfold copyStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
    RegFile.get_set_self _ _ _ (by decide : Reg.x6 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28)]

theorem copyStepRf_get_x7 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x7 = rf.get .x7 + signExtend12 (-1 : BitVec 12) := by
  unfold copyStepRf
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x7 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28)]

theorem copyStepRf_get_x10 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x10 = rf.get .x10 := by
  simp [copyStepRf]

theorem copyStepRf_get_x11 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x11 = rf.get .x11 := by
  simp [copyStepRf]

theorem copyStepRf_get_x12 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x12 = rf.get .x12 := by
  simp [copyStepRf]

theorem copy_engine (src dst : Word) (len i : Nat)
    (srcBytes : List (BitVec 8)) (rf : RegFile) (ws : List (BitVec 8))
    (hx5 : rf.get .x5 = src + BitVec.ofNat 64 i)
    (hx6 : rf.get .x6 = dst + BitVec.ofNat 64 i)
    (hi : i < len) (hsrcLen : len ≤ srcBytes.length)
    (hsrc : src.toNat + len < 2 ^ 64)
    (hdst : dst.toNat + outLen len < 2 ^ 64)
    (hdisj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + outLen len ≤ src.toNat)
    (hws : ws.length = outLen len) :
    execBlock ⟨src, srcBytes⟩ dst rf ws copyStepBlock =
      (copyStepRf rf (srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrcLen)),
        setBytes ws i [srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrcLen)]) := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hi64 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  have hload : rf.get .x5 + signExtend12 (0 : BitVec 12) =
      src + BitVec.ofNat 64 i := by rw [hx5, hse0]; simp
  have hnr : ¬ inRw dst ws (rf.get .x5 + signExtend12 (0 : BitVec 12)) 1 := by
    rw [hload]
    unfold inRw
    rw [hws]
    have hsub : (src + BitVec.ofNat 64 i - dst).toNat =
        (src.toNat + i + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi64]; congr 1; omega
    rw [hsub]
    rcases hdisj with h | h <;> omega
  have hval : Region.byteAt ⟨src, srcBytes⟩
      (rf.get .x5 + signExtend12 (0 : BitVec 12)) =
      srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrcLen) := by
    rw [hload]
    show srcBytes.getD ((src + BitVec.ofNat 64 i - src).toNat) 0 = _
    rw [show (src + BitVec.ofNat 64 i - src).toNat = i by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi64]; omega]
    simp [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hi hsrcLen)]
  have hstore : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
    rw [hx6, hse0]
    bv_omega
  rw [copyStepBlock, execBlock_cons,
    execInstrRF_lbu_ro _ _ _ _ _ _ _ hnr]
  dsimp only
  rw [hval]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ i]
  · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    simp [copyStepRf]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28), hstore]

def padStepBlock : List Instr :=
  [.SB .x6 .x0 (0 : BitVec 12),
   .ADDI .x6 .x6 (1 : BitVec 12),
   .ADDI .x7 .x7 (-1 : BitVec 12)]

def padStepRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x6 (rf.get .x6 + signExtend12 (1 : BitVec 12))
  r1.set .x7 (r1.get .x7 + signExtend12 (-1 : BitVec 12))

theorem padStepRf_get_x6 (rf : RegFile) :
    (padStepRf rf).get .x6 = rf.get .x6 + signExtend12 (1 : BitVec 12) := by
  unfold padStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
    RegFile.get_set_self _ _ _ (by decide : Reg.x6 ≠ .x0)]

theorem padStepRf_get_x7 (rf : RegFile) :
    (padStepRf rf).get .x7 = rf.get .x7 + signExtend12 (-1 : BitVec 12) := by
  unfold padStepRf
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x7 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6)]

theorem padStepRf_get_x10 (rf : RegFile) :
    (padStepRf rf).get .x10 = rf.get .x10 := by simp [padStepRf]

theorem padStepRf_get_x11 (rf : RegFile) :
    (padStepRf rf).get .x11 = rf.get .x11 := by simp [padStepRf]

theorem padStepRf_get_x12 (rf : RegFile) :
    (padStepRf rf).get .x12 = rf.get .x12 := by simp [padStepRf]

theorem pad_engine (src dst : Word) (len rem k : Nat)
    (srcBytes : List (BitVec 8)) (rf : RegFile) (ws : List (BitVec 8))
    (hx6 : rf.get .x6 = dst + BitVec.ofNat 64 (len + k))
    (hk : k < rem) (hrem : len + rem = outLen len)
    (hdst : dst.toNat + outLen len < 2 ^ 64)
    (hws : ws.length = outLen len) :
    execBlock ⟨src, srcBytes⟩ dst rf ws padStepBlock =
      (padStepRf rf, setBytes ws (len + k) [0]) := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hstore : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat = len + k := by
    rw [hx6, hse0]
    bv_omega
  rw [padStepBlock, execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ (len + k)]
  · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    simp [padStepRf]
  · rw [hstore]

def copyInv (src dst : Word) (len : Nat) (srcBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    rf.get .x5 = src + BitVec.ofNat 64 i ∧
    rf.get .x6 = dst + BitVec.ofNat 64 i ∧
    rf.get .x7 = BitVec.ofNat 64 (len - i) ∧
    rf.get .x10 = src ∧ rf.get .x11 = BitVec.ofNat 64 len ∧
    rf.get .x12 = dst ∧ i ≤ len ∧
    srcBytes.length ≥ len ∧ orig.length = outLen len ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + outLen len < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + outLen len ≤ src.toNat) ∧
    ws = copyWin srcBytes orig i ∧ A = empAssertion

def padInv (src dst : Word) (len rem : Nat) (srcBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun k rf ws A =>
    rf.get .x6 = dst + BitVec.ofNat 64 (len + k) ∧
    rf.get .x7 = BitVec.ofNat 64 (rem - k) ∧
    rf.get .x10 = src ∧ rf.get .x11 = BitVec.ofNat 64 len ∧
    rf.get .x12 = dst ∧ k ≤ rem ∧
    srcBytes.length ≥ len ∧ orig.length = outLen len ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + outLen len < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + outLen len ≤ src.toNat) ∧
    ws = padWin srcBytes orig len k ∧ A = empAssertion

theorem pad_inv_step (src dst : Word) (len rem k : Nat)
    (srcBytes orig : List (BitVec 8)) (rf : RegFile) (ws : List (BitVec 8))
    (A : Assertion) (hk : k < rem) (hrem : len + rem = outLen len)
    (hsrcLen : len ≤ srcBytes.length)
    (h_inv : padInv src dst len rem srcBytes orig k rf ws A) :
    padInv src dst len rem srcBytes orig (k + 1) (padStepRf rf)
      (setBytes ws (len + k) [0]) A := by
  rcases h_inv with ⟨hx6, hx7, hx10, hx11, hx12, hkle,
    _hsrcLen', horig, hsrc, hdst, hdisj, hwin, hA⟩
  have hwslen : ws.length = outLen len := by
    rw [hwin]
    simp only [padWin, List.length_append, List.length_take,
      Nat.min_eq_left hsrcLen, List.length_replicate, List.length_drop, horig]
    omega
  have hse_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hse_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, by omega, hsrcLen, horig, hsrc, hdst,
    hdisj, ?_, hA⟩
  · rw [padStepRf_get_x6, hx6, hse_1]
    have hk64 : (BitVec.ofNat 64 (len + k)).toNat = len + k := by
      rw [BitVec.toNat_ofNat]
      omega
    have hknext : (BitVec.ofNat 64 (len + (k + 1))).toNat = len + (k + 1) := by
      rw [BitVec.toNat_ofNat]
      omega
    bv_omega
  · rw [padStepRf_get_x7, hx7, hse_m1]
    have hk64 : (BitVec.ofNat 64 (rem - k)).toNat = rem - k := by
      rw [BitVec.toNat_ofNat]
      omega
    have hknext : (BitVec.ofNat 64 (rem - (k + 1))).toNat = rem - (k + 1) := by
      rw [BitVec.toNat_ofNat]
      omega
    bv_omega
  · exact padStepRf_get_x10 rf ▸ hx10
  · exact padStepRf_get_x11 rf ▸ hx11
  · exact padStepRf_get_x12 rf ▸ hx12
  · rw [hwin, padWin_step srcBytes orig len rem k hsrcLen horig hrem hk]

theorem copy_inv_step (src dst : Word) (len i : Nat)
    (srcBytes orig : List (BitVec 8)) (rf : RegFile) (ws : List (BitVec 8))
    (A : Assertion)
    (hi : i < len)
    (hsrcLen : len ≤ srcBytes.length)
    (h_inv : copyInv src dst len srcBytes orig i rf ws A) :
    copyInv src dst len srcBytes orig (i + 1)
      (copyStepRf rf (srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrcLen)))
      (setBytes ws i [srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrcLen)]) A := by
  rcases h_inv with ⟨hx5, hx6, hx7, hx10, hx11, hx12, hile,
    hsrcLen, horig, hsrc, hdst, hdisj, hwin, hA⟩
  have hse_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hse_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, hsrcLen, horig, hsrc, hdst,
    hdisj, ?_, hA⟩
  · rw [copyStepRf_get_x5, hx5, hse_1]
    have hi64 : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat]
      omega
    have hinext : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
      rw [BitVec.toNat_ofNat]
      omega
    bv_omega
  · rw [copyStepRf_get_x6, hx6, hse_1]
    have hi64 : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat]
      omega
    have hinext : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
      rw [BitVec.toNat_ofNat]
      omega
    bv_omega
  · rw [copyStepRf_get_x7, hx7, hse_m1]
    have hi64 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by
      rw [BitVec.toNat_ofNat]
      omega
    have hinext : (BitVec.ofNat 64 (len - (i + 1))).toNat = len - (i + 1) := by
      rw [BitVec.toNat_ofNat]
      omega
    bv_omega
  · exact copyStepRf_get_x10 rf (srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrcLen)) ▸ hx10
  · exact copyStepRf_get_x11 rf (srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrcLen)) ▸ hx11
  · exact copyStepRf_get_x12 rf (srcBytes[i]'(Nat.lt_of_lt_of_le hi hsrcLen)) ▸ hx12
  · rw [hwin, copyWin_step srcBytes orig len i hsrcLen horig hi]

def copyLoop (src dst : Word) (len : Nat) (srcBytes orig : List (BitVec 8)) : Stmt :=
  .«while» "copy" (.bne .x7 .x0) len (copyInv src dst len srcBytes orig)
    (.block "copyByte" copyStepBlock)

def padLoop (src dst : Word) (len rem : Nat) (srcBytes orig : List (BitVec 8)) : Stmt :=
  .«while» "pad" (.bne .x7 .x0) 32 (padInv src dst len rem srcBytes orig)
    (.block "zeroByte" padStepBlock)

/- theorem copyLoopFn_spec (src dst : Word) (len : Nat)
    (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf)
    (hrww : RwRegion.wf ⟨dst, outLen len⟩) (base : Word) :
    (copyLoopFn src dst len srcBytes orig).Spec base := by
  have hse_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hse_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case sszPackBytesCopy.copy.inv_init =>
    rintro rf ws A ⟨hx5, hx6, hx7, hx10, hx11, hx12, rfl,
      hsrcLen, horig, hsrc, hdst, hdj⟩
    refine ⟨?_, ?_, ?_, hx10, hx11, hx12, by omega, hsrcLen, horig,
      hsrc, hdst, hdj, ?_⟩
    · rw [hx5]; simp
    · rw [hx6]; simp
    · rw [hx7]; simp
    · rw [copyWin_zero]
  case sszPackBytesCopy.copy.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -,
      ⟨⟨hx5, hx6, hx7, hx10, hx11, hx12, hile, hsrcLen, horig,
          hsrc, hdst, hdj, hwin⟩, -⟩, rfl, rfl⟩
    have hwslen : ws₀.length = outLen len := by
      rw [hwin]
      simp only [copyWin, List.length_append, List.length_map,
        List.length_range, List.length_drop, horig]
      omega
    simp only [show (copyLoopFn src dst len srcBytes orig).rw.base = dst from rfl,
      show (copyLoopFn src dst len srcBytes orig).region = ⟨src, srcBytes⟩ from rfl]
    rw [copy_engine src dst len i srcBytes rf₀ ws₀ hx5 hx6 hi hsrcLen hsrc hdst hdj hwslen]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, hsrcLen, horig, hsrc, hdst, hdj, ?_⟩
    · rw [copyStepRf_get_x5, hx5, hse_1]
      have hi2 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      have hi2' : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [copyStepRf_get_x6, hx6, hse_1]
      have hi2 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      have hi2' : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [copyStepRf_get_x7, hx7, hse_m1]
      have hi2 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by
        rw [BitVec.toNat_ofNat]; omega
      have hi2' : (BitVec.ofNat 64 (len - (i + 1))).toNat = len - (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · simp [copyStepRf]
    · simp [copyStepRf]
    · simp [copyStepRf]
    · rw [hwin, copyWin_step srcBytes orig i horig hi]
  case sszPackBytesCopy.copy.exhausted =>
    rintro rf ws A ⟨-, -, hx7, -, -, -, hile, -, -, -, -, -, -⟩
    simp only [Cond.holds, not_not]
    rw [hx7]
    rw [show (BitVec.ofNat 64 (len - len)) = (0 : Word) by
      rw [show len - len = 0 by omega]; rfl]
    rfl
  case sszPackBytesCopy.post =>
    rintro rf ws A ⟨⟨j, hile, hx5, hx6, hx7, hx10, hx11, hx12,
      hle, hsrcLen, horig, hsrc, hdst, hdj, hwin⟩, hncond⟩
    have hi_len : j = len := by
      simp only [Cond.holds, not_not] at hncond
      rw [hx7] at hncond
      have hz : rf.get .x0 = 0 := rfl
      rw [hz] at hncond
      have hz' : (BitVec.ofNat 64 (len - j)).toNat = (0 : Word).toNat := by
        rw [hncond]
      rw [show (0 : Word).toNat = 0 from rfl, BitVec.toNat_ofNat] at hz'
      omega
    subst hi_len
    refine ⟨hx5, hx6, ?_, hx10, hx11, hx12, hwin⟩
    rw [hx7]
    rw [show (BitVec.ofNat 64 (len - len)) = (0 : Word) by
      rw [show len - len = 0 by omega]; rfl]
    rfl
-/

def sszPackBytesBody (src dst : Word) (len : Nat)
    (srcBytes orig : List (BitVec 8)) : Stmt :=
  .block "args" [.MV .x5 .x10, .MV .x6 .x12, .MV .x7 .x11] ;;;
  copyLoop src dst len srcBytes orig ;;;
  .block "remainder" [.ANDI .x7 .x11 (31 : BitVec 12)] ;;;
  .when "padGuard" (.bne .x7 .x0)
    (.block "padInit" [.LI .x28 (32 : Word),
                        .SUB .x7 .x28 .x7] ;;;
     padLoop src dst len (padLen len) srcBytes orig) ;;;
  .block "count" [.ADDI .x5 .x11 (31 : BitVec 12),
                   .SRLI .x10 .x5 (5 : BitVec 6)]

def sszPackBytesFn (src dst : Word) (len : Nat)
    (srcBytes orig : List (BitVec 8)) : Fn where
  name := "sszPackBytes"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, outLen len⟩
  pre := fun rf ws A =>
    rf.get .x10 = src ∧ rf.get .x11 = BitVec.ofNat 64 len ∧
    rf.get .x12 = dst ∧ ws = orig ∧
    srcBytes.length ≥ len ∧ orig.length = outLen len ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + outLen len < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + outLen len ≤ src.toNat) ∧ A = empAssertion
  post := fun rf ws A =>
    rf.get .x10 = BitVec.ofNat 64 (chunkCount len) ∧
    ws = packedBytes srcBytes len ∧ A = empAssertion
  body := sszPackBytesBody src dst len srcBytes orig

theorem count_engine (src dst : Word) (len : Nat)
    (srcBytes ws : List (BitVec 8)) (rf : RegFile)
    (hx11 : rf.get .x11 = BitVec.ofNat 64 len)
    (hlen : len + 31 < 2 ^ 64) :
    (execBlock ⟨src, srcBytes⟩ dst rf ws
      [.ADDI .x5 .x11 (31 : BitVec 12),
       .SRLI .x10 .x5 (5 : BitVec 6)]).1.get .x10 =
      BitVec.ofNat 64 (chunkCount len) := by
  have hse31 : signExtend12 (31 : BitVec 12) = (31 : Word) := by decide
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true, hse31, hx11]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  norm_num [BitVec.toNat_ofNat]
  change ((len + 31) % 2 ^ 64) >>> 5 = (chunkCount len) % 2 ^ 64
  have hto : (len + 31) % 2 ^ 64 = len + 31 := Nat.mod_eq_of_lt hlen
  rw [hto]
  simp only [chunkCount]
  omega

theorem count_bound_of_outLen_lt (len : Nat) (hout : outLen len < 2 ^ 64) :
    len + 31 < 2 ^ 64 := by
  unfold outLen padLen at hout
  split at hout <;> omega

theorem remainder_engine (src dst : Word) (len : Nat)
    (srcBytes ws : List (BitVec 8)) (rf : RegFile)
    (hx11 : rf.get .x11 = BitVec.ofNat 64 len) :
    execBlock ⟨src, srcBytes⟩ dst rf ws
      [.ANDI .x7 .x11 (31 : BitVec 12)] =
      (rf.set .x7 (BitVec.ofNat 64 (len % 32)), ws) := by
  have hse31 : signExtend12 (31 : BitVec 12) = (31 : Word) := by decide
  have hmask :
      (rf.get .x11 &&& signExtend12 (31 : BitVec 12)).toNat = len % 32 := by
    rw [hx11, hse31, toNat_and_31]
  have hmask_eq :
      rf.get .x11 &&& signExtend12 (31 : BitVec 12) =
        BitVec.ofNat 64 (len % 32) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hm64 : len % 32 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hm64]
    exact hmask
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, hmask_eq]

theorem sszPackBytesFn_spec (src dst : Word) (len : Nat)
    (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf)
    (hrww : RwRegion.wf ⟨dst, outLen len⟩) (base : Word) :
    (sszPackBytesFn src dst len srcBytes orig).Spec base := by
  have h_base : (sszPackBytesFn src dst len srcBytes orig).rw.base = dst := rfl
  have hse_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hse_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case sszPackBytes.copy.inv_init =>
    rintro rf' ws' A' h
    rcases h with ⟨rfInit, wsInit, _hwsLen, hpre, rfl, rfl⟩
    rcases hpre with ⟨hx10, hx11, hx12, hws, hsrcLen, horig, hsrc, hdst, hdj, hA⟩
    simp only [h_base]
    have h_x5_init :
        (execBlock (sszPackBytesFn src dst len srcBytes orig).region dst rfInit ws'
          [.MV .x5 .x10, .MV .x6 .x12, .MV .x7 .x11]).1.get .x5 = src := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hx10]
    have h_x6_init :
        (execBlock (sszPackBytesFn src dst len srcBytes orig).region dst rfInit ws'
          [.MV .x5 .x10, .MV .x6 .x12, .MV .x7 .x11]).1.get .x6 = dst := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hx12]
    have h_x7_init :
        (execBlock (sszPackBytesFn src dst len srcBytes orig).region dst rfInit ws'
          [.MV .x5 .x10, .MV .x6 .x12, .MV .x7 .x11]).1.get .x7 =
          BitVec.ofNat 64 len := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hx11]
    have h_x10_init :
        (execBlock (sszPackBytesFn src dst len srcBytes orig).region dst rfInit ws'
          [.MV .x5 .x10, .MV .x6 .x12, .MV .x7 .x11]).1.get .x10 = src := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx10]
    have h_x11_init :
        (execBlock (sszPackBytesFn src dst len srcBytes orig).region dst rfInit ws'
          [.MV .x5 .x10, .MV .x6 .x12, .MV .x7 .x11]).1.get .x11 =
          BitVec.ofNat 64 len := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx11]
    have h_x12_init :
        (execBlock (sszPackBytesFn src dst len srcBytes orig).region dst rfInit ws'
          [.MV .x5 .x10, .MV .x6 .x12, .MV .x7 .x11]).1.get .x12 = dst := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx12]
    refine ⟨(by simpa using h_x5_init), (by simpa using h_x6_init), h_x7_init, h_x10_init, h_x11_init,
      h_x12_init, by omega, hsrcLen, horig, hsrc, hdst, hdj, ?_, hA⟩
    rw [hws, copyWin_zero]
  case sszPackBytes.copy.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx5, hx6, hx7, hx10, hx11, hx12,
      hile, hsrcLen, horig, hsrc, hdst, hdj, hwin, hA⟩, _hcond⟩, rfl, rfl⟩
    have hwslen : ws₀.length = outLen len := by
      rw [hwin]
      simp only [copyWin, List.length_append, List.length_take,
        Nat.min_eq_left (Nat.le_trans (Nat.le_of_lt hi) hsrcLen),
        List.length_drop, horig]
      have hout : len ≤ outLen len := len_le_outLen len
      omega
    simp only [show (sszPackBytesFn src dst len srcBytes orig).rw.base = dst from rfl,
      show (sszPackBytesFn src dst len srcBytes orig).region = ⟨src, srcBytes⟩ from rfl]
    rw [copy_engine src dst len i srcBytes rf₀ ws₀ hx5 hx6 hi hsrcLen hsrc hdst hdj hwslen]
    exact copy_inv_step src dst len i srcBytes orig rf₀ ws₀ A' hi hsrcLen
      ⟨hx5, hx6, hx7, hx10, hx11, hx12, hile, hsrcLen, horig, hsrc, hdst, hdj, hwin,
        hA⟩
  case sszPackBytes.copy.exhausted =>
    rintro rf ws A ⟨-, -, hx7, -, -, -, hile, -, -, -, -, -, -, -⟩
    simp only [Cond.holds, not_not]
    rw [hx7]
    simp
  case sszPackBytes.copy.body.copyByte.mem =>
    rintro rf ws A hwslen ⟨i, hi, ⟨hx5, hx6, hx7, hx10, hx11, hx12,
      hile, hsrcLen, horig, hsrc, hdst, hdj, hwin, -⟩, -⟩
    change ws.length = outLen len at hwslen
    have hbase : (sszPackBytesFn src dst len srcBytes orig).rw.base = dst := rfl
    have hi2 : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat]
      omega
    have hloadaddr : rf.get .x5 + signExtend12 (0 : BitVec 12) =
        src + BitVec.ofNat 64 i := by
      rw [hx5, hse_0]
      simp
    have hnr : ¬ inRw dst ws (rf.get .x5 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [hloadaddr]
      unfold inRw
      rw [hwslen]
      have hsubd : (src + BitVec.ofNat 64 i - dst).toNat =
          (src.toNat + i + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
        rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]
        congr 1
        omega
      rw [hsubd]
      rcases hdj with hd | hd <;> omega
    have hload_ok : (src + BitVec.ofNat 64 i - src).toNat = i := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]
      omega
    have hstore : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
      rw [hx6, hse_0]
      bv_omega
    rw [show copyStepBlock =
        [.LBU .x28 .x5 0, .SB .x6 .x28 0, .ADDI .x5 .x5 (1 : BitVec 12),
         .ADDI .x6 .x6 (1 : BitVec 12), .ADDI .x7 .x7 (-1 : BitVec 12)] from rfl,
      show (sszPackBytesFn src dst len srcBytes orig).region = ⟨src, srcBytes⟩ from rfl,
      hbase]
    refine ⟨?_, ?_⟩
    · simp only [loadSem]
      rw [if_neg hnr]
      unfold Region.loadOk
      rw [hloadaddr, hload_ok]
      refine ⟨Nat.one_dvd _, ?_⟩
      show i + 1 ≤ srcBytes.length
      omega
    · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _ hnr]
      refine ⟨?_, trivial, trivial, trivial, trivial⟩
      dsimp only [storeSem]
      refine ⟨?_, ?_⟩
      · unfold inRw
        rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28), hwslen, hstore]
        have hout : len ≤ outLen len := len_le_outLen len
        omega
      · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28), hstore]
        exact Nat.one_dvd _
  case sszPackBytes.padGuard.pad.inv_init =>
    rintro rf ws A h
    rcases h with ⟨rf₀, ws₀, hwsLen, hreach, rfl, rfl⟩
    rcases hreach with ⟨hremReach, hguard⟩
    rcases hremReach with ⟨rf₁, ws₁, hws₁, hcopyReach, rfl, rfl⟩
    rcases hcopyReach with ⟨⟨i, hile, hInv⟩, hnot⟩
    change ws.length = outLen len at hwsLen
    change ws.length = outLen len at hws₁
    rcases hInv with ⟨hx5, hx6, hx7, hx10, hx11, hx12, hile',
      hsrcLen, horig, hsrc, hdst, hdj, hwin, hA⟩
    have hz : rf₁.get .x7 = 0 := by
      simpa [Cond.holds, RegFile.get_x0, not_not] using hnot
    have hi_len : i = len := by
      rw [hx7] at hz
      have hz' : (BitVec.ofNat 64 (len - i)).toNat = (0 : Word).toNat := by
        rw [hz]
      rw [show (0 : Word).toNat = 0 from rfl, BitVec.toNat_ofNat] at hz'
      omega
    subst i
    have hpad0 : ws = padWin srcBytes orig len 0 := by
      rw [hwin]
      simp [copyWin, padWin]
    simp only [show (sszPackBytesFn src dst len srcBytes orig).rw.base = dst from rfl,
      show (sszPackBytesFn src dst len srcBytes orig).region = ⟨src, srcBytes⟩ from rfl]
    have hrem_exec :
        execBlock ⟨src, srcBytes⟩ dst rf₁ ws
            [.ANDI .x7 .x11 (31 : BitVec 12)] =
          (rf₁.set .x7 (rf₁.get .x11 &&& signExtend12 (31 : BitVec 12)), ws) := by
      simp [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    rw [hrem_exec]
    have hmask :
        (rf₁.get .x11 &&& signExtend12 (31 : BitVec 12)).toNat = len % 32 := by
      rw [hx11]
      have hse : signExtend12 (31 : BitVec 12) = (31 : Word) := by decide
      rw [hse, toNat_and_31]
    have hguard_ne :
        (rf₁.get .x11 &&& signExtend12 (31 : BitVec 12)) ≠ (0 : Word) := by
      simpa [Cond.holds, RegFile.get_x0, execInstrRF, aluSem] using hguard
    have hmod_ne : len % 32 ≠ 0 := by
      intro hz
      apply hguard_ne
      apply BitVec.eq_of_toNat_eq
      rw [hmask, hz]
      rfl
    have hpad : padLen len = 32 - len % 32 := by
      unfold padLen
      split <;> omega
    have hsub :
        (32 : Word) - (rf₁.get .x11 &&& signExtend12 (31 : BitVec 12)) =
          BitVec.ofNat 64 (32 - len % 32) := by
      have hse31 : signExtend12 (31 : BitVec 12) = (31 : Word) := by decide
      have hmask_eq :
          rf₁.get .x11 &&& (31 : Word) =
            BitVec.ofNat 64 (len % 32) := by
        have hmask' := hmask
        rw [hse31] at hmask'
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        have hm64 : len % 32 < 2 ^ 64 := by omega
        have hmodmod : (len % 32) % 2 ^ 64 = len % 32 :=
          Nat.mod_eq_of_lt hm64
        rw [hmodmod]
        exact hmask'
      simp only [hse31]
      rw [hmask_eq]
      have hm : len % 32 < 32 := Nat.mod_lt _ (by decide)
      interval_cases h : len % 32 <;> simp
    have hpad_exec :
        (execBlock ⟨src, srcBytes⟩ dst
          (rf₁.set .x7 (rf₁.get .x11 &&& signExtend12 (31 : BitVec 12))) ws
          [.LI .x28 (32 : Word), .SUB .x7 .x28 .x7]).1 =
          (rf₁.set .x7 (BitVec.ofNat 64 (padLen len))).set .x28 32 := by
      funext r
      by_cases hr7 : r = .x7
      · subst r
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
          RegFile.set, if_pos, if_neg, true_and,
          false_and, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
          reduceCtorEq, not_false_eq_true]
        rw [hsub, hpad]
      · by_cases hr28 : r = .x28
        · subst r
          simp [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.set]
        · simp [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.set,
            hr7, hr28]
    rw [hpad_exec]
    subst ws
    refine ⟨?_, ?_, ?_, ?_, ?_, by omega, hsrcLen, horig,
      hsrc, hdst, hdj, ?_, hA⟩
    · simp [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        hx6]
    · simp [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        hpad]
    · simp [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        hx10]
    · simp [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        hx11]
    · simp [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        hx12]
    · exact hpad0
  case sszPackBytes.padGuard.pad.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, hwslen, hreach, rfl, rfl⟩
    rcases hreach with ⟨h_inv, hcond⟩
    rcases h_inv with ⟨hx6, hx7, hx10, hx11, hx12, hkle,
      hsrcLen, horig, hsrc, hdst, hdisj, hwin, hA⟩
    change ws₀.length = outLen len at hwslen
    have hne : (BitVec.ofNat 64 (padLen len - i)) ≠ 0 := by
      simpa [Cond.holds, hx7, RegFile.get_x0] using hcond
    have hk : i < padLen len := by
      have hto : (BitVec.ofNat 64 (padLen len - i)).toNat ≠ (0 : Word).toNat := by
        intro hz
        apply hne
        exact BitVec.eq_of_toNat_eq (by simpa using hz)
      rw [show (0 : Word).toNat = 0 from rfl, BitVec.toNat_ofNat] at hto
      omega
    have hrem : len + padLen len = outLen len := by rfl
    simp only [show (sszPackBytesFn src dst len srcBytes orig).rw.base = dst from rfl,
      show (sszPackBytesFn src dst len srcBytes orig).region = ⟨src, srcBytes⟩ from rfl]
    rw [pad_engine src dst len (padLen len) i srcBytes rf₀ ws₀ hx6 hk
      (by rfl) hdst hwslen]
    exact pad_inv_step src dst len (padLen len) i srcBytes orig rf₀ ws₀ A'
      hk (by rfl) hsrcLen
      ⟨hx6, hx7, hx10, hx11, hx12, hkle, hsrcLen, horig, hsrc, hdst,
        hdisj, hwin, hA⟩
  case sszPackBytes.padGuard.pad.exhausted =>
    rintro rf ws A ⟨hx6, hx7, hx10, hx11, hx12, hkle, hsrcLen, horig,
      hsrc, hdst, hdisj, hwin, -⟩
    simp only [Cond.holds, not_not]
    have hpad : padLen len ≤ 31 := by
      unfold padLen
      split
      · omega
      · have hmod : len % 32 < 32 := Nat.mod_lt _ (by decide)
        omega
    have hzero : padLen len - 32 = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hx7, hzero]
    rfl
  case sszPackBytes.padGuard.pad.body.zeroByte.mem =>
    rintro rf ws A hwslen ⟨i, hi, ⟨hx6, hx7, hx10, hx11, hx12, hkle,
      hsrcLen, horig, hsrc, hdst, hdj, hwin, -⟩, _hcond⟩
    change ws.length = outLen len at hwslen
    have hbase : (sszPackBytesFn src dst len srcBytes orig).rw.base = dst := rfl
    have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
    have hrem : len + padLen len = outLen len := by rfl
    have hlen_i : len + i ≤ outLen len := by
      rw [← hrem]
      omega
    have haddr : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat =
        len + i := by
      rw [hx6, hse0]
      bv_omega
    have hnonzero : (BitVec.ofNat 64 (padLen len - i)) ≠ 0 := by
      simpa [Cond.holds, hx7, RegFile.get_x0] using _hcond
    have hk : i < padLen len := by
      have hto : (BitVec.ofNat 64 (padLen len - i)).toNat ≠ (0 : Word).toNat := by
        intro hz
        apply hnonzero
        exact BitVec.eq_of_toNat_eq (by simpa using hz)
      rw [show (0 : Word).toNat = 0 from rfl, BitVec.toNat_ofNat] at hto
      omega
    simp only [padStepBlock, blockVCs, loadSem, storeSem, inRw,
      hbase, hwslen, and_true]
    rw [haddr]
    constructor
    · rw [← hrem]
      omega
    · exact Nat.one_dvd _

  case sszPackBytes.post =>
    rintro rf ws A hsp
    dsimp [sszPackBytesFn, sszPackBytesBody, copyLoop, padLoop] at hsp ⊢
    simp only [Stmt.sp] at hsp
    rcases hsp with ⟨rf₁, ws₁, hwslen, hbranch, hfinalRf, hfinalWs⟩
    rw [hfinalRf, hfinalWs]
    rcases hbranch with hpad | hcopy
    · rcases hpad with ⟨⟨i, hi, hinv⟩, hnot⟩
      rcases hinv with ⟨hx6, hx7, hx10, hx11, hx12, hkle,
        hsrcLen, horig, hsrc, hdst, hdj, hwin, hA⟩
      have hout : outLen len < 2 ^ 64 := by omega
      have hcount := count_engine src dst len srcBytes ws₁ rf₁ hx11
        (count_bound_of_outLen_lt len hout)
      have hz : rf₁.get .x7 = 0 := by
        simpa [Cond.holds, RegFile.get_x0] using hnot
      have hi_eq : i = padLen len := by
        rw [hx7] at hz
        have hz' : (BitVec.ofNat 64 (padLen len - i)).toNat =
            (0 : Word).toNat := by rw [hz]
        rw [show (0 : Word).toNat = 0 from rfl,
          BitVec.toNat_ofNat] at hz'
        have hpadle : padLen len ≤ 31 := by
          unfold padLen
          split
          · omega
          · have hmod : len % 32 < 32 := Nat.mod_lt _ (by decide)
            omega
        have hsmall : padLen len - i < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hsmall] at hz'
        omega
      refine ⟨?_, ?_, hA⟩
      · exact hcount
      · change ws₁ = packedBytes srcBytes len
        rw [hwin, hi_eq]
        unfold packedBytes padWin
        have hdrop : orig.drop (outLen len) = [] :=
          List.drop_eq_nil_of_le (by rw [horig])
        rw [show len + padLen len = outLen len by rfl, hdrop,
          List.append_nil]
    · rcases hcopy with ⟨hcopy, hnot⟩
      rcases hcopy with ⟨rf₂, ws₂, hws₂, hreach, hremRf, hremWs⟩
      rcases hreach with ⟨⟨i, hi, hinv⟩, hnot₂⟩
      rcases hinv with ⟨hx5, hx6, hx7, hx10, hx11, hx12, hile,
        hsrcLen, horig, hsrc, hdst, hdj, hwin, hA⟩
      have hi_eq : i = len := by
        have hz : rf₂.get .x7 = 0 := by
          simpa [Cond.holds, RegFile.get_x0] using hnot₂
        rw [hx7] at hz
        have hz' : (BitVec.ofNat 64 (len - i)).toNat =
            (0 : Word).toNat := by rw [hz]
        rw [show (0 : Word).toNat = 0 from rfl,
          BitVec.toNat_ofNat] at hz'
        omega
      have hremRf' : rf₁ = rf₂.set .x7 (BitVec.ofNat 64 (len % 32)) := by
        have hrem := remainder_engine src dst len srcBytes ws₂ rf₂ hx11
        calc
          rf₁ = (execBlock ⟨src, srcBytes⟩ dst rf₂ ws₂
            [.ANDI .x7 .x11 (31 : BitVec 12)]).1 := hremRf
          _ = (rf₂.set .x7 (BitVec.ofNat 64 (len % 32))) := by
            exact congrArg Prod.fst hrem
      have hremWs' : ws₁ = ws₂ := by
        have hrem := remainder_engine src dst len srcBytes ws₂ rf₂ hx11
        calc
          ws₁ = (execBlock ⟨src, srcBytes⟩ dst rf₂ ws₂
            [.ANDI .x7 .x11 (31 : BitVec 12)]).2 := hremWs
          _ = ws₂ := by exact congrArg Prod.snd hrem
      have hz : rf₁.get .x7 = 0 := by
        simpa [Cond.holds, RegFile.get_x0] using hnot
      have hmod : len % 32 = 0 := by
        rw [hremRf'] at hz
        have hz' : BitVec.ofNat 64 (len % 32) = (0 : Word) := by
          simpa using hz
        have hzNat := congrArg BitVec.toNat hz'
        rw [BitVec.toNat_ofNat] at hzNat
        have hmodlt : len % 32 < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hmodlt] at hzNat
        exact hzNat
      have hpad0 : padLen len = 0 := by
        unfold padLen
        simp [hmod]
      have hout : outLen len < 2 ^ 64 := by omega
      have hx11₁ : rf₁.get .x11 = BitVec.ofNat 64 len := by
        rw [hremRf']
        simp [hx11]
      have hcount := count_engine src dst len srcBytes ws₁ rf₁ hx11₁
        (count_bound_of_outLen_lt len hout)
      have hcopyWin : ws₂ = packedBytes srcBytes len := by
        rw [hwin, hi_eq]
        unfold copyWin packedBytes
        rw [hpad0]
        have houtEq : outLen len = len := by simp [outLen, hpad0]
        have hdrop : orig.drop len = [] :=
          List.drop_eq_nil_of_le (by rw [horig, houtEq])
        rw [hdrop, List.append_nil]
        simp
      refine ⟨?_, ?_, hA⟩
      · exact hcount
      · change ws₁ = packedBytes srcBytes len
        rw [hremWs', hcopyWin]

-- The structured body has exactly the emitted instruction layout.  This is
-- the drift guard; it intentionally remains independent of the pending VCs.
#guard (sszPackBytesBody 0 0 0 [] []).flatten 0 ++
    [Instr.JALR .x0 .x1 (0 : BitVec 12)] = sszPackBytes_prog

/-! ## Flat linked-entry contract (#12244)

    The last plain model-only leaf. Anchored over
    `CodeReq.ofProg (GuestAddrs.ssz_pack_bytes) sszPackBytes_prog` — the
    `GuestImageEntries` pairing — so this is a statement about the DEPLOYED image, not
    about a model.

    ⚠️ Two different register splits, one per direction, because the contract is
    asymmetric: the PRE pins three ABI registers (`a0`=src, `a1`=len, `a2`=dst) while the
    POST *publishes* `a0` as the SSZ chunk count and says nothing about `a1`/`a2`. So the
    pre peels `packArgScratch` (12 registers) and the post owns `packResScratch` (14).
    Templates: `RevLeBeFlat.revLeBeFlat_at` for the three-register copier pre,
    `AmbientLifted.exposedRegs_split_a0` for the published-result post.

    ⚠️ NOT total over its argument types: besides the length and no-wraparound
    hypotheses it needs `hdj` — source and destination DISJOINT — for the same reason as
    the reverse-copy: the block engine's `inRw` routing test is ARITHMETIC, so without it
    a byte load aimed at the source could be routed into the writable window. The source
    region is pinned INTACT in the post. -/

def sszPackBytesCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.ssz_pack_bytes : Word) sszPackBytes_prog

/-- Exposed registers excluding the three ABI argument registers. -/
def packArgScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x13, .x14, .x15, .x16, .x17]

/-- Exposed registers excluding only the result register `a0`. -/
def packResScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_pack3 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
          (.x12 ↦ᵣ vf .x12) ** regAtomsOf vf packArgScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [packArgScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem exposedRegs_split_pack1 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf packResScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [packResScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_packArgScratch : (.x10 : Reg) ∉ packArgScratch := by decide
private theorem x11_notin_packArgScratch : (.x11 : Reg) ∉ packArgScratch := by decide
private theorem x12_notin_packArgScratch : (.x12 : Reg) ∉ packArgScratch := by decide

/-- **`ssz_pack_bytes`, whole-routine flat triple at the guest entry.**

    Copies the first `len` bytes at `a0` into the output window at `a2` and zero-pads to
    the next 32-byte chunk boundary (`outLen len`), returning the CHUNK COUNT in `a0`.
    The output window becomes exactly `packedBytes srcBytes len`. -/
theorem sszPackBytesFlat_spec (ret src dst : Word) (len : Nat)
    (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf)
    (hrww : RwRegion.wf ⟨dst, outLen len⟩)
    (hsl : srcBytes.length ≥ len) (hol : orig.length = outLen len)
    (hsb : src.toNat + len < 2 ^ 64) (hdb : dst.toNat + outLen len < 2 ^ 64)
    (hdj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + outLen len ≤ src.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((sszPackBytesFn src dst len srcBytes orig).body.steps + 1)
      (GuestAddrs.ssz_pack_bytes : Word) ret sszPackBytesCr
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 len) ** ((.x12 : Reg) ↦ᵣ dst) **
        regOwns packArgScratch ** bytesRegion dst orig ** bytesRegion src srcBytes)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (chunkCount len)) **
        regOwns packResScratch ** bytesRegion dst (packedBytes srcBytes len) **
        bytesRegion src srcBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns packArgScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 len) ** ((.x12 : Reg) ↦ᵣ dst) **
        bytesRegion dst orig ** bytesRegion src srcBytes)
      (fun vf => ?_))
  -- ⚠️ if-valuation written INLINE: a `set` here puts the routine's arguments into the
  -- expected type of the `Fn.retSpecFlat` application and elaboration rejects it.
  have hpre : (sszPackBytesFn src dst len srcBytes orig).pre
      (fun r => if r = .x10 then src else if r = .x11 then BitVec.ofNat 64 len
        else if r = .x12 then dst else vf r)
      orig empAssertion := by
    refine ⟨?_, ?_, ?_, rfl, hsl, hol, hsb, hdb, hdj, rfl⟩
    · show RegFile.get _ .x10 = src
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = BitVec.ofNat 64 len
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0),
        if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
  have had := Fn.retSpecFlat (sszPackBytesFn src dst len srcBytes orig)
    (GuestAddrs.ssz_pack_bytes : Word)
    (sszPackBytesFn_spec src dst len srcBytes orig hwf hrww
      (GuestAddrs.ssz_pack_bytes : Word))
    -- 21 = the flattened body length; `sszPackBytes_prog` is 22 instructions with its ret.
    (by show 4 * (21 + 1) ≤ 2 ^ 64; decide)
    ret halign
    (fun r => if r = .x10 then src else if r = .x11 then BitVec.ofNat 64 len
      else if r = .x12 then dst else vf r)
    orig (by exact hol) hpre
    (Q := (((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (chunkCount len)) **
        regOwns packResScratch) ** bytesRegion dst (packedBytes srcBytes len))
    -- `hpostEmp`: the ambient is pinned by the `Fn` post's third conjunct.
    (fun _ _ _ hpost => hpost.2.2)
    (fun rf' ws' _hlen hpost hp hh => by
      obtain ⟨hx10, hws, -⟩ := hpost
      subst hws
      have g10 : rf' .x10 = BitVec.ofNat 64 (chunkCount len) := by
        rw [← hx10, RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_pack1, g10] at hh
      refine sepConj_mono_left ?_ hp hh
      exact fun h hx =>
        sepConj_mono_right (regAtomsOf_to_regOwns (fun r => rf' r) packResScratch) h hx)
  rw [show (sszPackBytesFn src dst len srcBytes orig).programRet
      (GuestAddrs.ssz_pack_bytes : Word) = sszPackBytes_prog from rfl] at had
  rw [show (sszPackBytesFn src dst len srcBytes orig).region.base = src from rfl,
      show (sszPackBytesFn src dst len srcBytes orig).region.bytes = srcBytes from rfl,
      show (sszPackBytesFn src dst len srcBytes orig).rw.base = dst from rfl] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_pack3,
    show (if (Reg.x10 : Reg) = .x10 then src else
        if (Reg.x10 : Reg) = .x11 then BitVec.ofNat 64 len else
        if (Reg.x10 : Reg) = .x12 then dst else vf .x10) = src from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then src else
        if (Reg.x11 : Reg) = .x11 then BitVec.ofNat 64 len else
        if (Reg.x11 : Reg) = .x12 then dst else vf .x11)
      = BitVec.ofNat 64 len from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    show (if (Reg.x12 : Reg) = .x10 then src else
        if (Reg.x12 : Reg) = .x11 then BitVec.ofNat 64 len else
        if (Reg.x12 : Reg) = .x12 then dst else vf .x12) = dst from by
      rw [if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x10)),
        if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x11))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then src else if r = .x11 then BitVec.ofNat 64 len
        else if r = .x12 then dst else vf r)
      vf packArgScratch
      (fun r hr => by
        show (if r = .x10 then src else if r = .x11 then BitVec.ofNat 64 len
          else if r = .x12 then dst else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_packArgScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_packArgScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x12) => x12_notin_packArgScratch (hc ▸ hr))])]
    at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

end SszPackBytesSAsm
end EvmAsm.Codegen
