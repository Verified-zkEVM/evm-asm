/-
  EvmAsm.Codegen.Programs.Bn254Fp2CopySAsm

  Verified SAsm port of `bnp_fp2_copy`: copy the 64-byte BN254 Fp2 buffer from
  `a0` to the writable destination at `a1`.  The emitted routine is a
  straight-line sequence of eight LD/SD dword pairs.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bn254Fp2

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Bn254Fp2CopySAsm

private def bnpFp2CopyInstrs : List Instr :=
  [.LD .x5 .x10 (0 : BitVec 12), .SD .x11 .x5 (0 : BitVec 12),
   .LD .x5 .x10 (8 : BitVec 12), .SD .x11 .x5 (8 : BitVec 12),
   .LD .x5 .x10 (16 : BitVec 12), .SD .x11 .x5 (16 : BitVec 12),
   .LD .x5 .x10 (24 : BitVec 12), .SD .x11 .x5 (24 : BitVec 12),
   .LD .x5 .x10 (32 : BitVec 12), .SD .x11 .x5 (32 : BitVec 12),
   .LD .x5 .x10 (40 : BitVec 12), .SD .x11 .x5 (40 : BitVec 12),
   .LD .x5 .x10 (48 : BitVec 12), .SD .x11 .x5 (48 : BitVec 12),
   .LD .x5 .x10 (56 : BitVec 12), .SD .x11 .x5 (56 : BitVec 12)]

def bnpFp2CopyBody : Stmt := .block "copy" bnpFp2CopyInstrs

def frameOk64 (src dst : Word) : Prop :=
  src.toNat + 64 < 2 ^ 64 ∧ dst.toNat + 64 < 2 ^ 64 ∧
    (src.toNat + 64 ≤ dst.toNat ∨ dst.toNat + 64 ≤ src.toNat)

def bnpFp2CopyFn (src dst : Word) (srcBytes orig : List (BitVec 8)) : Fn where
  name := "bnpFp2Copy"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 64⟩
  pre := fun rf ws _ =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ ws = orig ∧
    orig.length = 64 ∧ srcBytes.length = 64 ∧ frameOk64 src dst
  post := fun _ ws _ => ws = srcBytes
  body := bnpFp2CopyBody

def bnpFp2Copy_verified : Program := bnpFp2CopyBody.flatten 0

#guard (bnpFp2Copy_verified : List Instr).length = 16
#guard bnpFp2CopyBody.flatten 0 = bnpFp2CopyBody.flatten 0x80000000
#guard bnpFp2CopyBody.flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = bnpFp2Copy_prog

private theorem se12_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se12_8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem se12_16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
private theorem se12_24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
private theorem se12_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
private theorem se12_40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by decide
private theorem se12_48 : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
private theorem se12_56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide

private def copyWin64 (srcBytes orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  srcBytes.take (8 * i) ++ orig.drop (8 * i)

private theorem copyWin64_zero (srcBytes orig : List (BitVec 8)) :
    copyWin64 srcBytes orig 0 = orig := by
  simp [copyWin64]

private theorem copyWin64_8_eq (srcBytes orig : List (BitVec 8))
    (hs : srcBytes.length = 64) (ho : orig.length = 64) :
    copyWin64 srcBytes orig 8 = srcBytes := by
  simp only [copyWin64, Nat.reduceMul]
  rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.append_nil]

private theorem copyWin64_step (srcBytes orig : List (BitVec 8)) (i : Nat)
    (hs : srcBytes.length = 64) (ho : orig.length = 64) (hi : i < 8) :
    setBytes (copyWin64 srcBytes orig i) (8 * i)
      (dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8))) =
    copyWin64 srcBytes orig (i + 1) := by
  have htake : (srcBytes.take (8 * i)).length = 8 * i := by
    simp only [List.length_take, hs]
    omega
  have hseglen : ((srcBytes.drop (8 * i)).take 8).length = 8 := by
    simp only [List.length_take, List.length_drop, hs]
    omega
  have hpayload : dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8)) =
      (srcBytes.drop (8 * i)).take 8 := by
    exact dwordBytes_packBytes _ hseglen
  rw [hpayload]
  rw [copyWin64]
  rw [setBytes_append_right _ _ _ _ (by rw [htake])]
  rw [htake, Nat.sub_self]
  have hfit : 0 + ((srcBytes.drop (8 * i)).take 8).length ≤ (orig.drop (8 * i)).length := by
    rw [hseglen]
    simp only [List.length_drop, ho]
    omega
  have hslot := setBytes_slot (orig.drop (8 * i)) ((srcBytes.drop (8 * i)).take 8) 0 hfit
  rw [List.drop_zero, hseglen] at hslot
  have hdrop : (setBytes (orig.drop (8 * i)) 0 ((srcBytes.drop (8 * i)).take 8)).drop 8
      = (orig.drop (8 * i)).drop 8 := by
    simpa [hseglen] using
      (setBytes_drop_of_le ((srcBytes.drop (8 * i)).take 8) (orig.drop (8 * i)) 0 8 (by
        rw [hseglen]))
  have hset : setBytes (orig.drop (8 * i)) 0 ((srcBytes.drop (8 * i)).take 8)
      = (srcBytes.drop (8 * i)).take 8 ++ (orig.drop (8 * i)).drop 8 := by
    conv_lhs =>
      rw [← List.take_append_drop 8
        (setBytes (orig.drop (8 * i)) 0 ((srcBytes.drop (8 * i)).take 8))]
    rw [hslot, hdrop]
  rw [hset]
  rw [show (orig.drop (8 * i)).drop 8 = orig.drop (8 * (i + 1)) from by
    rw [List.drop_drop]
    congr 1]
  simp only [copyWin64]
  rw [← List.append_assoc]
  congr 1
  rw [show srcBytes.take (8 * i) ++ (srcBytes.drop (8 * i)).take 8 =
      srcBytes.take (8 * (i + 1)) from by
    rw [← List.take_add]
    congr 1]

private theorem copy_load_miss (src dst : Word) (w : List (BitVec 8)) (k : Nat)
    (hwl : w.length = 64) (hk : k ≤ 56) (hnw_s : src.toNat + 64 < 2 ^ 64)
    (hnw_d : dst.toNat + 64 < 2 ^ 64)
    (hdisj : src.toNat + 64 ≤ dst.toNat ∨ dst.toNat + 64 ≤ src.toNat) :
    ¬ inRw dst w (src + BitVec.ofNat 64 k) 8 := by
  unfold inRw
  rw [hwl]
  rcases hdisj with h | h <;> bv_omega

private theorem execInstrRF_ld_romiss (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (v : Word)
    (hmiss : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 8)
    (hv : ro.dwordAt (rf.get rs1 + signExtend12 ofs) = v) :
    execInstrRF ro rwBase rf ws (.LD rd rs1 ofs) = (rf.set rd v, ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg hmiss, hv]

private theorem copyFold64 (orig srcBytes : List (BitVec 8))
    (ho : orig.length = 64) (hs : srcBytes.length = 64) :
    setBytes (setBytes (setBytes (setBytes (setBytes (setBytes (setBytes (setBytes orig 0
        (dwordBytes (packBytes ((srcBytes.drop 0).take 8)))) 8
        (dwordBytes (packBytes ((srcBytes.drop 8).take 8)))) 16
        (dwordBytes (packBytes ((srcBytes.drop 16).take 8)))) 24
        (dwordBytes (packBytes ((srcBytes.drop 24).take 8)))) 32
        (dwordBytes (packBytes ((srcBytes.drop 32).take 8)))) 40
        (dwordBytes (packBytes ((srcBytes.drop 40).take 8)))) 48
        (dwordBytes (packBytes ((srcBytes.drop 48).take 8)))) 56
        (dwordBytes (packBytes ((srcBytes.drop 56).take 8))) = srcBytes := by
  rw [show orig = copyWin64 srcBytes orig 0 from by rw [copyWin64_zero]]
  rw [copyWin64_step srcBytes orig 0 hs ho (by omega),
    copyWin64_step srcBytes orig 1 hs ho (by omega),
    copyWin64_step srcBytes orig 2 hs ho (by omega),
    copyWin64_step srcBytes orig 3 hs ho (by omega),
    copyWin64_step srcBytes orig 4 hs ho (by omega),
    copyWin64_step srcBytes orig 5 hs ho (by omega),
    copyWin64_step srcBytes orig 6 hs ho (by omega),
    copyWin64_step srcBytes orig 7 hs ho (by omega),
    copyWin64_8_eq srcBytes orig hs ho]



private theorem off_load_ok64 (base : Word) (k : Nat) (hk : k ≤ 56) (hdiv : 8 ∣ k) :
    8 ∣ (base + BitVec.ofNat 64 k - base).toNat ∧
      (base + BitVec.ofNat 64 k - base).toNat + 8 ≤ 64 := by
  rw [show (base + BitVec.ofNat 64 k - base).toNat = k from by bv_omega]
  omega

private theorem off_store_ok64 (base : Word) (k : Nat) (hk : k ≤ 56) (hdiv : 8 ∣ k) :
    (base + BitVec.ofNat 64 k - base).toNat + 8 ≤ 64 ∧
      8 ∣ (base + BitVec.ofNat 64 k - base).toNat := by
  rw [show (base + BitVec.ofNat 64 k - base).toNat = k from by bv_omega]
  omega

private theorem copy_blockVCs (src dst : Word) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8))
    (hx10 : rf.get .x10 = src) (hx11 : rf.get .x11 = dst)
    (hws : ws.length = 64) (hs : srcBytes.length = 64) (hfr : frameOk64 src dst) :
    blockVCs ⟨src, srcBytes⟩ dst rf ws bnpFp2CopyInstrs := by
  obtain ⟨hnws, hnwd, hdisj⟩ := hfr
  have hxne1 : Reg.x10 ≠ Reg.x5 := by decide
  have hxne2 : Reg.x11 ≠ Reg.x5 := by decide
  have hmiss : ∀ (w : List (BitVec 8)) (ofs : BitVec 12) (k : Nat), w.length = 64 →
      signExtend12 ofs = BitVec.ofNat 64 k → k ≤ 56 →
      ¬ inRw dst w (rf.get .x10 + signExtend12 ofs) 8 := by
    intro w ofs k hwl hofs hk
    rw [hofs, hx10]
    exact copy_load_miss src dst w k hwl hk hnws hnwd hdisj
  simp only [bnpFp2CopyInstrs, blockVCs, loadSem, storeSem, execInstrRF_ld_snd,
    execInstrRF_sd_fst, execInstrRF_sd_snd, execInstrRF_ld_get_ne (h := hxne1),
    execInstrRF_ld_get_ne (h := hxne2)]
  rw [if_neg (hmiss _ 0 0 (by simp only [hws]) se12_0 (by decide)),
    if_neg (hmiss _ 8 8 (by simp only [length_setBytes, hws]) se12_8 (by decide)),
    if_neg (hmiss _ 16 16 (by simp only [length_setBytes, hws]) se12_16 (by decide)),
    if_neg (hmiss _ 24 24 (by simp only [length_setBytes, hws]) se12_24 (by decide)),
    if_neg (hmiss _ 32 32 (by simp only [length_setBytes, hws]) se12_32 (by decide)),
    if_neg (hmiss _ 40 40 (by simp only [length_setBytes, hws]) se12_40 (by decide)),
    if_neg (hmiss _ 48 48 (by simp only [length_setBytes, hws]) se12_48 (by decide)),
    if_neg (hmiss _ 56 56 (by simp only [length_setBytes, hws]) se12_56 (by decide))]
  simp only [Region.loadOk, inRw, hx10, hx11, se12_0, se12_8, se12_16, se12_24,
    se12_32, se12_40, se12_48, se12_56, length_setBytes, hws, hs]
  exact ⟨off_load_ok64 src 0 (by decide) (by decide),
    off_store_ok64 dst 0 (by decide) (by decide),
    off_load_ok64 src 8 (by decide) (by decide),
    off_store_ok64 dst 8 (by decide) (by decide),
    off_load_ok64 src 16 (by decide) (by decide),
    off_store_ok64 dst 16 (by decide) (by decide),
    off_load_ok64 src 24 (by decide) (by decide),
    off_store_ok64 dst 24 (by decide) (by decide),
    off_load_ok64 src 32 (by decide) (by decide),
    off_store_ok64 dst 32 (by decide) (by decide),
    off_load_ok64 src 40 (by decide) (by decide),
    off_store_ok64 dst 40 (by decide) (by decide),
    off_load_ok64 src 48 (by decide) (by decide),
    off_store_ok64 dst 48 (by decide) (by decide),
    off_load_ok64 src 56 (by decide) (by decide),
    off_store_ok64 dst 56 (by decide) (by decide), trivial⟩

private theorem copy_engine (src dst : Word) (srcBytes orig : List (BitVec 8))
    (rf : RegFile) (hsrc : srcBytes.length = 64) (horig : orig.length = 64)
    (hx10 : rf.get .x10 = src) (hx11 : rf.get .x11 = dst) (hfr : frameOk64 src dst) :
    (execBlock ⟨src, srcBytes⟩ dst rf orig bnpFp2CopyInstrs).2 = srcBytes := by
  obtain ⟨hnw_s, hnw_d, hdisj⟩ := hfr
  set v0 := Region.dwordAt ⟨src, srcBytes⟩ (src + signExtend12 0) with hv0
  set v8 := Region.dwordAt ⟨src, srcBytes⟩ (src + signExtend12 8) with hv8
  set v16 := Region.dwordAt ⟨src, srcBytes⟩ (src + signExtend12 16) with hv16
  set v24 := Region.dwordAt ⟨src, srcBytes⟩ (src + signExtend12 24) with hv24
  set v32 := Region.dwordAt ⟨src, srcBytes⟩ (src + signExtend12 32) with hv32
  set v40 := Region.dwordAt ⟨src, srcBytes⟩ (src + signExtend12 40) with hv40
  set v48 := Region.dwordAt ⟨src, srcBytes⟩ (src + signExtend12 48) with hv48
  set v56 := Region.dwordAt ⟨src, srcBytes⟩ (src + signExtend12 56) with hv56
  have hxne : (Reg.x10 ≠ .x5) ∧ (Reg.x11 ≠ .x5) := ⟨by decide, by decide⟩
  simp only [bnpFp2CopyInstrs]
  rw [execBlock_cons, execInstrRF_ld_romiss ⟨src, srcBytes⟩ dst rf orig .x5 .x10 0 v0
    (by rw [hx10]; exact copy_load_miss src dst orig 0 horig (by omega) hnw_s hnw_d hdisj)
    (by rw [hv0, hx10])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword ⟨src, srcBytes⟩ dst _ orig .x11 .x5 0 0
    (by rw [RegFile.get_set_ne _ _ _ _ hxne.2, hx11, se12_0]; bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide)]
  rw [execBlock_cons, execInstrRF_ld_romiss ⟨src, srcBytes⟩ dst _ _ .x5 .x10 8 v8
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.1, hx10]
        exact copy_load_miss src dst _ 8 (by simp [length_setBytes, horig]) (by omega)
          hnw_s hnw_d hdisj)
    (by simp only [hv8, RegFile.get_set_ne _ _ _ _ hxne.1, hx10])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword ⟨src, srcBytes⟩ dst _ _ .x11 .x5 8 8
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.2, hx11, se12_8]; bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide)]
  rw [execBlock_cons, execInstrRF_ld_romiss ⟨src, srcBytes⟩ dst _ _ .x5 .x10 16 v16
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.1, hx10]
        exact copy_load_miss src dst _ 16 (by simp [length_setBytes, horig]) (by omega)
          hnw_s hnw_d hdisj)
    (by simp only [hv16, RegFile.get_set_ne _ _ _ _ hxne.1, hx10])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword ⟨src, srcBytes⟩ dst _ _ .x11 .x5 16 16
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.2, hx11, se12_16]; bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide)]
  rw [execBlock_cons, execInstrRF_ld_romiss ⟨src, srcBytes⟩ dst _ _ .x5 .x10 24 v24
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.1, hx10]
        exact copy_load_miss src dst _ 24 (by simp [length_setBytes, horig]) (by omega)
          hnw_s hnw_d hdisj)
    (by simp only [hv24, RegFile.get_set_ne _ _ _ _ hxne.1, hx10])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword ⟨src, srcBytes⟩ dst _ _ .x11 .x5 24 24
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.2, hx11, se12_24]; bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide)]
  rw [execBlock_cons, execInstrRF_ld_romiss ⟨src, srcBytes⟩ dst _ _ .x5 .x10 32 v32
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.1, hx10]
        exact copy_load_miss src dst _ 32 (by simp [length_setBytes, horig]) (by omega)
          hnw_s hnw_d hdisj)
    (by simp only [hv32, RegFile.get_set_ne _ _ _ _ hxne.1, hx10])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword ⟨src, srcBytes⟩ dst _ _ .x11 .x5 32 32
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.2, hx11, se12_32]; bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide)]
  rw [execBlock_cons, execInstrRF_ld_romiss ⟨src, srcBytes⟩ dst _ _ .x5 .x10 40 v40
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.1, hx10]
        exact copy_load_miss src dst _ 40 (by simp [length_setBytes, horig]) (by omega)
          hnw_s hnw_d hdisj)
    (by simp only [hv40, RegFile.get_set_ne _ _ _ _ hxne.1, hx10])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword ⟨src, srcBytes⟩ dst _ _ .x11 .x5 40 40
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.2, hx11, se12_40]; bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide)]
  rw [execBlock_cons, execInstrRF_ld_romiss ⟨src, srcBytes⟩ dst _ _ .x5 .x10 48 v48
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.1, hx10]
        exact copy_load_miss src dst _ 48 (by simp [length_setBytes, horig]) (by omega)
          hnw_s hnw_d hdisj)
    (by simp only [hv48, RegFile.get_set_ne _ _ _ _ hxne.1, hx10])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword ⟨src, srcBytes⟩ dst _ _ .x11 .x5 48 48
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.2, hx11, se12_48]; bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide)]
  rw [execBlock_cons, execInstrRF_ld_romiss ⟨src, srcBytes⟩ dst _ _ .x5 .x10 56 v56
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.1, hx10]
        exact copy_load_miss src dst _ 56 (by simp [length_setBytes, horig]) (by omega)
          hnw_s hnw_d hdisj)
    (by simp only [hv56, RegFile.get_set_ne _ _ _ _ hxne.1, hx10])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword ⟨src, srcBytes⟩ dst _ _ .x11 .x5 56 56
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.2, hx11, se12_56]; bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), execBlock_nil]
  dsimp only
  rw [hv0, hv8, hv16, hv24, hv32, hv40, hv48, hv56]
  simp only [Region.dwordAt, se12_0, se12_8, se12_16, se12_24, se12_32, se12_40,
    se12_48, se12_56]
  rw [show (src + 0 - src).toNat = 0 from by bv_omega,
    show (src + 8 - src).toNat = 8 from by bv_omega,
    show (src + 16 - src).toNat = 16 from by bv_omega,
    show (src + 24 - src).toNat = 24 from by bv_omega,
    show (src + 32 - src).toNat = 32 from by bv_omega,
    show (src + 40 - src).toNat = 40 from by bv_omega,
    show (src + 48 - src).toNat = 48 from by bv_omega,
    show (src + 56 - src).toNat = 56 from by bv_omega]
  exact copyFold64 orig srcBytes horig hsrc

theorem bnpFp2CopyFn_spec (src dst : Word) (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf) (hrww : RwRegion.wf ⟨dst, 64⟩) (base : Word) :
    (bnpFp2CopyFn src dst srcBytes orig).Spec base := by
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case bnpFp2Copy.copy.mem =>
    rintro rf ws A hlen ⟨hx10, hx11, -, -, hs, hfr⟩
    exact copy_blockVCs src dst srcBytes rf ws hx10 hx11 hlen hs hfr
  case bnpFp2Copy.post =>
    rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨hx10, hx11, hwseq, hlenorig, hs, hfr⟩, hrfeq, hwseq2⟩
    subst ws₀
    rw [hwseq2]
    exact copy_engine src dst srcBytes orig rf₀ hs hlenorig hx10 hx11 hfr

end Bn254Fp2CopySAsm

end EvmAsm.Codegen
