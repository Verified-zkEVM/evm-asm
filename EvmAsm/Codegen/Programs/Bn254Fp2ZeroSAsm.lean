/-
  EvmAsm.Codegen.Programs.Bn254Fp2ZeroSAsm

  Verified SAsm port of `bnp_fp2_zero`: zero the 64-byte BN254 Fp2 buffer at
  `a0`.  The emitted routine is eight straight-line aligned dword stores.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bn254Fp2

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Bn254Fp2ZeroSAsm

/-- The eight stores of `bnp_fp2_zero`, excluding the shared `ret`. -/
private def bnpFp2ZeroInstrs : List Instr :=
  [ .SD .x10 .x0 (0 : BitVec 12),
    .SD .x10 .x0 (8 : BitVec 12),
    .SD .x10 .x0 (16 : BitVec 12),
    .SD .x10 .x0 (24 : BitVec 12),
    .SD .x10 .x0 (32 : BitVec 12),
    .SD .x10 .x0 (40 : BitVec 12),
    .SD .x10 .x0 (48 : BitVec 12),
    .SD .x10 .x0 (56 : BitVec 12) ]

def bnpFp2ZeroBody : Stmt :=
  .block "zero" bnpFp2ZeroInstrs

def bnpFp2ZeroFn (dst : Word) (orig : List (BitVec 8)) : Fn where
  name := "bnpFp2Zero"
  rw := ⟨dst, 64⟩
  pre := fun rf ws _ => rf.get .x10 = dst ∧ ws = orig ∧ orig.length = 64
  post := fun _ ws _ => ws = List.replicate 64 (0 : BitVec 8)
  body := bnpFp2ZeroBody

/-- Byte-identity to the emitted guest routine. -/
theorem bnpFp2Zero_byte_tie :
    bnpFp2ZeroBody.flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = bnpFp2Zero_prog := rfl

#guard bnpFp2ZeroBody.flatten 0 = bnpFp2ZeroBody.flatten 0x80000000
#guard (bnpFp2ZeroBody.flatten 0).length = 8

private theorem se12_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se12_8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem se12_16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
private theorem se12_24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
private theorem se12_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
private theorem se12_40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by decide
private theorem se12_48 : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
private theorem se12_56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide

private theorem inRw_store64 (dst : Word) (ws : List (BitVec 8)) (ofs : Word)
    (hws : ws.length = 64)
    (hofs : ofs = 0 ∨ ofs = 8 ∨ ofs = 16 ∨ ofs = 24 ∨
      ofs = 32 ∨ ofs = 40 ∨ ofs = 48 ∨ ofs = 56) :
    inRw dst ws (dst + ofs) 8 ∧ 8 ∣ ((dst + ofs) - dst).toNat := by
  rcases hofs with rfl | hofs
  · constructor <;> first | (unfold inRw; rw [hws]; bv_omega) | bv_omega
  rcases hofs with rfl | hofs
  · constructor <;> first | (unfold inRw; rw [hws]; bv_omega) | bv_omega
  rcases hofs with rfl | hofs
  · constructor <;> first | (unfold inRw; rw [hws]; bv_omega) | bv_omega
  rcases hofs with rfl | hofs
  · constructor <;> first | (unfold inRw; rw [hws]; bv_omega) | bv_omega
  rcases hofs with rfl | hofs
  · constructor <;> first | (unfold inRw; rw [hws]; bv_omega) | bv_omega
  rcases hofs with rfl | hofs
  · constructor <;> first | (unfold inRw; rw [hws]; bv_omega) | bv_omega
  rcases hofs with rfl | hofs
  · constructor <;> first | (unfold inRw; rw [hws]; bv_omega) | bv_omega
  rcases hofs with rfl
  constructor <;> first | (unfold inRw; rw [hws]; bv_omega) | bv_omega


private theorem inRw_store64_ofs (dst : Word) (ws : List (BitVec 8)) (ofs : Word)
    (hws : ws.length = 64)
    (hofs : ofs = 0 ∨ ofs = 8 ∨ ofs = 16 ∨ ofs = 24 ∨
      ofs = 32 ∨ ofs = 40 ∨ ofs = 48 ∨ ofs = 56) :
    inRw dst ws (dst + ofs) 8 :=
  (inRw_store64 dst ws ofs hws hofs).1

private theorem div8_store64_ofs (dst : Word) (ofs : Word)
    (hofs : ofs = 0 ∨ ofs = 8 ∨ ofs = 16 ∨ ofs = 24 ∨
      ofs = 32 ∨ ofs = 40 ∨ ofs = 48 ∨ ofs = 56) :
    8 ∣ ((dst + ofs) - dst).toNat :=
  (inRw_store64 dst (List.replicate 64 (0 : BitVec 8)) ofs (by simp) hofs).2

def zeroWin64 (orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  List.replicate (8 * i) (0 : BitVec 8) ++ orig.drop (8 * i)

theorem zeroWin64_zero (orig : List (BitVec 8)) : zeroWin64 orig 0 = orig := by
  simp [zeroWin64]

theorem zeroWin64_8_eq (orig : List (BitVec 8)) (h : orig.length = 64) :
    zeroWin64 orig 8 = List.replicate 64 (0 : BitVec 8) := by
  simp only [zeroWin64, Nat.reduceMul,
    List.drop_eq_nil_of_le (by omega : orig.length <= 64), List.append_nil]

theorem zeroWin64_step (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 64) (hi : i < 8) :
    setBytes (zeroWin64 orig i) (8 * i) (dwordBytes (0 : Word)) = zeroWin64 orig (i + 1) := by
  rw [zeroWin64]
  rw [setBytes_append_right _ _ _ _ (by simp)]
  simp only [List.length_replicate, Nat.sub_self]
  have hsuf : (orig.drop (8 * i)).length = 64 - 8 * i := by simp [h]
  have hfit : 0 + (dwordBytes (0 : Word)).length <= (orig.drop (8 * i)).length := by
    rw [length_dwordBytes, hsuf]
    omega
  have hslot := setBytes_slot (orig.drop (8 * i)) (dwordBytes (0 : Word)) 0 hfit
  rw [List.drop_zero, length_dwordBytes] at hslot
  have hdrop : (setBytes (orig.drop (8 * i)) 0 (dwordBytes (0 : Word))).drop 8
      = (orig.drop (8 * i)).drop 8 := by
    simpa [length_dwordBytes] using
      (setBytes_drop_of_le (dwordBytes (0 : Word)) (orig.drop (8 * i)) 0 8 (by
        rw [length_dwordBytes]))
  have hset : setBytes (List.drop (8 * i) orig) 0 (dwordBytes (0 : Word))
      = dwordBytes (0 : Word) ++ (List.drop (8 * i) orig).drop 8 := by
    conv_lhs =>
      rw [<- List.take_append_drop 8 (setBytes (List.drop (8 * i) orig) 0 (dwordBytes 0))]
    rw [hslot, hdrop]
  rw [hset]
  rw [show (List.drop (8 * i) orig).drop 8 = orig.drop (8 * (i + 1)) from by
    rw [List.drop_drop]
    congr 1]
  rw [show dwordBytes (0 : Word) = List.replicate 8 (0 : BitVec 8) from by decide]
  simp only [zeroWin64]
  rw [<- List.append_assoc]
  congr 1
  rw [List.replicate_append_replicate]
  congr


private def zeroStores64 (orig : List (BitVec 8)) : List (BitVec 8) :=
  setBytes
    (setBytes
      (setBytes
        (setBytes
          (setBytes
            (setBytes
              (setBytes
                (setBytes orig 0 (dwordBytes (0 : Word)))
                8 (dwordBytes (0 : Word)))
              16 (dwordBytes (0 : Word)))
            24 (dwordBytes (0 : Word)))
          32 (dwordBytes (0 : Word)))
        40 (dwordBytes (0 : Word)))
      48 (dwordBytes (0 : Word)))
    56 (dwordBytes (0 : Word))

private theorem setBytes_zero64 (orig : List (BitVec 8)) (h : orig.length = 64) :
    setBytes
      (setBytes
        (setBytes
          (setBytes
            (setBytes
              (setBytes
                (setBytes
                  (setBytes orig 0 (dwordBytes (0 : Word)))
                  8 (dwordBytes (0 : Word)))
                16 (dwordBytes (0 : Word)))
              24 (dwordBytes (0 : Word)))
            32 (dwordBytes (0 : Word)))
          40 (dwordBytes (0 : Word)))
        48 (dwordBytes (0 : Word)))
      56 (dwordBytes (0 : Word)) = List.replicate 64 (0 : BitVec 8) := by
  rw [show orig = zeroWin64 orig 0 by rw [zeroWin64_zero]]
  rw [zeroWin64_step orig 0 h (by omega)]
  rw [zeroWin64_step orig 1 h (by omega)]
  rw [zeroWin64_step orig 2 h (by omega)]
  rw [zeroWin64_step orig 3 h (by omega)]
  rw [zeroWin64_step orig 4 h (by omega)]
  rw [zeroWin64_step orig 5 h (by omega)]
  rw [zeroWin64_step orig 6 h (by omega)]
  rw [zeroWin64_step orig 7 h (by omega)]
  exact zeroWin64_8_eq orig h

private theorem zeroStores64_eq (orig : List (BitVec 8)) (h : orig.length = 64) :
    zeroStores64 orig = List.replicate 64 (0 : BitVec 8) := by
  unfold zeroStores64
  exact setBytes_zero64 orig h

private theorem bnpFp2Zero_blockVCs (dst : Word) (rf : RegFile) (ws : List (BitVec 8))
    (hx10 : rf.get .x10 = dst) (hws64 : ws.length = 64) :
    blockVCs Region.empty dst rf ws bnpFp2ZeroInstrs := by
  simp only [bnpFp2ZeroInstrs, blockVCs, loadSem, storeSem, hx10,
    RegFile.get_x0, se12_0, se12_8, se12_16, se12_24, se12_32, se12_40,
    se12_48, se12_56,
    execInstrRF_sd_dword Region.empty dst rf ws .x10 .x0 (0 : BitVec 12) 0
      (by rw [hx10, se12_0]; bv_omega),
    execInstrRF_sd_dword Region.empty dst rf
      (setBytes ws 0 (dwordBytes (0 : Word))) .x10 .x0 (8 : BitVec 12) 8
      (by rw [hx10, se12_8]; bv_omega),
    execInstrRF_sd_dword Region.empty dst rf
      (setBytes (setBytes ws 0 (dwordBytes (0 : Word))) 8 (dwordBytes (0 : Word)))
      .x10 .x0 (16 : BitVec 12) 16
      (by rw [hx10, se12_16]; bv_omega),
    execInstrRF_sd_dword Region.empty dst rf
      (setBytes
        (setBytes (setBytes ws 0 (dwordBytes (0 : Word))) 8 (dwordBytes (0 : Word)))
        16 (dwordBytes (0 : Word))) .x10 .x0 (24 : BitVec 12) 24
      (by rw [hx10, se12_24]; bv_omega),
    execInstrRF_sd_dword Region.empty dst rf
      (setBytes
        (setBytes
          (setBytes (setBytes ws 0 (dwordBytes (0 : Word))) 8 (dwordBytes (0 : Word)))
          16 (dwordBytes (0 : Word))) 24 (dwordBytes (0 : Word)))
      .x10 .x0 (32 : BitVec 12) 32
      (by rw [hx10, se12_32]; bv_omega),
    execInstrRF_sd_dword Region.empty dst rf
      (setBytes
        (setBytes
          (setBytes
            (setBytes (setBytes ws 0 (dwordBytes (0 : Word))) 8 (dwordBytes (0 : Word)))
            16 (dwordBytes (0 : Word))) 24 (dwordBytes (0 : Word)))
        32 (dwordBytes (0 : Word))) .x10 .x0 (40 : BitVec 12) 40
      (by rw [hx10, se12_40]; bv_omega),
    execInstrRF_sd_dword Region.empty dst rf
      (setBytes
        (setBytes
          (setBytes
            (setBytes
              (setBytes (setBytes ws 0 (dwordBytes (0 : Word))) 8 (dwordBytes (0 : Word)))
              16 (dwordBytes (0 : Word))) 24 (dwordBytes (0 : Word)))
          32 (dwordBytes (0 : Word))) 40 (dwordBytes (0 : Word)))
      .x10 .x0 (48 : BitVec 12) 48
      (by rw [hx10, se12_48]; bv_omega)]
  exact ⟨⟨inRw_store64_ofs dst _ (0 : Word) (by simp [hws64]) (by simp),
      div8_store64_ofs dst (0 : Word) (by simp)⟩,
    ⟨⟨inRw_store64_ofs dst _ (8 : Word) (by simp [hws64]) (by simp),
        div8_store64_ofs dst (8 : Word) (by simp)⟩,
      ⟨⟨inRw_store64_ofs dst _ (16 : Word) (by simp [hws64]) (by simp),
          div8_store64_ofs dst (16 : Word) (by simp)⟩,
        ⟨⟨inRw_store64_ofs dst _ (24 : Word) (by simp [hws64]) (by simp),
            div8_store64_ofs dst (24 : Word) (by simp)⟩,
          ⟨⟨inRw_store64_ofs dst _ (32 : Word) (by simp [hws64]) (by simp),
              div8_store64_ofs dst (32 : Word) (by simp)⟩,
            ⟨⟨inRw_store64_ofs dst _ (40 : Word) (by simp [hws64]) (by simp),
                div8_store64_ofs dst (40 : Word) (by simp)⟩,
              ⟨⟨inRw_store64_ofs dst _ (48 : Word) (by simp [hws64]) (by simp),
                  div8_store64_ofs dst (48 : Word) (by simp)⟩,
                ⟨⟨inRw_store64_ofs dst _ (56 : Word) (by simp [hws64]) (by simp),
                    div8_store64_ofs dst (56 : Word) (by simp)⟩, trivial⟩⟩⟩⟩⟩⟩⟩⟩

private theorem bnpFp2Zero_engine (dst : Word) (orig : List (BitVec 8)) (rf : RegFile)
    (hx10 : rf.get .x10 = dst) (hlen : orig.length = 64) :
    (execBlock Region.empty dst rf orig bnpFp2ZeroInstrs).2 =
      List.replicate 64 (0 : BitVec 8) := by
  rw [bnpFp2ZeroInstrs]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 0 (by
    rw [hx10, se12_0]; bv_omega)]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 8 (by
    rw [hx10, se12_8]; bv_omega)]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 16 (by
    rw [hx10, se12_16]; bv_omega)]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 24 (by
    rw [hx10, se12_24]; bv_omega)]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 32 (by
    rw [hx10, se12_32]; bv_omega)]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 40 (by
    rw [hx10, se12_40]; bv_omega)]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 48 (by
    rw [hx10, se12_48]; bv_omega)]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 56 (by
    rw [hx10, se12_56]; bv_omega)]
  rw [execBlock_nil, RegFile.get_x0]
  simp only
  exact setBytes_zero64 orig hlen

theorem bnpFp2ZeroFn_spec (dst : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 64⟩) (base : Word) :
    (bnpFp2ZeroFn dst orig).Spec base := by
  have hbase : (bnpFp2ZeroFn dst orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case bnpFp2Zero.zero.mem =>
    rintro rf ws A hws ⟨hx10, hwsOrig, hlen⟩
    exact bnpFp2Zero_blockVCs dst rf ws hx10 (by simpa [hwsOrig] using hlen)
  case bnpFp2Zero.post =>
    rintro rf' ws' A' ⟨rf, ws, hwsLen, ⟨hx10, hwsOrig, hlen⟩, hrf', hws'⟩
    rw [hws']
    rw [hwsOrig]
    simpa [bnpFp2ZeroBody] using bnpFp2Zero_engine dst orig rf hx10 hlen

end Bn254Fp2ZeroSAsm
end EvmAsm.Codegen
