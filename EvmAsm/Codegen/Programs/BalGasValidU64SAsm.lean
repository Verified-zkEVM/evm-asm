/-
  EvmAsm.Codegen.Programs.BalGasValidU64SAsm

  Verified SAsm port for `bgv_u64le`.
-/

import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace BalGasValidU64SAsm

open SgLoadU32leSAsm

/-- Accumulator after `n` iterations of the emitted little-endian u64 loop. -/
def leU64Prefix (bs : List (BitVec 8)) : Nat → Word
  | 0 => 0
  | n + 1 => leU64Prefix bs n ||| (leByte bs n <<< (8 * n))

def leU64 (bs : List (BitVec 8)) : Word :=
  leU64Prefix bs 8

def bgvU64leInv (p : Word) (bs : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun k rf ws _ =>
    rf.get .x10 = p ∧
    rf.get .x5 = leU64Prefix bs k ∧
    rf.get .x7 = BitVec.ofNat 64 k ∧
    rf.get .x28 = (8 : Word) ∧
    ws = [] ∧
    k ≤ 8 ∧
    8 ≤ bs.length

def bgvU64leLoopBody : Stmt :=
  .block "step"
    [.ADD .x29 .x10 .x7,
     .LBU .x30 .x29 (0 : BitVec 12),
     .SLLI .x31 .x7 (3 : BitVec 6),
     .SLL .x30 .x30 .x31,
     .OR .x5 .x5 .x30,
     .ADDI .x7 .x7 (1 : BitVec 12)]

def bgvU64leBody (p : Word) (bs : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (0 : Word), .LI .x7 (0 : Word)] ;;;
  .whileHeader "loop"
    (.block "limit" [.LI .x28 (8 : Word)])
    (.bne .x7 .x28)
    8
    (bgvU64leInv p bs)
    bgvU64leLoopBody ;;;
  .block "retVal" [.MV .x10 .x5]

/-- Verified port of `bgv_u64le`: `a0 := leU64 (bytes at a0)`. -/
def bgvU64leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "bgvU64le"
  region := ⟨p, bs⟩
  pre := fun rf ws _ => rf.get .x10 = p ∧ ws = [] ∧ 8 ≤ bs.length
  post := fun rf ws _ => rf.get .x10 = leU64 bs ∧ ws = []
  body := bgvU64leBody p bs

theorem bgvU64le_byte_tie :
    (bgvU64leFn 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = bgvU64le_prog := rfl

#guard ((bgvU64leFn 0 []).body.flatten 0).length = 12

private theorem idx_toNat (i : Nat) (hi : i < 8) :
    (BitVec.ofNat 64 i).toNat = i := by
  rw [BitVec.toNat_ofNat]
  omega

private theorem add_idx_sub_self (p : Word) (i : Nat) (hi : i < 8) :
    (p + BitVec.ofNat 64 i - p).toNat = i := by
  rw [BitVec.toNat_sub, BitVec.toNat_add, idx_toNat i hi]
  omega

private theorem shift_idx_three_mod (i : Nat) (hi : i < 8) :
    ((BitVec.ofNat 64 i <<< 3).toNat % 64) = 8 * i := by
  rw [BitVec.toNat_shiftLeft, idx_toNat i hi, Nat.shiftLeft_eq]
  omega

theorem bgvU64leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (bgvU64leFn p bs).Spec base := by
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case bgvU64le.loop.inv_init =>
    intro rf' ws' A' h
    unfold Stmt.sp at h
    obtain ⟨rf₁, ws₁, hws₁, hinit, hrf', hws'⟩ := h
    unfold Stmt.sp at hinit
    obtain ⟨rf₀, ws₀, hws₀, ⟨hx10, hws₀eq, hlen⟩, hrf₁, hws₁eq⟩ := hinit
    subst rf'
    subst ws'
    subst rf₁
    subst ws₁
    subst ws₀
    simp [bgvU64leInv, leU64Prefix, execBlock_cons, execBlock_nil, execInstrRF_nil,
      aluSem, RegFile.get_set_self, RegFile.get_set_ne, hlen, hx10]
  case bgvU64le.loop.inv_step =>
    intro i hi rf' ws' A' h
    unfold Stmt.sp at h
    obtain ⟨rf₁, ws₁, hws₁, hbody, hrf', hws'⟩ := h
    unfold Stmt.sp at hbody
    obtain ⟨rf₀, ws₀, hws₀, ⟨hinv, _hcond⟩, hrf₁, hws₁eq⟩ := hbody
    obtain ⟨hx10, hx5, hx7, _hx28, hws₀eq, hle, hlen⟩ := hinv
    subst rf'
    subst ws'
    subst rf₁
    subst ws₁
    subst ws₀
    have haddi : BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12) =
        BitVec.ofNat 64 (i + 1) := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      bv_omega
    have hshiftNat : (i % 18446744073709551616) <<< 3 % 64 = 8 * i := by
      have hiMod : i % 18446744073709551616 = i := by omega
      rw [hiMod, Nat.shiftLeft_eq]
      omega
    have haddr0 : (p + BitVec.ofNat 64 i + signExtend12 (0 : BitVec 12) - p).toNat = i := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      simpa [add_assoc] using add_idx_sub_self p i hi
    have hi_le7 : i ≤ 7 := by omega
    simp [bgvU64leInv, leU64Prefix, leByte, execBlock_cons, execBlock_nil,
      execInstrRF_nil, aluSem, loadSem, hi_le7, RegFile.get_set_self,
      RegFile.get_set_ne, hx10, hx5, hx7, hlen]
    constructor
    · unfold Region.byteAt
      change leU64Prefix bs i |||
          BitVec.setWidth 64
            (bs.getD ((p + BitVec.ofNat 64 i + signExtend12 (0 : BitVec 12) - p).toNat) 0) <<<
              ((i % 18446744073709551616) <<< 3 % 64) =
        leU64Prefix bs i ||| BitVec.setWidth 64 (bs.getD i 0) <<< (8 * i)
      rw [haddr0, hshiftNat]
    · exact haddi
  case bgvU64le.loop.exhausted =>
    intro rf ws A h
    obtain ⟨_, _, h7, h28, _⟩ := h
    simp [Cond.holds, h7, h28]
  case bgvU64le.loop.body.step.mem =>
    intro rf ws A hws h
    obtain ⟨i, hi, hinv, _hcond⟩ := h
    obtain ⟨hx10, _hx5, hx7, _hx28, hwsEq, _hle, hlen⟩ := hinv
    subst ws
    have haddr0 : (rf.get .x10 + rf.get .x7 + signExtend12 (0 : BitVec 12) - p).toNat = i := by
      rw [hx10, hx7, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      simpa [add_assoc] using add_idx_sub_self p i hi
    have htarget :
        (18446744073709551616 - p.toNat + (p.toNat + i + (signExtend12 (0#12)).toNat)) %
            18446744073709551616 = i := by
      simpa [hx10, hx7, BitVec.toNat_sub, BitVec.toNat_add, idx_toNat i hi]
        using haddr0
    simp [bgvU64leFn, blockVCs, execInstrRF_nil, aluSem, loadSem, storeSem,
      Region.loadOk, inRw, RegFile.get_set_self, hx10, hx7]
    rw [htarget]
    omega
  case bgvU64le.post =>
    intro rf ws A h
    simp [bgvU64leFn, bgvU64leBody, Stmt.sp] at h ⊢
    obtain ⟨rf₀, ws₀, hws₀, ⟨⟨i, hiFuel, hinv⟩, hnot⟩, hrf, hws⟩ := h
    obtain ⟨_hx10, hx5, hx7, hx28, hws₀eq, hle, _hlen⟩ := hinv
    subst rf
    subst ws
    subst ws₀
    have hidxEq : BitVec.ofNat 64 i = (8 : Word) := by
      by_contra hne
      exact hnot (by simpa [Cond.holds, hx7, hx28] using hne)
    have hi8 : i = 8 := by
      have hto := congrArg BitVec.toNat hidxEq
      rw [BitVec.toNat_ofNat] at hto
      change i % 18446744073709551616 = 8 at hto
      omega
    subst i
    simp [execInstrRF_nil, aluSem, leU64, hx5, RegFile.get_set_self]

end BalGasValidU64SAsm

end EvmAsm.Codegen
