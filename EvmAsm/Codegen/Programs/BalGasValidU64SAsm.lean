/-
  EvmAsm.Codegen.Programs.BalGasValidU64SAsm

  Verified SAsm port for `bgv_u64le`.
-/

import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Rv64.SAsm.FnFlat

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
  fun k rf ws A =>
    rf.get .x10 = p ∧
    rf.get .x5 = leU64Prefix bs k ∧
    rf.get .x7 = BitVec.ofNat 64 k ∧
    rf.get .x28 = (8 : Word) ∧
    ws = [] ∧
    k ≤ 8 ∧
    8 ≤ bs.length ∧
    A = empAssertion

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
  pre := fun rf ws A => rf.get .x10 = p ∧ ws = [] ∧ 8 ≤ bs.length ∧ A = empAssertion
  post := fun rf ws A => rf.get .x10 = leU64 bs ∧ ws = [] ∧ A = empAssertion
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
    obtain ⟨rf₀, ws₀, hws₀, ⟨hx10, hws₀eq, hlen, hA⟩, hrf₁, hws₁eq⟩ := hinit
    subst rf'
    subst ws'
    subst rf₁
    subst ws₁
    subst ws₀
    simp [bgvU64leInv, leU64Prefix, execBlock_cons, execBlock_nil, execInstrRF_nil,
      aluSem, RegFile.get_set_self, RegFile.get_set_ne, hlen, hx10]
    exact hA
  case bgvU64le.loop.inv_step =>
    intro i hi rf' ws' A' h
    unfold Stmt.sp at h
    obtain ⟨rf₁, ws₁, hws₁, hbody, hrf', hws'⟩ := h
    unfold Stmt.sp at hbody
    obtain ⟨rf₀, ws₀, hws₀, ⟨hinv, _hcond⟩, hrf₁, hws₁eq⟩ := hbody
    obtain ⟨hx10, hx5, hx7, _hx28, hws₀eq, hle, hlen, hA⟩ := hinv
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
    · exact ⟨haddi, hA⟩
  case bgvU64le.loop.exhausted =>
    intro rf ws A h
    obtain ⟨_, _, h7, h28, _, _, _, _⟩ := h
    simp [Cond.holds, h7, h28]
  case bgvU64le.loop.body.step.mem =>
    intro rf ws A hws h
    obtain ⟨i, hi, hinv, _hcond⟩ := h
    obtain ⟨hx10, _hx5, hx7, _hx28, hwsEq, _hle, hlen, _hA⟩ := hinv
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
    obtain ⟨_hx10, hx5, hx7, hx28, hws₀eq, hle, _hlen, hA⟩ := hinv
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
    exact hA

/-! ## Flat linked-entry contract -/

def bgvU64leCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.bgv_u64le : Word) bgvU64le_prog

def bgvU64leScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_u64le (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf bgvU64leScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [bgvU64leScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_scratch : (.x10 : Reg) ∉ bgvU64leScratch := by decide

theorem bgvU64leFlat_spec (ret p : Word) (bs : List (BitVec 8))
    (hlen : 8 ≤ bs.length)
    (hwf : (Region.mk p bs).wf)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((bgvU64leFn p bs).body.steps + 1)
      (GuestAddrs.bgv_u64le : Word) ret bgvU64leCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) ** regOwns bgvU64leScratch **
        bytesRegion p bs)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ leU64 bs) ** regOwns bgvU64leScratch **
        bytesRegion p bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns bgvU64leScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) ** bytesRegion p bs)
      (fun vf => ?_))
  have hpre : (bgvU64leFn p bs).pre
      (fun r => if r = .x10 then p else vf r)
      [] empAssertion := by
    refine ⟨?_, rfl, hlen, rfl⟩
    show RegFile.get (fun r => if r = .x10 then p else vf r) .x10 = p
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  have had := Fn.retSpecFlat
    (bgvU64leFn p bs) (GuestAddrs.bgv_u64le : Word)
    (bgvU64leFn_spec p bs hwf (GuestAddrs.bgv_u64le : Word))
    (by show 4 * (12 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then p else vf r)
    ([] : List (BitVec 8)) rfl hpre
    (fun _ _ _ h => h.2.2)
    (Q := (.x10 ↦ᵣ leU64 bs) ** regOwns bgvU64leScratch)
    (fun rf' ws' hws' hpost' hp hh => by
      obtain ⟨hx10', -, -⟩ := hpost'
      obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws'
      rw [show (bgvU64leFn p bs).rw.base = RwRegion.empty.base from rfl,
        bytesRegion_nil, sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_u64le,
        show rf' .x10 = leU64 bs from by
          rw [show rf' .x10 = rf'.get .x10 from by
            rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
          exact hx10'] at hh
      have hh2 := sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) bgvU64leScratch) hp hh
      xperm_hyp hh2)
  rw [show (bgvU64leFn p bs).programRet (GuestAddrs.bgv_u64le : Word)
      = bgvU64le_prog from rfl] at had
  have hadC := had
  rw [show (bgvU64leFn p bs).rw = RwRegion.empty from rfl,
    show (bgvU64leFn p bs).region = Region.mk p bs from rfl,
    bytesRegion_nil, sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_u64le,
    show (if (Reg.x10 : Reg) = .x10 then p else vf .x10) = p from if_pos rfl,
    regAtomsOf_congr (fun r => if r = .x10 then p else vf r) vf bgvU64leScratch
      (fun r hr => by
        show (if r = .x10 then p else vf r) = vf r
        exact if_neg (fun (hc : r = .x10) => x10_notin_scratch (hc ▸ hr)))] at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

end BalGasValidU64SAsm

end EvmAsm.Codegen
