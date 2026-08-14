/-
  EvmAsm.Codegen.Programs.Bls12Fq12IsZeroSAsm

  Verified SAsm port of `blq_is_zero`: OR the 72 64-bit limbs of a 576-byte
  BLS12 Fq12 buffer and return `a0 = 1` iff the accumulator is zero.
-/

import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Codegen.Programs.Bls12Fq12

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Bls12Fq12IsZeroSAsm

def fq12Dword (bs : List (BitVec 8)) (i : Nat) : Word :=
  packBytes ((bs.drop (8 * i)).take 8)

def fq12OrPrefix (bs : List (BitVec 8)) : Nat → Word
  | 0 => 0
  | n + 1 => fq12OrPrefix bs n ||| fq12Dword bs n

def fq12IsZeroResult (bs : List (BitVec 8)) : Word :=
  if BitVec.ult (fq12OrPrefix bs 72) (1 : Word) then (1 : Word) else 0

def blqIsZeroInv (src : Word) (bs : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    rf.get .x10 = src + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x5 = BitVec.ofNat 64 (72 - i) ∧
    rf.get .x6 = fq12OrPrefix bs i ∧
    ws = [] ∧ i ≤ 72 ∧ 576 ≤ bs.length ∧ A = empAssertion

def blqIsZeroStep : Stmt :=
  .block "step"
    [.LD .x7 .x10 (0 : BitVec 12),
     .OR .x6 .x6 .x7,
     .ADDI .x10 .x10 (8 : BitVec 12),
     .ADDI .x5 .x5 (-1 : BitVec 12)]

def blqIsZeroBody (src : Word) (bs : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (72 : Word), .LI .x6 (0 : Word)] ;;;
  .whileHeader "loop" (.block "guard" []) (.bne .x5 .x0) 73
    (blqIsZeroInv src bs) blqIsZeroStep ;;;
  .block "retVal" [.SLTIU .x10 .x6 (1 : BitVec 12)]

def blqIsZeroFn (src : Word) (bs : List (BitVec 8)) : Fn where
  name := "blqIsZero"
  region := ⟨src, bs⟩
  pre := fun rf ws A => rf.get .x10 = src ∧ ws = [] ∧ 576 ≤ bs.length ∧ A = empAssertion
  post := fun rf ws A => rf.get .x10 = fq12IsZeroResult bs ∧ ws = [] ∧ A = empAssertion
  body := blqIsZeroBody src bs

theorem blqIsZero_byte_tie :
    (blqIsZeroFn 0 []).body.flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] =
      blqIsZero_prog := rfl

#guard ((blqIsZeroFn 0 []).body.flatten 0).length = 9

private theorem idx_toNat (i : Nat) (hi : i < 72) :
    (BitVec.ofNat 64 (8 * i)).toNat = 8 * i := by
  rw [BitVec.toNat_ofNat]
  omega

private theorem add_idx_sub_self (src : Word) (i : Nat) (hi : i < 72) :
    (src + BitVec.ofNat 64 (8 * i) - src).toNat = 8 * i := by
  rw [BitVec.toNat_sub, BitVec.toNat_add, idx_toNat i hi]
  omega

private theorem fq12Dword_region (src : Word) (bs : List (BitVec 8)) (i : Nat)
    (hi : i < 72) :
    Region.dwordAt ⟨src, bs⟩ (src + BitVec.ofNat 64 (8 * i)) = fq12Dword bs i := by
  unfold Region.dwordAt fq12Dword
  rw [add_idx_sub_self src i hi]

theorem blqIsZeroFn_spec (src : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (base : Word) :
    (blqIsZeroFn src bs).Spec base := by
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case blqIsZero.loop.inv_init =>
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
    simp [blqIsZeroInv, fq12OrPrefix, execBlock_cons, execBlock_nil, execInstrRF_nil,
      aluSem, RegFile.get_set_self, RegFile.get_set_ne, hx10, hlen]
    exact hA
  case blqIsZero.loop.inv_step =>
    intro i hi rf' ws' A' h
    unfold Stmt.sp at h
    obtain ⟨rf₁, ws₁, hws₁, hbody, hrf', hws'⟩ := h
    unfold Stmt.sp at hbody
    obtain ⟨rf₀, ws₀, hws₀, ⟨hinv, hcond⟩, hrf₁, hws₁eq⟩ := hbody
    obtain ⟨hx10, hx5, hx6, hws₀eq, hle, hlen, hA⟩ := hinv
    subst rf'
    subst ws'
    subst rf₁
    subst ws₁
    subst ws₀
    have hcond_nonzero : BitVec.ofNat 64 (72 - i) ≠ (0 : Word) := by
      simpa [Cond.holds, hx5, RegFile.get_x0] using hcond
    have h_i_lt : i < 72 := by
      interval_cases i <;> first | contradiction | omega
    have h_i1 : i + 1 ≤ 72 := by omega
    have h_i_le71 : i ≤ 71 := by omega
    have haddi10 : src + BitVec.ofNat 64 (8 * i) + signExtend12 (8 : BitVec 12) =
        src + BitVec.ofNat 64 (8 * (i + 1)) := by
      rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    have haddi5 : BitVec.ofNat 64 (72 - i) + signExtend12 (-1 : BitVec 12) =
        BitVec.ofNat 64 (71 - i) := by
      rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      bv_omega
    simp [blqIsZeroInv, fq12OrPrefix, execBlock_cons, execBlock_nil,
      execInstrRF_nil, aluSem, loadSem, RegFile.get_set_self, RegFile.get_set_ne,
      hx10, hx5, hx6, hlen]
    constructor
    · exact haddi10
    constructor
    · exact haddi5
    constructor
    · change fq12OrPrefix bs i ||| Region.dwordAt ⟨src, bs⟩
          (src + BitVec.ofNat 64 (8 * i) + signExtend12 (0 : BitVec 12)) =
        fq12OrPrefix bs i ||| fq12Dword bs i
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      rw [show src + BitVec.ofNat 64 (8 * i) + (0 : Word) =
        src + BitVec.ofNat 64 (8 * i) from by bv_omega]
      rw [fq12Dword_region src bs i h_i_lt]
    exact ⟨h_i_le71, hA⟩
  case blqIsZero.loop.exhausted =>
    intro rf ws A h
    obtain ⟨_, hx5, _, _, _, _, _⟩ := h
    simp [Cond.holds, hx5, RegFile.get_x0]
  case blqIsZero.loop.body.step.mem =>
    intro rf ws A hws h
    obtain ⟨i, hi, hinv, hcond⟩ := h
    obtain ⟨hx10, hx5, _hx6, hwsEq, _hle, hlen, _hA⟩ := hinv
    subst ws
    have hcond_nonzero : BitVec.ofNat 64 (72 - i) ≠ (0 : Word) := by
      simpa [Cond.holds, hx5, RegFile.get_x0] using hcond
    have h_i_lt : i < 72 := by
      interval_cases i <;> first | contradiction | omega
    have haddr : (rf.get .x10 + signExtend12 (0 : BitVec 12) - src).toNat = 8 * i := by
      rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      simpa [add_assoc] using add_idx_sub_self src i h_i_lt
    have htarget :
        (18446744073709551616 - src.toNat +
              (src.toNat + 8 * i + (signExtend12 (0#12)).toNat)) %
            18446744073709551616 = 8 * i := by
      simpa [hx10, BitVec.toNat_sub, BitVec.toNat_add, idx_toNat i h_i_lt] using haddr
    simp [blqIsZeroFn, blockVCs, loadSem, Region.loadOk, inRw, hx10]
    rw [htarget]
    exact ⟨⟨Nat.dvd_mul_right 8 i, by omega⟩, by simp [storeSem]⟩
  case blqIsZero.post =>
    intro rf ws A h
    simp [blqIsZeroFn, blqIsZeroBody, Stmt.sp] at h ⊢
    obtain ⟨rf₀, ws₀, hws₀, ⟨⟨i, hiFuel, hinv⟩, hnot⟩, hrf, hws⟩ := h
    obtain ⟨_hx10, hx5, hx6, hws₀eq, hle, _hlen, hA⟩ := hinv
    subst rf
    subst ws
    subst ws₀
    have hidxEq : BitVec.ofNat 64 (72 - i) = (0 : Word) := by
      by_contra hne
      exact hnot (by simpa [Cond.holds, hx5, RegFile.get_x0] using hne)
    have hi72 : i = 72 := by
      have hto := congrArg BitVec.toNat hidxEq
      rw [BitVec.toNat_ofNat] at hto
      change (72 - i) % 18446744073709551616 = 0 at hto
      omega
    subst i
    simp [execInstrRF, aluSem, fq12IsZeroResult, hx6, signExtend12]
    exact hA

/-! ## Flat linked-entry contract -/

def blqIsZeroCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.blq_is_zero : Word) blqIsZero_prog

def blqIsZeroScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_is_zero (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf blqIsZeroScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [blqIsZeroScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_scratch : (.x10 : Reg) ∉ blqIsZeroScratch := by decide

theorem blqIsZeroFlat_spec (ret src : Word) (bs : List (BitVec 8))
    (hlen : 576 ≤ bs.length)
    (hwf : (Region.mk src bs).wf)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((blqIsZeroFn src bs).body.steps + 1)
      (GuestAddrs.blq_is_zero : Word) ret blqIsZeroCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) ** regOwns blqIsZeroScratch **
        bytesRegion src bs)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ fq12IsZeroResult bs) **
        regOwns blqIsZeroScratch ** bytesRegion src bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns blqIsZeroScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) ** bytesRegion src bs)
      (fun vf => ?_))
  have hpre : (blqIsZeroFn src bs).pre
      (fun r => if r = .x10 then src else vf r)
      [] empAssertion := by
    refine ⟨?_, rfl, hlen, rfl⟩
    show RegFile.get (fun r => if r = .x10 then src else vf r) .x10 = src
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  have had := Fn.retSpecFlat
    (blqIsZeroFn src bs) (GuestAddrs.blq_is_zero : Word)
    (blqIsZeroFn_spec src bs hwf (GuestAddrs.blq_is_zero : Word))
    (by show 4 * (9 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then src else vf r)
    ([] : List (BitVec 8)) rfl hpre
    (fun _ _ _ h => h.2.2)
    (Q := (.x10 ↦ᵣ fq12IsZeroResult bs) ** regOwns blqIsZeroScratch)
    (fun rf' ws' hws' hpost' hp hh => by
      obtain ⟨hx10', -, -⟩ := hpost'
      obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws'
      rw [show (blqIsZeroFn src bs).rw.base = RwRegion.empty.base from rfl,
        bytesRegion_nil, sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_is_zero,
        show rf' .x10 = fq12IsZeroResult bs from by
          rw [show rf' .x10 = rf'.get .x10 from by
            rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
          exact hx10'] at hh
      have hh2 := sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) blqIsZeroScratch) hp hh
      xperm_hyp hh2)
  rw [show (blqIsZeroFn src bs).programRet (GuestAddrs.blq_is_zero : Word)
      = blqIsZero_prog from rfl] at had
  have hadC := had
  rw [show (blqIsZeroFn src bs).rw = RwRegion.empty from rfl,
    show (blqIsZeroFn src bs).region = Region.mk src bs from rfl,
    bytesRegion_nil, sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_is_zero,
    show (if (Reg.x10 : Reg) = .x10 then src else vf .x10) = src from if_pos rfl,
    regAtomsOf_congr (fun r => if r = .x10 then src else vf r) vf blqIsZeroScratch
      (fun r hr => by
        show (if r = .x10 then src else vf r) = vf r
        exact if_neg (fun (hc : r = .x10) => x10_notin_scratch (hc ▸ hr)))] at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

end Bls12Fq12IsZeroSAsm

end EvmAsm.Codegen
