/-
  EvmAsm.Codegen.Programs.Bls12G2Zero192SAsm

  Verified SAsm port of `blsg2_zero192`: zero the 192-byte BLS12-381 G2
  point buffer at `a0`.  The emitted routine is a bottom-test dword loop:
  initialize `x5 = 24`, store a zero dword, advance `a0`, decrement `x5`, and
  branch back while `x5 != 0`.

  The postcondition is the genuine buffer effect: all 192 bytes are zero.  The
  structured `doWhile` body is byte-identical to `blsg2Zero192_prog` including
  the trailing `ret` drift guard below.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Codegen.Programs.Bls12G2

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Bls12G2Zero192SAsm

def zeroWin192 (orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  List.replicate (8 * i) (0 : BitVec 8) ++ orig.drop (8 * i)

theorem zeroWin192_zero (orig : List (BitVec 8)) : zeroWin192 orig 0 = orig := by
  simp [zeroWin192]

theorem zeroWin192_24_eq (orig : List (BitVec 8)) (h : orig.length = 192) :
    zeroWin192 orig 24 = List.replicate 192 (0 : BitVec 8) := by
  simp only [zeroWin192, Nat.reduceMul,
    List.drop_eq_nil_of_le (by omega : orig.length <= 192), List.append_nil]

theorem length_zeroWin192 (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 192) (hi : i <= 24) : (zeroWin192 orig i).length = 192 := by
  simp only [zeroWin192, List.length_append, List.length_replicate, List.length_drop, h]
  omega

theorem zeroWin192_step (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 192) (hi : i < 24) :
    setBytes (zeroWin192 orig i) (8 * i) (dwordBytes (0 : Word)) = zeroWin192 orig (i + 1) := by
  rw [zeroWin192]
  rw [setBytes_append_right _ _ _ _ (by simp)]
  simp only [List.length_replicate, Nat.sub_self]
  have hsuf : (orig.drop (8 * i)).length = 192 - 8 * i := by simp [h]
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
  simp only [zeroWin192]
  rw [<- List.append_assoc]
  congr 1
  rw [List.replicate_append_replicate]
  congr

def zeroStepBlock : List Instr :=
  [.SD .x10 .x0 (0 : BitVec 12),
   .ADDI .x10 .x10 (8 : BitVec 12),
   .ADDI .x5 .x5 (-1 : BitVec 12)]

def zeroStepRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x10 (rf.get .x10 + signExtend12 (8 : BitVec 12))
  r1.set .x5 (r1.get .x5 + signExtend12 (-1 : BitVec 12))

theorem zeroStepRf_get_x10 (rf : RegFile) :
    (zeroStepRf rf).get .x10 = rf.get .x10 + signExtend12 (8 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem zeroStepRf_get_x5 (rf : RegFile) :
    (zeroStepRf rf).get .x5 =
      rf.get .x5 + signExtend12 (-1 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem zero_engine (reg : Region) (dst : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i < 24)
    (hx10 : rf.get .x10 = dst + BitVec.ofNat 64 (8 * i)) :
    execBlock reg dst rf ws zeroStepBlock
      = (zeroStepRf rf, setBytes ws (8 * i) (dwordBytes (0 : Word))) := by
  have haddr : (rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  apply Prod.ext
  . rfl
  . show setBytes ws ((rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat)
        (dwordBytes (rf.get .x0)) = setBytes ws (8 * i) (dwordBytes (0 : Word))
    rw [haddr, RegFile.get_x0]

def zeroInv (dst : Word) (orig : List (BitVec 8)) :
    Nat -> RegFile -> List (BitVec 8) -> Assertion -> Prop :=
  fun i rf ws A =>
    rf.get .x10 = dst + BitVec.ofNat 64 (8 * (i + 1)) ∧
    rf.get .x5 = BitVec.ofNat 64 (24 - (i + 1)) ∧
    i < 24 ∧ orig.length = 192 ∧ ws = zeroWin192 orig (i + 1) ∧ A = empAssertion

def blsg2Zero192Body (dst : Word) (orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (24 : Word)] ;;;
  .doWhile "loop" (.bne .x5 .x0) 23 (zeroInv dst orig)
    (.block "zero" zeroStepBlock)

def blsg2Zero192Fn (dst : Word) (orig : List (BitVec 8)) : Fn where
  name := "blsg2Zero192"
  rw := ⟨dst, 192⟩
  pre := fun rf ws A => rf.get .x10 = dst ∧ ws = orig ∧ orig.length = 192 ∧ A = empAssertion
  post := fun _ ws A => ws = List.replicate 192 (0 : BitVec 8) ∧ A = empAssertion
  body := blsg2Zero192Body dst orig

def blsg2Zero192_verified : Program :=
  (blsg2Zero192Body 0 []).flatten 0

#guard (blsg2Zero192_verified : List Instr).length = 5
#guard (blsg2Zero192Body 0 []).flatten 0 = (blsg2Zero192Body 0 []).flatten 0x80000000
#guard (blsg2Zero192Body 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = blsg2Zero192_prog

theorem blsg2Zero192Fn_spec (dst : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 192⟩) (base : Word) :
    (blsg2Zero192Fn dst orig).Spec base := by
  have hbase : (blsg2Zero192Fn dst orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case blsg2Zero192.loop.inv_init =>
    rintro rf' ws' A' h
    rcases h with ⟨rf0, ws0, -, hreach, rfl, rfl⟩
    rcases hreach with ⟨rfInit, wsInit, -, hpre, rfl, rfl⟩
    rcases hpre with ⟨hx10, rfl, hlen, hA⟩
    simp only [hbase]
    have hx10Init : (execBlock (blsg2Zero192Fn dst ws0).region dst rfInit ws0
        [Instr.LI Reg.x5 24]).1.get .x10 = dst := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true, hx10]
    rw [zero_engine _ dst _ ws0 0 (by omega) (by simpa using hx10Init)]
    refine ⟨?_, ?_, by omega, hlen, ?_, hA⟩
    · rw [zeroStepRf_get_x10, hx10Init, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [zeroStepRf_get_x5]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      decide
    · change setBytes ws0 (8 * 0) (dwordBytes (0 : Word)) = zeroWin192 ws0 (0 + 1)
      simpa [zeroWin192_zero ws0] using zeroWin192_step ws0 0 hlen (by omega)
  case blsg2Zero192.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx10, hx5, hlt, hlen, hws₀, hA⟩, hcond⟩, rfl, rfl⟩
    simp only [hbase]
    rw [zero_engine _ dst rf₀ ws₀ (i + 1) (by omega) hx10]
    refine ⟨?_, ?_, by omega, hlen, ?_, hA⟩
    · rw [zeroStepRf_get_x10, hx10, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from by decide]
      omega
    · rw [zeroStepRf_get_x5, hx5, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> decide
    · rw [hws₀, zeroWin192_step orig (i + 1) hlen (by omega)]
  case blsg2Zero192.loop.exhausted =>
    rintro rf ws A ⟨-, hx5, -, -, -, _⟩
    simp only [Cond.holds, hx5, not_not, RegFile.get_x0]
    decide
  case blsg2Zero192.loop.body.zero.mem =>
    rintro rf ws A hlen (hpre | hloop)
    · rcases hpre with ⟨rfInit, wsInit, -, ⟨hx10, rfl, horiglen, _hA⟩, rfl, rfl⟩
      have hlen192 : ws.length = 192 := by simpa [blsg2Zero192Fn] using hlen
      have haddr0 : (dst + signExtend12 (0 : BitVec 12) - dst).toNat = 0 := by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega
      simp only [zeroStepBlock, blockVCs, execInstrRF, aluSem, loadSem, storeSem,
        inRw, hbase, execBlock_cons, execBlock_nil, RegFile.get_set_ne, ne_eq,
        reduceCtorEq, not_false_eq_true, hx10, hlen192, haddr0, and_true]
      constructor
      · omega
      · exact Nat.dvd_zero 8
    · rcases hloop with ⟨i, hi, ⟨hx10, hx5, hlt, horiglen, hws, _hA⟩, hcond⟩
      have haddr : (rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * (i + 1) := by
        rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega
      have hlen192 : ws.length = 192 := by simpa [blsg2Zero192Fn] using hlen
      simp only [zeroStepBlock, blockVCs, loadSem, storeSem, inRw, hbase, haddr, hlen192,
        and_true]
      constructor
      · omega
      · exact Nat.dvd_mul_right 8 (i + 1)
  case blsg2Zero192.post =>
    rintro rf ws A ⟨⟨i, hle, hx10, hx5, hlt, hlen, hws, hA⟩, hncond⟩
    have hi23 : i = 23 := by
      simp only [Cond.holds, hx5, RegFile.get_x0, not_not] at hncond
      interval_cases i <;> try contradiction
      rfl
    subst hi23
    rw [hws, zeroWin192_24_eq orig hlen]
    exact ⟨rfl, hA⟩

/-! ## Flat linked-entry contract -/

def blsg2Zero192Cr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.blsg2_zero192 : Word) blsg2Zero192_prog

def blsg2Zero192Scratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_zero192 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf blsg2Zero192Scratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [blsg2Zero192Scratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_scratch : (.x10 : Reg) ∉ blsg2Zero192Scratch := by decide

theorem blsg2Zero192Flat_spec (ret dst : Word) (orig : List (BitVec 8))
    (hlen : orig.length = 192)
    (hwf : RwRegion.wf ⟨dst, 192⟩)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((blsg2Zero192Fn dst orig).body.steps + 1)
      (GuestAddrs.blsg2_zero192 : Word) ret blsg2Zero192Cr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** regOwns blsg2Zero192Scratch **
        bytesRegion dst orig)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion dst (List.replicate 192 (0 : BitVec 8))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns blsg2Zero192Scratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** bytesRegion dst orig)
      (fun vf => ?_))
  have hpre : (blsg2Zero192Fn dst orig).pre
      (fun r => if r = .x10 then dst else vf r)
      orig empAssertion := by
    refine ⟨?_, rfl, ?_, rfl⟩
    · show RegFile.get (fun r => if r = .x10 then dst else vf r) .x10 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · exact hlen
  have had := Fn.retSpecFlat
    (blsg2Zero192Fn dst orig) (GuestAddrs.blsg2_zero192 : Word)
    (blsg2Zero192Fn_spec dst orig (by simpa using hwf) (GuestAddrs.blsg2_zero192 : Word))
    (by show 4 * (5 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then dst else vf r)
    orig hlen hpre
    (fun _ _ _ h => h.2)
    (Q := regOwns exposedRegs **
      bytesRegion dst (List.replicate 192 (0 : BitVec 8)))
    (fun rf' ws' _ hpost' hp hh => by
      obtain ⟨hws', _hA⟩ := hpost'
      subst ws'
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh)
  rw [show (blsg2Zero192Fn dst orig).programRet
      (GuestAddrs.blsg2_zero192 : Word) = blsg2Zero192_prog from rfl] at had
  have hadC := had
  rw [show (blsg2Zero192Fn dst orig).region = Region.empty from rfl,
    show bytesRegion Region.empty.base Region.empty.bytes = empAssertion from
      bytesRegion_nil _, sepConj_emp_right'] at hadC
  simp only [sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_zero192,
    show (if (Reg.x10 : Reg) = .x10 then dst else vf .x10) = dst from if_pos rfl,
    regAtomsOf_congr (fun r => if r = .x10 then dst else vf r) vf
      blsg2Zero192Scratch
      (fun r hr => by
        show (if r = .x10 then dst else vf r) = vf r
        exact if_neg (fun (hc : r = .x10) =>
          x10_notin_scratch (hc ▸ hr)))] at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

end Bls12G2Zero192SAsm

end EvmAsm.Codegen
