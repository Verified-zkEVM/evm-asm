/-
  Verified byte-identical SAsm port of `nibbles_common_prefix_len`.

  Both nibble arrays are read-only.  The routine scans at most the smaller
  caller-supplied count, stops at the first unequal byte, stores that exact
  common-prefix length as a u64, and returns status zero.
-/

import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace NibblesCommonPrefixLenSAsm

def firstDiff (bsA bsB : List (BitVec 8)) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if firstDiff bsA bsB n < n then firstDiff bsA bsB n
      else if bsA.getD n 0 ≠ bsB.getD n 0 then n else n + 1

@[simp] theorem firstDiff_zero (bsA bsB : List (BitVec 8)) :
    firstDiff bsA bsB 0 = 0 := rfl

@[simp] theorem firstDiff_succ (bsA bsB : List (BitVec 8)) (n : Nat) :
    firstDiff bsA bsB (n + 1) =
      (if firstDiff bsA bsB n < n then firstDiff bsA bsB n
       else if bsA.getD n 0 ≠ bsB.getD n 0 then n else n + 1) := by
  conv_lhs => rw [firstDiff]

theorem firstDiff_le (bsA bsB : List (BitVec 8)) : ∀ n, firstDiff bsA bsB n ≤ n
  | 0 => Nat.zero_le _
  | n + 1 => by
    rw [firstDiff_succ]
    by_cases h : firstDiff bsA bsB n < n
    · rw [if_pos h]
      exact Nat.le_succ_of_le (firstDiff_le bsA bsB n)
    · rw [if_neg h]
      split <;> omega

theorem firstDiff_all_eq (bsA bsB : List (BitVec 8)) (n : Nat)
    (h : ∀ j, j < n → bsA.getD j 0 = bsB.getD j 0) :
    firstDiff bsA bsB n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [firstDiff_succ, ih (fun j hj => h j (by omega)), if_neg (Nat.lt_irrefl _)]
    by_cases hne : bsA.getD n 0 ≠ bsB.getD n 0
    · exact absurd hne (fun h2 => h2 (h n (by omega)))
    · rw [if_neg hne]

theorem firstDiff_ne (bsA bsB : List (BitVec 8)) (i : Nat)
    (h_prev : ∀ j, j < i → bsA.getD j 0 = bsB.getD j 0)
    (h_ne : bsA.getD i 0 ≠ bsB.getD i 0) :
    firstDiff bsA bsB (i + 1) = i := by
  rw [firstDiff_succ, firstDiff_all_eq _ _ _ h_prev, if_neg (Nat.lt_irrefl _),
    if_pos h_ne]

theorem firstDiff_ne_of_lt (bsA bsB : List (BitVec 8)) (i n : Nat)
    (h_i : i < n) (h_prev : ∀ j, j < i → bsA.getD j 0 = bsB.getD j 0)
    (h_ne : bsA.getD i 0 ≠ bsB.getD i 0) : firstDiff bsA bsB n = i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hlt : i < n
    · have hih := ih hlt
      rw [firstDiff_succ, hih, if_pos hlt]
    · have hin : i = n := by omega
      subst i
      exact firstDiff_ne bsA bsB n h_prev h_ne

theorem slt_ofNat_iff (i n : Nat) (h_i : i < 2 ^ 63) (h_n : n < 2 ^ 63) :
    BitVec.slt (BitVec.ofNat 64 i) (BitVec.ofNat 64 n) = true ↔ i < n := by
  rw [BitVec.slt_eq_decide]
  simp [BitVec.toInt, BitVec.ofNat]
  omega

theorem add_ofNat_sub_self_toNat (ptr : Word) (i bound : Nat)
    (h_i : i < bound) (h_ptr : ptr.toNat + bound < 2 ^ 64) :
    (ptr + BitVec.ofNat 64 i - ptr).toNat = i := by
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

def scanInv (ptrA ptrB outPtr : Word) (lenA lenB : Nat)
    (bsA bsB orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    rf.get .x5 = BitVec.ofNat 64 i ∧
    rf.get .x6 = ptrA + BitVec.ofNat 64 i ∧
    rf.get .x7 = ptrB + BitVec.ofNat 64 i ∧
    rf.get .x11 = BitVec.ofNat 64 (Nat.min lenA lenB) ∧
    rf.get .x12 = ptrB ∧ rf.get .x14 = outPtr ∧ i ≤ Nat.min lenA lenB ∧
    (∀ j, j < i → bsA.getD j 0 = bsB.getD j 0) ∧
    lenA ≤ bsA.length ∧ lenB ≤ bsB.length ∧ orig.length = 8 ∧
    lenA < 2 ^ 63 ∧ lenB < 2 ^ 63 ∧
    ptrA.toNat + lenA < 2 ^ 64 ∧ ptrB.toNat + lenB < 2 ^ 64 ∧
    ws = [] ∧ A = (bytesRegion ptrB bsB ** bytesRegion outPtr orig)

def scanPost (ptrA ptrB outPtr : Word) (lenA lenB : Nat)
    (bsA bsB orig : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf ws A =>
    let n := firstDiff bsA bsB (Nat.min lenA lenB)
    rf.get .x5 = BitVec.ofNat 64 n ∧
    rf.get .x6 = ptrA + BitVec.ofNat 64 n ∧
    rf.get .x7 = ptrB + BitVec.ofNat 64 n ∧
    rf.get .x12 = ptrB ∧ rf.get .x14 = outPtr ∧ ws = [] ∧
    orig.length = 8 ∧
    A = (bytesRegion ptrB bsB ** bytesRegion outPtr orig)

def readB (ptrB outPtr : Word) (bsB orig : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ robytes rest =>
    rf.get .x12 = ptrB ∧ rf.get .x14 = outPtr ∧ robytes = bsB ∧
    rest = bytesRegion outPtr orig

def doneFocus (ptrB outPtr : Word) (bsB orig : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ win rest =>
    rf.get .x14 = outPtr ∧ win = orig ∧ rest = bytesRegion ptrB bsB

def nibblesCommonPrefixLenBody (ptrA ptrB outPtr : Word) (lenA lenB : Nat)
    (bsA bsB orig : List (BitVec 8)) : Stmt :=
  .when "min" (.bgeu .x11 .x13) (.block "useB" [.MV .x11 .x13]) ;;;
  .block "init" [.LI .x5 (0 : Word), .MV .x6 .x10, .MV .x7 .x12] ;;;
  .«whileBreak» "scan" (.blt .x5 .x11) (Nat.min lenA lenB)
    (scanInv ptrA ptrB outPtr lenA lenB bsA bsB orig)
    (scanPost ptrA ptrB outPtr lenA lenB bsA bsB orig)
    (.block "loadA" [.LBU .x28 .x6 0] ;;;
     .readAt "loadB" .x12 (readB ptrB outPtr bsB orig) [.LBU .x29 .x7 0])
    (.bne .x28 .x29)
    (.block "next" [.ADDI .x6 .x6 1, .ADDI .x7 .x7 1, .ADDI .x5 .x5 1]) ;;;
  .blockAt "doneStore" .x14 (doneFocus ptrB outPtr bsB orig) [.SD .x14 .x5 0] ;;;
  .block "doneStatus" [.LI .x10 (0 : Word)]

def nibblesCommonPrefixLenFn (ptrA ptrB outPtr : Word) (lenA lenB : Nat)
    (bsA bsB orig : List (BitVec 8)) : Fn where
  name := "nibblesCommonPrefixLen"
  region := ⟨ptrA, bsA⟩
  rw := RwRegion.empty
  pre := fun rf ws A =>
    rf.get .x10 = ptrA ∧ rf.get .x11 = BitVec.ofNat 64 lenA ∧
    rf.get .x12 = ptrB ∧ rf.get .x13 = BitVec.ofNat 64 lenB ∧
    rf.get .x14 = outPtr ∧ ws = [] ∧ lenA ≤ bsA.length ∧ lenB ≤ bsB.length ∧
    orig.length = 8 ∧ lenA < 2 ^ 63 ∧ lenB < 2 ^ 63 ∧
    ptrA.toNat + lenA < 2 ^ 64 ∧ ptrB.toNat + lenB < 2 ^ 64 ∧
    A = (bytesRegion ptrB bsB ** bytesRegion outPtr orig)
  post := fun rf ws A =>
    rf.get .x10 = 0 ∧
    ws = [] ∧ A = (bytesRegion outPtr (dwordBytes (BitVec.ofNat 64
      (firstDiff bsA bsB (Nat.min lenA lenB)))) ** bytesRegion ptrB bsB)
  body := nibblesCommonPrefixLenBody ptrA ptrB outPtr lenA lenB bsA bsB orig

theorem nibblesCommonPrefixLenBody_eq_prog (ptrA ptrB outPtr : Word)
    (lenA lenB : Nat) (bsA bsB orig : List (BitVec 8)) :
    (nibblesCommonPrefixLenBody ptrA ptrB outPtr lenA lenB bsA bsB orig).flatten 0 ++
      [Instr.JALR .x0 .x1 0] = nibblesCommonPrefixLen_prog := by
  rfl

#guard ((nibblesCommonPrefixLenBody 0 0 0 0 0 [] [] []).flatten 0).length = 15
#guard (nibblesCommonPrefixLenBody 0 0 0 0 0 [] [] []).flatten 0 =
  (nibblesCommonPrefixLenBody 0 0 0 0 0 [] [] []).flatten 0x80000000

private theorem init_inv (ptrA ptrB outPtr : Word) (lenA lenB : Nat)
    (bsA bsB orig : List (BitVec 8)) (rf : RegFile) (ws : List (BitVec 8))
    (hx10 : rf.get .x10 = ptrA)
    (hx11 : rf.get .x11 = BitVec.ofNat 64 (Nat.min lenA lenB))
    (hx12 : rf.get .x12 = ptrB) (hx14 : rf.get .x14 = outPtr)
    (h_ws : ws = []) (h_lenA : lenA ≤ bsA.length) (h_lenB : lenB ≤ bsB.length)
    (h_orig : orig.length = 8) (h_a63 : lenA < 2 ^ 63) (h_b63 : lenB < 2 ^ 63)
    (h_ptrA : ptrA.toNat + lenA < 2 ^ 64)
    (h_ptrB : ptrB.toNat + lenB < 2 ^ 64)
    (h_A : A = (bytesRegion ptrB bsB ** bytesRegion outPtr orig)) :
    scanInv ptrA ptrB outPtr lenA lenB bsA bsB orig 0
      (execBlock ⟨ptrA, bsA⟩ outPtr rf ws
        [.LI .x5 0, .MV .x6 .x10, .MV .x7 .x12]).1
      (execBlock ⟨ptrA, bsA⟩ outPtr rf ws
        [.LI .x5 0, .MV .x6 .x10, .MV .x7 .x12]).2 A := by
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, h_lenA, h_lenB, h_orig,
    h_a63, h_b63, h_ptrA, h_ptrB, ?_, h_A⟩
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
      RegFile.get_set_self _ _ _ (by decide)]
    rfl
  · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
      RegFile.get_set_self _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x0),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
    simp
  · simp only [RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
    simp
  · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
  · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
  · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x14 ≠ .x7),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x14 ≠ .x6),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x14 ≠ .x5), hx14]
  · intro j hj
    omega
  · exact h_ws

theorem nibblesCommonPrefixLenFn_spec (ptrA ptrB outPtr : Word)
    (lenA lenB : Nat) (bsA bsB orig : List (BitVec 8))
    (h_wfA : (Region.mk ptrA bsA).wf) (h_wfB : (Region.mk ptrB bsB).wf)
    (h_wfOut : RwRegion.wf ⟨outPtr, 8⟩) (base : Word) :
    (nibblesCommonPrefixLenFn ptrA ptrB outPtr lenA lenB bsA bsB orig).Spec base := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  vcgen
  case region => exact ⟨h_wfA, RwRegion.empty_wf⟩
  case nibblesCommonPrefixLen.scan.inv_init =>
    rintro rf ws A ⟨rfW, wsW, -, hwhen, hrf, hws⟩
    rcases hwhen with htake | hskip
    · rcases htake with ⟨rf0, ws0, -, ⟨hpre, hcond⟩, hrfW, hwsW⟩
      rcases hpre with ⟨hx10, hx11, hx12, hx13, hx14, rfl, hlenA, hlenB,
        hlenOrig, ha63, hb63, hptrA, hptrB, hA⟩
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] at hrfW hwsW
      subst rfW
      subst wsW
      subst rf
      subst ws
      have hle : lenB ≤ lenA := by
        simp only [Cond.holds, hx11, hx13] at hcond
        simp [BitVec.ult, BitVec.toNat_ofNat] at hcond
        omega
      apply init_inv ptrA ptrB outPtr lenA lenB bsA bsB orig _ []
      · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x11), hx10]
      · rw [RegFile.get_set_self _ _ _ (by decide : (Reg.x11 : Reg) ≠ .x0), hx13]
        congr 1
        exact (Nat.min_eq_right hle).symm
      · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x11), hx12]
      · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x14 ≠ .x11), hx14]
      · rfl
      · exact hlenA
      · exact hlenB
      · exact hlenOrig
      · exact ha63
      · exact hb63
      · exact hptrA
      · exact hptrB
      · exact hA
    · rcases hskip with ⟨hpre, hcond⟩
      rcases hpre with ⟨hx10, hx11, hx12, hx13, hx14, rfl, hlenA, hlenB,
        hlenOrig, ha63, hb63, hptrA, hptrB, hA⟩
      subst rf
      subst ws
      have hle : lenA ≤ lenB := by
        simp only [Cond.holds, not_not, hx11, hx13] at hcond
        simp [BitVec.ult, BitVec.toNat_ofNat] at hcond
        omega
      apply init_inv ptrA ptrB outPtr lenA lenB bsA bsB orig rfW []
      · exact hx10
      · rw [hx11]
        congr 1
        exact (Nat.min_eq_left hle).symm
      · exact hx12
      · exact hx14
      · rfl
      · exact hlenA
      · exact hlenB
      · exact hlenOrig
      · exact ha63
      · exact hb63
      · exact hptrA
      · exact hptrB
      · exact hA
  case nibblesCommonPrefixLen.scan.exhausted =>
    rintro rf ws A ⟨hx5, hx6, hx7, hx11, hx12, hx14, hile, hpref, hlenA,
      hlenB, hlenOrig, ha63, hb63, hptrA, hptrB, hws, hA⟩
    simp only [Cond.holds, hx5, hx11]
    have hcap63 : Nat.min lenA lenB < 2 ^ 63 :=
      lt_of_le_of_lt (Nat.min_le_left _ _) ha63
    rw [slt_ofNat_iff _ _ hcap63 hcap63]
    · omega
  case nibblesCommonPrefixLen.scan.guard_exit =>
    rintro i hile rf ws A ⟨hx5, hx6, hx7, hx11, hx12, hx14, hiCap, hpref,
      hlenA, hlenB, hlenOrig, ha63, hb63, hptrA, hptrB, hws, hA⟩ hng
    have hi : i = Nat.min lenA lenB := by
      by_contra hne
      have hlt : i < Nat.min lenA lenB := by omega
      apply hng
      simp only [Cond.holds, hx5, hx11]
      have hcap63 : Nat.min lenA lenB < 2 ^ 63 :=
        lt_of_le_of_lt (Nat.min_le_left _ _) ha63
      have hi63 : i < 2 ^ 63 := lt_trans hlt hcap63
      rw [slt_ofNat_iff _ _ hi63 hcap63]
      exact hlt
    have hfd : firstDiff bsA bsB (Nat.min lenA lenB) = Nat.min lenA lenB := by
      apply firstDiff_all_eq
      intro j hj
      exact hpref j (by omega)
    dsimp only [scanPost]
    refine ⟨?_, ?_, ?_, hx12, hx14, hws, hlenOrig, hA⟩
    · rw [hx5, hfd, hi]
    · rw [hx6, hfd, hi]
    · rw [hx7, hfd, hi]
  case nibblesCommonPrefixLen.scan.before.loadA.mem =>
    rintro rf ws A hws ⟨i, hi, hinv, hg⟩
    rcases hinv with ⟨hx5, hx6, hx7, hx11, hx12, hx14, hile, hpref, hlenA,
      hlenB, hlenOrig, ha63, hb63, hptrA, hptrB, hws0, hA⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    simp only [blockVCs, loadSem]
    refine ⟨⟨Nat.one_dvd _, ?_⟩, trivial⟩
    show ((rf.get .x6 + signExtend12 0) - ptrA).toNat + 1 ≤ bsA.length
    rw [hse0, hx6]
    have hiA : i < lenA := lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have haddr : ((ptrA + BitVec.ofNat 64 i + 0) - ptrA).toNat = i := by
      bv_omega
    rw [haddr]
    omega
  case nibblesCommonPrefixLen.scan.before.loadB.focus =>
    rintro rf ws A hreach h_a_pc hp hhp
    rcases hreach with ⟨rf0, ws0, -, ⟨i, hi, hinv, hg⟩, hrf, hws⟩
    rcases hinv with ⟨hx5, hx6, hx7, hx11, hx12, hx14, hile, hpref, hlenA,
      hlenB, hlenOrig, ha63, hb63, hptrA, hptrB, hws0, hA⟩
    subst ws0
    have hx12' : rf.get .x12 = ptrB := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28), hx12]
    have hx14' : rf.get .x14 = outPtr := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x14 ≠ .x28), hx14]
    refine ⟨bsB, bytesRegion outPtr orig, ⟨hx12', hx14', rfl, rfl⟩,
      ?_, bytesRegion_pcFree _ _, ?_⟩
    · rw [hx12']
      rw [hA] at hhp
      exact hhp
    · rw [hx12']
      exact h_wfB
  case nibblesCommonPrefixLen.scan.before.loadB.mem =>
    rintro rf ws A robytes rest hws hreach hro hsat
    rcases hreach with ⟨rf0, ws0, -, ⟨i, hi, hinv, hg⟩, hrf, hwsrf⟩
    rcases hinv with ⟨hx5, hx6, hx7, hx11, hx12, hx14, hile, hpref, hlenA,
      hlenB, hlenOrig, ha63, hb63, hptrA, hptrB, hws0, hA⟩
    rcases hro with ⟨hptr, hout, hrob, hrest⟩
    subst ws0
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hx7' : rf.get .x7 = ptrB + BitVec.ofNat 64 i := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx7]
    have hx12' : rf.get .x12 = ptrB := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28), hx12]
    simp only [blockVCs, loadSem]
    refine ⟨⟨Nat.one_dvd _, ?_⟩, trivial⟩
    show ((rf.get .x7 + signExtend12 0) - rf.get .x12).toNat + 1 ≤ robytes.length
    rw [hse0, hx7', hx12', hrob]
    have hiB : i < lenB := lt_of_lt_of_le hi (Nat.min_le_right _ _)
    have haddr : ((ptrB + BitVec.ofNat 64 i + 0) - ptrB).toNat = i := by
      bv_omega
    rw [haddr]
    omega
  case nibblesCommonPrefixLen.scan.inv_step =>
    rintro i hi rf' ws' A' hsp
    rcases hsp with ⟨rfa, wsa, hwsa, ⟨hload, hnbreak⟩, hrf', hws'⟩
    rcases hload with ⟨rf1, ws1, A1, robytes, rest, hlenRead, hsp1, hsat, hro,
      hrfa, hwsaEq, hAeq⟩
    rcases hsp1 with ⟨rfb, wsb, -, ⟨hinv, hg⟩, hrf1, hws1⟩
    rcases hinv with ⟨hx5, hx6, hx7, hx11, hx12, hx14, hile, hpref, hlenA,
      hlenB, hlenOrig, ha63, hb63, hptrA, hptrB, hws0, hA⟩
    rcases hro with ⟨hptr, hout, hrob, hrest⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hwsa
    subst wsb
    have hws1z : ws1 = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [nibblesCommonPrefixLenFn, RwRegion.empty] using hlenRead
    subst ws1
    have hbyteA :
        (nibblesCommonPrefixLenFn ptrA ptrB outPtr lenA lenB bsA bsB orig).region.byteAt
          (rfb.get .x6 + signExtend12 0) = bsA.getD i 0 := by
      unfold Region.byteAt
      rw [show (nibblesCommonPrefixLenFn ptrA ptrB outPtr lenA lenB bsA bsB orig).region.bytes =
          bsA from rfl,
        show (nibblesCommonPrefixLenFn ptrA ptrB outPtr lenA lenB bsA bsB orig).region.base =
          ptrA from rfl, hx6, hse0]
      congr 1
      simpa using add_ofNat_sub_self_toNat ptrA i lenA
        (lt_of_lt_of_le hi (Nat.min_le_left _ _)) hptrA
    have hrf1x5 : rf1.get .x5 = rfb.get .x5 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28)]
    have hrf1x6 : rf1.get .x6 = rfb.get .x6 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28)]
    have hrf1x7 : rf1.get .x7 = rfb.get .x7 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28)]
    have hrf1x11 : rf1.get .x11 = rfb.get .x11 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28)]
    have hrf1x12 : rf1.get .x12 = rfb.get .x12 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
    have hrf1x14 : rf1.get .x14 = rfb.get .x14 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x14 ≠ .x28)]
    have hrf1x28 : rf1.get .x28 = BitVec.zeroExtend 64 (bsA.getD i 0) := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x28 : Reg) ≠ .x0)]
      rw [hbyteA]
    have hbyteB : ({ base := rf1.get .x12, bytes := robytes } : Region).byteAt
        (rf1.get .x7 + signExtend12 0) = bsB.getD i 0 := by
      unfold Region.byteAt
      rw [hrob, hrf1x7, hrf1x12, hx7, hx12, hse0]
      congr 1
      simpa using add_ofNat_sub_self_toNat ptrB i lenB
        (lt_of_lt_of_le hi (Nat.min_le_right _ _)) hptrB
    have hrfa5 : rfa.get .x5 = rfb.get .x5 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x29)]
      exact hrf1x5
    have hrfa6 : rfa.get .x6 = rfb.get .x6 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29)]
      exact hrf1x6
    have hrfa7 : rfa.get .x7 = rfb.get .x7 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29)]
      exact hrf1x7
    have hrfa11 : rfa.get .x11 = rfb.get .x11 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x29)]
      exact hrf1x11
    have hrfa12 : rfa.get .x12 = rfb.get .x12 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x29)]
      exact hrf1x12
    have hrfa14 : rfa.get .x14 = rfb.get .x14 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x14 ≠ .x29)]
      exact hrf1x14
    have hrfa28 : rfa.get .x28 = BitVec.zeroExtend 64 (bsA.getD i 0) := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29)]
      exact hrf1x28
    have hrfa29 : rfa.get .x29 = BitVec.zeroExtend 64 (bsB.getD i 0) := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x29 : Reg) ≠ .x0)]
      rw [hbyteB]
    have heqByte : bsA.getD i 0 = bsB.getD i 0 := by
      have heq : rfa.get .x28 = rfa.get .x29 := by
        by_contra h
        exact hnbreak h
      rw [hrfa28, hrfa29] at heq
      bv_omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, hlenA, hlenB, hlenOrig,
      ha63, hb63, hptrA, hptrB, ?_, ?_⟩
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x5 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6), hrfa5, hx5, hse1]
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x0), hrfa6, hx6,
        hse1]
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x5),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6), hrfa7, hx7, hse1]
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6), hrfa11, hx11]
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6), hrfa12, hx12]
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x14 ≠ .x5),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x14 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x14 ≠ .x6), hrfa14, hx14]
    · intro j hj
      by_cases hji : j < i
      · exact hpref j hji
      · have hji' : j = i := by omega
        rw [hji']
        exact heqByte
    · rw [hws']
      rfl
    · rw [hAeq, hptr, hrob, hrest]
  case nibblesCommonPrefixLen.scan.break =>
    rintro i hi rf' ws' A' hload hbreak
    rcases hload with ⟨rf1, ws1, A1, robytes, rest, hlenRead, hsp1, hsat, hro,
      hrfLoad, hwsaEq, hAeq⟩
    rcases hsp1 with ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrf1, hws1⟩
    rcases hinv with ⟨hx5, hx6, hx7, hx11, hx12, hx14, hile, hpref, hlenA,
      hlenB, hlenOrig, ha63, hb63, hptrA, hptrB, hws0, hA⟩
    rcases hro with ⟨hptr, hout, hrob, hrest⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hws1z : ws1 = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [nibblesCommonPrefixLenFn, RwRegion.empty] using hlenRead
    subst ws1
    have hbyteA :
        (nibblesCommonPrefixLenFn ptrA ptrB outPtr lenA lenB bsA bsB orig).region.byteAt
          (rfb.get .x6 + signExtend12 0) = bsA.getD i 0 := by
      unfold Region.byteAt
      rw [show (nibblesCommonPrefixLenFn ptrA ptrB outPtr lenA lenB bsA bsB orig).region.bytes =
          bsA from rfl,
        show (nibblesCommonPrefixLenFn ptrA ptrB outPtr lenA lenB bsA bsB orig).region.base =
          ptrA from rfl, hx6, hse0]
      congr 1
      simpa using add_ofNat_sub_self_toNat ptrA i lenA
        (lt_of_lt_of_le hi (Nat.min_le_left _ _)) hptrA
    have hrf1x5 : rf1.get .x5 = rfb.get .x5 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28)]
    have hrf1x6 : rf1.get .x6 = rfb.get .x6 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28)]
    have hrf1x7 : rf1.get .x7 = rfb.get .x7 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28)]
    have hrf1x12 : rf1.get .x12 = rfb.get .x12 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
    have hrf1x14 : rf1.get .x14 = rfb.get .x14 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x14 ≠ .x28)]
    have hrf1x28 : rf1.get .x28 = BitVec.zeroExtend 64 (bsA.getD i 0) := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x28 : Reg) ≠ .x0)]
      rw [hbyteA]
    have hbyteB : ({ base := rf1.get .x12, bytes := robytes } : Region).byteAt
        (rf1.get .x7 + signExtend12 0) = bsB.getD i 0 := by
      unfold Region.byteAt
      rw [hrob, hrf1x7, hrf1x12, hx7, hx12, hse0]
      congr 1
      simpa using add_ofNat_sub_self_toNat ptrB i lenB
        (lt_of_lt_of_le hi (Nat.min_le_right _ _)) hptrB
    have hrfa5 : rf'.get .x5 = rfb.get .x5 := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x29)]
      exact hrf1x5
    have hrfa6 : rf'.get .x6 = rfb.get .x6 := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29)]
      exact hrf1x6
    have hrfa7 : rf'.get .x7 = rfb.get .x7 := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29)]
      exact hrf1x7
    have hrfa12 : rf'.get .x12 = rfb.get .x12 := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x29)]
      exact hrf1x12
    have hrfa14 : rf'.get .x14 = rfb.get .x14 := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x14 ≠ .x29)]
      exact hrf1x14
    have hrfa28 : rf'.get .x28 = BitVec.zeroExtend 64 (bsA.getD i 0) := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29)]
      exact hrf1x28
    have hrfa29 : rf'.get .x29 = BitVec.zeroExtend 64 (bsB.getD i 0) := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x29 : Reg) ≠ .x0)]
      rw [hbyteB]
    have hneByte : bsA.getD i 0 ≠ bsB.getD i 0 := by
      have hne : rf'.get .x28 ≠ rf'.get .x29 := hbreak
      rw [hrfa28, hrfa29] at hne
      intro heq
      exact hne (by rw [heq])
    have hfd : firstDiff bsA bsB (Nat.min lenA lenB) = i :=
      firstDiff_ne_of_lt bsA bsB i _ hi hpref hneByte
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hlenOrig, ?_⟩
    · rw [hrfa5, hx5, hfd]
    · rw [hrfa6, hx6, hfd]
    · rw [hrfa7, hx7, hfd]
    · rw [hrfa12, hx12]
    · rw [hrfa14, hx14]
    · exact hwsaEq
    · rw [hAeq, hptr, hrob, hrest]
  case nibblesCommonPrefixLen.doneStore.focus =>
    rintro rf ws A hreach h_a_pc hp hhp
    rcases hreach with ⟨hx5, hx6, hx7, hx12, hx14, hws, hlenOrig, hA⟩
    refine ⟨orig, bytesRegion ptrB bsB, ⟨hx14, rfl, rfl⟩, ?_,
      bytesRegion_pcFree _ _, ?_⟩
    · rw [hx14]
      rw [hA] at hhp
      xperm_hyp hhp
    · rw [hx14, hlenOrig]
      exact h_wfOut
  case nibblesCommonPrefixLen.doneStore.mem =>
    rintro rf ws A win rest hws hreach ⟨hx14, hwin, hrest⟩ hsat
    have haddr :
        (rf.get .x14 + signExtend12 (0 : BitVec 12) - rf.get .x14).toNat = 0 := by
      rw [hse0]
      bv_omega
    have hwl : win.length = 8 := by
      rw [hwin]
      rcases hreach with ⟨-, -, -, -, -, -, hlenOrig, -⟩
      exact hlenOrig
    simp only [blockVCs, storeSem, inRw, and_true]
    refine ⟨?_, ?_⟩
    · rw [haddr, hwl]
    · rw [haddr]
      exact ⟨0, rfl⟩
  case nibblesCommonPrefixLen.post =>
    rintro rf ws A hpost
    rcases hpost with ⟨rfStatus, wsStatus, hwsStatus, hbeforeStatus, hrf, hws⟩
    rcases hbeforeStatus with ⟨rfStore, AStore, win, rest, hwsStore, hscan,
      hsat, hfocus, hrfStatus, hAeq⟩
    rcases hscan with ⟨hx5, hx6, hx7, hx12, hx14, hwsEmpty, hlenOrig, hAStore⟩
    rcases hfocus with ⟨hx14Focus, hwin, hrest⟩
    have hwinLen : win.length = 8 := by rw [hwin, hlenOrig]
    have hsdws :
        (execBlock
          (nibblesCommonPrefixLenFn ptrA ptrB outPtr lenA lenB bsA bsB orig).region
          (rfStore.get .x14) rfStore win [.SD .x14 .x5 0]).2 =
          dwordBytes (rfStore.get .x5) := by
      rw [execBlock_cons,
        execInstrRF_sd_dword _ _ _ _ _ _ _ 0
          (by rw [hse0]; bv_omega),
        execBlock_nil, setBytes_dword_full _ _ hwinLen]
    have hstatusRf : rfStatus = rfStore := by
      rw [hrfStatus, execBlock_cons, execBlock_nil]
      rfl
    rw [hstatusRf] at hrf hws
    have hsdwsOut :
        (execBlock
          (nibblesCommonPrefixLenFn ptrA ptrB outPtr lenA lenB bsA bsB orig).region
          outPtr rfStore win [.SD .x14 .x5 0]).2 = dwordBytes (rfStore.get .x5) := by
      rw [← hx14Focus]
      exact hsdws
    dsimp only [nibblesCommonPrefixLenFn]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
    · rw [hws]
      simpa only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem] using hwsEmpty
    · rw [hAeq, hx14Focus, hsdwsOut, hrest, hx5]

#print axioms nibblesCommonPrefixLenFn_spec

end NibblesCommonPrefixLenSAsm

end EvmAsm.Codegen
