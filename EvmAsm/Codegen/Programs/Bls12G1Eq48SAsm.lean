/-
  EvmAsm.Codegen.Programs.Bls12G1Eq48SAsm

  Verified SAsm drop-in for `blsg_eq48`: a single-exit `whileBreak`
  replacement for the two-exit emitted byte comparison.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.WhileBreakDemo
import EvmAsm.Rv64.SAsm.MultiRead
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.Stmt
open EvmAsm.Rv64.SAsm.WhileBreakDemo

namespace Bls12G1Eq48SAsm

/-! ## blsg_eq48 — verified drop-in (two-exit byte comparison via single-exit whileBreak)

    The emitted `blsgEq48_prog` is a two-exit byte comparison (top `BEQ x5,x0`
    completion + mid `BNE x28,x29` break-on-mismatch), where the two exits
    jump to *different* result blocks (`LI x10,1` / `LI x10,0`).

    Per the drop-in policy (same technique as `secfIsZero48`), the scaffold
    below models it as a **single-exit `whileBreak`** whose body scans 48
    bytes (break on first mismatch), followed by a post-loop block that derives
    the result from the **counter** `x5` (`x5 = 0` ⟺ all 48 bytes matched ⟺
    buffers equal).

    This PR re-emits `blsgEq48_prog` from the verified body; the drop-in gate is
    the `blsgEq48Fn_spec` proof plus EEST A/B parity. -/


/-- Loop invariant at header evaluation `i`: counter `x5 = 48-i`, cursors
    `x6 = ptr1+i`, `x7 = ptr2+i`, and the first `i` bytes are pairwise
    equal (`∀ j < i, bs1.getD j 0 = bs2.getD j 0`). -/
def blsgEqScanInv (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 (48 - i) ∧
    rf.get .x6 = ptr1 + BitVec.ofNat 64 i ∧
    rf.get .x7 = ptr2 + BitVec.ofNat 64 i ∧
    rf.get .x11 = ptr2 ∧
    (∀ j, j < i → bs1.getD j 0 = bs2.getD j 0) ∧
    bs1.length = 48 ∧ bs2.length = 48 ∧
    ptr1.toNat + 48 < 2 ^ 64 ∧ ptr2.toNat + 48 < 2 ^ 64 ∧
    (ptr1.toNat + 48 ≤ ptr2.toNat ∨ ptr2.toNat + 48 ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2

/-- Number of consecutive matching bytes from the front of `bs1`/`bs2`
    (up to `n`).  Returns `n` if all match, else the first mismatch index. -/
def firstDiff (bs1 bs2 : List (BitVec 8)) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if firstDiff bs1 bs2 n < n then firstDiff bs1 bs2 n
      else if bs1.getD n 0 ≠ bs2.getD n 0 then n
      else n + 1

@[simp] theorem firstDiff_zero (bs1 bs2 : List (BitVec 8)) :
    firstDiff bs1 bs2 0 = 0 := rfl

@[simp] theorem firstDiff_succ (bs1 bs2 : List (BitVec 8)) (n : Nat) :
    firstDiff bs1 bs2 (n + 1) =
      (if firstDiff bs1 bs2 n < n then firstDiff bs1 bs2 n
       else if bs1.getD n 0 ≠ bs2.getD n 0 then n else n + 1) := by
  conv_lhs => rw [firstDiff]

theorem firstDiff_le (bs1 bs2 : List (BitVec 8)) : ∀ n, firstDiff bs1 bs2 n ≤ n
  | 0 => Nat.zero_le _
  | n + 1 => by
    rw [firstDiff_succ]
    by_cases h : firstDiff bs1 bs2 n < n
    · rw [if_pos h]; exact Nat.le_succ_of_le (firstDiff_le bs1 bs2 n)
    · rw [if_neg h]; split <;> omega

theorem firstDiff_all_eq (bs1 bs2 : List (BitVec 8)) (n : Nat)
    (h : ∀ j, j < n → bs1.getD j 0 = bs2.getD j 0) :
    firstDiff bs1 bs2 n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [firstDiff_succ, ih (fun j hj => h j (by omega)), if_neg (Nat.lt_irrefl _)]
    by_cases hne : bs1.getD n 0 ≠ bs2.getD n 0
    · exact absurd hne (fun h2 => h2 (h n (by omega)))
    · rw [if_neg hne]

theorem firstDiff_ne (bs1 bs2 : List (BitVec 8)) (i : Nat)
    (hprev : ∀ j, j < i → bs1.getD j 0 = bs2.getD j 0)
    (hne : bs1.getD i 0 ≠ bs2.getD i 0) :
    firstDiff bs1 bs2 (i + 1) = i := by
  rw [firstDiff_succ, firstDiff_all_eq _ _ _ hprev, if_neg (Nat.lt_irrefl _), if_pos hne]

theorem firstDiff_ne_of_lt (bs1 bs2 : List (BitVec 8)) (i n : Nat)
    (hi : i < n)
    (hprev : ∀ j, j < i → bs1.getD j 0 = bs2.getD j 0)
    (hne : bs1.getD i 0 ≠ bs2.getD i 0) :
    firstDiff bs1 bs2 n = i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hlt : i < n
    · have hih := ih hlt
      rw [firstDiff_succ, hih, if_pos hlt]
    · have hin : i = n := by omega
      subst i
      exact firstDiff_ne bs1 bs2 n hprev hne

/-- `whileBreak` post (at the single `Lend`): the scan stopped at index
    `firstDiff`; `x5 = 48 - firstDiff` (so `x5 = 0` ⟺ all 48 bytes matched). -/
def blsgEqScanPost (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 (48 - firstDiff bs1 bs2 48) ∧
    rf.get .x6 = ptr1 + BitVec.ofNat 64 (firstDiff bs1 bs2 48) ∧
    rf.get .x7 = ptr2 + BitVec.ofNat 64 (firstDiff bs1 bs2 48) ∧
    rf.get .x11 = ptr2 ∧
    bs1.length = 48 ∧ bs2.length = 48 ∧
    ptr1.toNat + 48 < 2 ^ 64 ∧ ptr2.toNat + 48 < 2 ^ 64 ∧
    (ptr1.toNat + 48 ≤ ptr2.toNat ∨ ptr2.toNat + 48 ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2

/-- Focus relation for the second read-only input: `x11` remains the stable
    base pointer for `bs2`, while the loop body may load through cursor `x7`. -/
def blsgEqReadA1 (ptr2 : Word) (bs2 : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rest => rf.get .x11 = ptr2 ∧ rob = bs2 ∧ rest = empAssertion

/-- `blsg_eq48` body: init counter/cursors, scan-and-break, then derive
    the result from the counter (`LI x10,1`; clear to 0 if `x5≠0`). -/
def blsgEq48Body (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (48 : Word), .MV .x6 .x10, .MV .x7 .x11] ;;;
  .«whileBreak» "scan" (.bne .x5 .x0) 48
    (blsgEqScanInv ptr1 ptr2 bs1 bs2) (blsgEqScanPost ptr1 ptr2 bs1 bs2)
    (.block "load1" [.LBU .x28 .x6 (0 : BitVec 12)] ;;;
     .readAt "load2" .x11 (blsgEqReadA1 ptr2 bs2) [.LBU .x29 .x7 (0 : BitVec 12)])
    (.bne .x28 .x29)
    (.block "next" [.ADDI .x6 .x6 (1 : BitVec 12), .ADDI .x7 .x7 (1 : BitVec 12),
                    .ADDI .x5 .x5 (-1 : BitVec 12)]) ;;;
  .block "res1" [.LI .x10 (1 : Word)] ;;;
  .when "clr" (.bne .x5 .x0) (.block "clr0" [.LI .x10 (0 : Word)])

/-- Verified `Fn`: `x10 := if (the 48 bytes at `a0` equal the 48 bytes at
    `a1`) then 1 else 0`. -/
def blsgEq48Fn (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Fn where
  name := "blsgEq48"
  region := ⟨ptr1, bs1⟩
  pre := fun rf _ A =>
    rf.get .x10 = ptr1 ∧ rf.get .x11 = ptr2 ∧
    bs1.length = 48 ∧ bs2.length = 48 ∧
    ptr1.toNat + 48 < 2 ^ 64 ∧ ptr2.toNat + 48 < 2 ^ 64 ∧
    (ptr1.toNat + 48 ≤ ptr2.toNat ∨ ptr2.toNat + 48 ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2
  post := fun rf _ A =>
    (rf.get .x10 = if firstDiff bs1 bs2 48 = 48 then (1 : Word) else (0 : Word)) ∧
    bs1.length = 48 ∧ bs2.length = 48 ∧
    ptr1.toNat + 48 < 2 ^ 64 ∧ ptr2.toNat + 48 < 2 ^ 64 ∧
    A = bytesRegion ptr2 bs2
  body := blsgEq48Body ptr1 ptr2 bs1 bs2

/-- Re-emitted drop-in: the verified `blsgEq48Body` flatten + `ret`. -/
def blsgEq48_prog : Program :=
  (blsgEq48Body 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]

def blsgEq48Function : String :=
  "blsg_eq48:\n" ++ emitProgram blsgEq48_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    the verified re-emitted `blsgEq48_prog` rendered under its label. -/
theorem blsgEq48Function_eq_prog :
    blsgEq48Function = "blsg_eq48:\n" ++ emitProgram blsgEq48_prog := rfl

#guard blsgEq48Function.startsWith "blsg_eq48:\n"
-- The drop-in is position-independent (no PC-relative instruction).
#guard (blsgEq48Body 0 0 [] []).flatten 0 = (blsgEq48Body 0 0 [] []).flatten 0x80000000

theorem blsgEq48Fn_spec (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8))
    (hwf1 : (Region.mk ptr1 bs1).wf) (hwf2 : (Region.mk ptr2 bs2).wf) (base : Word) :
    (blsgEq48Fn ptr1 ptr2 bs1 bs2).Spec base := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hsem1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  vcgen
  case region => exact ⟨hwf1, RwRegion.empty_wf⟩
  case blsgEq48.scan.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, ⟨hx10, hx11, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]
      decide
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
      simp
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
      simp
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]
      exact hx11
    · intro j hj; omega
  case blsgEq48.scan.exhausted =>
    rintro rf ws A ⟨hx5, -, -, -, -, -, -, -, -, -, -⟩
    intro hc
    apply hc
    rw [hx5, show 48 - 48 = 0 from by omega]; rfl
  case blsgEq48.scan.guard_exit =>
    rintro i hile rf ws A ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ hng
    have hil : i = 48 := by
      by_contra hne
      apply hng
      show rf.get .x5 ≠ rf.get .x0
      rw [hx5, show rf.get .x0 = 0 from rfl]
      intro h
      have := congrArg (fun w : Word => w.toNat) h
      simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this
      omega
    have hfd : firstDiff bs1 bs2 48 = 48 := by
      apply firstDiff_all_eq
      intro j hj
      exact hpref j (by omega)
    refine ⟨?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩
    · rw [hx5, hfd, hil]
    · rw [hx6, hfd, hil]
    · rw [hx7, hfd, hil]
    · exact hx11

  case blsgEq48.scan.before.load1.mem =>
    rintro rf ws A hws ⟨i, hi, ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩, hg⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hilt : i < 48 := by
      rcases Nat.lt_or_ge i 48 with h | h
      · exact h
      · exfalso; apply hg
        rw [hx5, show 48 - i = 0 from by omega]; rfl
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial⟩
    show ((rf.get .x6 + signExtend12 (0 : BitVec 12)) - ptr1).toNat + 1 ≤ bs1.length
    rw [hse0, hx6]
    have haddr : ((ptr1 + BitVec.ofNat 64 i + 0) - ptr1).toNat = i := by bv_omega
    rw [haddr]; omega
  case blsgEq48.scan.before.load2.focus =>
    rintro rf ws A hreach hApc hp hhp
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv, hg⟩, hrf, hws⟩ := hreach
    obtain ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ := hinv
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    have hx11' : rf.get .x11 = ptr2 := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem, inRw]
      exact hx11
    refine ⟨bs2, empAssertion, ⟨hx11', rfl, rfl⟩, ?_, pcFree_emp, ?_⟩
    · rw [hx11', sepConj_emp_right']
      rw [hA] at hhp
      exact hhp
    · rw [hx11']
      exact hwf2

  case blsgEq48.scan.before.load2.mem =>
    rintro rf ws A robytes rest hws hreach hro hsat
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv, hg⟩, hrf, hwsrf⟩ := hreach
    obtain ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hx7' : rf.get .x7 = ptr2 + BitVec.ofNat 64 i := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem, inRw]
      exact hx7
    have hx11' : rf.get .x11 = ptr2 := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem, inRw]
      exact hx11
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial⟩
    show ((rf.get .x7 + signExtend12 (0 : BitVec 12)) - rf.get .x11).toNat + 1 ≤ robytes.length
    rw [hse0, hx7', hx11', hrob]
    have haddr : ((ptr2 + BitVec.ofNat 64 i + 0) - ptr2).toNat = i := by bv_omega
    rw [haddr]; omega

  case blsgEq48.scan.inv_step =>
    rintro i hi rf' ws' A' hsp
    obtain ⟨rfa, wsa, hwsa, ⟨hload, hnbreak⟩, hrf', hws'⟩ := hsp
    obtain ⟨rf1, ws1, A1, robytes, rest, hlenRead, hsp1, hsat, hro, hrfa, hwsaEq, hAeq⟩ := hload
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrf1, hws1⟩ := hsp1
    obtain ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hws1len0 : ws1.length = 0 := by simpa [blsgEq48Fn, RwRegion.empty] using hlenRead
    obtain rfl := List.eq_nil_of_length_eq_zero hws1len0
    have hbyte1 : (blsgEq48Fn ptr1 ptr2 bs1 bs2).region.byteAt (rfb.get .x6 + signExtend12 0)
        = bs1.getD i 0 := by
      unfold Region.byteAt
      rw [show (blsgEq48Fn ptr1 ptr2 bs1 bs2).region.bytes = bs1 from rfl,
          show (blsgEq48Fn ptr1 ptr2 bs1 bs2).region.base = ptr1 from rfl, hx6, hse0]
      congr 1
      bv_omega
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
    have hrf1x28 : rf1.get .x28 = BitVec.zeroExtend 64 (bs1.getD i 0) := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x28 : Reg) ≠ .x0)]
      rw [hbyte1]
    have hbyte2 : ({ base := rf1.get .x11, bytes := robytes } : Region).byteAt
        (rf1.get .x7 + signExtend12 0) = bs2.getD i 0 := by
      unfold Region.byteAt
      rw [hrob, hrf1x7, hrf1x11, hx7, hx11, hse0]
      congr 1
      bv_omega
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
    have hrfa28 : rfa.get .x28 = BitVec.zeroExtend 64 (bs1.getD i 0) := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29)]
      exact hrf1x28
    have hrfa29 : rfa.get .x29 = BitVec.zeroExtend 64 (bs2.getD i 0) := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x29 : Reg) ≠ .x0)]
      rw [hbyte2]
    have heqByte : bs1.getD i 0 = bs2.getD i 0 := by
      have hne : rfa.get .x28 = rfa.get .x29 := by
        by_contra h; exact hnbreak h
      rw [hrfa28, hrfa29] at hne
      bv_omega
    refine ⟨?_, ?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, ?_⟩
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x5 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6)]
      rw [hrfa5, hx5, hsem1]
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x0)]
      rw [hrfa6, hx6, hse1]
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x5),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6)]
      rw [hrfa7, hx7, hse1]
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6)]
      rw [hrfa11, hx11]
    · intro j hj
      by_cases hji : j < i
      · exact hpref j hji
      · have hji' : j = i := by omega
        rw [hji']; exact heqByte
    · rw [hAeq, hptr, hrob, hrest, sepConj_emp_right']
  case blsgEq48.scan.break =>
    rintro i hi rf' ws' A' hload hbreak
    obtain ⟨rf1, ws1, A1, robytes, rest, hlenRead, hsp1, hsat, hro, hrfLoad, hwsaEq, hAeq⟩ := hload
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrf1, hws1⟩ := hsp1
    obtain ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hws1len0 : ws1.length = 0 := by simpa [blsgEq48Fn, RwRegion.empty] using hlenRead
    obtain rfl := List.eq_nil_of_length_eq_zero hws1len0
    have hbyte1 : (blsgEq48Fn ptr1 ptr2 bs1 bs2).region.byteAt (rfb.get .x6 + signExtend12 0)
        = bs1.getD i 0 := by
      unfold Region.byteAt
      rw [show (blsgEq48Fn ptr1 ptr2 bs1 bs2).region.bytes = bs1 from rfl,
          show (blsgEq48Fn ptr1 ptr2 bs1 bs2).region.base = ptr1 from rfl, hx6, hse0]
      congr 1
      bv_omega
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
    have hrf1x28 : rf1.get .x28 = BitVec.zeroExtend 64 (bs1.getD i 0) := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x28 : Reg) ≠ .x0)]
      rw [hbyte1]
    have hbyte2 : ({ base := rf1.get .x11, bytes := robytes } : Region).byteAt
        (rf1.get .x7 + signExtend12 0) = bs2.getD i 0 := by
      unfold Region.byteAt
      rw [hrob, hrf1x7, hrf1x11, hx7, hx11, hse0]
      congr 1
      bv_omega
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
    have hrfa11 : rf'.get .x11 = rfb.get .x11 := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x29)]
      exact hrf1x11
    have hrfa28 : rf'.get .x28 = BitVec.zeroExtend 64 (bs1.getD i 0) := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29)]
      exact hrf1x28
    have hrfa29 : rf'.get .x29 = BitVec.zeroExtend 64 (bs2.getD i 0) := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x29 : Reg) ≠ .x0)]
      rw [hbyte2]
    have hneByte : bs1.getD i 0 ≠ bs2.getD i 0 := by
      have hne : rf'.get .x28 ≠ rf'.get .x29 := hbreak
      rw [hrfa28, hrfa29] at hne
      intro heq
      exact hne (by rw [heq])
    have hfd : firstDiff bs1 bs2 48 = i := firstDiff_ne_of_lt bs1 bs2 i 48 hi hpref hneByte
    refine ⟨?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, ?_⟩
    · rw [hrfa5, hx5, hfd]
    · rw [hrfa6, hx6, hfd]
    · rw [hrfa7, hx7, hfd]
    · rw [hrfa11, hx11]
    · rw [hAeq, hptr, hrob, hrest, sepConj_emp_right']
  case blsgEq48.post =>
    rintro rf ws A hpost
    rcases hpost with
      ⟨rf₁, ws₁, hws₁, ⟨hres1, hcond⟩, hrf1, rfl⟩ | ⟨hres1, hnc⟩
    · obtain rfl := List.eq_nil_of_length_eq_zero hws₁
      obtain ⟨rfa, wsa, hwsa, hscanPost, hrf1eq, -⟩ := hres1
      obtain rfl := List.eq_nil_of_length_eq_zero hwsa
      obtain ⟨hx5a, -, -, -, hlen1, hlen2, hpl1, hpl2, -, hA⟩ := hscanPost
      have hx10rf : rf.get .x10 = (0 : Word) := by
        rw [hrf1]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have hr1x5 : rf₁.get .x5 = rfa.get .x5 := by
        rw [hrf1eq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x10)]
      have hne : firstDiff bs1 bs2 48 ≠ 48 := by
        dsimp only [Cond.holds] at hcond
        intro heq
        apply hcond
        rw [hr1x5, hx5a, heq]
        rfl
      refine ⟨?_, hlen1, hlen2, hpl1, hpl2, hA⟩
      rw [hx10rf]
      by_cases h : firstDiff bs1 bs2 48 = 48
      · rw [if_pos h]
        exact False.elim (hne h)
      · rw [if_neg h]
    · obtain ⟨rfa, wsa, hwsa, hscanPost, hrfeq, -⟩ := hres1
      obtain rfl := List.eq_nil_of_length_eq_zero hwsa
      obtain ⟨hx5a, -, -, -, hlen1, hlen2, hpl1, hpl2, -, hA⟩ := hscanPost
      have hx10rf : rf.get .x10 = (1 : Word) := by
        rw [hrfeq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have hrfx5 : rf.get .x5 = rfa.get .x5 := by
        rw [hrfeq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x10)]
      dsimp only [Cond.holds] at hnc
      have heq : firstDiff bs1 bs2 48 = 48 := by
        have hrfeq5 : rf.get .x5 = BitVec.ofNat 64 (48 - firstDiff bs1 bs2 48) := by
          rw [hrfx5, hx5a]
        have h0 : rf.get .x5 = (0 : Word) := by
          by_contra hne
          exact hnc hne
        rw [hrfeq5] at h0
        have hT : (BitVec.ofNat 64 (48 - firstDiff bs1 bs2 48)).toNat =
            (48 - firstDiff bs1 bs2 48) % 2 ^ 64 := BitVec.toNat_ofNat ..
        have hz : (0 : Word).toNat = 0 := rfl
        have hmod : (48 - firstDiff bs1 bs2 48) % 2 ^ 64 = 0 := by
          have := congrArg BitVec.toNat h0
          rw [hT, hz] at this
          exact this
        have hle : firstDiff bs1 bs2 48 ≤ 48 := firstDiff_le bs1 bs2 48
        omega
      refine ⟨?_, hlen1, hlen2, hpl1, hpl2, hA⟩
      rw [hx10rf, if_pos heq]

/-! ## Flat linked-entry contract -/

def blsgEq48Cr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.blsg_eq48 : Word) blsgEq48_prog

def blsgEq48Scratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_eq48 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
        regAtomsOf vf blsgEq48Scratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [blsgEq48Scratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem eq48_args_notin_scratch :
    ∀ r ∈ blsgEq48Scratch,
      r ≠ (.x10 : Reg) ∧ r ≠ (.x11 : Reg) := by
  decide

theorem blsgEq48Flat_spec (ret ptr1 ptr2 : Word)
    (bs1 bs2 : List (BitVec 8))
    (hwf1 : (Region.mk ptr1 bs1).wf)
    (hwf2 : (Region.mk ptr2 bs2).wf)
    (hlen1 : bs1.length = 48) (hlen2 : bs2.length = 48)
    (hpl1 : ptr1.toNat + 48 < 2 ^ 64)
    (hpl2 : ptr2.toNat + 48 < 2 ^ 64)
    (hdisj : ptr1.toNat + 48 ≤ ptr2.toNat ∨ ptr2.toNat + 48 ≤ ptr1.toNat)
    (hsize : 4 * ((blsgEq48Fn ptr1 ptr2 bs1 bs2).body.size + 1) ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((blsgEq48Fn ptr1 ptr2 bs1 bs2).body.steps + 1)
      (GuestAddrs.blsg_eq48 : Word) ret blsgEq48Cr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ ptr1) ** (.x11 ↦ᵣ ptr2) **
        regOwns blsgEq48Scratch ** bytesRegion ptr2 bs2 **
        bytesRegion ptr1 bs1)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion ptr2 bs2 ** bytesRegion ptr1 bs1) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns blsgEq48Scratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ ptr1) ** (.x11 ↦ᵣ ptr2) **
        bytesRegion ptr2 bs2 ** bytesRegion ptr1 bs1)
      (fun vf => ?_))
  have hpre : (blsgEq48Fn ptr1 ptr2 bs1 bs2).pre
      (fun r => if r = .x10 then ptr1 else
        if r = .x11 then ptr2 else vf r)
      [] (bytesRegion ptr2 bs2) := by
    refine ⟨?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, rfl⟩
    · show RegFile.get _ .x10 = ptr1
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = ptr2
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (blsgEq48Fn ptr1 ptr2 bs1 bs2)
    (GuestAddrs.blsg_eq48 : Word)
    (blsgEq48Fn_spec ptr1 ptr2 bs1 bs2 hwf1 hwf2
      (GuestAddrs.blsg_eq48 : Word))
    hsize ret halign
    (fun r => if r = .x10 then ptr1 else
      if r = .x11 then ptr2 else vf r)
    [] (bytesRegion ptr2 bs2) (bytesRegion_pcFree _ _) rfl hpre
    (fun _ _ _ hpost => hpost.2.2.2.2.2)
    (Q := regOwns exposedRegs ** bytesRegion ptr2 bs2)
    (fun rf' ws' hws' hpost' hp hh => by
      obtain rfl := List.eq_nil_of_length_eq_zero hws'
      rw [bytesRegion_nil, sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh)
  rw [show (blsgEq48Fn ptr1 ptr2 bs1 bs2).programRet
      (GuestAddrs.blsg_eq48 : Word) = blsgEq48_prog from rfl] at had
  have hadC := had
  rw [show (blsgEq48Fn ptr1 ptr2 bs1 bs2).rw = RwRegion.empty from rfl,
    show (blsgEq48Fn ptr1 ptr2 bs1 bs2).region = Region.mk ptr1 bs1 from rfl,
    bytesRegion_nil, sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_eq48,
    show (if (Reg.x10 : Reg) = .x10 then ptr1 else
        if (Reg.x10 : Reg) = .x11 then ptr2 else vf .x10) = ptr1
      from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then ptr1 else
        if (Reg.x11 : Reg) = .x11 then ptr2 else vf .x11) = ptr2
      from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then ptr1 else
        if r = .x11 then ptr2 else vf r)
      vf blsgEq48Scratch
      (fun r hr => by
        show (if r = .x10 then ptr1 else
          if r = .x11 then ptr2 else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) =>
              (eq48_args_notin_scratch r hr).1 hc),
            if_neg (fun (hc : r = .x11) =>
              (eq48_args_notin_scratch r hr).2 hc)])] at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC



end Bls12G1Eq48SAsm

end EvmAsm.Codegen
