/-
  EvmAsm.Codegen.Programs.Bls12G2EqNSAsm

  Verified SAsm drop-in for `blsg2_eq_n`: a single-exit `whileBreak`
  replacement for the two-exit emitted byte comparison.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.WhileBreakDemo
import EvmAsm.Rv64.SAsm.MultiRead
import EvmAsm.Rv64.SAsm.DualReadByteScan

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.Stmt
open EvmAsm.Rv64.SAsm.WhileBreakDemo

namespace Bls12G2EqNSAsm

/-! ## blsg2_eq_n — verified drop-in (two-exit byte comparison via single-exit whileBreak)

    The emitted `blsg2EqN_prog` is a two-exit byte comparison (top `BEQ x5,x0`
    completion + mid `BNE x28,x29` break-on-mismatch), where the two exits
    jump to *different* result blocks (`LI x10,1` / `LI x10,0`).

    Per the drop-in policy (same technique as `secfEq32`), the scaffold
    below models it as a **single-exit `whileBreak`** whose body scans `a2`
    bytes (break on first mismatch), followed by a post-loop block that derives
    the result from the **counter** `x5` (`x5 = 0` ⟺ all a2 bytes matched ⟺
    buffers equal).

    This PR re-emits `blsg2EqN_prog` from the verified body; the drop-in gate is
    the `blsg2EqNFn_spec` proof plus EEST A/B parity. -/


/-- Loop invariant at header evaluation `i`: counter `x5 = n-i`, cursors
    `x6 = ptr1+i`, `x7 = ptr2+i`, and the first `i` bytes are pairwise
    equal (`∀ j < i, bs1.getD j 0 = bs2.getD j 0`). -/
def blsg2EqScanInv (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) (n : Nat) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 (n - i) ∧
    rf.get .x6 = ptr1 + BitVec.ofNat 64 i ∧
    rf.get .x7 = ptr2 + BitVec.ofNat 64 i ∧
    rf.get .x11 = ptr2 ∧
    (∀ j, j < i → bs1.getD j 0 = bs2.getD j 0) ∧
    bs1.length = n ∧ bs2.length = n ∧
    ptr1.toNat + n < 2 ^ 64 ∧ ptr2.toNat + n < 2 ^ 64 ∧
    (ptr1.toNat + n ≤ ptr2.toNat ∨ ptr2.toNat + n ≤ ptr1.toNat) ∧
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
    `firstDiff`; `x5 = n - firstDiff` (so `x5 = 0` ⟺ all a2 bytes matched). -/
def blsg2EqScanPost (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) (n : Nat) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 (n - firstDiff bs1 bs2 n) ∧
    rf.get .x6 = ptr1 + BitVec.ofNat 64 (firstDiff bs1 bs2 n) ∧
    rf.get .x7 = ptr2 + BitVec.ofNat 64 (firstDiff bs1 bs2 n) ∧
    rf.get .x11 = ptr2 ∧
    bs1.length = n ∧ bs2.length = n ∧
    ptr1.toNat + n < 2 ^ 64 ∧ ptr2.toNat + n < 2 ^ 64 ∧
    (ptr1.toNat + n ≤ ptr2.toNat ∨ ptr2.toNat + n ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2

/-- Focus relation for the second read-only input: `x11` remains the stable
    base pointer for `bs2`, while the loop body may load through cursor `x7`. -/
def blsg2EqReadA1 (ptr2 : Word) (bs2 : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rest => rf.get .x11 = ptr2 ∧ rob = bs2 ∧ rest = empAssertion

/-- `blsg2_eq_n` body: init counter/cursors, scan-and-break, then derive
    the result from the counter (`LI x10,1`; clear to 0 if `x5≠0`). -/
def blsg2EqNBody (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) (n : Nat) : Stmt :=
  .block "init" [.MV .x6 .x10, .MV .x7 .x11, .MV .x5 .x12] ;;;
  .«whileBreak» "scan" (.bne .x5 .x0) n
    (blsg2EqScanInv ptr1 ptr2 bs1 bs2 n) (blsg2EqScanPost ptr1 ptr2 bs1 bs2 n)
    (.block "load1" [.LBU .x28 .x6 (0 : BitVec 12)] ;;;
     .readAt "load2" .x11 (blsg2EqReadA1 ptr2 bs2) [.LBU .x29 .x7 (0 : BitVec 12)])
    (.bne .x28 .x29)
    (.block "next" [.ADDI .x6 .x6 (1 : BitVec 12), .ADDI .x7 .x7 (1 : BitVec 12),
                    .ADDI .x5 .x5 (-1 : BitVec 12)]) ;;;
  .block "res1" [.LI .x10 (1 : Word)] ;;;
  .when "clr" (.bne .x5 .x0) (.block "clr0" [.LI .x10 (0 : Word)])

/-- Verified `Fn`: `x10 := if (the a2 bytes at `a0` equal the a2 bytes at
    `a1`) then 1 else 0`. -/
def blsg2EqNFn (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) (n : Nat) : Fn where
  name := "blsg2EqN"
  region := ⟨ptr1, bs1⟩
  pre := fun rf _ A =>
    rf.get .x10 = ptr1 ∧ rf.get .x11 = ptr2 ∧ rf.get .x12 = BitVec.ofNat 64 n ∧
    bs1.length = n ∧ bs2.length = n ∧
    ptr1.toNat + n < 2 ^ 64 ∧ ptr2.toNat + n < 2 ^ 64 ∧
    (ptr1.toNat + n ≤ ptr2.toNat ∨ ptr2.toNat + n ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2
  post := fun rf _ A =>
    (rf.get .x10 = if firstDiff bs1 bs2 n = n then (1 : Word) else (0 : Word)) ∧
    bs1.length = n ∧ bs2.length = n ∧
    ptr1.toNat + n < 2 ^ 64 ∧ ptr2.toNat + n < 2 ^ 64 ∧
    A = bytesRegion ptr2 bs2
  body := blsg2EqNBody ptr1 ptr2 bs1 bs2 n

/-- Re-emitted drop-in: the verified `blsg2EqNBody` flatten + `ret`. -/
def blsg2EqN_prog : Program :=
  (blsg2EqNBody 0 0 [] [] 0).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]

def blsg2EqNFunction : String :=
  "blsg2_eq_n:\n" ++ emitProgram blsg2EqN_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    the verified re-emitted `blsg2EqN_prog` rendered under its label. -/
theorem blsg2EqNFunction_eq_prog :
    blsg2EqNFunction = "blsg2_eq_n:\n" ++ emitProgram blsg2EqN_prog := rfl

#guard blsg2EqNFunction.startsWith "blsg2_eq_n:\n"
#guard blsg2EqN_prog.length = 15
-- The drop-in is position-independent (no PC-relative instruction).
#guard (blsg2EqNBody 0 0 [] [] 0).flatten 0 = (blsg2EqNBody 0 0 [] [] 0).flatten 0x80000000

theorem blsg2EqNFn_spec (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) (n : Nat)
    (hwf1 : (Region.mk ptr1 bs1).wf) (hwf2 : (Region.mk ptr2 bs2).wf) (base : Word) :
    (blsg2EqNFn ptr1 ptr2 bs1 bs2 n).Spec base := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hsem1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  vcgen
  case region => exact ⟨hwf1, RwRegion.empty_wf⟩
  case blsg2EqN.scan.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, ⟨hx10, hx11, hx12, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩
    · simp [hx12]
    · simp [hx10]
    · simp [hx11]
    · simp [hx11]
    · intro j hj; omega
  case blsg2EqN.scan.exhausted =>
    rintro rf ws A ⟨hx5, -, -, -, -, -, -, -, -, -, -⟩
    intro hc
    apply hc
    rw [hx5, show n - n = 0 from by omega]; rfl
  case blsg2EqN.scan.guard_exit =>
    rintro i hile rf ws A ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ hng
    have hil : i = n := by
      by_contra hne
      apply hng
      show rf.get .x5 ≠ rf.get .x0
      rw [hx5, show rf.get .x0 = 0 from rfl]
      intro h
      have := congrArg (fun w : Word => w.toNat) h
      simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this
      omega
    have hfd : firstDiff bs1 bs2 n = n := by
      apply firstDiff_all_eq
      intro j hj
      exact hpref j (by omega)
    refine ⟨?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩
    · rw [hx5, hfd, hil]
    · rw [hx6, hfd, hil]
    · rw [hx7, hfd, hil]
    · exact hx11

  case blsg2EqN.scan.before.load1.mem =>
    rintro rf ws A hws ⟨i, hi, ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩, hg⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hilt : i < n := by
      rcases Nat.lt_or_ge i n with h | h
      · exact h
      · exfalso; apply hg
        rw [hx5, show n - i = 0 from by omega]; rfl
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial⟩
    show ((rf.get .x6 + signExtend12 (0 : BitVec 12)) - ptr1).toNat + 1 ≤ bs1.length
    rw [hse0, hx6]
    have haddr : ((ptr1 + BitVec.ofNat 64 i + 0) - ptr1).toNat = i := by bv_omega
    rw [haddr]; omega
  case blsg2EqN.scan.before.load2.focus =>
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

  case blsg2EqN.scan.before.load2.mem =>
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

  case blsg2EqN.scan.inv_step =>
    rintro i hi rf' ws' A' hsp
    obtain ⟨rfa, wsa, hwsa, ⟨hload, hnbreak⟩, hrf', hws'⟩ := hsp
    obtain ⟨rf1, ws1, A1, robytes, rest, hlenRead, hsp1, hsat, hro, hrfa, hwsaEq, hAeq⟩ := hload
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrf1, hws1⟩ := hsp1
    obtain ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hws1len0 : ws1.length = 0 := by simpa [blsg2EqNFn, RwRegion.empty] using hlenRead
    obtain rfl := List.eq_nil_of_length_eq_zero hws1len0
    have hbyte1 : (blsg2EqNFn ptr1 ptr2 bs1 bs2 n).region.byteAt (rfb.get .x6 + signExtend12 0)
        = bs1.getD i 0 := by
      unfold Region.byteAt
      rw [show (blsg2EqNFn ptr1 ptr2 bs1 bs2 n).region.bytes = bs1 from rfl,
          show (blsg2EqNFn ptr1 ptr2 bs1 bs2 n).region.base = ptr1 from rfl, hx6, hse0]
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
  case blsg2EqN.scan.break =>
    rintro i hi rf' ws' A' hload hbreak
    obtain ⟨rf1, ws1, A1, robytes, rest, hlenRead, hsp1, hsat, hro, hrfLoad, hwsaEq, hAeq⟩ := hload
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrf1, hws1⟩ := hsp1
    obtain ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hws1len0 : ws1.length = 0 := by simpa [blsg2EqNFn, RwRegion.empty] using hlenRead
    obtain rfl := List.eq_nil_of_length_eq_zero hws1len0
    have hbyte1 : (blsg2EqNFn ptr1 ptr2 bs1 bs2 n).region.byteAt (rfb.get .x6 + signExtend12 0)
        = bs1.getD i 0 := by
      unfold Region.byteAt
      rw [show (blsg2EqNFn ptr1 ptr2 bs1 bs2 n).region.bytes = bs1 from rfl,
          show (blsg2EqNFn ptr1 ptr2 bs1 bs2 n).region.base = ptr1 from rfl, hx6, hse0]
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
    have hfd : firstDiff bs1 bs2 n = i := firstDiff_ne_of_lt bs1 bs2 i n hi hpref hneByte
    refine ⟨?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, ?_⟩
    · rw [hrfa5, hx5, hfd]
    · rw [hrfa6, hx6, hfd]
    · rw [hrfa7, hx7, hfd]
    · rw [hrfa11, hx11]
    · rw [hAeq, hptr, hrob, hrest, sepConj_emp_right']
  case blsg2EqN.post =>
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
      have hne : firstDiff bs1 bs2 n ≠ n := by
        dsimp only [Cond.holds] at hcond
        intro heq
        apply hcond
        rw [hr1x5, hx5a, heq, show n - n = 0 from by omega]
        rfl
      refine ⟨?_, hlen1, hlen2, hpl1, hpl2, hA⟩
      rw [hx10rf]
      by_cases h : firstDiff bs1 bs2 n = n
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
      have heq : firstDiff bs1 bs2 n = n := by
        have hrfeq5 : rf.get .x5 = BitVec.ofNat 64 (n - firstDiff bs1 bs2 n) := by
          rw [hrfx5, hx5a]
        have h0 : rf.get .x5 = (0 : Word) := by
          by_contra hne
          exact hnc hne
        rw [hrfeq5] at h0
        have hT : (BitVec.ofNat 64 (n - firstDiff bs1 bs2 n)).toNat =
            (n - firstDiff bs1 bs2 n) % 2 ^ 64 := BitVec.toNat_ofNat ..
        have hz : (0 : Word).toNat = 0 := rfl
        have hmod : (n - firstDiff bs1 bs2 n) % 2 ^ 64 = 0 := by
          have := congrArg BitVec.toNat h0
          rw [hT, hz] at this
          exact this
        have hle : firstDiff bs1 bs2 n ≤ n := firstDiff_le bs1 bs2 n
        omega
      refine ⟨?_, hlen1, hlen2, hpl1, hpl2, hA⟩
      rw [hx10rf, if_pos heq]


#print axioms blsg2EqNFn_spec

/-! ## The byte-transparent whole-routine spec (genuine byte-equality post)

    `blsg2EqN_spec` supersedes the `firstDiff`-shaped `Fn` post above: it is
    stated at the `#guard`-tied `GuestAddrs.blsg2_eq_n` directly over the
    emitted `blsg2EqN_prog` (byte-transparent — the program IS the 3-`MV`
    init followed by `DualReadByteScan.byteScanProg` at the emitted
    registers, kernel-checked below), with the REAL dynamic-length
    byte-equality verdict:

    `a0 = (if bs1 = bs2 then 1 else 0)`, both `n`-byte inputs untouched
    (`n` the entry value of `a2`), via `DualReadByteScan.scan_spec` and its
    per-byte → byte-list bridge `bytes_eq_of_prefix_eq`. -/

-- Address anchor (fails the build if the guest link moves).
#guard GuestAddrs.blsg2_eq_n = 0x80033d74

/-- Byte-tie: the emitted `blsg2_eq_n` IS the `mv;mv;mv` init followed by
    the dynamic-length byte dual-read scan at the emitted registers. -/
theorem blsg2EqN_prog_eq_scan :
    [Instr.MV .x6 .x10, .MV .x7 .x11, .MV .x5 .x12]
      ++ DualReadByteScan.byteScanProg .x5 .x28 .x29 .x6 .x7
      = blsg2EqN_prog := rfl

#guard [Instr.MV .x6 .x10, .MV .x7 .x11, .MV .x5 .x12]
  ++ DualReadByteScan.byteScanProg .x5 .x28 .x29 .x6 .x7 = blsg2EqN_prog

/-- **`blsg2_eq_n` at its linked address** (genuine post): `a0 = 1` iff the
    two `n`-byte buffers at `a0`/`a1` are byte-equal (`n` = the entry value
    of `a2`), else `a0 = 0`; both inputs untouched. -/
theorem blsg2EqN_spec (ptr1 ptr2 ret : Word) (bs1 bs2 : List (BitVec 8))
    (n : Nat)
    (hlen1 : bs1.length = n) (hlen2 : bs2.length = n)
    (halign1 : ptr1.toNat % 8 = 0) (halign2 : ptr2.toNat % 8 = 0)
    (hov1 : ptr1.toNat + n < 2 ^ 64) (hov2 : ptr2.toNat + n < 2 ^ 64)
    (hvalid1 : ∀ k, k < n → isValidByteAccess (ptr1 + BitVec.ofNat 64 k) = true)
    (hvalid2 : ∀ k, k < n → isValidByteAccess (ptr2 + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (n * 8 + 7) (GuestAddrs.blsg2_eq_n : Word) ret
      (CodeReq.ofProg (GuestAddrs.blsg2_eq_n : Word) blsg2EqN_prog)
      (((.x10 : Reg) ↦ᵣ ptr1) ** ((.x11 : Reg) ↦ᵣ ptr2) **
       ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
       bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
      (((.x10 : Reg) ↦ᵣ (if bs1 = bs2 then (1 : Word) else (0 : Word))) **
       ((.x11 : Reg) ↦ᵣ ptr2) ** ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
       bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2) := by
  set CR := CodeReq.ofProg (GuestAddrs.blsg2_eq_n : Word) blsg2EqN_prog with hCR
  -- peel the MV destinations x6, x7, x5
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := ((.x10 : Reg) ↦ᵣ ptr1) ** ((.x11 : Reg) ↦ᵣ ptr2) **
        ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
      (fun v6 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
      (P := ((.x10 : Reg) ↦ᵣ ptr1) ** ((.x11 : Reg) ↦ᵣ ptr2) **
        ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** ((.x6 : Reg) ↦ᵣ v6) ** regOwn .x28 ** regOwn .x29 **
        bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
      (fun v7 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := ((.x10 : Reg) ↦ᵣ ptr1) ** ((.x11 : Reg) ↦ᵣ ptr2) **
        ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        regOwn .x28 ** regOwn .x29 **
        bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
      (fun v5 => ?_))
  -- ---- init: mv x6, a0 ; mv x7, a1 ; mv x5, a2 ----
  have hmv6 := liftCode (cr' := CR)
    (mv_spec_gen_within .x6 .x10 ptr1 v6 (GuestAddrs.blsg2_eq_n : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (GuestAddrs.blsg2_eq_n : Word) + 4 = ((GuestAddrs.blsg2_eq_n + 4) : Word) from by decide] at hmv6
  have hmv7 := liftCode (cr' := CR)
    (mv_spec_gen_within .x7 .x11 ptr2 v7 ((GuestAddrs.blsg2_eq_n + 4) : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show ((GuestAddrs.blsg2_eq_n + 4) : Word) + 4 = ((GuestAddrs.blsg2_eq_n + 8) : Word) from by decide] at hmv7
  have hmv5 := liftCode (cr' := CR)
    (mv_spec_gen_within .x5 .x12 (BitVec.ofNat 64 n) v5 ((GuestAddrs.blsg2_eq_n + 8) : Word)
      (by decide))
    (by rw [hCR]; code_mem)
  rw [show ((GuestAddrs.blsg2_eq_n + 8) : Word) + 4 = ((GuestAddrs.blsg2_eq_n + 12) : Word) from by decide] at hmv5
  -- ---- the dynamic-length byte dual-read scan (lifted into CR) ----
  have hscan := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact CodeReq.ofProg_mono_sub (GuestAddrs.blsg2_eq_n : Word) ((GuestAddrs.blsg2_eq_n + 12) : Word)
        blsg2EqN_prog (DualReadByteScan.byteScanProg .x5 .x28 .x29 .x6 .x7) 3
        (by decide) (by decide) (by decide) (by decide))
    (h := DualReadByteScan.scan_spec .x5 .x28 .x29 .x6 .x7
      ((GuestAddrs.blsg2_eq_n + 12) : Word) ret ptr1 ptr2 bs1 bs2 n
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hlen1 hlen2 halign1 halign2 hov1 hov2 hvalid1 hvalid2 halignRet)
  -- ---- frames + chain ----
  have hmv6F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ ptr2) ** ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ v5) ** ((.x7 : Reg) ↦ᵣ v7) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
    (by pcf) hmv6
  have hmv7F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr1) ** ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ ptr1) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
    (by pcf) hmv7
  have hmv5F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr1) ** ((.x11 : Reg) ↦ᵣ ptr2) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ ptr1) ** ((.x7 : Reg) ↦ᵣ ptr2) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
    (by pcf) hmv5
  have hscanF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ ptr2) ** ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n))
    (by pcf) hscan
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hmv6F hmv7F
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc1 hmv5F
  have hc3 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hp1 : (((.x10 : Reg) ↦ᵣ ptr1) **
          (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x6 : Reg) ↦ᵣ ptr1) **
           ((.x7 : Reg) ↦ᵣ ptr2) ** ((.x1 : Reg) ↦ᵣ ret) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2 **
           regOwn .x28 ** regOwn .x29 **
           ((.x11 : Reg) ↦ᵣ ptr2) ** ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n))) h := by
        xperm_hyp hp
      have hp2 := sepConj_mono (regIs_to_regOwn .x10 _)
        (fun _ hh => hh) h hp1
      xperm_hyp hp2) hc2 hscanF
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTripleWithin_mono_nSteps (by omega) hc3)

#print axioms blsg2EqN_spec

end Bls12G2EqNSAsm

end EvmAsm.Codegen
