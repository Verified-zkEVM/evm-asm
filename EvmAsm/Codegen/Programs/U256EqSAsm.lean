/-
  EvmAsm.Codegen.Programs.U256EqSAsm

  SAsm model for `u256_eq` (bead evm-asm-i6mdy.1): compare two
  32-byte big-endian buffers at `a0`/`a1` and return `a0 = 1` iff they are
  byte-identical.  The source routine has two real `ret` tails, so this module
  is intended for the return-terminating `Stmt.retSound` path rather than the
  legacy single-exit `Fn.Spec` epilogue path.
-/

import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Bn254Field
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace U256EqSAsm

/-- Loop invariant for the `u256_eq` byte scan.  At loop header `x5` is the
    next byte index; all earlier bytes are known equal. -/
def u256EqInv (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 i ∧
    rf.get .x10 = ptr1 ∧
    rf.get .x11 = ptr2 ∧
    rf.get .x31 = (32 : Word) ∧
    (∀ j, j < i → bs1.getD j 0 = bs2.getD j 0) ∧
    bs1.length = 32 ∧ bs2.length = 32 ∧
    ptr1.toNat + 32 < 2 ^ 64 ∧ ptr2.toNat + 32 < 2 ^ 64 ∧
    (ptr1.toNat + 32 ≤ ptr2.toNat ∨ ptr2.toNat + 32 ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2

/-- Focus relation for the second read-only input. -/
def u256EqReadA1 (ptr2 : Word) (bs2 : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rest => rf.get .x11 = ptr2 ∧ rob = bs2 ∧ rest = empAssertion

/-- `u256_eq` as a return-terminating SAsm body, byte-for-byte identical to
    `u256Eq_prog`. -/
def u256EqBody (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (0 : Word), .LI .x31 (32 : Word)] ;;;
  .retWhileBreak "scan" (.bne .x5 .x31) 32 (u256EqInv ptr1 ptr2 bs1 bs2)
    (.block "before1" [.ADD .x6 .x10 .x5, .ADD .x7 .x11 .x5, .LBU .x28 .x6 (0 : BitVec 12)] ;;;
     .readAt "before2" .x11 (u256EqReadA1 ptr2 bs2) [.LBU .x29 .x7 (0 : BitVec 12)])
    (.bne .x28 .x29)
    (.block "after" [.ADDI .x5 .x5 (1 : BitVec 12)])
    (.block "eq" [.LI .x10 (1 : Word)] ;;; .ret "ret_eq")
    (.block "ne" [.LI .x10 (0 : Word)] ;;; .ret "ret_ne")

/-- Entry condition: `a0`/`a1` point at the two read-only 32-byte buffers. -/
def u256EqPre (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Reach :=
  fun rf _ A =>
    rf.get .x10 = ptr1 ∧ rf.get .x11 = ptr2 ∧
    bs1.length = 32 ∧ bs2.length = 32 ∧
    ptr1.toNat + 32 < 2 ^ 64 ∧ ptr2.toNat + 32 < 2 ^ 64 ∧
    (ptr1.toNat + 32 ≤ ptr2.toNat ∨ ptr2.toNat + 32 ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2

/-- Return condition: `a0 = 1` iff all 32 bytes matched. -/
def u256EqPost (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Reach :=
  fun rf _ A =>
    rf.get .x10 = (if firstDiff bs1 bs2 32 = 32 then (1 : Word) else (0 : Word)) ∧
    bs1.length = 32 ∧ bs2.length = 32 ∧
    ptr1.toNat + 32 < 2 ^ 64 ∧ ptr2.toNat + 32 < 2 ^ 64 ∧
    A = bytesRegion ptr2 bs2



private theorem u256Eq_vcs (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8))
    (_hwf1 : (Region.mk ptr1 bs1).wf) (hwf2 : (Region.mk ptr2 bs2).wf) :
    VCs.Hold (Stmt.vcs (Region.mk ptr1 bs1) RwRegion.empty (u256EqBody ptr1 ptr2 bs1 bs2)
      "u256Eq." (u256EqPre ptr1 ptr2 bs1 bs2)) := by
  intro vc hvc
  unfold u256EqBody at hvc
  simp [Stmt.vcs, Stmt.ret, hasLoad, blockOk, loadSem, storeSem] at hvc
  rcases hvc with hinitOk | hinvInit | hinvStep | hexhausted | hbeforeOk | hbeforeMem |
    hreadOk | hfocus | hreadMem | hafterOk | heqOk | hneOk
  · subst vc; decide
  · subst vc
    rintro rf ws A ⟨rf₀, ws₀, hws₀, ⟨hx10, hx11, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩, hrf, hws⟩
    have hws0z : ws₀.length = 0 := by simpa [RwRegion.empty] using hws₀
    obtain rfl := List.eq_nil_of_length_eq_zero hws0z
    subst hrf
    subst hws
    unfold u256EqInv
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x31),
        RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x31),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x31),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
    · rw [RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · intro j hj; omega
  · subst vc
    rintro i hi rf' ws' A' hsp
    obtain ⟨rfa, wsa, hwsa, ⟨hload, hnbreak⟩, hrf', hws'⟩ := hsp
    obtain ⟨rf1, ws1, A1, robytes, rest, hlenRead, hsp1, _hsat, hro, hrfa, _hwsaEq, hAeq⟩ := hload
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, _hg⟩, hrf1, _hws1⟩ := hsp1
    change wsb.length = 0 at hwsb
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hws1len0 : ws1.length = 0 := by simpa [RwRegion.empty] using hlenRead
    obtain rfl := List.eq_nil_of_length_eq_zero hws1len0
    unfold u256EqInv at hinv
    obtain ⟨hx5, hx10, hx11, hx31, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, _hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    have hse0 : signExtend12 0#12 = (0 : Word) := by decide
    have hse1 : signExtend12 1#12 = (1 : Word) := by decide
    have hbyte1 : ({ base := ptr1, bytes := bs1 } : Region).byteAt
        (rfb.get .x10 + rfb.get .x5 + signExtend12 0#12) = bs1.getD i 0 := by
      unfold Region.byteAt
      rw [hx10, hx5, hse0]
      congr 1
      bv_omega
    have hrf1x5 : rf1.get .x5 = rfb.get .x5 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6)]
    have hrf1x10 : rf1.get .x10 = rfb.get .x10 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x28),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6)]
    have hrf1x11 : rf1.get .x11 = rfb.get .x11 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6)]
    have hrf1x31 : rf1.get .x31 = rfb.get .x31 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x31 ≠ .x28),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x31 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x31 ≠ .x6)]
    have hrf1x7 : rf1.get .x7 = ptr2 + BitVec.ofNat 64 i := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6)]
      rw [hx11, hx5]
    have hrf1x28 : rf1.get .x28 = BitVec.zeroExtend 64 (bs1.getD i 0) := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x28 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x0)]
      simpa using congrArg (fun b : BitVec 8 => BitVec.zeroExtend 64 b) hbyte1
    have hbyte2 : ({ base := rf1.get .x11, bytes := robytes } : Region).byteAt
        (rf1.get .x7 + signExtend12 0#12) = bs2.getD i 0 := by
      unfold Region.byteAt
      rw [hrob, hrf1x7, hrf1x11, hx11, hse0]
      congr 1
      bv_omega
    have hrfa5 : rfa.get .x5 = rfb.get .x5 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x29)]
      exact hrf1x5
    have hrfa10 : rfa.get .x10 = rfb.get .x10 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x29)]
      exact hrf1x10
    have hrfa11 : rfa.get .x11 = rfb.get .x11 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x29)]
      exact hrf1x11
    have hrfa31 : rfa.get .x31 = rfb.get .x31 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x31 ≠ .x29)]
      exact hrf1x31
    have hrfa28 : rfa.get .x28 = BitVec.zeroExtend 64 (bs1.getD i 0) := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29)]
      exact hrf1x28
    have hrfa29 : rfa.get .x29 = BitVec.zeroExtend 64 (bs2.getD i 0) := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x29 : Reg) ≠ .x0)]
      simpa using congrArg (fun b : BitVec 8 => BitVec.zeroExtend 64 b) hbyte2
    have heqByte : bs1.getD i 0 = bs2.getD i 0 := by
      have heq : rfa.get .x28 = rfa.get .x29 := by
        by_contra hne
        exact hnbreak hne
      rw [hrfa28, hrfa29] at heq
      bv_omega
    unfold u256EqInv
    refine ⟨?_, ?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, ?_⟩
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x5 : Reg) ≠ .x0)]
      rw [hrfa5, hx5, hse1]
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]
      rw [hrfa10, hx10]
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]
      rw [hrfa11, hx11]
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x31 ≠ .x5)]
      rw [hrfa31, hx31]
    · intro j hj
      by_cases hji : j < i
      · exact hpref j hji
      · have hji' : j = i := by omega
        rw [hji']; exact heqByte
    · rw [hAeq, hptr, hrob, hrest, sepConj_emp_right']
  · subst vc
    rintro rf ws A hinv
    unfold u256EqInv at hinv
    obtain ⟨hx5, _hx10, _hx11, hx31, _hpref, _hlen1, _hlen2, _hpl1, _hpl2, _hdisj, _hA⟩ := hinv
    intro hc
    apply hc
    rw [hx5, hx31]
    rfl
  · subst vc; decide
  · subst vc
    rintro rf ws A hws i hi hinv _hg
    change ws.length = 0 at hws
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    unfold u256EqInv at hinv
    obtain ⟨hx5, hx10, _hx11, _hx31, _hpref, hlen1, _hlen2, _hpl1, _hpl2, _hdisj, _hA⟩ := hinv
    simp only [blockVCs, loadSem, storeSem, execInstrRF_nil, aluSem]
    refine ⟨trivial, ⟨trivial, ?_, trivial⟩⟩
    simp only [inRw, RwRegion.empty, List.length_nil]
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
      RegFile.get_set_self _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x0), hx10, hx5,
      show signExtend12 0#12 = (0 : Word) from by decide]
    unfold Region.loadOk
    simp [hlen1]
    omega
  · subst vc; decide
  · subst vc
    rintro rf ws A hsp _hApc hp hhp
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, _hi, hinv, _hg⟩, hrf, _hws⟩ := hsp
    change ws₀.length = 0 at hws₀
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    unfold u256EqInv at hinv
    obtain ⟨_hx5, _hx10, hx11, _hx31, _hpref, _hlen1, _hlen2, _hpl1, _hpl2, _hdisj, hA⟩ := hinv
    have hx11' : rf.get .x11 = ptr2 := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6)]
      exact hx11
    refine ⟨bs2, empAssertion, ⟨hx11', rfl, rfl⟩, ?_, pcFree_emp, ?_⟩
    · rw [hx11', sepConj_emp_right']
      rw [hA] at hhp
      exact hhp
    · rw [hx11']
      exact hwf2
  · subst vc
    rintro rf ws A robytes rest hws hsp hro _hp _hhp
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv, _hg⟩, hrf, _hwsrf⟩ := hsp
    change ws₀.length = 0 at hws₀
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    change ws.length = 0 at hws
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    unfold u256EqInv at hinv
    obtain ⟨hx5, _hx10, hx11, _hx31, _hpref, _hlen1, hlen2, _hpl1, _hpl2, _hdisj, _hA⟩ := hinv
    obtain ⟨hptr, hrob, _hrest⟩ := hro
    have hx7' : rf.get .x7 = ptr2 + BitVec.ofNat 64 i := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6)]
      rw [hx11, hx5]
    have hx11' : rf.get .x11 = ptr2 := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6)]
      exact hx11
    simp only [blockVCs, loadSem]
    refine ⟨?_, trivial⟩
    simp only [inRw, RwRegion.empty, List.length_nil]
    rw [hx7', hx11', hrob, show signExtend12 0#12 = (0 : Word) from by decide]
    unfold Region.loadOk
    simp [hlen2]
    omega
  · subst vc; decide
  · subst vc; decide
  · subst vc; decide

private theorem u256Eq_sp_post (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) :
    ∀ rf ws A,
      Stmt.sp (Region.mk ptr1 bs1) RwRegion.empty (u256EqBody ptr1 ptr2 bs1 bs2)
        (u256EqPre ptr1 ptr2 bs1 bs2) rf ws A →
        u256EqPost ptr1 ptr2 bs1 bs2 rf ws A := by
  intro rf ws A hsp
  unfold u256EqBody at hsp
  simp only [Stmt.sp, Stmt.ret] at hsp
  rcases hsp with heq | hne
  · obtain ⟨rft, wst, hwst, hreach, hrf, _hws⟩ := heq
    obtain ⟨⟨i, hile, hinv⟩, hng⟩ := hreach
    unfold u256EqInv at hinv
    obtain ⟨hx5, _hx10, _hx11, hx31, hpref, hlen1, hlen2, hpl1, hpl2, _hdisj, hA⟩ := hinv
    have hi32 : i = 32 := by
      by_contra _hne32
      apply hng
      show rft.get .x5 ≠ rft.get .x31
      rw [hx5, hx31]
      intro h
      have hto := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at hto
      have hiLt : i < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hiLt, show (32 : Word).toNat = 32 from rfl] at hto
      omega
    have hfd : firstDiff bs1 bs2 32 = 32 := by
      apply firstDiff_all_eq
      intro j hj
      exact hpref j (by omega)
    unfold u256EqPost
    obtain rfl := List.eq_nil_of_length_eq_zero hwst
    refine ⟨?_, hlen1, hlen2, hpl1, hpl2, hA⟩
    rw [hrf]
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
      RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
    rw [if_pos hfd]
  · obtain ⟨rft, wst, hwst, hreach, hrf, _hws⟩ := hne
    obtain ⟨⟨i, hi, hbb⟩, hbreak⟩ := hreach
    obtain ⟨rf1, ws1, A1, robytes, rest, hlenRead, hsp1, _hsat, hro, hrft, _hwstEq, hAeq⟩ := hbb
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, _hg⟩, hrf1, _hws1⟩ := hsp1
    change wsb.length = 0 at hwsb
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hws1len0 : ws1.length = 0 := by simpa [RwRegion.empty] using hlenRead
    obtain rfl := List.eq_nil_of_length_eq_zero hws1len0
    unfold u256EqInv at hinv
    obtain ⟨hx5, hx10, hx11, _hx31, hpref, hlen1, hlen2, hpl1, hpl2, _hdisj, _hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    have hse0 : signExtend12 0#12 = (0 : Word) := by decide
    have hbyte1 : ({ base := ptr1, bytes := bs1 } : Region).byteAt
        (rfb.get .x10 + rfb.get .x5 + signExtend12 0#12) = bs1.getD i 0 := by
      unfold Region.byteAt
      rw [hx10, hx5, hse0]
      congr 1
      bv_omega
    have hrf1x11 : rf1.get .x11 = rfb.get .x11 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6)]
    have hrf1x7 : rf1.get .x7 = ptr2 + BitVec.ofNat 64 i := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6)]
      rw [hx11, hx5]
    have hrf1x28 : rf1.get .x28 = BitVec.zeroExtend 64 (bs1.getD i 0) := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x28 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x0)]
      simpa using congrArg (fun b : BitVec 8 => BitVec.zeroExtend 64 b) hbyte1
    have hbyte2 : ({ base := rf1.get .x11, bytes := robytes } : Region).byteAt
        (rf1.get .x7 + signExtend12 0#12) = bs2.getD i 0 := by
      unfold Region.byteAt
      rw [hrob, hrf1x7, hrf1x11, hx11, hse0]
      congr 1
      bv_omega
    have hrft28 : rft.get .x28 = BitVec.zeroExtend 64 (bs1.getD i 0) := by
      rw [hrft]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29)]
      exact hrf1x28
    have hrft29 : rft.get .x29 = BitVec.zeroExtend 64 (bs2.getD i 0) := by
      rw [hrft]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x29 : Reg) ≠ .x0)]
      simpa using congrArg (fun b : BitVec 8 => BitVec.zeroExtend 64 b) hbyte2
    have hneByte : bs1.getD i 0 ≠ bs2.getD i 0 := by
      have hne : rft.get .x28 ≠ rft.get .x29 := hbreak
      rw [hrft28, hrft29] at hne
      intro heq
      exact hne (by rw [heq])
    have hfd : firstDiff bs1 bs2 32 = i := firstDiff_ne_of_lt bs1 bs2 i 32 hi hpref hneByte
    unfold u256EqPost
    obtain rfl := List.eq_nil_of_length_eq_zero hwst
    refine ⟨?_, hlen1, hlen2, hpl1, hpl2, ?_⟩
    · rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
      rw [hfd]
      rw [if_neg (by omega)]
    · rw [hAeq, hptr, hrob, hrest, sepConj_emp_right']

/-- Return-terminating semantic spec for the byte-identical `u256_eq` body. -/
theorem u256Eq_spec (ptr1 ptr2 base ret : Word) (bs1 bs2 : List (BitVec 8))
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hwf1 : (Region.mk ptr1 bs1).wf) (hwf2 : (Region.mk ptr2 bs2).wf) :
    cpsTripleWithin (u256EqBody ptr1 ptr2 bs1 bs2).steps base ret
      (CodeReq.ofProg base ((u256EqBody ptr1 ptr2 bs1 bs2).flatten base))
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM (Region.mk ptr1 bs1) RwRegion.empty
        (u256EqPre ptr1 ptr2 bs1 bs2))
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM (Region.mk ptr1 bs1) RwRegion.empty
        (u256EqPost ptr1 ptr2 bs1 bs2)) := by
  have hsound := Stmt.retSound (Region.mk ptr1 bs1) RwRegion.empty
    (u256EqBody ptr1 ptr2 bs1 bs2) base ret "u256Eq."
    (u256EqPre ptr1 ptr2 bs1 bs2)
    hwf1 RwRegion.empty_wf
    (by rfl) (by rfl)
    (by
      change 4 * 14 < 2 ^ 64
      norm_num)
    halign (fun _ _ h => h)
    (u256Eq_vcs ptr1 ptr2 bs1 bs2 hwf1 hwf2)
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (sepConj_mono_right (asrtM_mono (u256Eq_sp_post ptr1 ptr2 bs1 bs2))) hsound

#print axioms u256Eq_spec

-- Byte-identity to the existing emitted `u256_eq` program.
#guard (u256EqBody 0 0 [] []).flatten 0 = u256Eq_prog
#guard (u256EqBody 0 0 [] []).retOffsetsOk
#guard !(u256EqBody 0 0 [] []).offsetsOk

end U256EqSAsm
end EvmAsm.Codegen
