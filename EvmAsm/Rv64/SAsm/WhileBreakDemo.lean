/-
  EvmAsm.Rv64.SAsm.WhileBreakDemo

  End-to-end demo for the early-exit / break loop combinator `Stmt.whileBreak`
  (bead evm-asm-huy8w).

  `scanNzFn` is a *scan-until-predicate* loop: starting from a pointer `a0`
  over a read-only byte region, count the leading zero bytes of `a0[0..a1)`,
  stopping at the first non-zero byte (the mid-loop **break**) or when the
  window is exhausted (the header guard).  Both exits establish the SAME
  functional postcondition — `a0`-cursor and remaining count as functions of
  the input — which is exactly the payoff of the break arm (`breakPost ⇒
  post`).

  This is the control-flow shape the single-exit `«while»` cannot express: a
  header guard `beq x6,x0` PLUS a mid-loop `bne x7,x0` that jumps out *past*
  the back-edge `JAL`.  The `#guard` below pins the flattened code
  byte-for-byte against the hand-written break-past-`JAL` instruction stream.
-/

import EvmAsm.Rv64.SAsm.LoopFuel
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64
namespace SAsm
namespace WhileBreakDemo

open Stmt

-- ============================================================================
-- Ghost spec: number of leading zero bytes (self-contained, no `takeWhile`)
-- ============================================================================

/-- Number of leading zero bytes of the first `len` bytes of `bs`. -/
def nlz : List (BitVec 8) → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | b :: bs, n + 1 => if b = 0 then nlz bs n + 1 else 0

@[simp] theorem nlz_zero (bs : List (BitVec 8)) : nlz bs 0 = 0 := by
  cases bs <;> rfl

theorem nlz_le (bs : List (BitVec 8)) (len : Nat) : nlz bs len ≤ len := by
  induction bs generalizing len with
  | nil => cases len <;> simp [nlz]
  | cons b bs ih =>
      cases len with
      | zero => simp
      | succ n =>
          unfold nlz
          split
          · have := ih n; omega
          · omega

/-- Every index below `nlz` names a zero byte. -/
theorem nlz_spec (bs : List (BitVec 8)) (len i : Nat)
    (hi : i < nlz bs len) : bs.getD i 0 = 0 := by
  induction bs generalizing len i with
  | nil => cases len <;> simp [nlz] at hi
  | cons b bs ih =>
      cases len with
      | zero => simp [nlz] at hi
      | succ n =>
          unfold nlz at hi
          by_cases hb : b = 0
          · simp only [hb, if_true] at hi
            cases i with
            | zero => simpa using hb
            | succ k =>
                rw [List.getD_cons_succ]
                exact ih n k (by omega)
          · simp only [hb, if_false] at hi; omega

/-- If `nlz` stops before `len` (with the window in range), the boundary byte
    is non-zero — that is why the scan stopped. -/
theorem nlz_boundary (bs : List (BitVec 8)) (len : Nat)
    (hlt : nlz bs len < len) (hlen : len ≤ bs.length) : bs.getD (nlz bs len) 0 ≠ 0 := by
  induction bs generalizing len with
  | nil => cases len <;> simp_all [nlz]
  | cons b bs ih =>
      cases len with
      | zero => simp [nlz] at hlt
      | succ n =>
          simp only [nlz] at hlt ⊢
          by_cases hb : b = 0
          · simp only [hb, if_true] at hlt ⊢
            rw [List.getD_cons_succ]
            exact ih n (by omega) (by simpa using hlen)
          · simp only [hb, if_false]; simpa using hb

/-- Continue step: still inside a zero run. -/
theorem nlz_continue (bs : List (BitVec 8)) (len i : Nat)
    (hi : i < len) (hlen : len ≤ bs.length) (hz : bs.getD i 0 = 0)
    (hle : i ≤ nlz bs len) : i + 1 ≤ nlz bs len := by
  rcases Nat.lt_or_ge i (nlz bs len) with h | h
  · omega
  · have hieq : i = nlz bs len := by omega
    have hb := nlz_boundary bs len (by omega) hlen
    rw [← hieq] at hb
    exact absurd hz hb

/-- Break step: the first non-zero byte is exactly at index `nlz`. -/
theorem nlz_break (bs : List (BitVec 8)) (len i : Nat)
    (hle : i ≤ nlz bs len) (hnz : bs.getD i 0 ≠ 0) : i = nlz bs len := by
  rcases Nat.lt_or_ge i (nlz bs len) with h | h
  · exact absurd (nlz_spec bs len i h) hnz
  · omega

-- ============================================================================
-- The function
-- ============================================================================

/-- Loop invariant at header evaluation `i`: `i` leading zeros consumed. -/
def scanInv (ptr : Word) (bs : List (BitVec 8)) (len : Nat) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ _ =>
    rf.get .x5 = ptr + BitVec.ofNat 64 i
    ∧ rf.get .x6 = BitVec.ofNat 64 (len - i)
    ∧ i ≤ nlz bs len
    ∧ len ≤ bs.length
    ∧ ptr.toNat + len < 2 ^ 64

/-- Unified postcondition: cursor and remaining count as functions of input. -/
def scanPost (ptr : Word) (bs : List (BitVec 8)) (len : Nat) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ =>
    rf.get .x5 = ptr + BitVec.ofNat 64 (nlz bs len)
    ∧ rf.get .x6 = BitVec.ofNat 64 (len - nlz bs len)

/-- Scan `a0[0..a1)` for the first non-zero byte, counting leading zeros.
    `x5` = cursor, `x6` = remaining; the loop breaks out at the first non-zero
    byte (`bne x7,x0`) and exits at the top when the window empties
    (`beq x6,x0`). -/
def scanNzFn (ptr : Word) (bs : List (BitVec 8)) (len : Nat) : Fn where
  name := "scanNz"
  region := ⟨ptr, bs⟩
  pre := fun rf _ _ =>
    rf.get .x10 = ptr ∧ rf.get .x11 = BitVec.ofNat 64 len
    ∧ len ≤ bs.length ∧ ptr.toNat + len < 2 ^ 64
  post := scanPost ptr bs len
  body :=
    .block "init" [.MV .x5 .x10, .MV .x6 .x11] ;;;
    .«whileBreak» "scan" (.bne .x6 .x0) len (scanInv ptr bs len) (scanPost ptr bs len)
      (.block "load" [.LBU .x7 .x5 0]) (.bne .x7 .x0)
      (.block "next" [.ADDI .x5 .x5 1, .ADDI .x6 .x6 (-1 : BitVec 12)])

-- The flattened code, byte-for-byte, is the hand-written break-past-`JAL`
-- pattern: init, header guard, load, break branch (jumps PAST the back-edge),
-- decrements, back-edge.
def scanNz_verified : Program := (scanNzFn 0 [] 0).body.flatten 0

-- **Byte-identity pin**: the structured body flattens to exactly the
-- hand-written scan-until-non-zero instruction stream, with the break branch
-- at `+16` (past the `JAL -20` back-edge).
#guard (scanNzFn 0 [] 0).body.flatten 0 =
  [ .MV .x5 .x10,
    .MV .x6 .x11,
    .BEQ .x6 .x0 (24 : BitVec 13),
    .LBU .x7 .x5 (0 : BitVec 12),
    .BNE .x7 .x0 (16 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21) ]

-- Position independence: no PC-relative instruction in the loop body.
#guard (scanNzFn 0 [] 0).body.flatten 0 = (scanNzFn 0 [] 0).body.flatten 0x80000000

theorem scanNzFn_spec (ptr : Word) (bs : List (BitVec 8)) (len : Nat)
    (hwf : (Region.mk ptr bs).wf) (base : Word) :
    (scanNzFn ptr bs len).Spec base := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hsem1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case scanNz.scan.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, ⟨hx10, hx11, hlen, hptr⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_, Nat.zero_le _, hlen, hptr⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide), hx10]
      simp
    · rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
      simp
  case scanNz.scan.inv_step =>
    rintro i hi rf' ws' A' hsp
    -- unfold the after-block sp, then the before-block sp (named, not `rfl`)
    obtain ⟨rfa, wsa, hwsa, ⟨hspbb, hnbreak⟩, hrf', -⟩ := hsp
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrfa, -⟩ := hspbb
    obtain ⟨hx5, hx6, hle, hlen, hptr⟩ := hinv
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hilt : i < len := by
      rcases Nat.lt_or_ge i len with h | h
      · exact h
      · exfalso; apply hg
        show rfb.get .x6 = rfb.get .x0
        rw [hx6, show len - i = 0 from by omega]; rfl
    have hbyte : (scanNzFn ptr bs len).region.byteAt (rfb.get .x5 + signExtend12 0)
        = bs.getD i 0 := by
      unfold Region.byteAt
      rw [show (scanNzFn ptr bs len).region.bytes = bs from rfl,
          show (scanNzFn ptr bs len).region.base = ptr from rfl, hx5, hse0]
      congr 1
      have hti : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    -- load block: `x7 := byte`, `x5`/`x6` unchanged
    have hrfa5 : rfa.get .x5 = rfb.get .x5 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7)]
    have hrfa6 : rfa.get .x6 = rfb.get .x6 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7)]
    have hrfa7 : rfa.get .x7 = BitVec.zeroExtend 64 (bs.getD i 0) := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0)]
      rw [hbyte]
    -- ¬ breakCond ⇒ byte is zero
    have hz : bs.getD i 0 = 0 := by
      have hne : rfa.get .x7 = rfa.get .x0 := by
        by_contra h; exact hnbreak h
      rw [hrfa7, show rfa.get .x0 = 0 from rfl] at hne
      bv_omega
    refine ⟨?_, ?_, nlz_continue bs len i hilt hlen hz hle, hlen, hptr⟩
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x5 : Reg) ≠ .x0)]
      rw [hrfa5, hx5, hse1]
      have h1 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5)]
      rw [hrfa6, hx6, hsem1]
      have h1 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (len - (i + 1))).toNat = len - (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
  case scanNz.scan.exhausted =>
    rintro rf ws A ⟨-, hx6, -, -, -⟩
    intro hc
    apply hc
    rw [hx6, show len - len = 0 from by omega]; rfl
  case scanNz.scan.guard_exit =>
    rintro i hile rf ws A ⟨hx5, hx6, hle, hlen, hptr⟩ hng
    -- ¬guard: x6 = 0 ⇒ i = len ⇒ nlz = len
    have hil : i = len := by
      by_contra hne
      apply hng
      show rf.get .x6 ≠ rf.get .x0
      rw [hx6, show rf.get .x0 = 0 from rfl]
      intro h
      have := congrArg (fun w : Word => w.toNat) h
      simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this
      omega
    have hnlz : nlz bs len = len := by
      have := nlz_le bs len; omega
    refine ⟨?_, ?_⟩
    · rw [hx5, hnlz, hil]
    · rw [hx6, hnlz, hil]
  case scanNz.scan.break =>
    rintro i hi rf' ws' A' hsp hbreak
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrf', -⟩ := hsp
    obtain ⟨hx5, hx6, hle, hlen, hptr⟩ := hinv
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hbyte : (scanNzFn ptr bs len).region.byteAt (rfb.get .x5 + signExtend12 0)
        = bs.getD i 0 := by
      unfold Region.byteAt
      rw [show (scanNzFn ptr bs len).region.bytes = bs from rfl,
          show (scanNzFn ptr bs len).region.base = ptr from rfl, hx5, hse0]
      congr 1
      have hti : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    have hrf7 : rf'.get .x7 = BitVec.zeroExtend 64 (bs.getD i 0) := by
      rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0)]
      rw [hbyte]
    have hrf5 : rf'.get .x5 = rfb.get .x5 := by
      rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7)]
    have hrf6 : rf'.get .x6 = rfb.get .x6 := by
      rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7)]
    -- breakCond ⇒ byte ≠ 0
    have hnz : bs.getD i 0 ≠ 0 := by
      have hne : rf'.get .x7 ≠ rf'.get .x0 := hbreak
      rw [hrf7, show rf'.get .x0 = 0 from rfl] at hne
      intro hz
      exact hne (by rw [hz]; rfl)
    have hieq : i = nlz bs len := nlz_break bs len i hle hnz
    refine ⟨?_, ?_⟩
    · rw [hrf5, hx5, hieq]
    · rw [hrf6, hx6, hieq]
  case scanNz.scan.before.load.mem =>
    rintro rf ws A hws ⟨i, hi, ⟨hx5, hx6, hle, hlen, hptr⟩, hg⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hilt : i < len := by
      rcases Nat.lt_or_ge i len with h | h
      · exact h
      · exfalso; apply hg
        rw [hx6, show len - i = 0 from by omega]; rfl
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial⟩
    show ((rf.get .x5 + signExtend12 (0 : BitVec 12)) - ptr).toNat + 1 ≤ bs.length
    rw [hse0, hx5]
    have : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    have haddr : ((ptr + BitVec.ofNat 64 i + 0) - ptr).toNat = i := by bv_omega
    rw [haddr]; omega
  case scanNz.post =>
    rintro rf ws A h
    exact h

#print axioms scanNzFn_spec

end WhileBreakDemo
end SAsm
end EvmAsm.Rv64
