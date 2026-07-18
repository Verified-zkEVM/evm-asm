/-
  EvmAsm.Codegen.Programs.Bn254CurveIsInfSAsm

  Verified SAsm drop-in for `bnc_is_inf64`: return `a0 = 1` iff the
  64-byte BN254 affine point encoding at `a0` is all-zero (point at infinity).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.WhileBreakDemo

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.Stmt
open EvmAsm.Rv64.SAsm.WhileBreakDemo

namespace Bn254CurveIsInfSAsm

/-! ## bnc_is_inf64 — verified drop-in (two-exit scan via single-exit whileBreak)

    The emitted `bncIsInf64_prog` is a two-exit byte scan (top `BEQ x5,x0`
    completion guard + mid `BNE x7,x0` break-on-nonzero), where the two exits
    jump to *different* result blocks (`LI x10,1` / `LI x10,0`). Plain
    `Stmt.whileBreak` flattens both its guard-fail and its break to a single
    `Lend`, so it cannot byte-match a two-distinct-target routine.

    Per the drop-in policy, we model it as a **single-exit `whileBreak`** whose
    body scans 64 bytes (break on first nonzero), followed by a post-loop block
    that derives the result from the **counter** `x5` (`x5 = 0` ⟺ all 64 bytes
    scanned without breaking ⟺ all-zero). The re-emitted `_prog` is this
    verified body's flatten (same 12-instruction length as the original, so no
    downstream offset shift). The EEST A/B run is the drop-in gate that
    replaces byte-identity (guest bytes move, but semantics are preserved). -/


/-- Loop invariant at header evaluation `i`: counter `x5 = 64-i`, cursor
    `x6 = ptr+i`, the first `i` bytes are all zero (`i ≤ nlz bs 64`). -/
def bncIsInfScanInv (ptr : Word) (bs : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ _ =>
    rf.get .x5 = BitVec.ofNat 64 (64 - i) ∧
    rf.get .x6 = ptr + BitVec.ofNat 64 i ∧
    i ≤ nlz bs 64 ∧ 64 ≤ bs.length ∧ ptr.toNat + 64 < 2 ^ 64

/-- `whileBreak` post (at the single `Lend`): the scan stopped at index `nlz`;
    `x5 = 64 - nlz` (so `x5 = 0` ⟺ `nlz = 64` ⟺ all bytes zero). -/
def bncIsInfScanPost (ptr : Word) (bs : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ =>
    rf.get .x5 = BitVec.ofNat 64 (64 - nlz bs 64) ∧
    rf.get .x6 = ptr + BitVec.ofNat 64 (nlz bs 64) ∧
    64 ≤ bs.length ∧ ptr.toNat + 64 < 2 ^ 64

/-- `bnc_is_inf64` body: init counter/cursor, scan-and-break, then derive the
    result from the counter (`LI x10,1`; clear to 0 if `x5≠0`). -/
def bncIsInf64Body (ptr : Word) (bs : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (64 : Word), .MV .x6 .x10] ;;;
  .«whileBreak» "scan" (.bne .x5 .x0) 64
    (bncIsInfScanInv ptr bs) (bncIsInfScanPost ptr bs)
    (.block "load" [.LBU .x7 .x6 (0 : BitVec 12)]) (.bne .x7 .x0)
    (.block "next" [.ADDI .x6 .x6 (1 : BitVec 12), .ADDI .x5 .x5 (-1 : BitVec 12)]) ;;;
  .block "res1" [.LI .x10 (1 : Word)] ;;;
  .when "clr" (.bne .x5 .x0) (.block "clr0" [.LI .x10 (0 : Word)])

/-- `mset_memcpy`-style verified `Fn`: `x10 := if (the 64 bytes at `a0` are all
    zero) then 1 else 0`. Single read-only region ⟨ptr, bs⟩; no writes. -/
def bncIsInf64Fn (ptr : Word) (bs : List (BitVec 8)) : Fn where
  name := "bncIsInf64"
  region := ⟨ptr, bs⟩
  pre := fun rf _ _ => rf.get .x10 = ptr ∧ bs.length = 64 ∧ ptr.toNat + 64 < 2 ^ 64
  post := fun rf _ _ =>
    (rf.get .x10 = if nlz bs 64 = 64 then (1 : Word) else (0 : Word)) ∧
    64 ≤ bs.length ∧ ptr.toNat + 64 < 2 ^ 64
  body := bncIsInf64Body ptr bs

/-- Return a0 = 1 iff the 64-byte buffer at a0 is all-zero. Leaf helper.

    Re-emitted drop-in: the verified `bncIsInf64Body` flatten + `ret` (12
    instrs, same length as the pre-drop-in hand-written routine). -/
def bncIsInf64_prog : Program :=
  (bncIsInf64Body 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]

def bncIsInf64Function : String :=
  "bnc_is_inf64:\n" ++ emitProgram bncIsInf64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bncIsInf64_prog` (the re-emitted drop-in) rendered under its label. -/
theorem bncIsInf64Function_eq_prog :
    bncIsInf64Function = "bnc_is_inf64:\n" ++ emitProgram bncIsInf64_prog := rfl

#guard bncIsInf64Function.startsWith "bnc_is_inf64:\n"
#guard bncIsInf64_prog.length = 12
-- The drop-in is position-independent (no PC-relative instruction).
#guard (bncIsInf64Body 0 []).flatten 0 = (bncIsInf64Body 0 []).flatten 0x80000000

theorem bncIsInf64Fn_spec (ptr : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk ptr bs).wf) (base : Word) :
    (bncIsInf64Fn ptr bs).Spec base := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hsem1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case bncIsInf64.scan.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, ⟨hx10, hlen, hpl⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_, Nat.zero_le _, (by omega : 64 ≤ bs.length), hpl⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]
      decide
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
      simp
  case bncIsInf64.scan.inv_step =>
    rintro i hi rf' ws' A' hsp
    obtain ⟨rfa, wsa, hwsa, ⟨hspbb, hnbreak⟩, hrf', -⟩ := hsp
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrfa, -⟩ := hspbb
    obtain ⟨hx5, hx6, hle, hlen, hpl⟩ := hinv
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hilt : i < 64 := by
      rcases Nat.lt_or_ge i 64 with h | h
      · exact h
      · exfalso; apply hg
        show rfb.get .x5 = rfb.get .x0
        rw [hx5, show 64 - i = 0 from by omega]; rfl
    have hbyte : (bncIsInf64Fn ptr bs).region.byteAt (rfb.get .x6 + signExtend12 0)
        = bs.getD i 0 := by
      unfold Region.byteAt
      rw [show (bncIsInf64Fn ptr bs).region.bytes = bs from rfl,
          show (bncIsInf64Fn ptr bs).region.base = ptr from rfl, hx6, hse0]
      congr 1
      have hti : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    have hrfa6 : rfa.get .x6 = rfb.get .x6 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7)]
    have hrfa5 : rfa.get .x5 = rfb.get .x5 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7)]
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
    refine ⟨?_, ?_, nlz_continue bs 64 i hilt hlen hz hle, hlen, hpl⟩
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x5 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6)]
      rw [hrfa5, hx5, hsem1]
      have h1 : (BitVec.ofNat 64 (64 - i)).toNat = 64 - i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (64 - (i + 1))).toNat = 64 - (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x0)]
      rw [hrfa6, hx6, hse1]
      have h1 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
  case bncIsInf64.scan.exhausted =>
    rintro rf ws A ⟨hx5, -, -, -, -⟩
    intro hc
    apply hc
    rw [hx5, show 64 - 64 = 0 from by omega]; rfl
  case bncIsInf64.scan.guard_exit =>
    rintro i hile rf ws A ⟨hx5, hx6, hle, hlen, hpl⟩ hng
    have hil : i = 64 := by
      by_contra hne
      apply hng
      show rf.get .x5 ≠ rf.get .x0
      rw [hx5, show rf.get .x0 = 0 from rfl]
      intro h
      have := congrArg (fun w : Word => w.toNat) h
      simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this
      omega
    have hnlz : nlz bs 64 = 64 := by
      have := nlz_le bs 64; omega
    refine ⟨?_, ?_, hlen, hpl⟩
    · rw [hx5, hnlz, hil]
    · rw [hx6, hnlz, hil]
  case bncIsInf64.scan.break =>
    rintro i hi rf' ws' A' hsp hbreak
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrf', -⟩ := hsp
    obtain ⟨hx5, hx6, hle, hlen, hpl⟩ := hinv
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hbyte : (bncIsInf64Fn ptr bs).region.byteAt (rfb.get .x6 + signExtend12 0)
        = bs.getD i 0 := by
      unfold Region.byteAt
      rw [show (bncIsInf64Fn ptr bs).region.bytes = bs from rfl,
          show (bncIsInf64Fn ptr bs).region.base = ptr from rfl, hx6, hse0]
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
    have hnz : bs.getD i 0 ≠ 0 := by
      have hne : rf'.get .x7 ≠ rf'.get .x0 := hbreak
      rw [hrf7, show rf'.get .x0 = 0 from rfl] at hne
      intro hz
      exact hne (by rw [hz]; rfl)
    have hieq : i = nlz bs 64 := nlz_break bs 64 i hle hnz
    refine ⟨?_, ?_, hlen, hpl⟩
    · rw [hrf5, hx5, hieq]
    · rw [hrf6, hx6, hieq]
  case bncIsInf64.scan.before.load.mem =>
    rintro rf ws A hws ⟨i, hi, ⟨hx5, hx6, hle, hlen, hpl⟩, hg⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hilt : i < 64 := by
      rcases Nat.lt_or_ge i 64 with h | h
      · exact h
      · exfalso; apply hg
        rw [hx5, show 64 - i = 0 from by omega]; rfl
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial⟩
    show ((rf.get .x6 + signExtend12 (0 : BitVec 12)) - ptr).toNat + 1 ≤ bs.length
    rw [hse0, hx6]
    have hti : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    have haddr : ((ptr + BitVec.ofNat 64 i + 0) - ptr).toNat = i := by bv_omega
    rw [haddr]; omega
  case bncIsInf64.post =>
    rintro rf ws A hpost
    -- sp(body) = sp(when clr)(sp(res1)(sp(whileBreak)(sp(init)(pre)))).
    -- sp(whileBreak) = scanPost (definitionally); split the `when`.
    rcases hpost with
      ⟨rf₁, ws₁, hws₁, ⟨hres1, hcond⟩, hrf1, rfl⟩ | ⟨hres1, hnc⟩
    · -- x5 ≠ 0 branch (`clr0` ran): x10 = 0; nlz ≠ 64.
      obtain rfl := List.eq_nil_of_length_eq_zero hws₁
      obtain ⟨rfa, wsa, hwsa, hscanPost, hrf1eq, -⟩ := hres1
      obtain rfl := List.eq_nil_of_length_eq_zero hwsa
      obtain ⟨hx5a, -, hle, hpl⟩ := hscanPost
      have hx10rf : rf.get .x10 = (0 : Word) := by
        rw [hrf1]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have hr1x5 : rf₁.get .x5 = rfa.get .x5 := by
        rw [hrf1eq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x10)]
      have hne : nlz bs 64 ≠ 64 := by
        dsimp only [Cond.holds] at hcond
        intro heq
        apply hcond
        rw [hr1x5, hx5a, heq]; rfl
      refine ⟨?_, hle, hpl⟩
      rw [hx10rf]
      by_cases h : nlz bs 64 = 64
      · rw [if_pos h]; exact False.elim (hne h)
      · rw [if_neg h]
    · -- x5 = 0 branch (skip `clr0`): x10 = 1; nlz = 64.
      obtain ⟨rfa, wsa, hwsa, hscanPost, hrfeq, -⟩ := hres1
      obtain rfl := List.eq_nil_of_length_eq_zero hwsa
      obtain ⟨hx5a, -, hle, hpl⟩ := hscanPost
      have hx10rf : rf.get .x10 = (1 : Word) := by
        rw [hrfeq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have hrfx5 : rf.get .x5 = rfa.get .x5 := by
        rw [hrfeq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x10)]
      dsimp only [Cond.holds] at hnc
      have heq : nlz bs 64 = 64 := by
        have hrfeq5 : rf.get .x5 = BitVec.ofNat 64 (64 - nlz bs 64) := by
          rw [hrfx5, hx5a]
        have h0 : rf.get .x5 = (0 : Word) := by
          by_contra hne
          exact hnc hne
        rw [hrfeq5] at h0
        have hT : (BitVec.ofNat 64 (64 - nlz bs 64)).toNat = (64 - nlz bs 64) % 2 ^ 64 :=
          BitVec.toNat_ofNat ..
        have hz : (0 : Word).toNat = 0 := rfl
        have hmod : (64 - nlz bs 64) % 2 ^ 64 = 0 := by
          have := congrArg BitVec.toNat h0
          rw [hT, hz] at this
          exact this
        have hle : nlz bs 64 ≤ 64 := nlz_le bs 64
        omega
      refine ⟨?_, hle, hpl⟩
      rw [hx10rf, if_pos heq]


end Bn254CurveIsInfSAsm

end EvmAsm.Codegen
