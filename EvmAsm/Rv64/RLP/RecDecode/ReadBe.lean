/-
  EvmAsm.Rv64.RLP.RecDecode.ReadBe

  Leaf routine for the recursive RLP decoder (#12419 fresh-tree track):
  `rlp_read_be(x29 = ptr, x30 = n)` reads the `n ≤ 8` bytes at `ptr`
  (inside the read-only input region) big-endian into `x31`.  This is the
  length-field reader shared by every long-form arm of `rlp_decode`
  (`Uint.from_be_bytes(encoded[1 : 1 + lenLen])` in the reference).

  Call-free, so it packages with `Fn.toHandleS` into a snapshot-
  parameterized `FnHandleS`: the postcondition names the *entry* registers
  (the window it read) and pins every register outside `{x28,x29,x30,x31}`
  to its entry value — no ghost threading through the caller, which is what
  a call site *inside a loop* needs.

  Register discipline: clobbers x28 (byte scratch), x29/x30 (consumed
  cursor/count), writes x31 (result).  Touches neither memory (its `ws` is
  the caller's stack window, untouched) nor any other register.
-/

import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.LoopFuel
import EvmAsm.EL.RLP.Properties

namespace EvmAsm.Rv64
namespace SAsm
namespace RecDecode

open Stmt
open EvmAsm.EL.RLP (Byte)

/-- Byte index of an input pointer inside the region at `inBase`. -/
def idxOf (inBase p : Word) : Nat := (p - inBase).toNat

/-- The value the reader returns: the big-endian number in
    `bs[j : j + n]`. -/
def beVal (bs : List Byte) (j n : Nat) : Nat :=
  EvmAsm.EL.RLP.Nat.fromBytesBE ((bs.drop j).take n)

private theorem se12_zero' : signExtend12 (0 : BitVec 12) = (0 : Word) := by
  decide
private theorem se12_one' : signExtend12 (1 : BitVec 12) = (1 : Word) := by
  decide
private theorem se12_neg1' : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by
  decide

/-- An `LBU` whose address resolves outside the writable window reads the
    read-only region (local copy of the InterpLoopDemo lemma). -/
private theorem execInstrRF_lbu_ro' (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd
          ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

/-- Layout facts every routine in this family carries: well-formed input
    region and stack window, and the two disjoint (input strictly below the
    stack, or strictly above it). -/
structure RdLayout (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) : Prop where
  regWf : (Region.mk inBase bs).wf
  rwWf : (RwRegion.mk rwBase rwLen).wf
  disj : inBase.toNat + bs.length ≤ rwBase.toNat
    ∨ rwBase.toNat + rwLen ≤ inBase.toNat

/-- Any 1-byte access inside the input region misses the writable window. -/
theorem RdLayout.not_inRw {inBase : Word} {bs : List Byte} {rwBase : Word}
    {rwLen : Nat} (L : RdLayout inBase bs rwBase rwLen)
    {ws : List (BitVec 8)} (hws : ws.length = rwLen)
    {k : Nat} (hk : k < bs.length) :
    ¬ inRw rwBase ws (inBase + BitVec.ofNat 64 k) 1 := by
  intro hin
  unfold inRw at hin
  have hb : inBase.toNat + bs.length < 2 ^ 64 := by
    have := L.regWf.2.1
    omega
  have haddr : (inBase + BitVec.ofNat 64 k).toNat = inBase.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hws, BitVec.toNat_sub, haddr] at hin
  have hrwB : rwBase.toNat < 2 ^ 64 := rwBase.isLt
  have hrwL : rwBase.toNat + rwLen < 2 ^ 64 := L.rwWf.2.1
  rcases L.disj with hlo | hhi <;> omega

/-- Reading a region byte at a ghost index. -/
theorem region_byteAt {inBase : Word} {bs : List Byte}
    (hreg : (Region.mk inBase bs).wf) {k : Nat} (hk : k < bs.length) :
    (Region.mk inBase bs).byteAt (inBase + BitVec.ofNat 64 k)
      = bs.getD k 0 := by
  unfold Region.byteAt
  have hb : inBase.toNat + bs.length < 2 ^ 64 := by
    have := hreg.2.1
    omega
  have haddr : (inBase + BitVec.ofNat 64 k).toNat = inBase.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hidx : ((inBase + BitVec.ofNat 64 k) - inBase).toNat = k := by
    rw [BitVec.toNat_sub, haddr]
    omega
  rw [hidx]

/-- A 1-byte load at a ghost index is within the region. -/
theorem region_loadOk1 {inBase : Word} {bs : List Byte}
    (hreg : (Region.mk inBase bs).wf) {k : Nat} (hk : k < bs.length) :
    (Region.mk inBase bs).loadOk (inBase + BitVec.ofNat 64 k) 1 := by
  have hb : inBase.toNat + bs.length < 2 ^ 64 := hreg.2.1
  have haddr : (inBase + BitVec.ofNat 64 k).toNat = inBase.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  constructor
  · exact one_dvd _
  · show ((inBase + BitVec.ofNat 64 k) - inBase).toNat + 1 ≤ bs.length
    rw [BitVec.toNat_sub, haddr]
    omega

/-- The BE-reader as an SAsm function family.  `bs`/`inBase` are the input
    ghost; the writable window is the (untouched) caller stack window. -/
def readBeFn (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) : Fn where
  name := "rdbe"
  region := ⟨inBase, bs⟩
  rw := ⟨rwBase, rwLen⟩
  pre := fun rf _ _ => ∃ j n : Nat,
    rf.get .x29 = inBase + BitVec.ofNat 64 j ∧
    rf.get .x30 = BitVec.ofNat 64 n ∧
    n ≤ 8 ∧ j + n ≤ bs.length
  post := fun _ _ _ => True
  body :=
    .block "init" [.LI .x31 0] ;;;
    .«whileS» "be" (.bne .x30 .x0) 8
      (fun rfL wsL AL i rf ws A =>
        i ≤ (rfL.get .x30).toNat
        ∧ rf.get .x29 = rfL.get .x29 + BitVec.ofNat 64 i
        ∧ rf.get .x30 = rfL.get .x30 - BitVec.ofNat 64 i
        ∧ rf.get .x31 = BitVec.ofNat 64
            (EvmAsm.EL.RLP.Nat.fromBytesBE
              ((bs.drop (idxOf inBase (rfL.get .x29))).take i))
        ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
            rf.get r = rfL.get r)
        ∧ ws = wsL ∧ A = AL)
      (.block "step"
        [.LBU .x28 .x29 0, .SLLI .x31 .x31 8, .ADD .x31 .x31 .x28,
         .ADDI .x29 .x29 1, .ADDI .x30 .x30 (-1)])

/-- Snapshot-parameterized guarantee: the result keyed to the entry
    registers; everything outside the scratch set pinned; window and
    ambient untouched. -/
def readBePost (inBase : Word) (bs : List Byte) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    rf.get .x31 = BitVec.ofNat 64
      (beVal bs (idxOf inBase (rf₀.get .x29)) (rf₀.get .x30).toNat)
    ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
        rf.get r = rf₀.get r)
    ∧ ws = ws₀ ∧ A = A₀

-- ============================================================================
-- Pure BE-fold facts
-- ============================================================================

private theorem beVal_zero (bs : List Byte) (j : Nat) : beVal bs j 0 = 0 := by
  simp [beVal, EvmAsm.EL.RLP.Nat.fromBytesBE]

private theorem beVal_lt (bs : List Byte) (j n : Nat) (hn : n ≤ 8) :
    beVal bs j n < 2 ^ 64 := by
  have h := EvmAsm.EL.RLP.Nat.fromBytesBE_lt ((bs.drop j).take n)
  have hlen : ((bs.drop j).take n).length ≤ n := by
    rw [List.length_take]
    omega
  calc beVal bs j n < 256 ^ ((bs.drop j).take n).length := h
    _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)

private theorem beVal_snoc (bs : List Byte) (j i : Nat)
    (hji : j + i < bs.length) :
    beVal bs j (i + 1) = beVal bs j i * 256 + (bs.getD (j + i) 0).toNat := by
  unfold beVal
  have hi : i < (bs.drop j).length := by
    rw [List.length_drop]
    omega
  have htake : (bs.drop j).take (i + 1)
      = (bs.drop j).take i ++ [(bs.drop j).getD i 0] := by
    rw [List.take_add_one]
    congr 1
    rw [List.getElem?_eq_getElem hi]
    simp [List.getD, List.getElem?_eq_getElem hi]
  rw [htake, EvmAsm.EL.RLP.Nat.fromBytesBE_snoc]
  congr 2
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_drop]

/-- The machine fold step: shift-add with the next byte is the BE snoc. -/
private theorem be_step_word (a : Nat) (b : Byte)
    (_h : a * 256 + b.toNat < 2 ^ 64) :
    BitVec.ofNat 64 a <<< (8 : Nat) + (b.zeroExtend 64)
      = BitVec.ofNat 64 (a * 256 + b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have hb : b.toNat < 256 := b.isLt
  have ha : a % 2 ^ 64 * 2 ^ 8 % 2 ^ 64 = a * 256 % 2 ^ 64 := by
    conv_rhs => rw [show (256 : Nat) = 2 ^ 8 from rfl]
    rw [Nat.mul_mod, Nat.mod_mod_of_dvd _ (by norm_num), ← Nat.mul_mod]
  omega

-- ============================================================================
-- The snapshot spec
-- ============================================================================

theorem readBeFn_specS (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat)
    (L : RdLayout inBase bs rwBase rwLen) (base : Word) :
    (readBeFn inBase bs rwBase rwLen).SpecS base (readBePost inBase bs) := by
  intro rf₀ ws₀ A₀ hpre
  obtain ⟨j, n, hx29, hx30, hn8, hjn⟩ := hpre
  have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hidx0 : idxOf inBase (rf₀.get .x29) = j := by
    unfold idxOf
    rw [hx29]
    have haddr : (inBase + BitVec.ofNat 64 j).toNat = inBase.toNat + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [BitVec.toNat_sub, haddr]
    omega
  have hn0 : (rf₀.get .x30).toNat = n := by
    rw [hx30, BitVec.toNat_ofNat]
    omega
  vcgen
  case region => exact ⟨L.regWf, L.rwWf⟩
  case rdbe.be.inv_init =>
    rintro rf ws A ⟨rfE, wsE, hlen, ⟨h1, h2, h3⟩, hrf, hws⟩
    subst hrf hws
    refine ⟨Nat.zero_le _, ?_, ?_, ?_, fun r _ _ _ _ => rfl, rfl, rfl⟩
    · simp
    · simp
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      simp [EvmAsm.EL.RLP.Nat.fromBytesBE]
  case rdbe.be.body.step.mem =>
    rintro rf ws A hws ⟨rfL, wsL, AL, ⟨rfE, wsE, hlenE, ⟨h1, h2, h3⟩, hrfL,
      hwsL⟩, i, hi8, ⟨hile, h29, h30, h31, hpins, hwseq, hAeq⟩, hcond⟩
    have hL29 : rfL.get .x29 = inBase + BitVec.ofNat 64 j := by
      rw [hrfL, h1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx29
    have hL30 : rfL.get .x30 = BitVec.ofNat 64 n := by
      rw [hrfL, h1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx30
    have hnL : (rfL.get .x30).toNat = n := by
      rw [hL30, BitVec.toNat_ofNat]
      omega
    have hin : i < n := by
      rcases Nat.lt_or_ge i n with hlt | hge
      · exact hlt
      · exfalso
        apply hcond
        show rf.get .x30 = rf.get .x0
        have hieq : i = n := by omega
        rw [h30, hL30, hieq]
        simp
    have hji : j + i < bs.length := by omega
    have haddr29 : rf.get .x29 + signExtend12 (0 : BitVec 12)
        = inBase + BitVec.ofNat 64 (j + i) := by
      rw [se12_zero', h29, hL29]
      bv_omega
    have hnorw : ¬ inRw rwBase ws
        (rf.get .x29 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [haddr29]
      exact L.not_inRw hws hji
    simp only [readBeFn, blockVCs, loadSem, storeSem]
    refine ⟨?_, trivial, trivial, trivial, trivial, trivial⟩
    rw [if_neg hnorw, haddr29]
    exact region_loadOk1 L.regWf hji
  case rdbe.be.inv_step =>
    rintro rfL wsL AL ⟨rfE, wsE, hlenE, ⟨h1, h2, h3⟩, hrfL, hwsL⟩ i hi8
      rf' ws' A' hsp
    have hL29 : rfL.get .x29 = inBase + BitVec.ofNat 64 j := by
      rw [hrfL, h1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx29
    have hL30 : rfL.get .x30 = BitVec.ofNat 64 n := by
      rw [hrfL, h1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx30
    have hidxL : idxOf inBase (rfL.get .x29) = j := by
      unfold idxOf
      rw [hL29]
      have haddr : (inBase + BitVec.ofNat 64 j).toNat = inBase.toNat + j := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rw [BitVec.toNat_sub, haddr]
      omega
    obtain ⟨rfB, wsB, hlenB, ⟨⟨hile, h29, h30, h31, hpins, hwseq, hAeq⟩,
      hcond⟩, hrf', hws'⟩ := hsp
    rw [hidxL] at h31
    have hnL : (rfL.get .x30).toNat = n := by
      rw [hL30, BitVec.toNat_ofNat]
      omega
    have hin : i < n := by
      rcases Nat.lt_or_ge i n with h | hge
      · exact h
      · exfalso
        apply hcond
        show rfB.get .x30 = rfB.get .x0
        have hieq : i = n := by omega
        rw [h30, hL30, hieq]
        simp
    have hji : j + i < bs.length := by omega
    have haddr29 : rfB.get .x29 + signExtend12 (0 : BitVec 12)
        = inBase + BitVec.ofNat 64 (j + i) := by
      rw [se12_zero', h29, hL29]
      bv_omega
    have hnorw : ¬ inRw rwBase wsB
        (rfB.get .x29 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [haddr29]
      exact L.not_inRw hlenB hji
    have hbyte : (Region.mk inBase bs).byteAt
        (rfB.get .x29 + signExtend12 (0 : BitVec 12)) = bs.getD (j + i) 0 := by
      rw [haddr29]
      exact region_byteAt L.regWf hji
    have hws'' : ws' = wsB := hws'
    subst hrf'
    refine ⟨by omega, ?_, ?_, ?_, ?_, by rw [hws'', hwseq], hAeq⟩
    · -- x29 advances
      simp only [readBeFn, execBlock_cons, execBlock_nil]
      rw [execInstrRF_lbu_ro' _ _ _ _ _ _ _ hnorw]
      simp only [execInstrRF, aluSem]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true, se12_one']
      rw [h29]
      bv_omega
    · -- x30 decrements
      simp only [readBeFn, execBlock_cons, execBlock_nil]
      rw [execInstrRF_lbu_ro' _ _ _ _ _ _ _ hnorw]
      simp only [execInstrRF, aluSem]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true, se12_neg1']
      rw [h30]
      bv_omega
    · -- x31 folds the next byte
      simp only [readBeFn, execBlock_cons, execBlock_nil]
      rw [execInstrRF_lbu_ro' _ _ _ _ _ _ _ hnorw]
      simp only [execInstrRF, aluSem]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
      rw [h31, hbyte, hidxL]
      show BitVec.ofNat 64 (beVal bs j i) <<< ((8 : BitVec 6)).toNat
          + (bs.getD (j + i) 0).zeroExtend 64
        = BitVec.ofNat 64 (beVal bs j (i + 1))
      rw [show ((8 : BitVec 6)).toNat = (8 : Nat) from rfl]
      have hbound : beVal bs j i * 256 + (bs.getD (j + i) 0).toNat
          < 2 ^ 64 := by
        have hs := beVal_snoc bs j i hji
        have hl := beVal_lt bs j (i + 1) (by omega)
        omega
      rw [beVal_snoc bs j i hji, be_step_word _ _ hbound]
    · -- pins survive the step
      intro r h28 h29' h30' h31'
      simp only [readBeFn, execBlock_cons, execBlock_nil]
      rw [execInstrRF_lbu_ro' _ _ _ _ _ _ _ hnorw]
      simp only [execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ h30', RegFile.get_set_ne _ _ _ _ h29',
        RegFile.get_set_ne _ _ _ _ h31', RegFile.get_set_ne _ _ _ _ h31',
        RegFile.get_set_ne _ _ _ _ h28]
      exact hpins r h28 h29' h30' h31'
  case rdbe.be.exhausted =>
    rintro rfL wsL AL ⟨rfE, wsE, hlenE, ⟨h1, h2, h3⟩, hrfL, hwsL⟩
      rf ws A ⟨hile, h29, h30, h31, hpins, hwseq, hAeq⟩ hcond
    have hL30 : rfL.get .x30 = BitVec.ofNat 64 n := by
      rw [hrfL, h1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx30
    have hnL : (rfL.get .x30).toNat = n := by
      rw [hL30, BitVec.toNat_ofNat]
      omega
    have hn8' : n = 8 := by omega
    apply hcond
    show rf.get .x30 = rf.get .x0
    rw [h30, hL30, hn8']
    simp
  case rdbe.post =>
    rintro rf ws A ⟨rfL, wsL, AL, ⟨rfE, wsE, hlenE, ⟨h1, h2, h3⟩, hrfL, hwsL⟩,
      ⟨i, hi8, hile, h29, h30, h31, hpins, hwseq, hAeq⟩, hncond⟩
    have hL29 : rfL.get .x29 = inBase + BitVec.ofNat 64 j := by
      rw [hrfL, h1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx29
    have hL30 : rfL.get .x30 = BitVec.ofNat 64 n := by
      rw [hrfL, h1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx30
    have hidxL : idxOf inBase (rfL.get .x29) = j := by
      unfold idxOf
      rw [hL29]
      have haddr : (inBase + BitVec.ofNat 64 j).toNat = inBase.toNat + j := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rw [BitVec.toNat_sub, haddr]
      omega
    have hnL : (rfL.get .x30).toNat = n := by
      rw [hL30, BitVec.toNat_ofNat]
      omega
    have hieq : i = n := by
      rcases Nat.lt_or_ge i n with h | hge
      · exfalso
        apply hncond
        show rf.get .x30 ≠ rf.get .x0
        rw [h30, hL30]
        simp only [RegFile.get_x0]
        intro hzero
        have hz : ((BitVec.ofNat 64 n) - BitVec.ofNat 64 i).toNat = 0 := by
          rw [hzero]
          rfl
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hz
        omega
      · omega
    refine ⟨?_, ?_, by rw [hwseq, hwsL, h2]; rfl, by
      have hA'' : A = AL := hAeq
      rw [hA'', h3]⟩
    · rw [h31, hidxL, hieq, hidx0, hn0]
      rfl
    · intro r h28 h29' h30' h31'
      rw [hpins r h28 h29' h30' h31', hrfL, h1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ h31']

/-- The reader packaged as a snapshot handle at entry `base`. -/
def readBeHandleS (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat)
    (L : RdLayout inBase bs rwBase rwLen) (base : Word)
    (hsz : 4 * ((readBeFn inBase bs rwBase rwLen).body.size + 1) ≤ 2 ^ 64) :
    FnHandleS :=
  (readBeFn inBase bs rwBase rwLen).toHandleS base (readBePost inBase bs)
    (readBeFn_specS inBase bs rwBase rwLen L base) hsz

end RecDecode
end SAsm
end EvmAsm.Rv64
