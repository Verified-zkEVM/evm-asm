/-
  EvmAsm.Rv64.RLP.RecDecode.ItemsStep

  The sibling loop's induction step: one iteration of `itemsBodyStmt`
  carries `decInv i` to `decInv (i + 1)`.  Factored through the mid-body
  state `CascadeOut` (the join after the `decode_item_length` cascade):

    sp(cascade)(inv i ∧ guard)  ⟹  CascadeOut
    sp(calltail)(CascadeOut)    ⟹  inv (i + 1)

  `CascadeOut` is the machine form of `decode_item_length`'s contract: on
  the OK side the length register holds `some L` of the reference function
  with `L` bounded; on the POISON side the whole payload is already known
  rejected and the cursor was forced to the end.
-/

import EvmAsm.Rv64.RLP.RecDecode.Widen
import EvmAsm.Rv64.BitAux

namespace EvmAsm.Rv64
namespace SAsm
namespace RecDecode

open Stmt
open EvmAsm.EL.RLP (Byte)
open EvmAsm.EL.RLP.Ref (decodeD decodeJoinedEncodingsD decodeItemLength win
  winBE)

/-- The mid-iteration join state, after the item-length cascade. -/
def CascadeOut (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) (i : Nat) : Reach :=
  fun rf ws A =>
    ∃ c : Nat,
      pStart ≤ c ∧ c < pEnd ∧ pStart + i ≤ c
      ∧ rf.get .x16 = inBase + BitVec.ofNat 64 pEnd
      ∧ rf.get .x12 = BitVec.ofNat 64 d
      ∧ rf.get .x13 = fp
      ∧ ws.take 8 = dwordBytes v
      ∧ ws.length = 40 * d + 40
      ∧ A = A₀
      ∧ ((rf.get .x14 = 0
          ∧ rf.get .x15 = inBase + BitVec.ofNat 64 c
          ∧ ((decodeJoinedEncodingsD d (win bs c (pEnd - c))).isSome
            ↔ (decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))).isSome)
          ∧ ∃ L : Nat,
              rf.get .x17 = BitVec.ofNat 64 L
              ∧ decodeItemLength (win bs c (pEnd - c)) = some L
              ∧ L < 2 ^ 64)
        ∨ (rf.get .x14 = 1
          ∧ rf.get .x15 = inBase + BitVec.ofNat 64 pEnd
          ∧ decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart)) = none))

/-- Offset of a region pointer (specialized `idxOf` computation). -/
private theorem idxOf_add (inBase : Word) (k : Nat) (bnd : Nat)
    (hk : k ≤ bnd) (hb : inBase.toNat + bnd < 2 ^ 64) :
    idxOf inBase (inBase + BitVec.ofNat 64 k) = k := by
  unfold idxOf
  have haddr : (inBase + BitVec.ofNat 64 k).toNat = inBase.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [BitVec.toNat_sub, haddr]
  omega

/-- Local copy of the loop-guard characterization. -/
private theorem guard_iff' (inBase : Word) (c q : Nat) (rf : RegFile)
    (h15 : rf.get .x15 = inBase + BitVec.ofNat 64 c)
    (h16 : rf.get .x16 = inBase + BitVec.ofNat 64 q)
    (hbound : inBase.toNat + q < 2 ^ 64) (hcq : c ≤ q) :
    (Cond.bltu .x15 .x16).holds rf ↔ c < q := by
  show BitVec.ult (rf.get .x15) (rf.get .x16) = true ↔ c < q
  rw [h15, h16]
  constructor
  · intro h
    by_contra hge
    have hceq : c = q := by omega
    subst hceq
    simp [BitVec.ult] at h
  · intro h
    have h1 : (inBase + BitVec.ofNat 64 c).toNat = inBase.toNat + c := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have h2 : (inBase + BitVec.ofNat 64 q).toNat = inBase.toNat + q := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    simp only [BitVec.ult, decide_eq_true_eq, h1, h2]
    omega

/-- Local copy of the ro-LBU step (ReadBe's is private). -/
private theorem lbu_ro (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd
          ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

private theorem se12c_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by
  decide
private theorem se12c_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by
  decide
private theorem se12c_n1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by
  decide
private theorem se12c_n7F : signExtend12 (-0x7F : BitVec 12)
    = (-0x7F : Word) := by decide
private theorem se12c_nB7 : signExtend12 (-0xB7 : BitVec 12)
    = (-0xB7 : Word) := by decide
private theorem se12c_nBF : signExtend12 (-0xBF : BitVec 12)
    = (-0xBF : Word) := by decide
private theorem se12c_nF7 : signExtend12 (-0xF7 : BitVec 12)
    = (-0xF7 : Word) := by decide

/-- The state after the iteration's first block: header byte, remaining
    window, running iff, all frame facts. -/
def Ib0Out (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) (i : Nat) : Reach :=
  fun rf ws A =>
    ∃ c : Nat,
      pStart ≤ c ∧ c < pEnd ∧ pStart + i ≤ c
      ∧ rf.get .x5 = (bs.getD c 0).zeroExtend 64
      ∧ rf.get .x6 = BitVec.ofNat 64 (pEnd - c)
      ∧ rf.get .x7 = (0x80 : Word)
      ∧ rf.get .x14 = 0
      ∧ rf.get .x15 = inBase + BitVec.ofNat 64 c
      ∧ rf.get .x16 = inBase + BitVec.ofNat 64 pEnd
      ∧ rf.get .x12 = BitVec.ofNat 64 d
      ∧ rf.get .x13 = fp
      ∧ ws.take 8 = dwordBytes v
      ∧ ws.length = 40 * d + 40
      ∧ A = A₀
      ∧ ((decodeJoinedEncodingsD d (win bs c (pEnd - c))).isSome
        ↔ (decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))).isSome)

private theorem ib0_sp (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) (i : Nat)
    (Lay : RdLayout inBase bs fp (40 * d + 40))
    (hq : pEnd ≤ bs.length) :
    ∀ rf' ws' A', Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp)
        (.block "ib0" [.LBU .x5 .x15 0, .SUB .x6 .x16 .x15, .LI .x7 0x80])
        (fun rf ws A => decInv bs inBase d fp pStart pEnd v A₀ i rf ws A
          ∧ (Cond.bltu .x15 .x16).holds rf) rf' ws' A'
      → Ib0Out bs inBase d fp pStart pEnd v A₀ i rf' ws' A' := by
  rintro rf' ws' A' ⟨rfE, wsE, hlenE, ⟨⟨c, hc1, hc2, hci, h15, h16, h12, h13,
    hslot, hwlen, hA, hdisj⟩, hguard⟩, hrf', hws'⟩
  have hb : inBase.toNat + bs.length < 2 ^ 64 := Lay.regWf.2.1
  have hclt : c < pEnd :=
    (guard_iff' inBase c pEnd rfE h15 h16 (by omega) hc2).mp hguard
  have hiff : (decodeJoinedEncodingsD d (win bs c (pEnd - c))).isSome
      ↔ (decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))).isSome := by
    rcases hdisj with ⟨-, hi⟩ | ⟨-, -, hceq⟩
    · exact hi
    · omega
  have hx14E : rfE.get .x14 = 0 := by
    rcases hdisj with ⟨h0, -⟩ | ⟨-, -, hceq⟩
    · exact h0
    · omega
  have haddr : rfE.get .x15 + signExtend12 (0 : BitVec 12)
      = inBase + BitVec.ofNat 64 c := by
    rw [se12c_0, h15]
    bv_omega
  have hnorw : ¬ inRw (itemsRw d fp).base wsE
      (rfE.get .x15 + signExtend12 (0 : BitVec 12)) 1 := by
    rw [haddr]
    exact Lay.not_inRw (show wsE.length = 40 * d + 40 from hlenE)
      (by omega)
  have hbyte : (Region.mk inBase bs).byteAt
      (rfE.get .x15 + signExtend12 (0 : BitVec 12)) = bs.getD c 0 := by
    rw [haddr]
    exact region_byteAt Lay.regWf (by omega)
  have hws'' : ws' = wsE := hws'
  subst hrf'
  refine ⟨c, hc1, hclt, hci, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hiff⟩
  all_goals first
    | (-- register components through the three-instruction engine
       simp only [execBlock_cons, execBlock_nil]
       rw [lbu_ro _ _ _ _ _ _ _ hnorw]
       simp only [execInstrRF, aluSem]
       simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
         reduceCtorEq, not_false_eq_true]
       all_goals first
         | rfl
         | rw [hbyte]
         | (rw [h16, h15]; bv_omega)
         | exact hx14E
         | exact h15
         | exact h16
         | exact h12
         | exact h13)
    | (rw [hws'']; exact hslot)
    | (rw [hws'']; exact hwlen)
    | exact hA

/-- The long-form entry facts with the header byte's class bounds.  The
    long-form arms overwrite `x7` before using it, so this view deliberately
    omits the `ib0` sentinel value in that register. -/
def Ib0OutCls (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) (i lo hi : Nat) : Reach :=
  fun rf ws A =>
    (∃ c : Nat,
      pStart ≤ c ∧ c < pEnd ∧ pStart + i ≤ c
      ∧ rf.get .x5 = (bs.getD c 0).zeroExtend 64
      ∧ rf.get .x6 = BitVec.ofNat 64 (pEnd - c)
      ∧ rf.get .x14 = 0
      ∧ rf.get .x15 = inBase + BitVec.ofNat 64 c
      ∧ rf.get .x16 = inBase + BitVec.ofNat 64 pEnd
      ∧ rf.get .x12 = BitVec.ofNat 64 d
      ∧ rf.get .x13 = fp
      ∧ ws.take 8 = dwordBytes v
      ∧ ws.length = 40 * d + 40
      ∧ A = A₀
      ∧ ((decodeJoinedEncodingsD d (win bs c (pEnd - c))).isSome
        ↔ (decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))).isSome))
    ∧ lo ≤ (rf.get .x5).toNat ∧ (rf.get .x5).toNat ≤ hi

private theorem toNat_zx_byte (b : BitVec 8) :
    ((b.zeroExtend 64)).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]
  have := b.isLt
  omega

/-- Propagate a rejected remaining window to the whole payload. -/
private theorem full_none_of_rem_none {bs : List Byte} {d c pEnd pStart : Nat}
    (hiff : (decodeJoinedEncodingsD d (win bs c (pEnd - c))).isSome
      ↔ (decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))).isSome)
    (hnone : decodeJoinedEncodingsD d (win bs c (pEnd - c)) = none) :
    decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart)) = none := by
  rcases hopt : decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))
    with _ | val
  · rfl
  · exfalso
    have h2 := hiff.mpr (by rw [hopt]; rfl)
    rw [hnone] at h2
    exact Bool.noConfusion h2

private theorem winBE_lt (bs : List Byte) (j n : Nat) (hn : n ≤ 8) :
    winBE bs j n < 2 ^ 64 := by
  have h := EvmAsm.EL.RLP.Nat.fromBytesBE_lt (win bs j n)
  have hlen : (win bs j n).length ≤ n := by
    unfold EvmAsm.EL.RLP.Ref.win
    rw [List.length_take]
    omega
  calc winBE bs j n < 256 ^ (win bs j n).length := h
    _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ 2 ^ 64 := by norm_num

/-- The state entering the long-form tail (`ibargs...`): header byte
    classified long, `ll` in range, nonzero first length byte. -/
def LongTailPre (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) (i base : Nat) : Reach :=
  fun rf ws A =>
    ∃ c : Nat,
      pStart ≤ c ∧ c < pEnd ∧ pStart + i ≤ c
      ∧ base + 1 ≤ (bs.getD c 0).toNat ∧ (bs.getD c 0).toNat ≤ base + 8
      ∧ (bs.getD c 0).toNat - base < pEnd - c
      ∧ bs.getD (c + 1) 0 ≠ 0
      ∧ rf.get .x6 = BitVec.ofNat 64 (pEnd - c)
      ∧ rf.get .x7 = BitVec.ofNat 64 ((bs.getD c 0).toNat - base)
      ∧ rf.get .x14 = 0
      ∧ rf.get .x15 = inBase + BitVec.ofNat 64 c
      ∧ rf.get .x16 = inBase + BitVec.ofNat 64 pEnd
      ∧ rf.get .x12 = BitVec.ofNat 64 d
      ∧ rf.get .x13 = fp
      ∧ ws.take 8 = dwordBytes v
      ∧ ws.length = 40 * d + 40
      ∧ A = A₀
      ∧ ((decodeJoinedEncodingsD d (win bs c (pEnd - c))).isSome
        ↔ (decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))).isSome)

/-- The item-length fact the long tail needs: at either base, the header
    parses to `some (1 + ll + value)` (this is where the two long forms
    differ only in the base constant). -/
def LongItemFact (bs : List Byte) (pEnd : Nat) (base : Nat) : Prop :=
  ∀ c : Nat, c + (pEnd - c) ≤ bs.length → 1 ≤ pEnd - c →
    base + 1 ≤ (bs.getD c 0).toNat → (bs.getD c 0).toNat ≤ base + 8 →
    (bs.getD c 0).toNat - base < pEnd - c → bs.getD (c + 1) 0 ≠ 0 →
    decodeItemLength (win bs c (pEnd - c))
      = some (1 + ((bs.getD c 0).toNat - base)
          + winBE bs (c + 1) ((bs.getD c 0).toNat - base))

/-- Both long-form item headers parse per the reference. -/
theorem longItemFact_B (bs : List Byte) (pEnd : Nat) :
    LongItemFact bs pEnd 0xB7 := by
  intro c hle hrem hlo hhi htr hz
  have := EvmAsm.EL.RLP.Ref.itemLength_long_ok (bs := bs) (c := c)
    (rem := pEnd - c) hle hrem ⟨by omega, Or.inl (by omega)⟩
    (by rw [if_pos (show (bs.getD c 0).toNat ≤ 0xBF from by omega)]; omega)
    hz
  rw [if_pos (show (bs.getD c 0).toNat ≤ 0xBF from by omega)] at this
  exact this

theorem longItemFact_L (bs : List Byte) (pEnd : Nat) :
    LongItemFact bs pEnd 0xF7 := by
  intro c hle hrem hlo hhi htr hz
  have := EvmAsm.EL.RLP.Ref.itemLength_long_ok (bs := bs) (c := c)
    (rem := pEnd - c) hle hrem ⟨by omega, Or.inr (by omega)⟩
    (by rw [if_neg (show ¬ (bs.getD c 0).toNat ≤ 0xBF from by omega)]; omega)
    hz
  rw [if_neg (show ¬ (bs.getD c 0).toNat ≤ 0xBF from by omega)] at this
  exact this

/-- The mid-tail state: after the leaf call and the remaining-window
    arithmetic, just before the fit branch. -/
def MidOut (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) (i base : Nat) : Reach :=
  fun rf ws A =>
    ∃ c : Nat,
      pStart ≤ c ∧ c < pEnd ∧ pStart + i ≤ c
      ∧ base + 1 ≤ (bs.getD c 0).toNat ∧ (bs.getD c 0).toNat ≤ base + 8
      ∧ (bs.getD c 0).toNat - base < pEnd - c
      ∧ decodeItemLength (win bs c (pEnd - c))
          = some (1 + ((bs.getD c 0).toNat - base)
              + winBE bs (c + 1) ((bs.getD c 0).toNat - base))
      ∧ winBE bs (c + 1) ((bs.getD c 0).toNat - base) < 2 ^ 64
      ∧ rf.get .x6 = BitVec.ofNat 64
          (pEnd - c - 1 - ((bs.getD c 0).toNat - base))
      ∧ rf.get .x31 = BitVec.ofNat 64
          (winBE bs (c + 1) ((bs.getD c 0).toNat - base))
      ∧ rf.get .x7 = BitVec.ofNat 64 ((bs.getD c 0).toNat - base)
      ∧ rf.get .x14 = 0
      ∧ rf.get .x15 = inBase + BitVec.ofNat 64 c
      ∧ rf.get .x16 = inBase + BitVec.ofNat 64 pEnd
      ∧ rf.get .x12 = BitVec.ofNat 64 d
      ∧ rf.get .x13 = fp
      ∧ ws.take 8 = dwordBytes v
      ∧ ws.length = 40 * d + 40
      ∧ A = A₀
      ∧ ((decodeJoinedEncodingsD d (win bs c (pEnd - c))).isSome
        ↔ (decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))).isSome)

/-- Leaf call + remaining-window arithmetic land in `MidOut` (the `ib` copy). -/
private theorem longMidB_sp (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (pStart pEnd : Nat) (v : Word) (A₀ : Assertion)
    (beS : FnHandleS) (i : Nat)
    (Lay : RdLayout inBase bs fp (40 * d + 40))
    (hq : pEnd ≤ bs.length)
    (hfact : LongItemFact bs pEnd 0xB7)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁) :
    ∀ rfF wsF AF, Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp)
        (.block "ibargs" [.ADDI .x29 .x15 1, .MV .x30 .x7,
           .LI .x28 (0x1800 : Word)] ;;;
         .callRegS "ibbe" .x28 [beS] ;;;
         .block "ibrem" [.ADDI .x6 .x6 (-1), .SUB .x6 .x6 .x7])
        (LongTailPre bs inBase d fp pStart pEnd v A₀ i 0xB7) rfF wsF AF
      → MidOut bs inBase d fp pStart pEnd v A₀ i 0xB7 rfF wsF AF := by
  intro rfF wsF AF hsp
  have hb : inBase.toNat + bs.length < 2 ^ 64 := Lay.regWf.2.1
  obtain ⟨rfR, wsR, hlenR, hspCall, hrfF, hwsF⟩ := hsp
  obtain ⟨rfG, wsG, AG, hspArgs, hmemb⟩ := hspCall
  obtain ⟨hh, hhm, hx28e, hhpre, hhpost⟩ := hmemb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hhm
  subst hhm
  obtain ⟨rfE, wsE, hlenE, hpre, hrfG, hwsG⟩ := hspArgs
  obtain ⟨c, hc1, hc2, hci, hlo, hhi, htr, hz1, h6, h7, h14, h15, h16,
    h12, h13, hslot, hwlen, hA, hiff⟩ := hpre
  set ll := (bs.getD c 0).toNat - 0xB7 with hlldef
  have hll8 : ll ≤ 8 := by omega
  have hrfG29 : rfG.get .x29 = inBase + BitVec.ofNat 64 (c + 1) := by
    rw [hrfG]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [h15, se12c_1]
    bv_omega
  have hrfG30 : rfG.get .x30 = BitVec.ofNat 64 ll := by
    rw [hrfG]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [h7]
  have hgetG : ∀ r : Reg, r ≠ .x29 → r ≠ .x30 → r ≠ .x28 →
      rfG.get r = rfE.get r := by
    intro r h29 h30 h28
    rw [hrfG]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    rw [RegFile.get_set_ne _ _ _ _ h28, RegFile.get_set_ne _ _ _ _ h30,
      RegFile.get_set_ne _ _ _ _ h29]
  obtain ⟨h31R, hpinsR, hwsRG, hAG⟩ := hbePost rfG wsG AG rfR wsR AF hhpost
  set val := winBE bs (c + 1) ll with hvaldef
  have hval64 : val < 2 ^ 64 := winBE_lt bs (c + 1) ll hll8
  have h31R' : rfR.get .x31 = BitVec.ofNat 64 val := by
    rw [h31R, hrfG29, hrfG30,
      idxOf_add inBase (c + 1) bs.length (by omega) hb,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rfl
  have h6R : rfR.get .x6 = BitVec.ofNat 64 (pEnd - c) :=
    (hpinsR .x6 (by decide) (by decide) (by decide) (by decide)).trans
      ((hgetG .x6 (by decide) (by decide) (by decide)).trans h6)
  have h7R : rfR.get .x7 = BitVec.ofNat 64 ll :=
    (hpinsR .x7 (by decide) (by decide) (by decide) (by decide)).trans
      ((hgetG .x7 (by decide) (by decide) (by decide)).trans h7)
  have hRthread : ∀ r : Reg, r ≠ .x28 → r ≠ .x29 →
      r ≠ .x30 → r ≠ .x31 → rfR.get r = rfE.get r := by
    intro r h28 h29 h30 h31
    exact (hpinsR r h28 h29 h30 h31).trans (hgetG r h29 h30 h28)
  have hsome := hfact c (by omega) (by omega) hlo hhi htr hz1
  rw [← hlldef, ← hvaldef] at hsome
  have hgetF : ∀ r : Reg, r ≠ .x6 → rfF.get r = rfR.get r := by
    intro r hr
    rw [hrfF]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    rw [RegFile.get_set_ne _ _ _ _ hr, RegFile.get_set_ne _ _ _ _ hr]
  have h6F : rfF.get .x6 = BitVec.ofNat 64 (pEnd - c - 1 - ll) := by
    rw [hrfF]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    rw [RegFile.get_set_self _ _ _ (by decide),
      RegFile.get_set_self _ _ _ (by decide), h6R, se12c_n1,
      RegFile.get_set_ne _ _ _ _ (by decide), h7R]
    bv_omega
  have hwsFE : wsF = wsE := by
    rw [hwsF, hwsRG]
    exact (show wsG = wsE from hwsG)
  refine ⟨c, hc1, hc2, hci, hlo, hhi, htr, hsome, hval64, h6F,
    (hgetF .x31 (by decide)).trans h31R',
    (hgetF .x7 (by decide)).trans h7R,
    (hgetF .x14 (by decide)).trans ((hRthread .x14 (by decide) (by decide)
      (by decide) (by decide)).trans h14),
    (hgetF .x15 (by decide)).trans ((hRthread .x15 (by decide) (by decide)
      (by decide) (by decide)).trans h15),
    (hgetF .x16 (by decide)).trans ((hRthread .x16 (by decide) (by decide)
      (by decide) (by decide)).trans h16),
    (hgetF .x12 (by decide)).trans ((hRthread .x12 (by decide) (by decide)
      (by decide) (by decide)).trans h12),
    (hgetF .x13 (by decide)).trans ((hRthread .x13 (by decide) (by decide)
      (by decide) (by decide)).trans h13),
    hwsFE ▸ hslot, hwsFE ▸ hwlen, hAG.trans hA, hiff⟩

/-- The fit branch from `MidOut` (generic in the base). -/
private theorem fitArms_sp (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (pStart pEnd : Nat) (v : Word) (A₀ : Assertion)
    (i base : Nat)
    (hq : pEnd ≤ bs.length)
    (hblen : bs.length < 2 ^ 64) :
    ∀ rf' ws' A', Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp)
        (.ite "ibfit" (.bltu .x6 .x31)
          (.block "ibpf" [.LI .x14 1, .MV .x15 .x16])
          (.block "ibL" [.ADDI .x17 .x7 1, .ADD .x17 .x17 .x31]))
        (MidOut bs inBase d fp pStart pEnd v A₀ i base) rf' ws' A'
      → CascadeOut bs inBase d fp pStart pEnd v A₀ i rf' ws' A' := by
  intro rf' ws' A' hsp
  rcases hsp with hpf | hLok
  case _ =>
    obtain ⟨rfF, wsF, hlenF, ⟨hmid, hfitc⟩, hrf', hws'⟩ := hpf
    obtain ⟨c, hc1, hc2, hci, hlo, hhi, htr, hsome, hval64, h6F, h31F, h7F,
      h14, h15, h16, h12, h13, hslot, hwlen, hA, hiff⟩ := hmid
    have hbig : pEnd - c - 1 - ((bs.getD c 0).toNat - base)
        < winBE bs (c + 1) ((bs.getD c 0).toNat - base) := by
      have hc' : BitVec.ult (rfF.get .x6) (rfF.get .x31) = true := hfitc
      rw [h6F, h31F] at hc'
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hc'
      omega
    have hjnone := EvmAsm.EL.RLP.Ref.joinedD_unfit d
      (show c + (pEnd - c) ≤ bs.length from by omega)
      (show 1 ≤ pEnd - c from by omega) hsome (by omega)
    subst hrf'
    have hws'' : ws' = wsF := hws'
    refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, hA,
      Or.inr ⟨?_, ?_, full_none_of_rem_none hiff hjnone⟩⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h16]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h12]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h13]
    · rw [hws'']
      exact hslot
    · rw [hws'']
      exact hwlen
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h16]
  case _ =>
    obtain ⟨rfF, wsF, hlenF, ⟨hmid, hfitc⟩, hrf', hws'⟩ := hLok
    obtain ⟨c, hc1, hc2, hci, hlo, hhi, htr, hsome, hval64, h6F, h31F, h7F,
      h14, h15, h16, h12, h13, hslot, hwlen, hA, hiff⟩ := hmid
    have hfit : winBE bs (c + 1) ((bs.getD c 0).toNat - base)
        ≤ pEnd - c - 1 - ((bs.getD c 0).toNat - base) := by
      by_contra hgt
      apply hfitc
      show BitVec.ult (rfF.get .x6) (rfF.get .x31) = true
      rw [h6F, h31F]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
      omega
    subst hrf'
    have hws'' : ws' = wsF := hws'
    refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, hA,
      Or.inl ⟨?_, ?_, hiff,
        1 + ((bs.getD c 0).toNat - base)
          + winBE bs (c + 1) ((bs.getD c 0).toNat - base),
        ?_, hsome, by omega⟩⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h16]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h12]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h13]
    · rw [hws'']
      exact hslot
    · rw [hws'']
      exact hwlen
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h14]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h15]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        h7F, se12c_1, h31F]
      bv_omega

/-- The whole long-form sub-tree at byte-string base. -/
private theorem longHeadB_sp (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (pStart pEnd : Nat) (v : Word) (A₀ : Assertion)
    (beS : FnHandleS) (i : Nat)
    (Lay : RdLayout inBase bs fp (40 * d + 40))
    (hq : pEnd ≤ bs.length)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁) :
    ∀ rf' ws' A', Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp) (itemLongFormB beS)
        (Ib0OutCls bs inBase d fp pStart pEnd v A₀ i 0xB8 0xBF) rf' ws' A'
      → CascadeOut bs inBase d fp pStart pEnd v A₀ i rf' ws' A' := by
  have hb : inBase.toNat + bs.length < 2 ^ 64 := Lay.regWf.2.1
  -- entry extractor
  have hll : ∀ (rfE : RegFile) (wsE : List (BitVec 8)) (AE : Assertion),
      Ib0OutCls bs inBase d fp pStart pEnd v A₀ i 0xB8 0xBF rfE wsE AE →
      ∃ c : Nat, pStart ≤ c ∧ c < pEnd ∧ pStart + i ≤ c
        ∧ rfE.get .x5 = (bs.getD c 0).zeroExtend 64
        ∧ rfE.get .x6 = BitVec.ofNat 64 (pEnd - c)
        ∧ rfE.get .x14 = 0
        ∧ rfE.get .x15 = inBase + BitVec.ofNat 64 c
        ∧ rfE.get .x16 = inBase + BitVec.ofNat 64 pEnd
        ∧ rfE.get .x12 = BitVec.ofNat 64 d
        ∧ rfE.get .x13 = fp
        ∧ wsE.take 8 = dwordBytes v
        ∧ wsE.length = 40 * d + 40
        ∧ AE = A₀
        ∧ ((decodeJoinedEncodingsD d (win bs c (pEnd - c))).isSome
          ↔ (decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))).isSome)
        ∧ 0xB8 ≤ (bs.getD c 0).toNat ∧ (bs.getD c 0).toNat ≤ 0xBF := by
    rintro rfE wsE AE ⟨⟨c, hc1, hc2, hci, h5, h6, h14, h15, h16, h12, h13,
      hslot, hwlen, hA, hiff⟩, hlo, hhi⟩
    rw [h5, toNat_zx_byte] at hlo hhi
    exact ⟨c, hc1, hc2, hci, h5, h6, h14, h15, h16, h12, h13, hslot, hwlen,
      hA, hiff, hlo, hhi⟩
  intro rf' ws' A' hsp
  rcases hsp with hthen | hpt
  case _ =>
    rcases hthen with hpz | htail
    case _ =>
      -- b1 = 0: reject
      obtain ⟨rfZ, wsZ, hlenZ, ⟨hspB1, hzc⟩, hrf', hws'⟩ := hpz
      obtain ⟨rfB, wsB, hlenB, ⟨hspLL, htrc⟩, hrfZ, hwsZ⟩ := hspB1
      obtain ⟨rfE, wsE, hlenE, hpre, hrfB, hwsB⟩ := hspLL
      obtain ⟨c, hc1, hc2, hci, h5, h6, h14, h15, h16, h12, h13, hslot,
        hwlen, hA, hiff, hlo, hhi⟩ := hll rfE wsE A' hpre
      have h7B : rfB.get .x7
          = BitVec.ofNat 64 ((bs.getD c 0).toNat - 0xB7) := by
        rw [hrfB]
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_self _ _ _ (by decide), h5, se12c_nB7]
        bv_omega
      have hgetB : ∀ r : Reg, r ≠ .x7 → rfB.get r = rfE.get r := by
        intro r hr
        rw [hrfB]
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ hr]
      have htr : (bs.getD c 0).toNat - 0xB7 < pEnd - c := by
        have hc' : BitVec.ult (rfB.get .x7) (rfB.get .x6) = true := htrc
        rw [h7B, (hgetB .x6 (by decide)).trans h6] at hc'
        simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hc'
        omega
      have haddr1 : rfB.get .x15 + signExtend12 (1 : BitVec 12)
          = inBase + BitVec.ofNat 64 (c + 1) := by
        rw [se12c_1, (hgetB .x15 (by decide)).trans h15]
        bv_omega
      have hc1lt : c + 1 < bs.length := by omega
      have hnorw1 : ¬ inRw (itemsRw d fp).base wsB
          (rfB.get .x15 + signExtend12 (1 : BitVec 12)) 1 := by
        rw [haddr1]
        exact Lay.not_inRw (show wsB.length = 40 * d + 40 from hlenB) hc1lt
      have hbyte1 : (Region.mk inBase bs).byteAt
          (rfB.get .x15 + signExtend12 (1 : BitVec 12))
          = bs.getD (c + 1) 0 := by
        rw [haddr1]
        exact region_byteAt Lay.regWf hc1lt
      have hrfZ' : rfZ = rfB.set .x31 ((bs.getD (c + 1) 0).zeroExtend 64)
          := by
        rw [hrfZ]
        simp only [execBlock_cons, execBlock_nil]
        rw [lbu_ro _ _ _ _ _ _ _ hnorw1, hbyte1]
      have hz1 : bs.getD (c + 1) 0 = 0 := by
        have hzc' : rfZ.get .x31 = rfZ.get .x0 := hzc
        rw [hrfZ', RegFile.get_set_self _ _ _ (by decide),
          RegFile.get_x0] at hzc'
        have := congrArg BitVec.toNat hzc'
        rw [toNat_zx_byte] at this
        apply BitVec.eq_of_toNat_eq
        simpa using this
      have hnone := EvmAsm.EL.RLP.Ref.itemLength_long_zero
        (show c + (pEnd - c) ≤ bs.length from by omega)
        (show 1 ≤ pEnd - c from by omega)
        ⟨by omega, Or.inl (by omega)⟩
        (by rw [if_pos (show (bs.getD c 0).toNat ≤ 0xBF from by omega)]
            omega)
        hz1
      have hjnone := EvmAsm.EL.RLP.Ref.joinedD_itemLength_none d
        (show c + (pEnd - c) ≤ bs.length from by omega)
        (show 1 ≤ pEnd - c from by omega) hnone
      subst hrf'
      have hgetZ : ∀ r : Reg, r ≠ .x31 → rfZ.get r = rfB.get r := by
        intro r hr
        rw [hrfZ', RegFile.get_set_ne _ _ _ _ hr]
      have hws'' : ws' = wsE :=
        (show ws' = wsZ from hws').trans
          ((show wsZ = wsB from hwsZ).trans (show wsB = wsE from hwsB))
      refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, hA,
        Or.inr ⟨?_, ?_, full_none_of_rem_none hiff hjnone⟩⟩
      · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide),
          (hgetZ .x16 (by decide)).trans ((hgetB .x16 (by decide)).trans h16)]
      · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide),
          (hgetZ .x12 (by decide)).trans ((hgetB .x12 (by decide)).trans h12)]
      · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide),
          (hgetZ .x13 (by decide)).trans ((hgetB .x13 (by decide)).trans h13)]
      · rw [hws'']
        exact hslot
      · rw [hws'']
        exact hwlen
      · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_self _ _ _ (by decide)]
      · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_self _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide),
          (hgetZ .x16 (by decide)).trans ((hgetB .x16 (by decide)).trans h16)]
    case _ =>
      -- b1 ≠ 0: the tail
      refine fitArms_sp bs inBase d fp pStart pEnd v A₀ i 0xB7 hq (by omega)
        rf' ws' A' ?_
      -- htail : sp(ite-fit)(mid-sp over the raw reach); convert inside out
      refine Stmt.sp_mono ⟨inBase, bs⟩ (itemsRw d fp)
        (.ite "ibfit" (.bltu .x6 .x31)
          (.block "ibpf" [.LI .x14 1, .MV .x15 .x16])
          (.block "ibL" [.ADDI .x17 .x7 1, .ADD .x17 .x17 .x31]))
        (fun rfF wsF AF hm =>
          longMidB_sp bs inBase d fp pStart pEnd v A₀ beS i Lay hq
            (longItemFact_B bs pEnd) hbePost rfF wsF AF
            (Stmt.sp_mono ⟨inBase, bs⟩ (itemsRw d fp)
              (.block "ibargs" [.ADDI .x29 .x15 1, .MV .x30 .x7,
                 .LI .x28 (0x1800 : Word)] ;;;
               .callRegS "ibbe" .x28 [beS] ;;;
               .block "ibrem" [.ADDI .x6 .x6 (-1), .SUB .x6 .x6 .x7])
              ?_ rfF wsF AF hm))
        rf' ws' A' htail
      intro rf ws A hRR
      obtain ⟨hspB1, hnzc⟩ := hRR
      obtain ⟨rfB, wsB, hlenB, ⟨hspLL, htrc⟩, hrfZ, hwsZ⟩ := hspB1
      obtain ⟨rfE, wsE, hlenE, hpre, hrfB, hwsB⟩ := hspLL
      obtain ⟨c, hc1, hc2, hci, h5, h6, h14, h15, h16, h12, h13, hslot,
        hwlen, hA, hiff, hlo, hhi⟩ := hll rfE wsE A hpre
      have h7B : rfB.get .x7
          = BitVec.ofNat 64 ((bs.getD c 0).toNat - 0xB7) := by
        rw [hrfB]
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_self _ _ _ (by decide), h5, se12c_nB7]
        bv_omega
      have hgetB : ∀ r : Reg, r ≠ .x7 → rfB.get r = rfE.get r := by
        intro r hr
        rw [hrfB]
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ hr]
      have htr : (bs.getD c 0).toNat - 0xB7 < pEnd - c := by
        have hc' : BitVec.ult (rfB.get .x7) (rfB.get .x6) = true := htrc
        rw [h7B, (hgetB .x6 (by decide)).trans h6] at hc'
        simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hc'
        omega
      have haddr1 : rfB.get .x15 + signExtend12 (1 : BitVec 12)
          = inBase + BitVec.ofNat 64 (c + 1) := by
        rw [se12c_1, (hgetB .x15 (by decide)).trans h15]
        bv_omega
      have hc1lt : c + 1 < bs.length := by omega
      have hnorw1 : ¬ inRw (itemsRw d fp).base wsB
          (rfB.get .x15 + signExtend12 (1 : BitVec 12)) 1 := by
        rw [haddr1]
        exact Lay.not_inRw (show wsB.length = 40 * d + 40 from hlenB) hc1lt
      have hbyte1 : (Region.mk inBase bs).byteAt
          (rfB.get .x15 + signExtend12 (1 : BitVec 12))
          = bs.getD (c + 1) 0 := by
        rw [haddr1]
        exact region_byteAt Lay.regWf hc1lt
      have hrfZ' : rf = rfB.set .x31 ((bs.getD (c + 1) 0).zeroExtend 64)
          := by
        rw [hrfZ]
        simp only [execBlock_cons, execBlock_nil]
        rw [lbu_ro _ _ _ _ _ _ _ hnorw1, hbyte1]
      have hz1 : bs.getD (c + 1) 0 ≠ 0 := by
        intro h0
        apply hnzc
        show rf.get .x31 = rf.get .x0
        rw [hrfZ', RegFile.get_set_self _ _ _ (by decide), RegFile.get_x0,
          h0]
        rfl
      have hgetZ : ∀ r : Reg, r ≠ .x31 → rf.get r = rfB.get r := by
        intro r hr
        rw [hrfZ', RegFile.get_set_ne _ _ _ _ hr]
      have hwsE : ws = wsE :=
        (show ws = wsB from hwsZ).trans (show wsB = wsE from hwsB)
      exact ⟨c, hc1, hc2, hci, by omega, by omega, htr, hz1,
        (hgetZ .x6 (by decide)).trans ((hgetB .x6 (by decide)).trans h6),
        (hgetZ .x7 (by decide)).trans h7B,
        (hgetZ .x14 (by decide)).trans ((hgetB .x14 (by decide)).trans h14),
        (hgetZ .x15 (by decide)).trans ((hgetB .x15 (by decide)).trans h15),
        (hgetZ .x16 (by decide)).trans ((hgetB .x16 (by decide)).trans h16),
        (hgetZ .x12 (by decide)).trans ((hgetB .x12 (by decide)).trans h12),
        (hgetZ .x13 (by decide)).trans ((hgetB .x13 (by decide)).trans h13),
        hwsE ▸ hslot, hwsE ▸ hwlen, hA, hiff⟩
  case _ =>
    -- rem ≤ ll: truncated header; reject
    obtain ⟨rfT, wsT, hlenT, ⟨hspLL, hntrc⟩, hrf', hws'⟩ := hpt
    obtain ⟨rfE, wsE, hlenE, hpre, hrfT2, hwsT2⟩ := hspLL
    obtain ⟨c, hc1, hc2, hci, h5, h6, h14, h15, h16, h12, h13, hslot,
      hwlen, hA, hiff, hlo, hhi⟩ := hll rfE wsE A' hpre
    have h7T : rfT.get .x7
        = BitVec.ofNat 64 ((bs.getD c 0).toNat - 0xB7) := by
      rw [hrfT2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide), h5, se12c_nB7]
      bv_omega
    have hgetT : ∀ r : Reg, r ≠ .x7 → rfT.get r = rfE.get r := by
      intro r hr
      rw [hrfT2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ hr]
    have hntr : pEnd - c ≤ (bs.getD c 0).toNat - 0xB7 := by
      by_contra hlt
      apply hntrc
      show BitVec.ult (rfT.get .x7) (rfT.get .x6) = true
      rw [h7T, (hgetT .x6 (by decide)).trans h6]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
      omega
    have hnone := EvmAsm.EL.RLP.Ref.itemLength_long_trunc
      (show c + (pEnd - c) ≤ bs.length from by omega)
      (show 1 ≤ pEnd - c from by omega)
      ⟨by omega, Or.inl (by omega)⟩
      (by rw [if_pos (show (bs.getD c 0).toNat ≤ 0xBF from by omega)]
          omega)
    have hjnone := EvmAsm.EL.RLP.Ref.joinedD_itemLength_none d
      (show c + (pEnd - c) ≤ bs.length from by omega)
      (show 1 ≤ pEnd - c from by omega) hnone
    subst hrf'
    have hws'' : ws' = wsE :=
      (show ws' = wsT from hws').trans (show wsT = wsE from hwsT2)
    refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, hA,
      Or.inr ⟨?_, ?_, full_none_of_rem_none hiff hjnone⟩⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        (hgetT .x16 (by decide)).trans h16]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        (hgetT .x12 (by decide)).trans h12]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        (hgetT .x13 (by decide)).trans h13]
    · rw [hws'']
      exact hslot
    · rw [hws'']
      exact hwlen
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        (hgetT .x16 (by decide)).trans h16]

/-- Leaf call + remaining-window arithmetic land in `MidOut` (the `il` copy). -/
private theorem longMidL_sp (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (pStart pEnd : Nat) (v : Word) (A₀ : Assertion)
    (beS : FnHandleS) (i : Nat)
    (Lay : RdLayout inBase bs fp (40 * d + 40))
    (hq : pEnd ≤ bs.length)
    (hfact : LongItemFact bs pEnd 0xF7)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁) :
    ∀ rfF wsF AF, Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp)
        (.block "ilargs" [.ADDI .x29 .x15 1, .MV .x30 .x7,
           .LI .x28 (0x1800 : Word)] ;;;
         .callRegS "ilbe" .x28 [beS] ;;;
         .block "ilrem" [.ADDI .x6 .x6 (-1), .SUB .x6 .x6 .x7])
        (LongTailPre bs inBase d fp pStart pEnd v A₀ i 0xF7) rfF wsF AF
      → MidOut bs inBase d fp pStart pEnd v A₀ i 0xF7 rfF wsF AF := by
  intro rfF wsF AF hsp
  have hb : inBase.toNat + bs.length < 2 ^ 64 := Lay.regWf.2.1
  obtain ⟨rfR, wsR, hlenR, hspCall, hrfF, hwsF⟩ := hsp
  obtain ⟨rfG, wsG, AG, hspArgs, hmemb⟩ := hspCall
  obtain ⟨hh, hhm, hx28e, hhpre, hhpost⟩ := hmemb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hhm
  subst hhm
  obtain ⟨rfE, wsE, hlenE, hpre, hrfG, hwsG⟩ := hspArgs
  obtain ⟨c, hc1, hc2, hci, hlo, hhi, htr, hz1, h6, h7, h14, h15, h16,
    h12, h13, hslot, hwlen, hA, hiff⟩ := hpre
  set ll := (bs.getD c 0).toNat - 0xF7 with hlldef
  have hll8 : ll ≤ 8 := by omega
  have hrfG29 : rfG.get .x29 = inBase + BitVec.ofNat 64 (c + 1) := by
    rw [hrfG]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [h15, se12c_1]
    bv_omega
  have hrfG30 : rfG.get .x30 = BitVec.ofNat 64 ll := by
    rw [hrfG]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [h7]
  have hgetG : ∀ r : Reg, r ≠ .x29 → r ≠ .x30 → r ≠ .x28 →
      rfG.get r = rfE.get r := by
    intro r h29 h30 h28
    rw [hrfG]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    rw [RegFile.get_set_ne _ _ _ _ h28, RegFile.get_set_ne _ _ _ _ h30,
      RegFile.get_set_ne _ _ _ _ h29]
  obtain ⟨h31R, hpinsR, hwsRG, hAG⟩ := hbePost rfG wsG AG rfR wsR AF hhpost
  set val := winBE bs (c + 1) ll with hvaldef
  have hval64 : val < 2 ^ 64 := winBE_lt bs (c + 1) ll hll8
  have h31R' : rfR.get .x31 = BitVec.ofNat 64 val := by
    rw [h31R, hrfG29, hrfG30,
      idxOf_add inBase (c + 1) bs.length (by omega) hb,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rfl
  have h6R : rfR.get .x6 = BitVec.ofNat 64 (pEnd - c) :=
    (hpinsR .x6 (by decide) (by decide) (by decide) (by decide)).trans
      ((hgetG .x6 (by decide) (by decide) (by decide)).trans h6)
  have h7R : rfR.get .x7 = BitVec.ofNat 64 ll :=
    (hpinsR .x7 (by decide) (by decide) (by decide) (by decide)).trans
      ((hgetG .x7 (by decide) (by decide) (by decide)).trans h7)
  have hRthread : ∀ r : Reg, r ≠ .x28 → r ≠ .x29 →
      r ≠ .x30 → r ≠ .x31 → rfR.get r = rfE.get r := by
    intro r h28 h29 h30 h31
    exact (hpinsR r h28 h29 h30 h31).trans (hgetG r h29 h30 h28)
  have hsome := hfact c (by omega) (by omega) hlo hhi htr hz1
  rw [← hlldef, ← hvaldef] at hsome
  have hgetF : ∀ r : Reg, r ≠ .x6 → rfF.get r = rfR.get r := by
    intro r hr
    rw [hrfF]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    rw [RegFile.get_set_ne _ _ _ _ hr, RegFile.get_set_ne _ _ _ _ hr]
  have h6F : rfF.get .x6 = BitVec.ofNat 64 (pEnd - c - 1 - ll) := by
    rw [hrfF]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    rw [RegFile.get_set_self _ _ _ (by decide),
      RegFile.get_set_self _ _ _ (by decide), h6R, se12c_n1,
      RegFile.get_set_ne _ _ _ _ (by decide), h7R]
    bv_omega
  have hwsFE : wsF = wsE := by
    rw [hwsF, hwsRG]
    exact (show wsG = wsE from hwsG)
  refine ⟨c, hc1, hc2, hci, hlo, hhi, htr, hsome, hval64, h6F,
    (hgetF .x31 (by decide)).trans h31R',
    (hgetF .x7 (by decide)).trans h7R,
    (hgetF .x14 (by decide)).trans ((hRthread .x14 (by decide) (by decide)
      (by decide) (by decide)).trans h14),
    (hgetF .x15 (by decide)).trans ((hRthread .x15 (by decide) (by decide)
      (by decide) (by decide)).trans h15),
    (hgetF .x16 (by decide)).trans ((hRthread .x16 (by decide) (by decide)
      (by decide) (by decide)).trans h16),
    (hgetF .x12 (by decide)).trans ((hRthread .x12 (by decide) (by decide)
      (by decide) (by decide)).trans h12),
    (hgetF .x13 (by decide)).trans ((hRthread .x13 (by decide) (by decide)
      (by decide) (by decide)).trans h13),
    hwsFE ▸ hslot, hwsFE ▸ hwlen, hAG.trans hA, hiff⟩

/-- The fit branch from `MidOut` (`il`-labeled copy). -/
private theorem fitArmsL_sp (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (pStart pEnd : Nat) (v : Word) (A₀ : Assertion)
    (i base : Nat)
    (hq : pEnd ≤ bs.length)
    (hblen : bs.length < 2 ^ 64) :
    ∀ rf' ws' A', Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp)
        (.ite "ilfit" (.bltu .x6 .x31)
          (.block "ilpf" [.LI .x14 1, .MV .x15 .x16])
          (.block "ilL" [.ADDI .x17 .x7 1, .ADD .x17 .x17 .x31]))
        (MidOut bs inBase d fp pStart pEnd v A₀ i base) rf' ws' A'
      → CascadeOut bs inBase d fp pStart pEnd v A₀ i rf' ws' A' := by
  intro rf' ws' A' hsp
  rcases hsp with hpf | hLok
  case _ =>
    obtain ⟨rfF, wsF, hlenF, ⟨hmid, hfitc⟩, hrf', hws'⟩ := hpf
    obtain ⟨c, hc1, hc2, hci, hlo, hhi, htr, hsome, hval64, h6F, h31F, h7F,
      h14, h15, h16, h12, h13, hslot, hwlen, hA, hiff⟩ := hmid
    have hbig : pEnd - c - 1 - ((bs.getD c 0).toNat - base)
        < winBE bs (c + 1) ((bs.getD c 0).toNat - base) := by
      have hc' : BitVec.ult (rfF.get .x6) (rfF.get .x31) = true := hfitc
      rw [h6F, h31F] at hc'
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hc'
      omega
    have hjnone := EvmAsm.EL.RLP.Ref.joinedD_unfit d
      (show c + (pEnd - c) ≤ bs.length from by omega)
      (show 1 ≤ pEnd - c from by omega) hsome (by omega)
    subst hrf'
    have hws'' : ws' = wsF := hws'
    refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, hA,
      Or.inr ⟨?_, ?_, full_none_of_rem_none hiff hjnone⟩⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h16]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h12]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h13]
    · rw [hws'']
      exact hslot
    · rw [hws'']
      exact hwlen
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h16]
  case _ =>
    obtain ⟨rfF, wsF, hlenF, ⟨hmid, hfitc⟩, hrf', hws'⟩ := hLok
    obtain ⟨c, hc1, hc2, hci, hlo, hhi, htr, hsome, hval64, h6F, h31F, h7F,
      h14, h15, h16, h12, h13, hslot, hwlen, hA, hiff⟩ := hmid
    have hfit : winBE bs (c + 1) ((bs.getD c 0).toNat - base)
        ≤ pEnd - c - 1 - ((bs.getD c 0).toNat - base) := by
      by_contra hgt
      apply hfitc
      show BitVec.ult (rfF.get .x6) (rfF.get .x31) = true
      rw [h6F, h31F]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
      omega
    subst hrf'
    have hws'' : ws' = wsF := hws'
    refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, hA,
      Or.inl ⟨?_, ?_, hiff,
        1 + ((bs.getD c 0).toNat - base)
          + winBE bs (c + 1) ((bs.getD c 0).toNat - base),
        ?_, hsome, by omega⟩⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h16]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h12]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h13]
    · rw [hws'']
      exact hslot
    · rw [hws'']
      exact hwlen
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h14]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), h15]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        h7F, se12c_1, h31F]
      bv_omega

/-- The whole long-form sub-tree at list base. -/
private theorem longHeadL_sp (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (pStart pEnd : Nat) (v : Word) (A₀ : Assertion)
    (beS : FnHandleS) (i : Nat)
    (Lay : RdLayout inBase bs fp (40 * d + 40))
    (hq : pEnd ≤ bs.length)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁) :
    ∀ rf' ws' A', Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp) (itemLongFormL beS)
        (Ib0OutCls bs inBase d fp pStart pEnd v A₀ i 0xF8 0xFF) rf' ws' A'
      → CascadeOut bs inBase d fp pStart pEnd v A₀ i rf' ws' A' := by
  have hb : inBase.toNat + bs.length < 2 ^ 64 := Lay.regWf.2.1
  -- entry extractor
  have hll : ∀ (rfE : RegFile) (wsE : List (BitVec 8)) (AE : Assertion),
      Ib0OutCls bs inBase d fp pStart pEnd v A₀ i 0xF8 0xFF rfE wsE AE →
      ∃ c : Nat, pStart ≤ c ∧ c < pEnd ∧ pStart + i ≤ c
        ∧ rfE.get .x5 = (bs.getD c 0).zeroExtend 64
        ∧ rfE.get .x6 = BitVec.ofNat 64 (pEnd - c)
        ∧ rfE.get .x14 = 0
        ∧ rfE.get .x15 = inBase + BitVec.ofNat 64 c
        ∧ rfE.get .x16 = inBase + BitVec.ofNat 64 pEnd
        ∧ rfE.get .x12 = BitVec.ofNat 64 d
        ∧ rfE.get .x13 = fp
        ∧ wsE.take 8 = dwordBytes v
        ∧ wsE.length = 40 * d + 40
        ∧ AE = A₀
        ∧ ((decodeJoinedEncodingsD d (win bs c (pEnd - c))).isSome
          ↔ (decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))).isSome)
        ∧ 0xF8 ≤ (bs.getD c 0).toNat ∧ (bs.getD c 0).toNat ≤ 0xFF := by
    rintro rfE wsE AE ⟨⟨c, hc1, hc2, hci, h5, h6, h14, h15, h16, h12, h13,
      hslot, hwlen, hA, hiff⟩, hlo, hhi⟩
    rw [h5, toNat_zx_byte] at hlo hhi
    exact ⟨c, hc1, hc2, hci, h5, h6, h14, h15, h16, h12, h13, hslot, hwlen,
      hA, hiff, hlo, hhi⟩
  intro rf' ws' A' hsp
  rcases hsp with hthen | hpt
  case _ =>
    rcases hthen with hpz | htail
    case _ =>
      -- b1 = 0: reject
      obtain ⟨rfZ, wsZ, hlenZ, ⟨hspB1, hzc⟩, hrf', hws'⟩ := hpz
      obtain ⟨rfB, wsB, hlenB, ⟨hspLL, htrc⟩, hrfZ, hwsZ⟩ := hspB1
      obtain ⟨rfE, wsE, hlenE, hpre, hrfB, hwsB⟩ := hspLL
      obtain ⟨c, hc1, hc2, hci, h5, h6, h14, h15, h16, h12, h13, hslot,
        hwlen, hA, hiff, hlo, hhi⟩ := hll rfE wsE A' hpre
      have h7B : rfB.get .x7
          = BitVec.ofNat 64 ((bs.getD c 0).toNat - 0xF7) := by
        rw [hrfB]
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_self _ _ _ (by decide), h5, se12c_nF7]
        bv_omega
      have hgetB : ∀ r : Reg, r ≠ .x7 → rfB.get r = rfE.get r := by
        intro r hr
        rw [hrfB]
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ hr]
      have htr : (bs.getD c 0).toNat - 0xF7 < pEnd - c := by
        have hc' : BitVec.ult (rfB.get .x7) (rfB.get .x6) = true := htrc
        rw [h7B, (hgetB .x6 (by decide)).trans h6] at hc'
        simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hc'
        omega
      have haddr1 : rfB.get .x15 + signExtend12 (1 : BitVec 12)
          = inBase + BitVec.ofNat 64 (c + 1) := by
        rw [se12c_1, (hgetB .x15 (by decide)).trans h15]
        bv_omega
      have hc1lt : c + 1 < bs.length := by omega
      have hnorw1 : ¬ inRw (itemsRw d fp).base wsB
          (rfB.get .x15 + signExtend12 (1 : BitVec 12)) 1 := by
        rw [haddr1]
        exact Lay.not_inRw (show wsB.length = 40 * d + 40 from hlenB) hc1lt
      have hbyte1 : (Region.mk inBase bs).byteAt
          (rfB.get .x15 + signExtend12 (1 : BitVec 12))
          = bs.getD (c + 1) 0 := by
        rw [haddr1]
        exact region_byteAt Lay.regWf hc1lt
      have hrfZ' : rfZ = rfB.set .x31 ((bs.getD (c + 1) 0).zeroExtend 64)
          := by
        rw [hrfZ]
        simp only [execBlock_cons, execBlock_nil]
        rw [lbu_ro _ _ _ _ _ _ _ hnorw1, hbyte1]
      have hz1 : bs.getD (c + 1) 0 = 0 := by
        have hzc' : rfZ.get .x31 = rfZ.get .x0 := hzc
        rw [hrfZ', RegFile.get_set_self _ _ _ (by decide),
          RegFile.get_x0] at hzc'
        have := congrArg BitVec.toNat hzc'
        rw [toNat_zx_byte] at this
        apply BitVec.eq_of_toNat_eq
        simpa using this
      have hnone := EvmAsm.EL.RLP.Ref.itemLength_long_zero
        (show c + (pEnd - c) ≤ bs.length from by omega)
        (show 1 ≤ pEnd - c from by omega)
        ⟨by omega, Or.inr (by omega)⟩
        (by rw [if_neg (show ¬ (bs.getD c 0).toNat ≤ 0xBF from by omega)]
            omega)
        hz1
      have hjnone := EvmAsm.EL.RLP.Ref.joinedD_itemLength_none d
        (show c + (pEnd - c) ≤ bs.length from by omega)
        (show 1 ≤ pEnd - c from by omega) hnone
      subst hrf'
      have hgetZ : ∀ r : Reg, r ≠ .x31 → rfZ.get r = rfB.get r := by
        intro r hr
        rw [hrfZ', RegFile.get_set_ne _ _ _ _ hr]
      have hws'' : ws' = wsE :=
        (show ws' = wsZ from hws').trans
          ((show wsZ = wsB from hwsZ).trans (show wsB = wsE from hwsB))
      refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, hA,
        Or.inr ⟨?_, ?_, full_none_of_rem_none hiff hjnone⟩⟩
      · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide),
          (hgetZ .x16 (by decide)).trans ((hgetB .x16 (by decide)).trans h16)]
      · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide),
          (hgetZ .x12 (by decide)).trans ((hgetB .x12 (by decide)).trans h12)]
      · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide),
          (hgetZ .x13 (by decide)).trans ((hgetB .x13 (by decide)).trans h13)]
      · rw [hws'']
        exact hslot
      · rw [hws'']
        exact hwlen
      · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_self _ _ _ (by decide)]
      · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_self _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide),
          (hgetZ .x16 (by decide)).trans ((hgetB .x16 (by decide)).trans h16)]
    case _ =>
      -- b1 ≠ 0: the tail
      refine fitArmsL_sp bs inBase d fp pStart pEnd v A₀ i 0xF7 hq (by omega)
        rf' ws' A' ?_
      -- htail : sp(ite-fit)(mid-sp over the raw reach); convert inside out
      refine Stmt.sp_mono ⟨inBase, bs⟩ (itemsRw d fp)
        (.ite "ilfit" (.bltu .x6 .x31)
          (.block "ilpf" [.LI .x14 1, .MV .x15 .x16])
          (.block "ilL" [.ADDI .x17 .x7 1, .ADD .x17 .x17 .x31]))
        (fun rfF wsF AF hm =>
          longMidL_sp bs inBase d fp pStart pEnd v A₀ beS i Lay hq
            (longItemFact_L bs pEnd) hbePost rfF wsF AF
            (Stmt.sp_mono ⟨inBase, bs⟩ (itemsRw d fp)
              (.block "ilargs" [.ADDI .x29 .x15 1, .MV .x30 .x7,
                 .LI .x28 (0x1800 : Word)] ;;;
               .callRegS "ilbe" .x28 [beS] ;;;
               .block "ilrem" [.ADDI .x6 .x6 (-1), .SUB .x6 .x6 .x7])
              ?_ rfF wsF AF hm))
        rf' ws' A' htail
      intro rf ws A hRR
      obtain ⟨hspB1, hnzc⟩ := hRR
      obtain ⟨rfB, wsB, hlenB, ⟨hspLL, htrc⟩, hrfZ, hwsZ⟩ := hspB1
      obtain ⟨rfE, wsE, hlenE, hpre, hrfB, hwsB⟩ := hspLL
      obtain ⟨c, hc1, hc2, hci, h5, h6, h14, h15, h16, h12, h13, hslot,
        hwlen, hA, hiff, hlo, hhi⟩ := hll rfE wsE A hpre
      have h7B : rfB.get .x7
          = BitVec.ofNat 64 ((bs.getD c 0).toNat - 0xF7) := by
        rw [hrfB]
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_self _ _ _ (by decide), h5, se12c_nF7]
        bv_omega
      have hgetB : ∀ r : Reg, r ≠ .x7 → rfB.get r = rfE.get r := by
        intro r hr
        rw [hrfB]
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ hr]
      have htr : (bs.getD c 0).toNat - 0xF7 < pEnd - c := by
        have hc' : BitVec.ult (rfB.get .x7) (rfB.get .x6) = true := htrc
        rw [h7B, (hgetB .x6 (by decide)).trans h6] at hc'
        simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hc'
        omega
      have haddr1 : rfB.get .x15 + signExtend12 (1 : BitVec 12)
          = inBase + BitVec.ofNat 64 (c + 1) := by
        rw [se12c_1, (hgetB .x15 (by decide)).trans h15]
        bv_omega
      have hc1lt : c + 1 < bs.length := by omega
      have hnorw1 : ¬ inRw (itemsRw d fp).base wsB
          (rfB.get .x15 + signExtend12 (1 : BitVec 12)) 1 := by
        rw [haddr1]
        exact Lay.not_inRw (show wsB.length = 40 * d + 40 from hlenB) hc1lt
      have hbyte1 : (Region.mk inBase bs).byteAt
          (rfB.get .x15 + signExtend12 (1 : BitVec 12))
          = bs.getD (c + 1) 0 := by
        rw [haddr1]
        exact region_byteAt Lay.regWf hc1lt
      have hrfZ' : rf = rfB.set .x31 ((bs.getD (c + 1) 0).zeroExtend 64)
          := by
        rw [hrfZ]
        simp only [execBlock_cons, execBlock_nil]
        rw [lbu_ro _ _ _ _ _ _ _ hnorw1, hbyte1]
      have hz1 : bs.getD (c + 1) 0 ≠ 0 := by
        intro h0
        apply hnzc
        show rf.get .x31 = rf.get .x0
        rw [hrfZ', RegFile.get_set_self _ _ _ (by decide), RegFile.get_x0,
          h0]
        rfl
      have hgetZ : ∀ r : Reg, r ≠ .x31 → rf.get r = rfB.get r := by
        intro r hr
        rw [hrfZ', RegFile.get_set_ne _ _ _ _ hr]
      have hwsE : ws = wsE :=
        (show ws = wsB from hwsZ).trans (show wsB = wsE from hwsB)
      exact ⟨c, hc1, hc2, hci, by omega, by omega, htr, hz1,
        (hgetZ .x6 (by decide)).trans ((hgetB .x6 (by decide)).trans h6),
        (hgetZ .x7 (by decide)).trans h7B,
        (hgetZ .x14 (by decide)).trans ((hgetB .x14 (by decide)).trans h14),
        (hgetZ .x15 (by decide)).trans ((hgetB .x15 (by decide)).trans h15),
        (hgetZ .x16 (by decide)).trans ((hgetB .x16 (by decide)).trans h16),
        (hgetZ .x12 (by decide)).trans ((hgetB .x12 (by decide)).trans h12),
        (hgetZ .x13 (by decide)).trans ((hgetB .x13 (by decide)).trans h13),
        hwsE ▸ hslot, hwsE ▸ hwlen, hA, hiff⟩
  case _ =>
    -- rem ≤ ll: truncated header; reject
    obtain ⟨rfT, wsT, hlenT, ⟨hspLL, hntrc⟩, hrf', hws'⟩ := hpt
    obtain ⟨rfE, wsE, hlenE, hpre, hrfT2, hwsT2⟩ := hspLL
    obtain ⟨c, hc1, hc2, hci, h5, h6, h14, h15, h16, h12, h13, hslot,
      hwlen, hA, hiff, hlo, hhi⟩ := hll rfE wsE A' hpre
    have h7T : rfT.get .x7
        = BitVec.ofNat 64 ((bs.getD c 0).toNat - 0xF7) := by
      rw [hrfT2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide), h5, se12c_nF7]
      bv_omega
    have hgetT : ∀ r : Reg, r ≠ .x7 → rfT.get r = rfE.get r := by
      intro r hr
      rw [hrfT2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ hr]
    have hntr : pEnd - c ≤ (bs.getD c 0).toNat - 0xF7 := by
      by_contra hlt
      apply hntrc
      show BitVec.ult (rfT.get .x7) (rfT.get .x6) = true
      rw [h7T, (hgetT .x6 (by decide)).trans h6]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
      omega
    have hnone := EvmAsm.EL.RLP.Ref.itemLength_long_trunc
      (show c + (pEnd - c) ≤ bs.length from by omega)
      (show 1 ≤ pEnd - c from by omega)
      ⟨by omega, Or.inr (by omega)⟩
      (by rw [if_neg (show ¬ (bs.getD c 0).toNat ≤ 0xBF from by omega)]
          omega)
    have hjnone := EvmAsm.EL.RLP.Ref.joinedD_itemLength_none d
      (show c + (pEnd - c) ≤ bs.length from by omega)
      (show 1 ≤ pEnd - c from by omega) hnone
    subst hrf'
    have hws'' : ws' = wsE :=
      (show ws' = wsT from hws').trans (show wsT = wsE from hwsT2)
    refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, hA,
      Or.inr ⟨?_, ?_, full_none_of_rem_none hiff hjnone⟩⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        (hgetT .x16 (by decide)).trans h16]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        (hgetT .x12 (by decide)).trans h12]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        (hgetT .x13 (by decide)).trans h13]
    · rw [hws'']
      exact hslot
    · rw [hws'']
      exact hwlen
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        (hgetT .x16 (by decide)).trans h16]

/-- The cascade half of one iteration: `decode_item_length` in registers. -/
theorem cascade_sp (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) (beS : FnHandleS) (i : Nat)
    (L : RdLayout inBase bs fp (40 * d + 40))
    (hq : pEnd ≤ bs.length)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁) :
    ∀ rf' ws' A', Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp) (itemLenCascade beS)
        (fun rf ws A => decInv bs inBase d fp pStart pEnd v A₀ i rf ws A
          ∧ (Cond.bltu .x15 .x16).holds rf) rf' ws' A'
      → CascadeOut bs inBase d fp pStart pEnd v A₀ i rf' ws' A' := by
  intro rf' ws' A' hsp
  have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hib0 : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion),
      Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp)
        (.block "ib0" [.LBU .x5 .x15 0, .SUB .x6 .x16 .x15, .LI .x7 0x80])
        (fun rf ws A => decInv bs inBase d fp pStart pEnd v A₀ i rf ws A
          ∧ (Cond.bltu .x15 .x16).holds rf) rf₁ ws₁ A₁ →
      Ib0Out bs inBase d fp pStart pEnd v A₀ i rf₁ ws₁ A₁ := by
    intro rf₁ ws₁ A₁ h
    exact ib0_sp bs inBase d fp pStart pEnd v A₀ i L hq rf₁ ws₁ A₁ h
  rcases hsp with hL | hsp2
  · -- iL1: a single-byte item.
    obtain ⟨rf1, ws1, hlen1, ⟨hIb0, hcond⟩, hrf', hws'⟩ := hL
    obtain ⟨c, hc1, hc2, hci, h5, h6, h7, h14, h15, h16, h12, h13,
      hslot, hwlen, hA, hiff⟩ := hib0 _ _ _ hIb0
    subst hrf'
    have hcb : (bs.getD c 0).toNat < 0x80 := by
      change BitVec.ult (rf1.get .x5) (rf1.get .x7) = true at hcond
      rw [h5, h7] at hcond
      simp only [BitVec.ult, decide_eq_true_eq, toNat_zx_byte] at hcond
      exact hcond
    have hlen : decodeItemLength (win bs c (pEnd - c)) = some 1 :=
      EvmAsm.EL.RLP.Ref.itemLength_single (by omega) (by omega)
        hcb
    refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, hA,
      Or.inl ⟨?_, ?_, hiff, 1, ?_, hlen, by omega⟩⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h16
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h12
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h13
    · rw [hws']
      exact hslot
    · rw [hws']
      exact hwlen
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h14
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h15
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      rfl
  rcases hsp2 with hL | hsp2
  · -- iL2: a short byte string.
    obtain ⟨rf2, ws2, hlen2, ⟨hSp, hcond2⟩, hrf', hws'⟩ := hL
    obtain ⟨rf1, ws1, hlen1, ⟨hIb0, hcond1⟩, hrf2, hws2⟩ := hSp
    obtain ⟨c, hc1, hc2, hci, h5, h6, h7, h14, h15, h16, h12, h13,
      hslot, hwlen, hA, hiff⟩ := hib0 _ _ _ hIb0
    have hrf2x5 : rf2.get .x5 = (bs.getD c 0).zeroExtend 64 := by
      rw [hrf2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide), h5]
    have hrf2x7 : rf2.get .x7 = (0xB8 : Word) := by
      rw [hrf2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
    have hcb : 0x80 ≤ (bs.getD c 0).toNat ∧
        (bs.getD c 0).toNat < 0xB8 := by
      change BitVec.ult (rf2.get .x5) (rf2.get .x7) = true at hcond2
      rw [hrf2x5, hrf2x7] at hcond2
      simp only [BitVec.ult, decide_eq_true_eq, toNat_zx_byte] at hcond2
      have hcond1' : ¬ BitVec.ult (rf1.get .x5) (rf1.get .x7) = true := by
        change ¬ BitVec.ult (rf1.get .x5) (rf1.get .x7) = true at hcond1
        exact hcond1
      rw [h5, h7] at hcond1'
      simp only [BitVec.ult, decide_eq_true_eq, toNat_zx_byte] at hcond1'
      have h128 : (128 : Word).toNat = 128 := by decide
      have hB8 : (0xB8 : Word).toNat = 0xB8 := by decide
      rw [h128] at hcond1'
      rw [hB8] at hcond2
      omega
    have hrf2x16 : rf2.get .x16 = inBase + BitVec.ofNat 64 pEnd := by
      rw [hrf2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h16
    have hrf2x12 : rf2.get .x12 = BitVec.ofNat 64 d := by
      rw [hrf2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h12
    have hrf2x13 : rf2.get .x13 = fp := by
      rw [hrf2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h13
    have hrf2x14 : rf2.get .x14 = 0 := by
      rw [hrf2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h14
    have hrf2x15 : rf2.get .x15 = inBase + BitVec.ofNat 64 c := by
      rw [hrf2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h15
    have hws2' : ws2 = ws1 := by
      simpa only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] using hws2
    have hse : signExtend12 (-0x7F : BitVec 12) = (-0x7F : Word) := by
      decide
    subst hrf'
    have hlen : decodeItemLength (win bs c (pEnd - c)) =
        some (1 + ((bs.getD c 0).toNat - 0x80)) :=
      EvmAsm.EL.RLP.Ref.itemLength_short_bytes (by omega) (by omega)
        hcb.1 (by omega)
    refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, hA,
      Or.inl ⟨?_, ?_, hiff, 1 + ((bs.getD c 0).toNat - 0x80), ?_, hlen,
        by omega⟩⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hrf2x16
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hrf2x12
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hrf2x13
    · rw [hws', hws2']
      exact hslot
    · rw [hws', hws2']
      exact hwlen
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hrf2x14
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hrf2x15
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide), hrf2x5, hse]
      bv_omega
  rcases hsp2 with hL | hsp2
  · refine longHeadB_sp bs inBase d fp pStart pEnd v A₀ beS i L hq hbePost
      rf' ws' A' ?_
    refine Stmt.sp_mono ⟨inBase, bs⟩ (itemsRw d fp) (itemLongFormB beS)
      ?_ rf' ws' A' hL
    intro rf ws A hpre
    obtain ⟨hIc2, hcond3⟩ := hpre
    obtain ⟨rf2, ws2, hlen2, ⟨hIc1, hcond2⟩, hrf, hws⟩ := hIc2
    obtain ⟨rf1, ws1, hlen1, ⟨hIb0, hcond1⟩, hrf2, hws2⟩ := hIc1
    obtain ⟨c, hc1, hc2, hci, h5, h6, h7, h14, h15, h16, h12, h13,
      hslot, hwlen, hA, hiff⟩ := hib0 _ _ _ hIb0
    have hget2 : ∀ r : Reg, r ≠ .x7 → rf2.get r = rf1.get r := by
      intro r hr
      rw [hrf2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ hr]
    have hget : ∀ r : Reg, r ≠ .x7 → rf.get r = rf2.get r := by
      intro r hr
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ hr]
    have hrf2x5 : rf2.get .x5 = (bs.getD c 0).zeroExtend 64 :=
      (hget2 .x5 (by decide)).trans h5
    have hrf2x7 : rf2.get .x7 = (0xB8 : Word) := by
      rw [hrf2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
    have hcb_lo : 0xB8 ≤ (bs.getD c 0).toNat := by
      change ¬ BitVec.ult (rf2.get .x5) (rf2.get .x7) = true at hcond2
      rw [hrf2x5, hrf2x7] at hcond2
      simp only [BitVec.ult, decide_eq_true_eq, toNat_zx_byte] at hcond2
      have hB8 : (0xB8 : Word).toNat = 0xB8 := by decide
      rw [hB8] at hcond2
      omega
    have hrf3x5 : rf.get .x5 = (bs.getD c 0).zeroExtend 64 :=
      (hget .x5 (by decide)).trans hrf2x5
    have hrf3x7 : rf.get .x7 = (0xC0 : Word) := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
    have hcb_hi : (bs.getD c 0).toNat < 0xC0 := by
      change BitVec.ult (rf.get .x5) (rf.get .x7) = true at hcond3
      rw [hrf3x5, hrf3x7] at hcond3
      simp only [BitVec.ult, decide_eq_true_eq, toNat_zx_byte] at hcond3
      have hC0 : (0xC0 : Word).toNat = 0xC0 := by decide
      rw [hC0] at hcond3
      exact hcond3
    have hws2' : ws2 = ws1 := by
      simpa only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] using hws2
    have hws' : ws = ws1 := by
      have hws0 : ws = ws2 := by
        simpa only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] using hws
      exact hws0.trans hws2'
    have hcb_lo_rf : 0xB8 ≤ (rf.get .x5).toNat := by
      rw [hrf3x5, toNat_zx_byte]
      exact hcb_lo
    have hcb_hi_rf : (rf.get .x5).toNat ≤ 0xBF := by
      rw [hrf3x5, toNat_zx_byte]
      omega
    refine ⟨?_, hcb_lo_rf, hcb_hi_rf⟩
    · refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hA,
        hiff⟩
      · exact hrf3x5
      · exact (hget .x6 (by decide)).trans ((hget2 .x6 (by decide)).trans h6)
      · exact (hget .x14 (by decide)).trans ((hget2 .x14 (by decide)).trans h14)
      · exact (hget .x15 (by decide)).trans ((hget2 .x15 (by decide)).trans h15)
      · exact (hget .x16 (by decide)).trans ((hget2 .x16 (by decide)).trans h16)
      · exact (hget .x12 (by decide)).trans ((hget2 .x12 (by decide)).trans h12)
      · exact (hget .x13 (by decide)).trans ((hget2 .x13 (by decide)).trans h13)
      · rw [hws']
        exact hslot
      · rw [hws']
        exact hwlen
  rcases hsp2 with hL | hsp2
  · -- iL4: a short list.
    obtain ⟨rf4, ws4, hlen4, ⟨hSp3, hcond4⟩, hrf', hws'⟩ := hL
    obtain ⟨rf3, ws3, hlen3, ⟨hSp2, hcond3⟩, hrf4, hws4⟩ := hSp3
    obtain ⟨rf2, ws2, hlen2, ⟨hSp1, hcond2⟩, hrf3, hws3⟩ := hSp2
    obtain ⟨rf1, ws1, hlen1, ⟨hIb0, hcond1⟩, hrf2, hws2⟩ := hSp1
    obtain ⟨c, hc1, hc2, hci, h5, h6, h7, h14, h15, h16, h12, h13,
      hslot, hwlen, hA, hiff⟩ := hib0 _ _ _ hIb0
    have hget2 : ∀ r : Reg, r ≠ .x7 → rf2.get r = rf1.get r := by
      intro r hr
      rw [hrf2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ hr]
    have hget3 : ∀ r : Reg, r ≠ .x7 → rf3.get r = rf2.get r := by
      intro r hr
      rw [hrf3]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ hr]
    have hget4 : ∀ r : Reg, r ≠ .x7 → rf4.get r = rf3.get r := by
      intro r hr
      rw [hrf4]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ hr]
    have hget4o : ∀ r : Reg, r ≠ .x17 → rf'.get r = rf4.get r := by
      intro r hr
      rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ hr]
    have hrf3x5 : rf3.get .x5 = (bs.getD c 0).zeroExtend 64 :=
      (hget3 .x5 (by decide)).trans ((hget2 .x5 (by decide)).trans h5)
    have hrf3x7 : rf3.get .x7 = (0xC0 : Word) := by
      rw [hrf3]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
    have hcb_lo : 0xC0 ≤ (bs.getD c 0).toNat := by
      change ¬ BitVec.ult (rf3.get .x5) (rf3.get .x7) = true at hcond3
      rw [hrf3x5, hrf3x7] at hcond3
      simp only [BitVec.ult, decide_eq_true_eq, toNat_zx_byte] at hcond3
      have hC0 : (0xC0 : Word).toNat = 0xC0 := by decide
      rw [hC0] at hcond3
      omega
    have hrf4x5 : rf4.get .x5 = (bs.getD c 0).zeroExtend 64 :=
      (hget4 .x5 (by decide)).trans hrf3x5
    have hrf4x7 : rf4.get .x7 = (0xF8 : Word) := by
      rw [hrf4]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
    have hcb_hi : (bs.getD c 0).toNat < 0xF8 := by
      change BitVec.ult (rf4.get .x5) (rf4.get .x7) = true at hcond4
      rw [hrf4x5, hrf4x7] at hcond4
      simp only [BitVec.ult, decide_eq_true_eq, toNat_zx_byte] at hcond4
      have hF8 : (0xF8 : Word).toNat = 0xF8 := by decide
      rw [hF8] at hcond4
      exact hcond4
    have hws2' : ws2 = ws1 := by
      simpa only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] using hws2
    have hws3' : ws3 = ws1 := by
      have hws0 : ws3 = ws2 := by
        simpa only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] using hws3
      exact hws0.trans hws2'
    have hws4' : ws4 = ws1 := by
      have hws0 : ws4 = ws3 := by
        simpa only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] using hws4
      exact hws0.trans hws3'
    have hse : signExtend12 (-0xBF : BitVec 12) = (-0xBF : Word) := by
      decide
    subst hrf'
    have hlen : decodeItemLength (win bs c (pEnd - c)) =
        some (1 + ((bs.getD c 0).toNat - 0xC0)) :=
      EvmAsm.EL.RLP.Ref.itemLength_short_list (by omega) (by omega)
        hcb_lo (by omega)
    refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, hA,
      Or.inl ⟨?_, ?_, hiff, 1 + ((bs.getD c 0).toNat - 0xC0), ?_, hlen,
        by omega⟩⟩
    · exact (hget4o .x16 (by decide)).trans
        ((hget4 .x16 (by decide)).trans
          ((hget3 .x16 (by decide)).trans ((hget2 .x16 (by decide)).trans h16)))
    · exact (hget4o .x12 (by decide)).trans
        ((hget4 .x12 (by decide)).trans
          ((hget3 .x12 (by decide)).trans ((hget2 .x12 (by decide)).trans h12)))
    · exact (hget4o .x13 (by decide)).trans
        ((hget4 .x13 (by decide)).trans
          ((hget3 .x13 (by decide)).trans ((hget2 .x13 (by decide)).trans h13)))
    · rw [hws', hws4']
      exact hslot
    · rw [hws', hws4']
      exact hwlen
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact (hget4 .x14 (by decide)).trans
        ((hget3 .x14 (by decide)).trans ((hget2 .x14 (by decide)).trans h14))
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact (hget4 .x15 (by decide)).trans
        ((hget3 .x15 (by decide)).trans ((hget2 .x15 (by decide)).trans h15))
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide), hrf4x5, hse]
      bv_omega
  · refine longHeadL_sp bs inBase d fp pStart pEnd v A₀ beS i L hq hbePost
      rf' ws' A' ?_
    refine Stmt.sp_mono ⟨inBase, bs⟩ (itemsRw d fp) (itemLongFormL beS)
      ?_ rf' ws' A' hsp2
    intro rf ws A hpre
    obtain ⟨hIc3, hcond4⟩ := hpre
    obtain ⟨rf3, ws3, hlen3, ⟨hIc2, -⟩, hrf4, hws4⟩ := hIc3
    obtain ⟨rf2, ws2, hlen2, ⟨hIc1, -⟩, hrf3, hws3⟩ := hIc2
    obtain ⟨rf1, ws1, hlen1, ⟨hIb0, -⟩, hrf2, hws2⟩ := hIc1
    obtain ⟨c, hc1, hc2, hci, h5, h6, h7, h14, h15, h16, h12, h13,
      hslot, hwlen, hA, hiff⟩ := hib0 _ _ _ hIb0
    have hget2 : ∀ r : Reg, r ≠ .x7 → rf2.get r = rf1.get r := by
      intro r hr
      rw [hrf2]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ hr]
    have hget3 : ∀ r : Reg, r ≠ .x7 → rf3.get r = rf2.get r := by
      intro r hr
      rw [hrf3]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ hr]
    have hget4 : ∀ r : Reg, r ≠ .x7 → rf.get r = rf3.get r := by
      intro r hr
      rw [hrf4]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ hr]
    have hrf4x5 : rf.get .x5 = (bs.getD c 0).zeroExtend 64 :=
      (hget4 .x5 (by decide)).trans
        ((hget3 .x5 (by decide)).trans ((hget2 .x5 (by decide)).trans h5))
    have hrf4x7 : rf.get .x7 = (0xF8 : Word) := by
      rw [hrf4]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
    have hcb_lo : 0xF8 ≤ (bs.getD c 0).toNat := by
      change ¬ BitVec.ult (rf.get .x5) (rf.get .x7) = true at hcond4
      rw [hrf4x5, hrf4x7] at hcond4
      simp only [BitVec.ult, decide_eq_true_eq, toNat_zx_byte] at hcond4
      have hF8 : (0xF8 : Word).toNat = 0xF8 := by decide
      rw [hF8] at hcond4
      omega
    have hws2' : ws2 = ws1 := by
      simpa only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] using hws2
    have hws3' : ws3 = ws1 := by
      have hws0 : ws3 = ws2 := by
        simpa only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] using hws3
      exact hws0.trans hws2'
    have hws4' : ws = ws1 := by
      have hws0 : ws = ws3 := by
        simpa only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] using hws4
      exact hws0.trans hws3'
    have hcb_lo_rf : 0xF8 ≤ (rf.get .x5).toNat := by
      rw [hrf4x5, toNat_zx_byte]
      exact hcb_lo
    have hcb_hi_rf : (rf.get .x5).toNat ≤ 0xFF := by
      rw [hrf4x5, toNat_zx_byte]
      omega
    refine ⟨?_, hcb_lo_rf, hcb_hi_rf⟩
    · refine ⟨c, hc1, hc2, hci, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hA,
        hiff⟩
      · exact hrf4x5
      · exact (hget4 .x6 (by decide)).trans
          ((hget3 .x6 (by decide)).trans ((hget2 .x6 (by decide)).trans h6))
      · exact (hget4 .x14 (by decide)).trans
          ((hget3 .x14 (by decide)).trans ((hget2 .x14 (by decide)).trans h14))
      · exact (hget4 .x15 (by decide)).trans
          ((hget3 .x15 (by decide)).trans ((hget2 .x15 (by decide)).trans h15))
      · exact (hget4 .x16 (by decide)).trans
          ((hget3 .x16 (by decide)).trans ((hget2 .x16 (by decide)).trans h16))
      · exact (hget4 .x12 (by decide)).trans
          ((hget3 .x12 (by decide)).trans ((hget2 .x12 (by decide)).trans h12))
      · exact (hget4 .x13 (by decide)).trans
          ((hget3 .x13 (by decide)).trans ((hget2 .x13 (by decide)).trans h13))
      · rw [hws4']
        exact hslot
      · rw [hws4']
        exact hwlen


private theorem se12c_8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by
  decide
private theorem se12c_16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by
  decide
private theorem se12c_24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by
  decide
private theorem se12c_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by
  decide
private theorem se12c_n32 : signExtend12 (-32 : BitVec 12)
    = (-32 : Word) := by decide

/-- Slices inside the first 32 bytes read through a `take 32` equality. -/
private theorem slice_of_take32 (l l' : List (BitVec 8)) (k m : Nat)
    (hkm : k + m ≤ 32) (h : l.take 32 = l'.take 32) :
    (l.drop k).take m = (l'.drop k).take m := by
  have h1 : ∀ (x : List (BitVec 8)),
      ((x.take 32).drop k).take m = (x.drop k).take m := by
    intro x
    rw [List.drop_take, List.take_take]
    congr 1
    omega
  rw [← h1 l, ← h1 l', h]

/-- The three spill stores leave the `ra` slot and expose the spilled
    dwords. -/
private theorem spill_chain_slot0 (wsF n8 n16 n24 : List (BitVec 8)) :
    (setBytes (setBytes (setBytes wsF 8 n8) 16 n16) 24 n24).take 8
      = wsF.take 8 := by
  rw [setBytes_take_of_ge _ _ _ _ (by omega),
    setBytes_take_of_ge _ _ _ _ (by omega),
    setBytes_take_of_ge _ _ _ _ (by omega)]

private theorem spill_chain_slot (wsF n8 n16 n24 : List (BitVec 8))
    (h8 : n8.length = 8) (h16 : n16.length = 8) (h24 : n24.length = 8)
    (hlen : 32 ≤ wsF.length) :
    ((setBytes (setBytes (setBytes wsF 8 n8) 16 n16) 24 n24).drop 8).take 8
        = n8
    ∧ ((setBytes (setBytes (setBytes wsF 8 n8) 16 n16) 24 n24).drop 16).take 8
        = n16
    ∧ ((setBytes (setBytes (setBytes wsF 8 n8) 16 n16) 24 n24).drop 24).take 8
        = n24 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [setBytes_drop_of_ge _ _ _ _ (by omega),
      setBytes_take_of_ge _ _ _ _ (by omega),
      setBytes_drop_of_ge _ _ _ _ (by omega),
      setBytes_take_of_ge _ _ _ _ (by omega)]
    have := setBytes_slot wsF n8 8 (by omega)
    rw [h8] at this
    exact this
  · rw [setBytes_drop_of_ge _ _ _ _ (by omega),
      setBytes_take_of_ge _ _ _ _ (by omega)]
    have h1 : (setBytes wsF 8 n8).length = wsF.length := by
      rw [length_setBytes]
    have := setBytes_slot (setBytes wsF 8 n8) n16 16 (by omega)
    rw [h16] at this
    have h0 : (16 : Nat) - 16 = 0 := by omega
    rw [setBytes_drop_of_ge _ _ _ _ (le_refl 16), h0] at this ⊢
    exact this
  · have h1 : (setBytes (setBytes wsF 8 n8) 16 n16).length = wsF.length := by
      rw [length_setBytes, length_setBytes]
    have := setBytes_slot (setBytes (setBytes wsF 8 n8) 16 n16) n24 24
      (by omega)
    rw [h24] at this
    have h0 : (24 : Nat) - 24 = 0 := by omega
    rw [setBytes_drop_of_ge _ _ _ _ (le_refl 24), h0] at this ⊢
    exact this

/-- A local copy of the call path (the `ifit`-else subtree of
    `itemCallTail`); definitionally equal to the inline subterm, so `sp`
    facts transfer by `exact`. -/
def callPath (childS : FnHandleS) : Stmt :=
  .block "spill" [.ADD .x7 .x15 .x17, .SD .x13 .x7 8,
     .SD .x13 .x16 16, .SD .x13 .x12 24, .MV .x10 .x15,
     .MV .x11 .x17, .ADDI .x13 .x13 32,
     .LI .x28 (0x1000 : Word)] ;;;
  .callRegS "child" .x28 [childS] ;;;
  .block "reload" [.ADDI .x13 .x13 (-32), .LD .x15 .x13 8,
    .LD .x16 .x13 16, .LD .x12 .x13 24] ;;;
  .ite "chst" (.beq .x10 .x0)
    (.block "chok" [.LI .x14 0])
    (.block "st_child" [.LI .x14 1, .MV .x15 .x16])

/-- The state at the call path's entry: some in-window cursor and a
    fitting item length, with the running iff. -/
def CallPre (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) (i : Nat) : Reach :=
  fun rf ws A =>
    ∃ c L : Nat,
      pStart ≤ c ∧ c < pEnd ∧ pStart + i ≤ c
      ∧ L ≤ pEnd - c
      ∧ decodeItemLength (win bs c (pEnd - c)) = some L
      ∧ ((decodeJoinedEncodingsD d (win bs c (pEnd - c))).isSome
        ↔ (decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))).isSome)
      ∧ rf.get .x15 = inBase + BitVec.ofNat 64 c
      ∧ rf.get .x16 = inBase + BitVec.ofNat 64 pEnd
      ∧ rf.get .x12 = BitVec.ofNat 64 d
      ∧ rf.get .x13 = fp
      ∧ rf.get .x17 = BitVec.ofNat 64 L
      ∧ ws.take 8 = dwordBytes v
      ∧ ws.length = 40 * d + 40
      ∧ A = A₀

/-- The spill block's engine, at known entry values. -/
private theorem spill_engine (bs : List Byte) (inBase fp : Word)
    (c L d pEnd : Nat) (rfP : RegFile) (wsP : List (BitVec 8))
    (h15 : rfP.get .x15 = inBase + BitVec.ofNat 64 c)
    (h16 : rfP.get .x16 = inBase + BitVec.ofNat 64 pEnd)
    (h12 : rfP.get .x12 = BitVec.ofNat 64 d)
    (h13 : rfP.get .x13 = fp)
    (h17 : rfP.get .x17 = BitVec.ofNat 64 L) :
    execBlock ⟨inBase, bs⟩ fp rfP wsP
      [.ADD .x7 .x15 .x17, .SD .x13 .x7 8, .SD .x13 .x16 16,
       .SD .x13 .x12 24, .MV .x10 .x15, .MV .x11 .x17,
       .ADDI .x13 .x13 32, .LI .x28 (0x1000 : Word)]
      = (((((rfP.set .x7 (inBase + BitVec.ofNat 64 c + BitVec.ofNat 64 L)).set
              .x10 (inBase + BitVec.ofNat 64 c)).set
              .x11 (BitVec.ofNat 64 L)).set
              .x13 (fp + 32)).set
              .x28 (0x1000 : Word),
          setBytes (setBytes (setBytes wsP
              8 (dwordBytes (inBase + BitVec.ofNat 64 c + BitVec.ofNat 64 L)))
              16 (dwordBytes (inBase + BitVec.ofNat 64 pEnd)))
              24 (dwordBytes (BitVec.ofNat 64 d))) := by
  have hx7v : rfP.get .x15 + rfP.get .x17
      = inBase + BitVec.ofNat 64 c + BitVec.ofNat 64 L := by
    rw [h15, h17]
  simp only [execBlock_cons, execBlock_nil]
  rw [show execInstrRF ⟨inBase, bs⟩ fp rfP wsP (.ADD .x7 .x15 .x17)
      = (rfP.set .x7 (inBase + BitVec.ofNat 64 c + BitVec.ofNat 64 L), wsP)
      from by simp only [execInstrRF, aluSem, hx7v]]
  dsimp only
  rw [execInstrRF_sd_dword _ _ _ _ .x13 .x7 (8 : BitVec 12) 8 (by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), h13, se12c_8]
    bv_omega)]
  dsimp only
  rw [execInstrRF_sd_dword _ _ _ _ .x13 .x16 (16 : BitVec 12) 16 (by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), h13, se12c_16]
    bv_omega)]
  dsimp only
  rw [execInstrRF_sd_dword _ _ _ _ .x13 .x12 (24 : BitVec 12) 24 (by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), h13, se12c_24]
    bv_omega)]
  dsimp only
  simp only [execInstrRF, aluSem]
  rw [RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide), h15,
    RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide), h17,
    RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide), h13, se12c_32,
    RegFile.get_set_ne _ _ _ _ (by decide), h16,
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ Reg.x7), h12]

/-- The reload block's engine, at known frame content. -/
private theorem reload_engine (bs : List Byte) (inBase fp : Word) (d : Nat)
    (rfR : RegFile) (wsR : List (BitVec 8)) (p16 p24 p32 : Word)
    (h13 : rfR.get .x13 = fp + 32)
    (hlen : wsR.length = 40 * d + 40)
    (hs8 : (wsR.drop 8).take 8 = dwordBytes p16)
    (hs16 : (wsR.drop 16).take 8 = dwordBytes p24)
    (hs24 : (wsR.drop 24).take 8 = dwordBytes p32) :
    execBlock ⟨inBase, bs⟩ fp rfR wsR
      [.ADDI .x13 .x13 (-32), .LD .x15 .x13 8, .LD .x16 .x13 16,
       .LD .x12 .x13 24]
      = ((((rfR.set .x13 fp).set .x15 p16).set .x16 p24).set .x12 p32,
         wsR) := by
  have h13' : rfR.get .x13 + signExtend12 (-32 : BitVec 12) = fp := by
    rw [h13, se12c_n32]
    bv_omega
  simp only [execBlock_cons, execBlock_nil]
  rw [show execInstrRF ⟨inBase, bs⟩ fp rfR wsR (.ADDI .x13 .x13 (-32))
      = (rfR.set .x13 fp, wsR) from by
    simp only [execInstrRF, aluSem, h13']]
  dsimp only
  rw [execInstrRF_ld_dword _ _ _ _ .x15 .x13 (8 : BitVec 12) 8 p16 (by
      rw [RegFile.get_set_self _ _ _ (by decide), se12c_8]
      bv_omega)
    (by omega)
    (by rw [hs8, packBytes_dwordBytes])]
  dsimp only
  rw [execInstrRF_ld_dword _ _ _ _ .x16 .x13 (16 : BitVec 12) 16 p24 (by
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide), se12c_16]
      bv_omega)
    (by omega)
    (by rw [hs16, packBytes_dwordBytes])]
  dsimp only
  rw [execInstrRF_ld_dword _ _ _ _ .x12 .x13 (24 : BitVec 12) 24 p32 (by
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide), se12c_24]
      bv_omega)
    (by omega)
    (by rw [hs24, packBytes_dwordBytes])]

/-- The call path carries `CallPre` to the stepped invariant. -/
theorem call_path_sp (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) (childS : FnHandleS)
    (i : Nat)
    (Lay : RdLayout inBase bs fp (40 * d + 40))
    (hq : pEnd ≤ bs.length)
    (hcE : childS.entry = decEntry)
    (hcPre : ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        decPreS bs inBase d (fp + 32) rf ws A → childS.pre rf ws A)
    (hcPost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8))
        (A₁ : Assertion) (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        childS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x10 = decStatus bs (offOf inBase rf₁) (lenOf rf₁) d
          ∧ rf.get .x13 = fp + 32
          ∧ ws.take 32 = ws₁.take 32
          ∧ A = A₁) :
    ∀ rf' ws' A', Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp) (callPath childS)
        (CallPre bs inBase d fp pStart pEnd v A₀ i) rf' ws' A'
      → decInv bs inBase d fp pStart pEnd v A₀ (i + 1) rf' ws' A' := by
  intro rf' ws' A' hsp
  have hb : inBase.toNat + bs.length < 2 ^ 64 := Lay.regWf.2.1
  -- shared prefix: destructure down to the spill entry, both chst arms
  rcases hsp with harm | harm
  all_goals (
    obtain ⟨rfC, wsC, hlenC, ⟨hR3, hchst⟩, hrf', hws'⟩ := harm
    obtain ⟨rf₂, ws₂, hlen₂, hR2, hrfC, hwsC⟩ := hR3
    obtain ⟨rf₁, ws₁, A₁, hspill, hmem⟩ := hR2
    obtain ⟨h, hhm, hx28e, hhpre, hhpost⟩ := hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hhm
    subst hhm
    obtain ⟨rfP, wsP, hlenP, hPre, hrf₁, hws₁⟩ := hspill
    obtain ⟨c, L, hc1, hc2, hci, hLfit, hL, hiff, p15, p16, p12, p13, p17,
      pslot, plen, pA⟩ := hPre
    have hL64 : L < 2 ^ 64 := by omega
    rw [show (itemsRw d fp).base = fp from rfl] at hrf₁ hws₁ hrfC hwsC
    have hsengine := spill_engine bs inBase fp c L d pEnd rfP wsP
      p15 p16 p12 p13 p17
    rw [hsengine] at hrf₁ hws₁
    dsimp only at hrf₁ hws₁
    have hx10₁ : rf₁.get .x10 = inBase + BitVec.ofNat 64 c := by
      rw [hrf₁]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
    have hx11₁ : rf₁.get .x11 = BitVec.ofNat 64 L := by
      rw [hrf₁]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
    have hpost := hcPost rf₁ ws₁ A₁ rf₂ ws₂ A' hhpost
    obtain ⟨hst₂, hx13₂, htake₂, hA₂⟩ := hpost
    have hoffOf : offOf inBase rf₁ = c := by
      unfold offOf
      rw [hx10₁]
      exact idxOf_add inBase c bs.length (by omega) hb
    have hlenOf : lenOf rf₁ = L := by
      unfold lenOf
      rw [hx11₁, BitVec.toNat_ofNat]
      omega
    rw [hoffOf, hlenOf] at hst₂
    -- window facts after the child call
    have hws32 : 32 ≤ wsP.length := by
      rw [plen]
      omega
    have hchain := spill_chain_slot wsP
      (dwordBytes (inBase + BitVec.ofNat 64 c + BitVec.ofNat 64 L))
      (dwordBytes (inBase + BitVec.ofNat 64 pEnd))
      (dwordBytes (BitVec.ofNat 64 d))
      (length_dwordBytes _) (length_dwordBytes _) (length_dwordBytes _)
      hws32
    have hs8₂ : (ws₂.drop 8).take 8
        = dwordBytes (inBase + BitVec.ofNat 64 c + BitVec.ofNat 64 L) := by
      rw [slice_of_take32 ws₂ ws₁ 8 8 (by omega) htake₂, hws₁]
      exact hchain.1
    have hs16₂ : (ws₂.drop 16).take 8
        = dwordBytes (inBase + BitVec.ofNat 64 pEnd) := by
      rw [slice_of_take32 ws₂ ws₁ 16 8 (by omega) htake₂, hws₁]
      exact hchain.2.1
    have hs24₂ : (ws₂.drop 24).take 8 = dwordBytes (BitVec.ofNat 64 d) := by
      rw [slice_of_take32 ws₂ ws₁ 24 8 (by omega) htake₂, hws₁]
      exact hchain.2.2
    have hlen₂' : ws₂.length = 40 * d + 40 := hlen₂
    have hrengine := reload_engine bs inBase fp d rf₂ ws₂
      (inBase + BitVec.ofNat 64 c + BitVec.ofNat 64 L)
      (inBase + BitVec.ofNat 64 pEnd) (BitVec.ofNat 64 d)
      hx13₂ hlen₂' hs8₂ hs16₂ hs24₂
    rw [hrengine] at hrfC hwsC
    dsimp only at hrfC hwsC
    have hx10C : rfC.get .x10 = decStatus bs c L d := by
      rw [hrfC]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hst₂
    have hslotC : wsC.take 8 = dwordBytes v := by
      rw [hwsC]
      have h00 := slice_of_take32 ws₂ ws₁ 0 8 (by omega) htake₂
      simp only [List.drop_zero] at h00
      rw [h00, hws₁]
      have h0 := spill_chain_slot0 wsP
        (dwordBytes (inBase + BitVec.ofNat 64 c + BitVec.ofNat 64 L))
        (dwordBytes (inBase + BitVec.ofNat 64 pEnd))
        (dwordBytes (BitVec.ofNat 64 d))
      rw [h0, pslot]
    have hlenval : 1 ≤ L := EvmAsm.EL.RLP.Ref.decodeItemLength_pos hL
    have hstep := EvmAsm.EL.RLP.Ref.joinedD_step_isSome (bs := bs)
      (c := c) (rem := pEnd - c) (L := L) d
      (by omega) (by omega) hL (by omega))
  case _ =>
    -- chst taken: the child accepted; advance
    have hcond0 : rfC.get .x10 = 0 := by simpa using hchst
    have hsome : (decodeD d (win bs c L)).isSome = true := by
      rw [hx10C] at hcond0
      unfold decStatus at hcond0
      by_cases hd0 : (decodeD d (win bs c L)).isSome
      · exact hd0
      · rw [if_neg hd0] at hcond0
        exact absurd hcond0 (by decide)
    subst hrf'
    have hws'' : ws' = wsC := hws'
    have hrest : (decodeJoinedEncodingsD d
        (win bs (c + L) (pEnd - c - L))).isSome
        ↔ (decodeJoinedEncodingsD d (win bs c (pEnd - c))).isSome := by
      rw [hstep]
      constructor
      · intro hr
        exact ⟨hsome, hr⟩
      · rintro ⟨-, hr⟩
        exact hr
    have hiff' : (decodeJoinedEncodingsD d
        (win bs (c + L) (pEnd - (c + L)))).isSome
        ↔ (decodeJoinedEncodingsD d
            (win bs pStart (pEnd - pStart))).isSome := by
      rw [show pEnd - (c + L) = pEnd - c - L from by omega]
      exact hrest.trans hiff
    refine ⟨c + L, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inl ⟨?_, hiff'⟩⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide), hrfC]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
      bv_omega
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide), hrfC]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide), hrfC]
      simp only [RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide), hrfC]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · rw [hws'']
      exact hslotC
    · rw [hws'', hwsC]
      exact hlen₂'
    · rw [hA₂, pA]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
  case _ =>
    -- chst not taken: the child rejected; poison
    have hcond1 : rfC.get .x10 ≠ 0 := by
      intro h0
      exact hchst (by simpa using h0)
    have hnone : decodeD d (win bs c L) = none := by
      rw [hx10C] at hcond1
      unfold decStatus at hcond1
      by_cases hd0 : (decodeD d (win bs c L)).isSome
      · rw [if_pos hd0] at hcond1
        exact absurd rfl hcond1
      · exact Option.not_isSome_iff_eq_none.mp hd0
    have hremnone := EvmAsm.EL.RLP.Ref.joinedD_head_none (bs := bs)
      (c := c) (rem := pEnd - c) (L := L) d
      (by omega) (by omega) hL (by omega) hnone
    have hfull : decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))
        = none := by
      rcases hopt : decodeJoinedEncodingsD d
          (win bs pStart (pEnd - pStart)) with _ | val
      · rfl
      · exfalso
        have h2 := hiff.mpr (by rw [hopt]; rfl)
        rw [hremnone] at h2
        exact Bool.noConfusion h2
    subst hrf'
    have hws'' : ws' = wsC := hws'
    refine ⟨pEnd, by omega, le_refl _, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inr ⟨?_, hfull, rfl⟩⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hrfC]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hrfC]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hrfC]
      simp only [RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hrfC]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · rw [hws'']
      exact hslotC
    · rw [hws'', hwsC]
      exact hlen₂'
    · rw [hA₂, pA]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]

/-- The call half of one iteration: fit check, recursive decode, advance. -/
theorem calltail_sp (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) (childS : FnHandleS)
    (i : Nat)
    (Lay : RdLayout inBase bs fp (40 * d + 40))
    (hq : pEnd ≤ bs.length)
    (hcE : childS.entry = decEntry)
    (hcPre : ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        decPreS bs inBase d (fp + 32) rf ws A → childS.pre rf ws A)
    (hcPost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8))
        (A₁ : Assertion) (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        childS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x10 = decStatus bs (offOf inBase rf₁) (lenOf rf₁) d
          ∧ rf.get .x13 = fp + 32
          ∧ ws.take 32 = ws₁.take 32
          ∧ A = A₁) :
    ∀ rf' ws' A', Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp) (itemCallTail childS)
        (CascadeOut bs inBase d fp pStart pEnd v A₀ i) rf' ws' A'
      → decInv bs inBase d fp pStart pEnd v A₀ (i + 1) rf' ws' A' := by
  intro rf' ws' A' hsp
  have hb : inBase.toNat + bs.length < 2 ^ 64 := Lay.regWf.2.1
  rcases hsp with htk | hntk
  case _ =>
    rcases htk with hunfit | hcall
    case _ =>
      -- ifit taken: rem < L, the item does not fit: reject
      obtain ⟨rfU, wsU, hlenU, ⟨hspF, hcondU⟩, hrf'U, hws'U⟩ := hunfit
      obtain ⟨rfF, wsF, hlenF, ⟨⟨c, hc1, hc2, hci, h16, h12, h13, hslot,
        hwlen, hA, hdisj⟩, hpz⟩, hrfU, hwsU⟩ := hspF
      have hx14F : rfF.get .x14 = 0 := by simpa using hpz
      rcases hdisj with ⟨-, h15, hiff, LL, h17, hL, hL64⟩ | ⟨h1, -, -⟩
      case _ =>
        -- register values after fit0
        have h6U : rfU.get .x6 = BitVec.ofNat 64 (pEnd - c) := by
          rw [hrfU]
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          rw [RegFile.get_set_self _ _ _ (by decide), h16, h15]
          bv_omega
        have hgetU : ∀ r : Reg, r ≠ .x6 → rfU.get r = rfF.get r := by
          intro r hr
          rw [hrfU]
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          rw [RegFile.get_set_ne _ _ _ _ hr]
        have h17U : rfU.get .x17 = BitVec.ofNat 64 LL :=
          (hgetU .x17 (by decide)).trans h17
        -- the taken branch: rem < LL
        have hbig : pEnd - c < LL := by
          have hcond' : BitVec.ult (rfU.get .x6) (rfU.get .x17) = true := hcondU
          rw [h6U, h17U] at hcond'
          simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hcond'
          omega
        have hnone := EvmAsm.EL.RLP.Ref.joinedD_unfit d
          (show c + (pEnd - c) ≤ bs.length from by omega)
          (show 1 ≤ pEnd - c from by omega) hL hbig
        have hfull : decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))
            = none := by
          rcases hopt : decodeJoinedEncodingsD d
              (win bs pStart (pEnd - pStart)) with _ | val
          · rfl
          · exfalso
            have h2 := hiff.mpr (by rw [hopt]; rfl)
            rw [hnone] at h2
            exact Bool.noConfusion h2
        -- the st_unfit block
        have hws'' : ws' = wsF :=
          (show ws' = wsU from hws'U).trans (show wsU = wsF from hwsU)
        subst hrf'U
        refine ⟨pEnd, by omega, le_refl _, by omega, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, Or.inr ⟨?_, hfull, rfl⟩⟩
        · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          rw [RegFile.get_set_self _ _ _ (by decide),
            RegFile.get_set_ne _ _ _ _ (by decide),
            hgetU .x16 (by decide), h16]
        · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          rw [RegFile.get_set_ne _ _ _ _ (by decide),
            RegFile.get_set_ne _ _ _ _ (by decide),
            hgetU .x16 (by decide), h16]
        · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          rw [RegFile.get_set_ne _ _ _ _ (by decide),
            RegFile.get_set_ne _ _ _ _ (by decide),
            hgetU .x12 (by decide), h12]
        · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          rw [RegFile.get_set_ne _ _ _ _ (by decide),
            RegFile.get_set_ne _ _ _ _ (by decide),
            hgetU .x13 (by decide), h13]
        · rw [hws'', hslot]
        · rw [hws'', hwlen]
        · exact hA
        · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          rw [RegFile.get_set_ne _ _ _ _ (by decide),
            RegFile.get_set_self _ _ _ (by decide)]
      case _ =>
        rw [hx14F] at h1
        exact absurd h1 (by decide)
    case _ =>
      -- ifit not taken: the call path at the witnessed (c, L)
      refine call_path_sp bs inBase d fp pStart pEnd v A₀ childS i Lay hq
        hcE hcPre hcPost rf' ws' A'
        (Stmt.sp_mono ⟨inBase, bs⟩ (itemsRw d fp) (callPath childS) ?_
          rf' ws' A' hcall)
      rintro rf ws A ⟨hspF, hncondU⟩
      obtain ⟨rfF, wsF, hlenF, ⟨⟨c, hc1, hc2, hci, h16, h12, h13, hslot,
        hwlen, hA, hdisj⟩, hpz⟩, hrfU, hwsU⟩ := hspF
      have hx14F : rfF.get .x14 = 0 := by simpa using hpz
      rcases hdisj with ⟨-, h15, hiff, LL, h17, hL, hL64⟩ | ⟨h1, -, -⟩
      case _ =>
        have h6U : rf.get .x6 = BitVec.ofNat 64 (pEnd - c) := by
          rw [hrfU]
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          rw [RegFile.get_set_self _ _ _ (by decide), h16, h15]
          bv_omega
        have hgetU : ∀ r : Reg, r ≠ .x6 → rf.get r = rfF.get r := by
          intro r hr
          rw [hrfU]
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          rw [RegFile.get_set_ne _ _ _ _ hr]
        have h17U : rf.get .x17 = BitVec.ofNat 64 LL :=
          (hgetU .x17 (by decide)).trans h17
        have hfit : LL ≤ pEnd - c := by
          by_contra hgt
          apply hncondU
          show BitVec.ult (rf.get .x6) (rf.get .x17) = true
          rw [h6U, h17U]
          simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
          omega
        exact ⟨c, LL, hc1, hc2, hci, hfit, hL, hiff,
          (hgetU .x15 (by decide)).trans h15, (hgetU .x16 (by decide)).trans h16,
          (hgetU .x12 (by decide)).trans h12, (hgetU .x13 (by decide)).trans h13,
          h17U, hwsU ▸ hslot, hwsU ▸ hwlen, hA⟩
      case _ =>
        rw [hx14F] at h1
        exact absurd h1 (by decide)
  case _ =>
    -- pz not taken: the cascade poisoned; pass through
    obtain ⟨rfN, wsN, hlenN, ⟨⟨c, hc1, hc2, hci, h16, h12, h13, hslot,
      hwlen, hA, hdisj⟩, hnpz⟩, hrfN, hwsN⟩ := hntk
    have hx14 : rfN.get .x14 ≠ 0 := by
      intro h0
      exact hnpz (by simpa using h0)
    rcases hdisj with ⟨h0, -, -, -⟩ | ⟨h1, h15, hnone⟩
    case _ => exact absurd h0 hx14
    case _ =>
      have hrf' : rf' = rfN := hrfN
      have hws' : ws' = wsN := hwsN
      subst hrf' hws'
      exact ⟨pEnd, by omega, le_refl _, by omega, h15, h16, h12, h13, hslot,
        hwlen, hA, Or.inr ⟨h1, hnone, rfl⟩⟩

/-- One loop iteration preserves the invariant (the `inv_step` obligation of
    `itemsFnV'_spec`). -/
theorem itemsStep (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) (beS childS : FnHandleS)
    (i : Nat)
    (L : RdLayout inBase bs fp (40 * d + 40))
    (hq : pEnd ≤ bs.length)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁)
    (hcE : childS.entry = decEntry)
    (hcPre : ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        decPreS bs inBase d (fp + 32) rf ws A → childS.pre rf ws A)
    (hcPost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8))
        (A₁ : Assertion) (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        childS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x10 = decStatus bs (offOf inBase rf₁) (lenOf rf₁) d
          ∧ rf.get .x13 = fp + 32
          ∧ ws.take 32 = ws₁.take 32
          ∧ A = A₁) :
    ∀ rf' ws' A', Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp)
        (itemsBodyStmt beS childS)
        (fun rf ws A => decInv bs inBase d fp pStart pEnd v A₀ i rf ws A
          ∧ (Cond.bltu .x15 .x16).holds rf) rf' ws' A'
      → decInv bs inBase d fp pStart pEnd v A₀ (i + 1) rf' ws' A' := by
  intro rf' ws' A' hsp
  have hsp' : Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp) (itemCallTail childS)
      (Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp) (itemLenCascade beS)
        (fun rf ws A => decInv bs inBase d fp pStart pEnd v A₀ i rf ws A
          ∧ (Cond.bltu .x15 .x16).holds rf)) rf' ws' A' := hsp
  exact calltail_sp bs inBase d fp pStart pEnd v A₀ childS i L hq hcE hcPre
    hcPost rf' ws' A'
    (Stmt.sp_mono ⟨inBase, bs⟩ (itemsRw d fp) (itemCallTail childS)
      (cascade_sp bs inBase d fp pStart pEnd v A₀ beS i L hq hbePost)
      rf' ws' A' hsp')

end RecDecode
end SAsm
end EvmAsm.Rv64
