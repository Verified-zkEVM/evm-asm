/-
  Verified byte-identical SAsm port of `hp_encode_nibbles`.

  The source nibble buffer is read-only and the encoded destination window is
  the sole writable region.  The semantic functions below deliberately model
  the emitted shifts, ORs, and byte truncations for every input byte and every
  `isLeaf` word; canonical nibble/Boolean inputs are not assumed.
-/

import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace HpEncodeNibblesSAsm

def hpOdd (len : Nat) : Nat := len % 2

def hpHeader (srcBytes : List (BitVec 8)) (len : Nat) (isLeaf : Word) : BitVec 8 :=
  let odd := BitVec.ofNat 64 (hpOdd len)
  let flags := ((isLeaf <<< 1) ||| odd) <<< 4
  let first := if hpOdd len = 1 then (srcBytes.getD 0 0).zeroExtend 64 else 0
  BitVec.truncate 8 (flags ||| first)

def hpPair (srcBytes : List (BitVec 8)) (odd i : Nat) : BitVec 8 :=
  let hi := (srcBytes.getD (odd + 2 * i) 0).zeroExtend 64 <<< 4
  let lo := (srcBytes.getD (odd + 2 * i + 1) 0).zeroExtend 64
  BitVec.truncate 8 (hi ||| lo)

def hpPrefix (srcBytes : List (BitVec 8)) (len : Nat) (isLeaf : Word) :
    Nat → List (BitVec 8)
  | 0 => [hpHeader srcBytes len isLeaf]
  | i + 1 => hpPrefix srcBytes len isLeaf i ++ [hpPair srcBytes (hpOdd len) i]

def hpEncoded (srcBytes : List (BitVec 8)) (len : Nat) (isLeaf : Word) :
    List (BitVec 8) :=
  hpPrefix srcBytes len isLeaf (len / 2)

def hpWin (srcBytes orig : List (BitVec 8)) (len : Nat) (isLeaf : Word)
    (i : Nat) : List (BitVec 8) :=
  hpPrefix srcBytes len isLeaf i ++ orig.drop (1 + i)

#guard hpEncoded [1, 2, 3, 4, 5] 5 1 = [0x31, 0x23, 0x45]
#guard hpEncoded [1, 2, 3, 4] 4 0 = [0x00, 0x12, 0x34]

theorem hpOdd_le_one (len : Nat) : hpOdd len ≤ 1 := by
  unfold hpOdd
  omega

theorem hpOdd_eq_zero_or_one (len : Nat) : hpOdd len = 0 ∨ hpOdd len = 1 := by
  have := hpOdd_le_one len
  omega

theorem hpOdd_add_twice_div (len : Nat) : hpOdd len + 2 * (len / 2) = len := by
  unfold hpOdd
  omega

theorem length_hpPrefix (srcBytes : List (BitVec 8)) (len : Nat)
    (isLeaf : Word) (i : Nat) :
    (hpPrefix srcBytes len isLeaf i).length = 1 + i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [hpPrefix, List.length_append, List.length_singleton, ih]; omega

theorem hpWin_zero (srcBytes orig : List (BitVec 8)) (len : Nat) (isLeaf : Word)
    : hpWin srcBytes orig len isLeaf 0 =
      [hpHeader srcBytes len isLeaf] ++ orig.drop 1 := by
  rfl

theorem hpWin_header (srcBytes orig : List (BitVec 8)) (len : Nat)
    (isLeaf : Word) (h_orig : orig.length = 1 + len / 2) :
    setBytes orig 0 [hpHeader srcBytes len isLeaf] =
      hpWin srcBytes orig len isLeaf 0 := by
  rw [setBytes_singleton]
  have hnonempty : 0 < orig.length := by omega
  have hcons : orig = orig[0] :: orig.drop 1 := by
    simpa using (List.drop_eq_getElem_cons (l := orig) (i := 0) hnonempty)
  rw [hcons]
  rfl

theorem length_hpWin (srcBytes orig : List (BitVec 8)) (len : Nat)
    (isLeaf : Word) (i : Nat) (h_orig : orig.length = 1 + len / 2)
    (h_i : i ≤ len / 2) :
    (hpWin srcBytes orig len isLeaf i).length = 1 + len / 2 := by
  simp only [hpWin, List.length_append, length_hpPrefix, List.length_drop, h_orig]
  omega

theorem hpWin_step (srcBytes orig : List (BitVec 8)) (len : Nat)
    (isLeaf : Word) (i : Nat) (h_orig : orig.length = 1 + len / 2)
    (h_i : i < len / 2) :
    setBytes (hpWin srcBytes orig len isLeaf i) (1 + i)
      [hpPair srcBytes (hpOdd len) i] = hpWin srcBytes orig len isLeaf (i + 1) := by
  rw [setBytes_singleton]
  unfold hpWin
  have hpre : (hpPrefix srcBytes len isLeaf i).length = 1 + i :=
    length_hpPrefix _ _ _ _
  have hdrop : orig.drop (1 + i) = orig[1 + i] :: orig.drop (1 + (i + 1)) :=
    List.drop_eq_getElem_cons (by omega)
  rw [hdrop]
  simp only [hpre, List.set_append_right, Nat.le_refl, Nat.sub_self,
    List.set_cons_zero, hpPrefix, List.append_assoc, List.singleton_append]

theorem hpWin_done (srcBytes orig : List (BitVec 8)) (len : Nat)
    (isLeaf : Word) (h_orig : orig.length = 1 + len / 2) :
    hpWin srcBytes orig len isLeaf (len / 2) = hpEncoded srcBytes len isLeaf := by
  unfold hpWin hpEncoded
  rw [List.drop_eq_nil_of_le (by omega), List.append_nil]

def hpInitBlock : List Instr :=
  [.ANDI .x5 .x11 1, .MV .x6 .x13, .SLLI .x7 .x12 1,
   .OR .x7 .x7 .x5, .SLLI .x7 .x7 4]

def hpOddBlock : List Instr :=
  [.LBU .x28 .x10 0, .OR .x7 .x7 .x28, .SB .x6 .x7 0,
   .ADDI .x6 .x6 1, .ADDI .x10 .x10 1, .ADDI .x11 .x11 (-1 : BitVec 12)]

def hpEvenBlock : List Instr :=
  [.SB .x6 .x7 0, .ADDI .x6 .x6 1]

def hpPairBlock : List Instr :=
  [.LBU .x28 .x10 0, .SLLI .x28 .x28 4, .LBU .x29 .x10 1,
   .OR .x28 .x28 .x29, .SB .x6 .x28 0, .ADDI .x6 .x6 1,
   .ADDI .x10 .x10 2, .ADDI .x11 .x11 (-2 : BitVec 12)]

def hpPairsInv (src dst : Word) (len : Nat) (isLeaf : Word)
    (srcBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    rf.get .x5 = BitVec.ofNat 64 (hpOdd len) ∧
    rf.get .x6 = dst + BitVec.ofNat 64 (1 + i) ∧
    rf.get .x10 = src + BitVec.ofNat 64 (hpOdd len + 2 * i) ∧
    rf.get .x11 = BitVec.ofNat 64 (len - hpOdd len - 2 * i) ∧
    rf.get .x12 = isLeaf ∧ rf.get .x13 = dst ∧
    i ≤ len / 2 ∧ len ≤ srcBytes.length ∧ orig.length = 1 + len / 2 ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + 1 + len / 2 < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + 1 + len / 2 ≤ src.toNat) ∧
    ws = hpWin srcBytes orig len isLeaf i ∧ A = empAssertion

def hpEncodeNibblesBody (src dst : Word) (len : Nat) (isLeaf : Word)
    (srcBytes orig : List (BitVec 8)) : Stmt :=
  .block "init" hpInitBlock ;;;
  .ite "header" (.bne .x5 .x0)
    (.block "odd" hpOddBlock) (.block "even" hpEvenBlock) ;;;
  .«while» "pairs" (.bne .x11 .x0) (len / 2)
    (hpPairsInv src dst len isLeaf srcBytes orig)
    (.block "pair" hpPairBlock) ;;;
  .block "done" [.SUB .x10 .x6 .x13]

def hpEncodeNibblesFn (src dst : Word) (len : Nat) (isLeaf : Word)
    (srcBytes orig : List (BitVec 8)) : Fn where
  name := "hpEncodeNibbles"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 1 + len / 2⟩
  pre := fun rf ws A =>
    rf.get .x10 = src ∧ rf.get .x11 = BitVec.ofNat 64 len ∧
    rf.get .x12 = isLeaf ∧ rf.get .x13 = dst ∧ ws = orig ∧
    len ≤ srcBytes.length ∧ orig.length = 1 + len / 2 ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + 1 + len / 2 < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + 1 + len / 2 ≤ src.toNat) ∧
    A = empAssertion
  post := fun rf ws A =>
    rf.get .x10 = BitVec.ofNat 64 (1 + len / 2) ∧
    ws = hpEncoded srcBytes len isLeaf ∧ A = empAssertion
  body := hpEncodeNibblesBody src dst len isLeaf srcBytes orig

#guard GuestAddrs.hp_encode_nibbles = 0x800045b8

#guard (hpEncodeNibblesBody 0 0 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0] =
  hpEncodeNibbles_prog

theorem hpParity_word (len : Nat) :
    (BitVec.ofNat 64 len &&& (1 : Word)) = BitVec.ofNat 64 (hpOdd len) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow]
  simp
  symm
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (hpOdd_le_one len) (by omega)

/-- An `LBU` outside the writable output window reads the source region. -/
theorem execInstrRF_lbu_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs) =
      (rf.set rd ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

theorem source_miss (src dst : Word) (len outLen k : Nat)
    (ws : List (BitVec 8)) (h_k : k < len)
    (h_src : src.toNat + len < 2 ^ 64)
    (h_dst : dst.toNat + outLen < 2 ^ 64)
    (h_disj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + outLen ≤ src.toNat)
    (h_ws : ws.length = outLen) :
    ¬ inRw dst ws (src + BitVec.ofNat 64 k) 1 := by
  unfold inRw
  rw [h_ws]
  have hkNat : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    omega
  have hsub : (src + BitVec.ofNat 64 k - dst).toNat =
      (src.toNat + k + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, hkNat]
    congr 1
    omega
  rw [hsub]
  rcases h_disj with hd | hd <;> omega

def initRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x5 (rf.get .x11 &&& signExtend12 (1 : BitVec 12))
  let r2 := r1.set .x6 (r1.get .x13)
  let r3 := r2.set .x7 (r2.get .x12 <<< 1)
  let r4 := r3.set .x7 (r3.get .x7 ||| r3.get .x5)
  r4.set .x7 (r4.get .x7 <<< 4)

theorem exec_init (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) :
    execBlock ro rwBase rf ws hpInitBlock = (initRf rf, ws) := by
  rfl

theorem initRf_get_x5 (rf : RegFile) :
    (initRf rf).get .x5 = rf.get .x11 &&& signExtend12 (1 : BitVec 12) := by
  unfold initRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem initRf_get_x6 (rf : RegFile) : (initRf rf).get .x6 = rf.get .x13 := by
  unfold initRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem initRf_get_x7 (rf : RegFile) :
    (initRf rf).get .x7 =
      ((rf.get .x12 <<< 1) ||| (rf.get .x11 &&& signExtend12 (1 : BitVec 12))) <<< 4 := by
  unfold initRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem initRf_get_x10 (rf : RegFile) : (initRf rf).get .x10 = rf.get .x10 := by
  unfold initRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem initRf_get_x11 (rf : RegFile) : (initRf rf).get .x11 = rf.get .x11 := by
  unfold initRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem initRf_get_x12 (rf : RegFile) : (initRf rf).get .x12 = rf.get .x12 := by
  unfold initRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem initRf_get_x13 (rf : RegFile) : (initRf rf).get .x13 = rf.get .x13 := by
  unfold initRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

def oddRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r1 := rf.set .x28 (b.zeroExtend 64)
  let r2 := r1.set .x7 (r1.get .x7 ||| r1.get .x28)
  let r3 := r2.set .x6 (r2.get .x6 + signExtend12 (1 : BitVec 12))
  let r4 := r3.set .x10 (r3.get .x10 + signExtend12 (1 : BitVec 12))
  r4.set .x11 (r4.get .x11 + signExtend12 (-1 : BitVec 12))

def evenRf (rf : RegFile) : RegFile :=
  rf.set .x6 (rf.get .x6 + signExtend12 (1 : BitVec 12))

theorem oddRf_get_x5 (rf : RegFile) (b : BitVec 8) :
    (oddRf rf b).get .x5 = rf.get .x5 := by
  unfold oddRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem oddRf_get_x6 (rf : RegFile) (b : BitVec 8) :
    (oddRf rf b).get .x6 = rf.get .x6 + signExtend12 (1 : BitVec 12) := by
  unfold oddRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem oddRf_get_x10 (rf : RegFile) (b : BitVec 8) :
    (oddRf rf b).get .x10 = rf.get .x10 + signExtend12 (1 : BitVec 12) := by
  unfold oddRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem oddRf_get_x11 (rf : RegFile) (b : BitVec 8) :
    (oddRf rf b).get .x11 = rf.get .x11 + signExtend12 (-1 : BitVec 12) := by
  unfold oddRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem oddRf_get_x12 (rf : RegFile) (b : BitVec 8) :
    (oddRf rf b).get .x12 = rf.get .x12 := by
  unfold oddRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem oddRf_get_x13 (rf : RegFile) (b : BitVec 8) :
    (oddRf rf b).get .x13 = rf.get .x13 := by
  unfold oddRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem evenRf_get_x5 (rf : RegFile) : (evenRf rf).get .x5 = rf.get .x5 := by
  unfold evenRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem evenRf_get_x6 (rf : RegFile) :
    (evenRf rf).get .x6 = rf.get .x6 + signExtend12 (1 : BitVec 12) := by
  rfl

theorem evenRf_get_x10 (rf : RegFile) : (evenRf rf).get .x10 = rf.get .x10 := by
  unfold evenRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem evenRf_get_x11 (rf : RegFile) : (evenRf rf).get .x11 = rf.get .x11 := by
  unfold evenRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem evenRf_get_x12 (rf : RegFile) : (evenRf rf).get .x12 = rf.get .x12 := by
  unfold evenRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem evenRf_get_x13 (rf : RegFile) : (evenRf rf).get .x13 = rf.get .x13 := by
  unfold evenRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem odd_header_eq (rf : RegFile) (srcBytes : List (BitVec 8)) (len : Nat)
    (isLeaf : Word) (hx11 : rf.get .x11 = BitVec.ofNat 64 len)
    (hx12 : rf.get .x12 = isLeaf) (h_odd : hpOdd len = 1) :
    BitVec.truncate 8 ((initRf rf).get .x7 ||| (srcBytes.getD 0 0).zeroExtend 64) =
      hpHeader srcBytes len isLeaf := by
  rw [initRf_get_x7, hx12, hx11]
  unfold hpHeader
  rw [if_pos h_odd]
  simp only [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide,
    hpParity_word, h_odd]

theorem even_header_eq (rf : RegFile) (srcBytes : List (BitVec 8)) (len : Nat)
    (isLeaf : Word) (hx11 : rf.get .x11 = BitVec.ofNat 64 len)
    (hx12 : rf.get .x12 = isLeaf) (h_even : hpOdd len = 0) :
    BitVec.truncate 8 ((initRf rf).get .x7) = hpHeader srcBytes len isLeaf := by
  rw [initRf_get_x7, hx12, hx11]
  unfold hpHeader
  rw [if_neg (by omega : ¬ hpOdd len = 1)]
  simp only [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide,
    hpParity_word, h_even]
  simp

theorem odd_engine (src dst : Word) (len : Nat) (isLeaf : Word)
    (srcBytes ws : List (BitVec 8)) (rf : RegFile)
    (hx10 : rf.get .x10 = src) (hx11 : rf.get .x11 = BitVec.ofNat 64 len)
    (hx12 : rf.get .x12 = isLeaf) (hx13 : rf.get .x13 = dst)
    (h_odd : hpOdd len = 1) (h_src : src.toNat + len < 2 ^ 64)
    (h_dst : dst.toNat + 1 + len / 2 < 2 ^ 64)
    (h_disj : src.toNat + len ≤ dst.toNat ∨
      dst.toNat + 1 + len / 2 ≤ src.toNat)
    (h_ws : ws.length = 1 + len / 2) :
    execBlock ⟨src, srcBytes⟩ dst (initRf rf) ws hpOddBlock =
      (oddRf (initRf rf) (srcBytes.getD 0 0),
        setBytes ws 0 [hpHeader srcBytes len isLeaf]) := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hload : (initRf rf).get .x10 + signExtend12 (0 : BitVec 12) = src := by
    rw [initRf_get_x10, hx10, hse0]
    simp
  have hmiss : ¬ inRw dst ws ((initRf rf).get .x10 + signExtend12 0) 1 := by
    rw [hload]
    unfold inRw
    rw [h_ws]
    have hpos : 0 < len := by
      unfold hpOdd at h_odd
      omega
    have hout : 1 + len / 2 ≤ len := by omega
    have hsub : (src - dst).toNat =
        (src.toNat + 0 + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub]
      congr 1
      omega
    rw [hsub]
    rcases h_disj with hd | hd
    · omega
    · omega
  have hbyte : (Region.byteAt ⟨src, srcBytes⟩
      ((initRf rf).get .x10 + signExtend12 0)) = srcBytes.getD 0 0 := by
    rw [hload]
    simp [Region.byteAt]
  have hstore : ((initRf rf).get .x6 + signExtend12 0 - dst).toNat = 0 := by
    rw [initRf_get_x6, hx13, hse0]
    simp
  rw [show hpOddBlock = [.LBU .x28 .x10 0, .OR .x7 .x7 .x28,
    .SB .x6 .x7 0, .ADDI .x6 .x6 1, .ADDI .x10 .x10 1,
    .ADDI .x11 .x11 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ _ _ _ hmiss, hbyte]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 0 (by
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hstore)]
  repeat' first | rw [execBlock_cons] | dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  apply Prod.ext
  · change oddRf (initRf rf) (srcBytes.getD 0 0) = _
    rfl
  · change setBytes ws 0
      [BitVec.truncate 8 ((initRf rf).get .x7 ||| (srcBytes.getD 0 0).zeroExtend 64)] = _
    rw [odd_header_eq rf srcBytes len isLeaf hx11 hx12 h_odd]

theorem even_engine (src dst : Word) (len : Nat) (isLeaf : Word)
    (srcBytes ws : List (BitVec 8)) (rf : RegFile)
    (hx11 : rf.get .x11 = BitVec.ofNat 64 len)
    (hx12 : rf.get .x12 = isLeaf) (hx13 : rf.get .x13 = dst)
    (h_even : hpOdd len = 0) :
    execBlock ⟨src, srcBytes⟩ dst (initRf rf) ws hpEvenBlock =
      (evenRf (initRf rf), setBytes ws 0 [hpHeader srcBytes len isLeaf]) := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hstore : ((initRf rf).get .x6 + signExtend12 0 - dst).toNat = 0 := by
    rw [initRf_get_x6, hx13, hse0]
    simp
  rw [show hpEvenBlock = [.SB .x6 .x7 0, .ADDI .x6 .x6 1] from rfl]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 0 hstore]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  apply Prod.ext
  · change evenRf (initRf rf) = _
    rfl
  · change setBytes ws 0 [BitVec.truncate 8 ((initRf rf).get .x7)] = _
    rw [even_header_eq rf srcBytes len isLeaf hx11 hx12 h_even]

def pairRf (rf : RegFile) (hi lo : BitVec 8) : RegFile :=
  let r1 := rf.set .x28 (hi.zeroExtend 64)
  let r2 := r1.set .x28 (r1.get .x28 <<< 4)
  let r3 := r2.set .x29 (lo.zeroExtend 64)
  let r4 := r3.set .x28 (r3.get .x28 ||| r3.get .x29)
  let r5 := r4.set .x6 (r4.get .x6 + signExtend12 (1 : BitVec 12))
  let r6 := r5.set .x10 (r5.get .x10 + signExtend12 (2 : BitVec 12))
  r6.set .x11 (r6.get .x11 + signExtend12 (-2 : BitVec 12))

theorem pairRf_get_x6 (rf : RegFile) (hi lo : BitVec 8) :
    (pairRf rf hi lo).get .x6 = rf.get .x6 + signExtend12 (1 : BitVec 12) := by
  unfold pairRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem pairRf_get_x10 (rf : RegFile) (hi lo : BitVec 8) :
    (pairRf rf hi lo).get .x10 = rf.get .x10 + signExtend12 (2 : BitVec 12) := by
  unfold pairRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem pairRf_get_x11 (rf : RegFile) (hi lo : BitVec 8) :
    (pairRf rf hi lo).get .x11 = rf.get .x11 + signExtend12 (-2 : BitVec 12) := by
  unfold pairRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem pairRf_get_x5 (rf : RegFile) (hi lo : BitVec 8) :
    (pairRf rf hi lo).get .x5 = rf.get .x5 := by
  unfold pairRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem pairRf_get_x12 (rf : RegFile) (hi lo : BitVec 8) :
    (pairRf rf hi lo).get .x12 = rf.get .x12 := by
  unfold pairRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem pairRf_get_x13 (rf : RegFile) (hi lo : BitVec 8) :
    (pairRf rf hi lo).get .x13 = rf.get .x13 := by
  unfold pairRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem pair_engine (src dst : Word) (len i : Nat) (srcBytes ws : List (BitVec 8))
    (rf : RegFile)
    (hx6 : rf.get .x6 = dst + BitVec.ofNat 64 (1 + i))
    (hx10 : rf.get .x10 = src + BitVec.ofNat 64 (hpOdd len + 2 * i))
    (h_i : i < len / 2) (h_src : src.toNat + len < 2 ^ 64)
    (h_dst : dst.toNat + 1 + len / 2 < 2 ^ 64)
    (h_disj : src.toNat + len ≤ dst.toNat ∨
      dst.toNat + 1 + len / 2 ≤ src.toNat)
    (h_ws : ws.length = 1 + len / 2) :
    execBlock ⟨src, srcBytes⟩ dst rf ws hpPairBlock =
      (pairRf rf (srcBytes.getD (hpOdd len + 2 * i) 0)
        (srcBytes.getD (hpOdd len + 2 * i + 1) 0),
       setBytes ws (1 + i) [hpPair srcBytes (hpOdd len) i]) := by
  let k := hpOdd len + 2 * i
  have hk : k + 1 < len := by
    dsimp only [k]
    have hp := hpOdd_add_twice_div len
    omega
  have hk0 : k < len := by omega
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hkNat : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    omega
  have hload0 : rf.get .x10 + signExtend12 0 = src + BitVec.ofNat 64 k := by
    rw [hx10, hse0]
    dsimp only [k]
    simp
  have hload1 : rf.get .x10 + signExtend12 1 = src + BitVec.ofNat 64 (k + 1) := by
    rw [hx10, hse1]
    dsimp only [k]
    bv_omega
  have hdst' : dst.toNat + (1 + len / 2) < 2 ^ 64 := by omega
  have hdisj' : src.toNat + len ≤ dst.toNat ∨
      dst.toNat + (1 + len / 2) ≤ src.toNat := by
    simpa only [Nat.add_assoc] using h_disj
  have hmiss0 : ¬ inRw dst ws (rf.get .x10 + signExtend12 0) 1 := by
    rw [hload0]
    exact source_miss src dst len (1 + len / 2) k ws hk0 h_src hdst' hdisj' h_ws
  have hmiss1 : ¬ inRw dst ws (rf.get .x10 + signExtend12 1) 1 := by
    rw [hload1]
    exact source_miss src dst len (1 + len / 2) (k + 1) ws hk h_src hdst' hdisj' h_ws
  have hbyte0 : (Region.byteAt ⟨src, srcBytes⟩
      (rf.get .x10 + signExtend12 0)) = srcBytes.getD k 0 := by
    rw [hload0]
    show srcBytes.getD ((src + BitVec.ofNat 64 k - src).toNat) 0 = _
    rw [show (src + BitVec.ofNat 64 k - src).toNat = k by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hkNat]
      omega]
  have hk1Nat : (BitVec.ofNat 64 (k + 1)).toNat = k + 1 := by
    rw [BitVec.toNat_ofNat]
    omega
  have hbyte1 : (Region.byteAt ⟨src, srcBytes⟩
      (rf.get .x10 + signExtend12 1)) = srcBytes.getD (k + 1) 0 := by
    rw [hload1]
    show srcBytes.getD ((src + BitVec.ofNat 64 (k + 1) - src).toNat) 0 = _
    rw [show (src + BitVec.ofNat 64 (k + 1) - src).toNat = k + 1 by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hk1Nat]
      omega]
  have hstore : (rf.get .x6 + signExtend12 0 - dst).toNat = 1 + i := by
    rw [hx6, hse0]
    bv_omega
  let rf2 := (rf.set .x28 ((srcBytes.getD k 0).zeroExtend 64)).set .x28
    (((rf.set .x28 ((srcBytes.getD k 0).zeroExtend 64)).get .x28) <<< 4)
  have hbyte1' : Region.byteAt ⟨src, srcBytes⟩
      (rf2.get .x10 + signExtend12 1) = srcBytes.getD (k + 1) 0 := by
    dsimp only [rf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hbyte1
  dsimp only [rf2] at hbyte1'
  rw [show hpPairBlock = [.LBU .x28 .x10 0, .SLLI .x28 .x28 4,
    .LBU .x29 .x10 1, .OR .x28 .x28 .x29, .SB .x6 .x28 0,
    .ADDI .x6 .x6 1, .ADDI .x10 .x10 2, .ADDI .x11 .x11 (-2 : BitVec 12)]
    from rfl]
  rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ _ _ _ hmiss0, hbyte0]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  simp only [show (4 : BitVec 6).toNat = 4 by decide]
  rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ _ _ _ (by
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hmiss1), hbyte1']
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ (1 + i) (by
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hstore)]
  repeat' first | rw [execBlock_cons] | dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  apply Prod.ext
  · change pairRf rf (srcBytes.getD k 0) (srcBytes.getD (k + 1) 0) = _
    rfl
  · change setBytes ws (1 + i)
      [BitVec.truncate 8
        ((srcBytes.getD k 0).zeroExtend 64 <<< 4 |||
          (srcBytes.getD (k + 1) 0).zeroExtend 64)] = _
    rfl

theorem hpEncodeNibblesFn_spec (src dst : Word) (len : Nat) (isLeaf : Word)
    (srcBytes orig : List (BitVec 8))
    (h_src_wf : (Region.mk src srcBytes).wf)
    (h_dst_wf : RwRegion.wf ⟨dst, 1 + len / 2⟩) (base : Word) :
    (hpEncodeNibblesFn src dst len isLeaf srcBytes orig).Spec base := by
  vcgen
  case region => exact ⟨h_src_wf, h_dst_wf⟩
  case hpEncodeNibbles.header.t.odd.mem =>
    rintro rf ws A hwslen ⟨hinit, hcond⟩
    rcases hinit with ⟨rf0, ws0, -, hpre, hrf, hws⟩
    rw [exec_init] at hrf hws
    subst rf
    subst ws
    rcases hpre with ⟨hx10, hx11, hx12, hx13, rfl, hlenSrc, hlenOrig,
      hsrc, hdst, hdisj, hA⟩
    have h_odd : hpOdd len = 1 := by
      have hn : BitVec.ofNat 64 (hpOdd len) ≠ 0 := by
        simpa only [Cond.holds, RegFile.get_x0, initRf_get_x5, hx11,
          show signExtend12 (1 : BitVec 12) = (1 : Word) by decide,
          hpParity_word] using hcond
      rcases hpOdd_eq_zero_or_one len with hz | ho
      · rw [hz] at hn
        exact (hn rfl).elim
      · exact ho
    have hpos : 0 < len := by
      unfold hpOdd at h_odd
      omega
    have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
    have hload : (initRf rf0).get .x10 + signExtend12 0 =
        src + BitVec.ofNat 64 0 := by
      rw [initRf_get_x10, hx10, hse0]
      simp
    have hmiss : ¬ inRw dst ws0 ((initRf rf0).get .x10 + signExtend12 0) 1 := by
      rw [hload]
      apply source_miss src dst len (1 + len / 2) 0 ws0 hpos hsrc
      · omega
      · simpa only [Nat.add_assoc] using hdisj
      · exact hlenOrig
    have hindex : (src + BitVec.ofNat 64 0 - src).toNat = 0 := by simp
    have hstore : ((initRf rf0).get .x6 + signExtend12 0 - dst).toNat = 0 := by
      rw [initRf_get_x6, hx13, hse0]
      simp
    simp only [show (hpEncodeNibblesFn src dst len isLeaf srcBytes ws0).region =
        ⟨src, srcBytes⟩ from rfl,
      show (hpEncodeNibblesFn src dst len isLeaf srcBytes ws0).rw.base = dst from rfl,
      show hpOddBlock = [.LBU .x28 .x10 0, .OR .x7 .x7 .x28,
        .SB .x6 .x7 0, .ADDI .x6 .x6 1, .ADDI .x10 .x10 1,
        .ADDI .x11 .x11 (-1 : BitVec 12)] from rfl]
    refine ⟨?_, ?_⟩
    · simp only [loadSem]
      rw [if_neg hmiss]
      unfold Region.loadOk
      rw [hload, hindex]
      refine ⟨Nat.one_dvd _, ?_⟩
      change 1 ≤ srcBytes.length
      omega
    · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _ hmiss]
      simp only [blockVCs, execInstrRF, aluSem, storeSem, loadSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      refine ⟨trivial, ?_, trivial, trivial, ⟨trivial, trivial⟩⟩
      refine ⟨?_, Nat.one_dvd _⟩
      unfold inRw
      rw [hlenOrig, hstore]
      omega
  case hpEncodeNibbles.header.e.even.mem =>
    rintro rf ws A hwslen ⟨hinit, hcond⟩
    rcases hinit with ⟨rf0, ws0, -, hpre, hrf, hws⟩
    rw [exec_init] at hrf hws
    subst rf
    subst ws
    rcases hpre with ⟨hx10, hx11, hx12, hx13, rfl, hlenSrc, hlenOrig,
      hsrc, hdst, hdisj, hA⟩
    have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
    have hstore : ((initRf rf0).get .x6 + signExtend12 0 - dst).toNat = 0 := by
      rw [initRf_get_x6, hx13, hse0]
      simp
    simp only [show (hpEncodeNibblesFn src dst len isLeaf srcBytes ws0).region =
        ⟨src, srcBytes⟩ from rfl,
      show (hpEncodeNibblesFn src dst len isLeaf srcBytes ws0).rw.base = dst from rfl,
      show hpEvenBlock = [.SB .x6 .x7 0, .ADDI .x6 .x6 1] from rfl,
      blockVCs, storeSem, execInstrRF, aluSem]
    refine ⟨⟨?_, Nat.one_dvd _⟩, trivial, trivial⟩
    unfold inRw
    rw [hlenOrig, hstore]
    omega
  case hpEncodeNibbles.pairs.inv_init =>
    rintro rf ws A (hodd | heven)
    · rcases hodd with ⟨rfh, wsh, -, ⟨hinit, hcond⟩, hrf, hws⟩
      rcases hinit with ⟨rf0, ws0, -, hpre, hrfh, hwsh⟩
      rw [exec_init] at hrfh hwsh
      subst rfh
      subst wsh
      rcases hpre with ⟨hx10, hx11, hx12, hx13, rfl, hlenSrc, hlenOrig,
        hsrc, hdst, hdisj, hA⟩
      have h_odd : hpOdd len = 1 := by
        have hn : BitVec.ofNat 64 (hpOdd len) ≠ 0 := by
          simpa only [Cond.holds, RegFile.get_x0, initRf_get_x5, hx11,
            show signExtend12 (1 : BitVec 12) = (1 : Word) by decide,
            hpParity_word] using hcond
        rcases hpOdd_eq_zero_or_one len with hz | ho
        · rw [hz] at hn
          exact (hn rfl).elim
        · exact ho
      simp only [show (hpEncodeNibblesFn src dst len isLeaf srcBytes ws0).region =
          ⟨src, srcBytes⟩ from rfl,
        show (hpEncodeNibblesFn src dst len isLeaf srcBytes ws0).rw.base = dst from rfl]
        at hrf hws
      rw [odd_engine src dst len isLeaf srcBytes ws0 rf0 hx10 hx11 hx12 hx13
        h_odd hsrc hdst hdisj hlenOrig] at hrf hws
      subst rf
      subst ws
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, hlenSrc, hlenOrig,
        hsrc, hdst, hdisj, hpWin_header srcBytes ws0 len isLeaf hlenOrig, hA⟩
      · rw [oddRf_get_x5, initRf_get_x5, hx11,
          show signExtend12 (1 : BitVec 12) = (1 : Word) by decide,
          hpParity_word]
      · rw [oddRf_get_x6, initRf_get_x6, hx13,
          show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
        bv_omega
      · rw [oddRf_get_x10, initRf_get_x10, hx10,
          show signExtend12 (1 : BitVec 12) = (1 : Word) by decide, h_odd]
        bv_omega
      · rw [oddRf_get_x11, initRf_get_x11, hx11,
          show signExtend12 (-1 : BitVec 12) = (-1 : Word) by decide, h_odd,
          Nat.sub_zero]
        have hpos : 0 < len := by
          unfold hpOdd at h_odd
          omega
        have hlt : len < 2 ^ 64 := by omega
        bv_omega
      · rw [oddRf_get_x12, initRf_get_x12, hx12]
      · rw [oddRf_get_x13, initRf_get_x13, hx13]
    · rcases heven with ⟨rfh, wsh, -, ⟨hinit, hcond⟩, hrf, hws⟩
      rcases hinit with ⟨rf0, ws0, -, hpre, hrfh, hwsh⟩
      rw [exec_init] at hrfh hwsh
      subst rfh
      subst wsh
      rcases hpre with ⟨hx10, hx11, hx12, hx13, rfl, hlenSrc, hlenOrig,
        hsrc, hdst, hdisj, hA⟩
      have h_even : hpOdd len = 0 := by
        have hz : BitVec.ofNat 64 (hpOdd len) = 0 := by
          simpa only [Cond.holds, RegFile.get_x0, not_not, initRf_get_x5, hx11,
            show signExtend12 (1 : BitVec 12) = (1 : Word) by decide,
            hpParity_word] using hcond
        rcases hpOdd_eq_zero_or_one len with he | ho
        · exact he
        · rw [ho] at hz
          have : (1 : Word) ≠ 0 := by decide
          exact (this hz).elim
      simp only [show (hpEncodeNibblesFn src dst len isLeaf srcBytes ws0).region =
          ⟨src, srcBytes⟩ from rfl,
        show (hpEncodeNibblesFn src dst len isLeaf srcBytes ws0).rw.base = dst from rfl]
        at hrf hws
      rw [even_engine src dst len isLeaf srcBytes ws0 rf0 hx11 hx12 hx13 h_even]
        at hrf hws
      subst rf
      subst ws
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, hlenSrc, hlenOrig,
        hsrc, hdst, hdisj, hpWin_header srcBytes ws0 len isLeaf hlenOrig, hA⟩
      · rw [evenRf_get_x5, initRf_get_x5, hx11,
          show signExtend12 (1 : BitVec 12) = (1 : Word) by decide,
          hpParity_word]
      · rw [evenRf_get_x6, initRf_get_x6, hx13,
          show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
        bv_omega
      · rw [evenRf_get_x10, initRf_get_x10, hx10, h_even]
        simp
      · rw [evenRf_get_x11, initRf_get_x11, hx11, h_even]
        simp
      · rw [evenRf_get_x12, initRf_get_x12, hx12]
      · rw [evenRf_get_x13, initRf_get_x13, hx13]
  case hpEncodeNibbles.pairs.inv_step =>
    rintro i hi rf' ws' A' hsp
    rcases hsp with ⟨rf0, ws0, -, ⟨hinv, hcond⟩, hrf, hws⟩
    rcases hinv with ⟨hx5, hx6, hx10, hx11, hx12, hx13, hile, hlenSrc,
      hlenOrig, hsrc, hdst, hdisj, hwin, hA⟩
    have hwslen : ws0.length = 1 + len / 2 := by
      rw [hwin]
      exact length_hpWin srcBytes orig len isLeaf i hlenOrig (by omega)
    simp only [show (hpEncodeNibblesFn src dst len isLeaf srcBytes orig).region =
        ⟨src, srcBytes⟩ from rfl,
      show (hpEncodeNibblesFn src dst len isLeaf srcBytes orig).rw.base = dst from rfl]
      at hrf hws
    rw [pair_engine src dst len i srcBytes ws0 rf0 hx6 hx10 hi hsrc hdst hdisj hwslen]
      at hrf hws
    subst rf'
    subst ws'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, hlenSrc, hlenOrig,
      hsrc, hdst, hdisj, ?_, hA⟩
    · rw [pairRf_get_x5, hx5]
    · rw [pairRf_get_x6, hx6,
        show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
      bv_omega
    · rw [pairRf_get_x10, hx10,
        show signExtend12 (2 : BitVec 12) = (2 : Word) by decide]
      bv_omega
    · rw [pairRf_get_x11, hx11,
        show signExtend12 (-2 : BitVec 12) = (-2 : Word) by decide]
      have hk : hpOdd len + 2 * i + 1 < len := by
        have hp := hpOdd_add_twice_div len
        omega
      have hlt : len < 2 ^ 64 := by omega
      bv_omega
    · rw [pairRf_get_x12, hx12]
    · rw [pairRf_get_x13, hx13]
    · rw [hwin, hpWin_step srcBytes orig len isLeaf i hlenOrig hi]
  case hpEncodeNibbles.pairs.exhausted =>
    rintro rf ws A ⟨hx5, hx6, hx10, hx11, hx12, hx13, hile, hlenSrc,
      hlenOrig, hsrc, hdst, hdisj, hwin, hA⟩
    simp only [Cond.holds, not_not, RegFile.get_x0, hx11]
    rw [show len - hpOdd len - 2 * (len / 2) = 0 by
      have hp := hpOdd_add_twice_div len
      omega]
    rfl
  case hpEncodeNibbles.pairs.body.pair.mem =>
    rintro rf ws A hwslen ⟨i, hi, hinv, hcond⟩
    rcases hinv with ⟨hx5, hx6, hx10, hx11, hx12, hx13, hile, hlenSrc,
      hlenOrig, hsrc, hdst, hdisj, hwin, hA⟩
    change ws.length = 1 + len / 2 at hwslen
    let k := hpOdd len + 2 * i
    have hk1 : k + 1 < len := by
      dsimp only [k]
      have hp := hpOdd_add_twice_div len
      omega
    have hk0 : k < len := by omega
    have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
    have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    have hload0 : rf.get .x10 + signExtend12 0 = src + BitVec.ofNat 64 k := by
      rw [hx10, hse0]
      dsimp only [k]
      simp
    have hload1 : rf.get .x10 + signExtend12 1 = src + BitVec.ofNat 64 (k + 1) := by
      rw [hx10, hse1]
      dsimp only [k]
      bv_omega
    have hdst' : dst.toNat + (1 + len / 2) < 2 ^ 64 := by omega
    have hdisj' : src.toNat + len ≤ dst.toNat ∨
        dst.toNat + (1 + len / 2) ≤ src.toNat := by
      simpa only [Nat.add_assoc] using hdisj
    have hmiss0 : ¬ inRw dst ws (rf.get .x10 + signExtend12 0) 1 := by
      rw [hload0]
      exact source_miss src dst len (1 + len / 2) k ws hk0 hsrc hdst' hdisj' hwslen
    have hmiss1 : ¬ inRw dst ws (rf.get .x10 + signExtend12 1) 1 := by
      rw [hload1]
      exact source_miss src dst len (1 + len / 2) (k + 1) ws hk1 hsrc hdst' hdisj' hwslen
    have hmiss1raw : ¬ (rf.get .x10 + signExtend12 1 - dst).toNat + 1 ≤ ws.length := by
      simpa only [inRw] using hmiss1
    have hkNat : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat]
      omega
    have hk1Nat : (BitVec.ofNat 64 (k + 1)).toNat = k + 1 := by
      rw [BitVec.toNat_ofNat]
      omega
    have hindex0 : (src + BitVec.ofNat 64 k - src).toNat = k := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hkNat]
      omega
    have hindex1 : (src + BitVec.ofNat 64 (k + 1) - src).toNat = k + 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hk1Nat]
      omega
    have hstore : (rf.get .x6 + signExtend12 0 - dst).toNat = 1 + i := by
      rw [hx6, hse0]
      bv_omega
    simp only [show (hpEncodeNibblesFn src dst len isLeaf srcBytes orig).region =
        ⟨src, srcBytes⟩ from rfl,
      show (hpEncodeNibblesFn src dst len isLeaf srcBytes orig).rw.base = dst from rfl,
      show hpPairBlock = [.LBU .x28 .x10 0, .SLLI .x28 .x28 4,
        .LBU .x29 .x10 1, .OR .x28 .x28 .x29, .SB .x6 .x28 0,
        .ADDI .x6 .x6 1, .ADDI .x10 .x10 2, .ADDI .x11 .x11 (-2 : BitVec 12)]
        from rfl]
    refine ⟨?_, ?_⟩
    · simp only [loadSem]
      rw [if_neg hmiss0]
      unfold Region.loadOk
      rw [hload0, hindex0]
      refine ⟨Nat.one_dvd _, ?_⟩
      change k + 1 ≤ srcBytes.length
      omega
    · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _ hmiss0]
      simp only [blockVCs, execInstrRF, aluSem, loadSem, storeSem,
        RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true, show (4 : BitVec 6).toNat = 4 by decide]
      rw [if_neg hmiss1]
      refine ⟨trivial, ?_, trivial, ?_, trivial, trivial, trivial, trivial⟩
      · unfold Region.loadOk
        rw [hload1, hindex1]
        refine ⟨Nat.one_dvd _, ?_⟩
        change k + 2 ≤ srcBytes.length
        omega
      · refine ⟨?_, Nat.one_dvd _⟩
        rw [if_neg hmiss1]
        simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
        unfold inRw
        rw [hstore]
        omega
  case hpEncodeNibbles.post =>
    rintro rf ws A ⟨rf0, ws0, -, ⟨⟨i, hile, hinv⟩, hncond⟩, rfl, rfl⟩
    rcases hinv with ⟨hx5, hx6, hx10, hx11, hx12, hx13, hi_le, hlenSrc,
      hlenOrig, hsrc, hdst, hdisj, hwin, hA⟩
    have hi : i = len / 2 := by
      simp only [Cond.holds, not_not, RegFile.get_x0] at hncond
      rw [hx11] at hncond
      have hto := congrArg BitVec.toNat hncond
      rw [BitVec.toNat_ofNat] at hto
      change (len - hpOdd len - 2 * i) % 2 ^ 64 = 0 at hto
      have hp := hpOdd_add_twice_div len
      omega
    subst hi
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, hA⟩
    · rw [RegFile.get_set_self _ _ _ (by decide), hx6, hx13]
      bv_omega
    · rw [hwin, hpWin_done srcBytes orig len isLeaf hlenOrig]

#print axioms hpEncodeNibblesFn_spec

end HpEncodeNibblesSAsm

end EvmAsm.Codegen
