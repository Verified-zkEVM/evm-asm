/-
  EvmAsm.Codegen.Programs.BalValueReverseSAsm

  Verified SAsm byte-reverse loop for the BAL tuple value cell.  The
  emitted program reverses the 32-byte cell at `t2` in place using a
  bounded `while` loop; `t0` and `t1` are preserved for the surrounding
  raw outer loop in AccountTupleSequencesConsistent.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.Stmt

namespace BalValueReverseSAsm

def reverseStep (ws : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  (ws.set i (ws.getD (31 - i) 0)).set (31 - i) (ws.getD i 0)

def reverseLoopWin (w : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  w.reverse.take i ++ (w.drop i).take (32 - 2 * i) ++ w.reverse.drop (32 - i)

theorem reverseLoopWin_zero (w : List (BitVec 8)) (hw : w.length = 32) :
    reverseLoopWin w 0 = w := by
  unfold reverseLoopWin
  simp only [Nat.mul_zero, tsub_zero, List.take_zero, List.nil_append, List.drop_zero]
  rw [List.take_of_length_le (by omega),
    List.drop_eq_nil_of_le (by simp [hw])]
  simp

theorem reverseLoopWin_16_eq_reverse (w : List (BitVec 8)) :
    reverseLoopWin w 16 = w.reverse := by
  unfold reverseLoopWin
  simp only [Nat.reduceMul, Nat.reduceSub, List.take_zero, List.append_nil]
  exact List.take_append_drop 16 w.reverse

@[simp] theorem length_reverseStep (ws : List (BitVec 8)) (i : Nat) :
    (reverseStep ws i).length = ws.length := by
  simp [reverseStep]

theorem length_reverseLoopWin_of_le (w : List (BitVec 8)) (i : Nat)
    (hw : w.length = 32) (hi : i ≤ 16) :
    (reverseLoopWin w i).length = 32 := by
  unfold reverseLoopWin
  simp only [List.length_append, List.length_take, List.length_reverse, List.length_drop]
  omega

private theorem bytes32_of_length (w : List (BitVec 8)) (hw : w.length = 32) :
    ∃ b0 : BitVec 8, ∃ b1 : BitVec 8, ∃ b2 : BitVec 8, ∃ b3 : BitVec 8, ∃ b4 : BitVec 8, ∃ b5 : BitVec 8, ∃ b6 : BitVec 8, ∃ b7 : BitVec 8, ∃ b8 : BitVec 8, ∃ b9 : BitVec 8, ∃ b10 : BitVec 8, ∃ b11 : BitVec 8, ∃ b12 : BitVec 8, ∃ b13 : BitVec 8, ∃ b14 : BitVec 8, ∃ b15 : BitVec 8, ∃ b16 : BitVec 8, ∃ b17 : BitVec 8, ∃ b18 : BitVec 8, ∃ b19 : BitVec 8, ∃ b20 : BitVec 8, ∃ b21 : BitVec 8, ∃ b22 : BitVec 8, ∃ b23 : BitVec 8, ∃ b24 : BitVec 8, ∃ b25 : BitVec 8, ∃ b26 : BitVec 8, ∃ b27 : BitVec 8, ∃ b28 : BitVec 8, ∃ b29 : BitVec 8, ∃ b30 : BitVec 8, ∃ b31 : BitVec 8, w = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] := by
  cases w with
  | nil => simp only [List.length_nil] at hw; omega
  | cons b0 w =>
    cases w with
    | nil => simp only [List.length_nil, List.length_cons] at hw; omega
    | cons b1 w =>
      cases w with
      | nil => simp only [List.length_nil, List.length_cons] at hw; omega
      | cons b2 w =>
        cases w with
        | nil => simp only [List.length_nil, List.length_cons] at hw; omega
        | cons b3 w =>
          cases w with
          | nil => simp only [List.length_nil, List.length_cons] at hw; omega
          | cons b4 w =>
            cases w with
            | nil => simp only [List.length_nil, List.length_cons] at hw; omega
            | cons b5 w =>
              cases w with
              | nil => simp only [List.length_nil, List.length_cons] at hw; omega
              | cons b6 w =>
                cases w with
                | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                | cons b7 w =>
                  cases w with
                  | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                  | cons b8 w =>
                    cases w with
                    | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                    | cons b9 w =>
                      cases w with
                      | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                      | cons b10 w =>
                        cases w with
                        | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                        | cons b11 w =>
                          cases w with
                          | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                          | cons b12 w =>
                            cases w with
                            | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                            | cons b13 w =>
                              cases w with
                              | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                              | cons b14 w =>
                                cases w with
                                | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                | cons b15 w =>
                                  cases w with
                                  | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                  | cons b16 w =>
                                    cases w with
                                    | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                    | cons b17 w =>
                                      cases w with
                                      | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                      | cons b18 w =>
                                        cases w with
                                        | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                        | cons b19 w =>
                                          cases w with
                                          | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                          | cons b20 w =>
                                            cases w with
                                            | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                            | cons b21 w =>
                                              cases w with
                                              | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                              | cons b22 w =>
                                                cases w with
                                                | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                                | cons b23 w =>
                                                  cases w with
                                                  | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                                  | cons b24 w =>
                                                    cases w with
                                                    | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                                    | cons b25 w =>
                                                      cases w with
                                                      | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                                      | cons b26 w =>
                                                        cases w with
                                                        | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                                        | cons b27 w =>
                                                          cases w with
                                                          | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                                          | cons b28 w =>
                                                            cases w with
                                                            | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                                            | cons b29 w =>
                                                              cases w with
                                                              | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                                              | cons b30 w =>
                                                                cases w with
                                                                | nil => simp only [List.length_nil, List.length_cons] at hw; omega
                                                                | cons b31 w =>
                                                                  cases w with
                                                                  | nil =>
                                                                    simp only [List.length_nil, List.length_cons] at hw
                                                                    exact ⟨b0, ⟨b1, ⟨b2, ⟨b3, ⟨b4, ⟨b5, ⟨b6, ⟨b7, ⟨b8, ⟨b9, ⟨b10, ⟨b11, ⟨b12, ⟨b13, ⟨b14, ⟨b15, ⟨b16, ⟨b17, ⟨b18, ⟨b19, ⟨b20, ⟨b21, ⟨b22, ⟨b23, ⟨b24, ⟨b25, ⟨b26, ⟨b27, ⟨b28, ⟨b29, ⟨b30, ⟨b31, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
                                                                  | cons _ _ => simp only [List.length_cons] at hw; omega

theorem reverseLoopWin_step (w : List (BitVec 8)) (i : Nat)
    (hw : w.length = 32) (hi : i < 16) :
    reverseStep (reverseLoopWin w i) i = reverseLoopWin w (i + 1) := by
  interval_cases i <;>
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
      b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, rfl⟩ := bytes32_of_length w hw <;>
    rfl

#guard reverseLoopWin ([0, 1, 2, 3, 4, 5, 6, 7] : List (BitVec 8)) 0 =
  [0, 1, 2, 3, 4, 5, 6, 7]

#guard reverseLoopWin (List.range 32 |>.map (fun n => BitVec.ofNat 8 n)) 16 =
  (List.range 32 |>.map (fun n => BitVec.ofNat 8 n)).reverse

#guard reverseStep (List.range 32 |>.map (fun n => BitVec.ofNat 8 n)) 0 =
  [31, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 0]

def balValueReverseSwapBlock : List Instr :=
  [.LBU .x31 .x28 0,
   .LBU .x30 .x29 0,
   .SB .x28 .x30 0,
   .SB .x29 .x31 0]

def balValueReverseBumpBlock : List Instr :=
  [.ADDI .x28 .x28 1,
   .ADDI .x29 .x29 (BitVec.ofInt 12 (-1)),
   .ADDI .x30 .x7 16]

def balValueReverseInitBlock : List Instr :=
  [.MV .x28 .x7,
   .ADDI .x29 .x7 31,
   .ADDI .x30 .x7 16]

def balValueReverseInv (p c r : Word) (w : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ A =>
    rf.get .x5 = c ∧
    rf.get .x6 = r ∧
    rf.get .x7 = p ∧
    rf.get .x28 = p + BitVec.ofNat 64 i ∧
    rf.get .x29 = p + BitVec.ofNat 64 (31 - i) ∧
    rf.get .x30 = p + 16 ∧
    i ≤ 16 ∧
    w.length = 32 ∧
    A = (⌜RwRegion.wf ⟨p, 32⟩⌝ ** bytesRegion p (reverseLoopWin w i))

def balValueReverseSwapR (p : Word) (w : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ win rest =>
    ∃ i, i < 16 ∧
      rf.get .x7 = p ∧
      rf.get .x28 = p + BitVec.ofNat 64 i ∧
      rf.get .x29 = p + BitVec.ofNat 64 (31 - i) ∧
      win = reverseLoopWin w i ∧
      win.length = 32 ∧
      rest = ⌜RwRegion.wf ⟨p, 32⟩⌝ ∧
      ((rf.get .x28 + signExtend12 (0 : BitVec 12)) - p).toNat = i ∧
      ((rf.get .x29 + signExtend12 (0 : BitVec 12)) - p).toNat = 31 - i

def balValueReverseBody (p c r : Word) (w : List (BitVec 8)) : Stmt :=
  .block "init" balValueReverseInitBlock ;;;
  .«while» "loop" (.bne .x28 .x30) 16 (balValueReverseInv p c r w)
    (.blockAt "swap" .x7 (balValueReverseSwapR p w) balValueReverseSwapBlock ;;;
     .block "bump" balValueReverseBumpBlock)

def balValueReverseFn (p c r : Word) (w : List (BitVec 8)) : Fn where
  name := "balValueReverse"
  pre := fun rf _ A =>
    rf.get .x7 = p ∧ rf.get .x5 = c ∧ rf.get .x6 = r ∧ w.length = 32 ∧
    A = (⌜RwRegion.wf ⟨p, 32⟩⌝ ** bytesRegion p w)
  post := fun rf _ A =>
    rf.get .x5 = c ∧ rf.get .x6 = r ∧
    A = (⌜RwRegion.wf ⟨p, 32⟩⌝ ** bytesRegion p w.reverse)
  body := balValueReverseBody p c r w

def balValueReverse_verified : Program :=
  (balValueReverseBody 0 0 0 []).flatten 0

#guard (balValueReverse_verified : List Instr).length = 12

#guard ((balValueReverseBody 0 0 0 []).flatten 0
  = (balValueReverseBody 0 0 0 []).flatten 0x80000000)

#guard ((balValueReverseBody 0 0 0 []).flatten 0 =
  [.MV .x28 .x7,
   .ADDI .x29 .x7 31,
   .ADDI .x30 .x7 16,
   .BEQ .x28 .x30 (36 : BitVec 13),
   .LBU .x31 .x28 0,
   .LBU .x30 .x29 0,
   .SB .x28 .x30 0,
   .SB .x29 .x31 0,
   .ADDI .x28 .x28 1,
   .ADDI .x29 .x29 (BitVec.ofInt 12 (-1)),
   .ADDI .x30 .x7 16,
   .JAL .x0 (BitVec.ofInt 21 (-32))])

def swapRf (rf : RegFile) (win : List (BitVec 8)) (i : Nat) : RegFile :=
  (rf.set .x31 ((win.getD i 0).zeroExtend 64)).set .x30
    ((win.getD (31 - i) 0).zeroExtend 64)

def bumpRf (rf : RegFile) : RegFile :=
  ((rf.set .x28 (rf.get .x28 + signExtend12 (1 : BitVec 12))).set .x29
    (rf.get .x29 + signExtend12 (BitVec.ofInt 12 (-1)))).set .x30
      (rf.get .x7 + signExtend12 (16 : BitVec 12))

theorem bumpRf_get_x5 (rf : RegFile) : (bumpRf rf).get .x5 = rf.get .x5 := by
  unfold bumpRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28)]

theorem bumpRf_get_x6 (rf : RegFile) : (bumpRf rf).get .x6 = rf.get .x6 := by
  unfold bumpRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28)]

theorem bumpRf_get_x7 (rf : RegFile) : (bumpRf rf).get .x7 = rf.get .x7 := by
  unfold bumpRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28)]

theorem bumpRf_get_x28 (rf : RegFile) :
    (bumpRf rf).get .x28 = rf.get .x28 + signExtend12 (1 : BitVec 12) := by
  unfold bumpRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29),
    RegFile.get_set_self _ _ _ (by decide)]

theorem bumpRf_get_x29 (rf : RegFile) :
    (bumpRf rf).get .x29 = rf.get .x29 + signExtend12 (BitVec.ofInt 12 (-1)) := by
  unfold bumpRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30),
    RegFile.get_set_self _ _ _ (by decide)]

theorem bumpRf_get_x30 (rf : RegFile) :
    (bumpRf rf).get .x30 = rf.get .x7 + signExtend12 (16 : BitVec 12) := by
  unfold bumpRf
  rw [RegFile.get_set_self _ _ _ (by decide)]

theorem swapRf_get_x5 (rf : RegFile) (win : List (BitVec 8)) (i : Nat) :
    (swapRf rf win i).get .x5 = rf.get .x5 := by
  unfold swapRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x31)]

theorem swapRf_get_x6 (rf : RegFile) (win : List (BitVec 8)) (i : Nat) :
    (swapRf rf win i).get .x6 = rf.get .x6 := by
  unfold swapRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31)]

theorem swapRf_get_x7 (rf : RegFile) (win : List (BitVec 8)) (i : Nat) :
    (swapRf rf win i).get .x7 = rf.get .x7 := by
  unfold swapRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x31)]

theorem swapRf_get_x28 (rf : RegFile) (win : List (BitVec 8)) (i : Nat) :
    (swapRf rf win i).get .x28 = rf.get .x28 := by
  unfold swapRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x31)]

theorem swapRf_get_x29 (rf : RegFile) (win : List (BitVec 8)) (i : Nat) :
    (swapRf rf win i).get .x29 = rf.get .x29 := by
  unfold swapRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31)]

theorem bumpSwap_get_x5 (rf : RegFile) (win : List (BitVec 8)) (i : Nat) :
    (bumpRf (swapRf rf win i)).get .x5 = rf.get .x5 := by
  rw [bumpRf_get_x5, swapRf_get_x5]

theorem bumpSwap_get_x6 (rf : RegFile) (win : List (BitVec 8)) (i : Nat) :
    (bumpRf (swapRf rf win i)).get .x6 = rf.get .x6 := by
  rw [bumpRf_get_x6, swapRf_get_x6]

theorem bumpSwap_get_x7 (rf : RegFile) (win : List (BitVec 8)) (i : Nat) :
    (bumpRf (swapRf rf win i)).get .x7 = rf.get .x7 := by
  rw [bumpRf_get_x7, swapRf_get_x7]

theorem bumpSwap_get_x28 (rf : RegFile) (win : List (BitVec 8)) (i : Nat) :
    (bumpRf (swapRf rf win i)).get .x28 = rf.get .x28 + signExtend12 (1 : BitVec 12) := by
  rw [bumpRf_get_x28, swapRf_get_x28]

theorem bumpSwap_get_x29 (rf : RegFile) (win : List (BitVec 8)) (i : Nat) :
    (bumpRf (swapRf rf win i)).get .x29 =
      rf.get .x29 + signExtend12 (BitVec.ofInt 12 (-1)) := by
  rw [bumpRf_get_x29, swapRf_get_x29]

theorem bumpSwap_get_x30 (rf : RegFile) (win : List (BitVec 8)) (i : Nat) :
    (bumpRf (swapRf rf win i)).get .x30 = rf.get .x7 + signExtend12 (16 : BitVec 12) := by
  rw [bumpRf_get_x30, swapRf_get_x7]

theorem bumpSwap_get_x28_next (p : Word) (rf : RegFile) (win : List (BitVec 8))
    (i : Nat) (hx28 : rf.get .x28 = p + BitVec.ofNat 64 i) :
    (bumpRf (swapRf rf win i)).get .x28 = p + BitVec.ofNat 64 (i + 1) := by
  rw [bumpSwap_get_x28, hx28,
    show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
  bv_omega

theorem bumpSwap_get_x29_next (p : Word) (rf : RegFile) (win : List (BitVec 8))
    (i : Nat) (hi : i < 16) (hx29 : rf.get .x29 = p + BitVec.ofNat 64 (31 - i)) :
    (bumpRf (swapRf rf win i)).get .x29 = p + BitVec.ofNat 64 (31 - (i + 1)) := by
  rw [bumpSwap_get_x29, hx29,
    show signExtend12 (BitVec.ofInt 12 (-1)) = (-1 : Word) from by decide]
  bv_omega

theorem bumpSwap_get_x30_base (p : Word) (rf : RegFile) (win : List (BitVec 8))
    (i : Nat) (hx7 : rf.get .x7 = p) :
    (bumpRf (swapRf rf win i)).get .x30 = p + 16 := by
  rw [bumpSwap_get_x30, hx7,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]

theorem balValueReverse_bump_engine (reg : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) :
    execBlock reg rwBase rf ws balValueReverseBumpBlock = (bumpRf rf, ws) := by
  rfl

theorem cursor_addr_toNat (p : Word) (i : Nat)
    (hi : i < 32) (hwf : RwRegion.wf ⟨p, 32⟩) :
    ((p + BitVec.ofNat 64 i + signExtend12 (0 : BitVec 12)) - p).toNat = i := by
  have hov : p.toNat + 32 < 2 ^ 64 := hwf.2.1
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  bv_omega

theorem balValueReverse_swap_engine (reg : Region) (p : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat)
    (hlo : ((rf.get .x28 + signExtend12 (0 : BitVec 12)) - p).toNat = i)
    (hhi : ((rf.get .x29 + signExtend12 (0 : BitVec 12)) - p).toNat = 31 - i)
    (hws : ws.length = 32) (hi : i < 16) :
    execBlock reg p rf ws balValueReverseSwapBlock =
      (swapRf rf ws i, reverseStep ws i) := by
  rw [show balValueReverseSwapBlock =
      [.LBU .x31 .x28 0, .LBU .x30 .x29 0, .SB .x28 .x30 0, .SB .x29 .x31 0] from rfl]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ i hlo (by omega)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ (31 - i)
    (by
      simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31)]
      exact hhi)
    (by omega)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ i
    (by
      simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x31),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30)]
      exact hlo)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ (31 - i)
    (by
      simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30)]
      exact hhi)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x31 ≠ .x30),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rfl

theorem balValueReverse_swap_blockVCs (reg : Region) (p : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat)
    (hlo : ((rf.get .x28 + signExtend12 (0 : BitVec 12)) - p).toNat = i)
    (hhi : ((rf.get .x29 + signExtend12 (0 : BitVec 12)) - p).toNat = 31 - i)
    (hws : ws.length = 32) (hi : i < 16) :
    blockVCs reg p rf ws balValueReverseSwapBlock := by
  rw [show balValueReverseSwapBlock =
      [.LBU .x31 .x28 0, .LBU .x30 .x29 0, .SB .x28 .x30 0, .SB .x29 .x31 0] from rfl]
  change (if inRw p ws (rf.get .x28 + signExtend12 (0 : BitVec 12)) 1
      then (Region.mk p ws).loadOk (rf.get .x28 + signExtend12 (0 : BitVec 12)) 1
      else reg.loadOk (rf.get .x28 + signExtend12 (0 : BitVec 12)) 1) ∧
    blockVCs reg p (execInstrRF reg p rf ws (.LBU .x31 .x28 0)).1
      (execInstrRF reg p rf ws (.LBU .x31 .x28 0)).2
      [.LBU .x30 .x29 0, .SB .x28 .x30 0, .SB .x29 .x31 0]
  constructor
  · rw [if_pos]
    · unfold Region.loadOk
      simp only [hlo]
      omega
    · unfold inRw
      rw [hlo, hws]
      omega
  · rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ i hlo (by rw [hws]; omega)]
    change (if inRw p ws (((rf.set .x31 ((ws.getD i 0).zeroExtend 64)).get .x29) + signExtend12 (0 : BitVec 12)) 1
        then (Region.mk p ws).loadOk (((rf.set .x31 ((ws.getD i 0).zeroExtend 64)).get .x29) + signExtend12 (0 : BitVec 12)) 1
        else reg.loadOk (((rf.set .x31 ((ws.getD i 0).zeroExtend 64)).get .x29) + signExtend12 (0 : BitVec 12)) 1) ∧
      blockVCs reg p (execInstrRF reg p (rf.set .x31 ((ws.getD i 0).zeroExtend 64)) ws (.LBU .x30 .x29 0)).1
        (execInstrRF reg p (rf.set .x31 ((ws.getD i 0).zeroExtend 64)) ws (.LBU .x30 .x29 0)).2
        [.SB .x28 .x30 0, .SB .x29 .x31 0]
    constructor
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31), if_pos]
      · unfold Region.loadOk
        simp only [hhi]
        omega
      · unfold inRw
        rw [hhi, hws]
        omega
    · rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ (31 - i)
        (by rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31)]; exact hhi)
        (by rw [hws]; omega)]
      change (inRw p ws ((((rf.set .x31 ((ws.getD i 0).zeroExtend 64)).set .x30 ((ws.getD (31 - i) 0).zeroExtend 64)).get .x28) + signExtend12 (0 : BitVec 12)) 1 ∧
          1 ∣ (((((rf.set .x31 ((ws.getD i 0).zeroExtend 64)).set .x30 ((ws.getD (31 - i) 0).zeroExtend 64)).get .x28) + signExtend12 (0 : BitVec 12)) - p).toNat) ∧
        blockVCs reg p (execInstrRF reg p ((rf.set .x31 ((ws.getD i 0).zeroExtend 64)).set .x30 ((ws.getD (31 - i) 0).zeroExtend 64)) ws (.SB .x28 .x30 0)).1
          (execInstrRF reg p ((rf.set .x31 ((ws.getD i 0).zeroExtend 64)).set .x30 ((ws.getD (31 - i) 0).zeroExtend 64)) ws (.SB .x28 .x30 0)).2
          [.SB .x29 .x31 0]
      constructor
      · constructor
        · unfold inRw
          simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x31),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30), hlo, hws]
          omega
        · omega
      · rw [execInstrRF_sb_byte _ _ _ _ _ _ _ i
          (by
            simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x31),
              RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30)]
            exact hlo)]
        change (inRw p (setBytes ws i [BitVec.truncate 8 (((rf.set .x31 ((ws.getD i 0).zeroExtend 64)).set .x30 ((ws.getD (31 - i) 0).zeroExtend 64)).get .x30)]) ((((rf.set .x31 ((ws.getD i 0).zeroExtend 64)).set .x30 ((ws.getD (31 - i) 0).zeroExtend 64)).get .x29) + signExtend12 (0 : BitVec 12)) 1 ∧
            1 ∣ (((((rf.set .x31 ((ws.getD i 0).zeroExtend 64)).set .x30 ((ws.getD (31 - i) 0).zeroExtend 64)).get .x29) + signExtend12 (0 : BitVec 12)) - p).toNat) ∧
          True
        constructor
        · constructor
          · unfold inRw
            simp only [length_setBytes, hws, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31),
              RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), hhi]
            omega
          · omega
        · trivial

theorem balValueReverseFn_spec (p c r : Word) (w : List (BitVec 8))
    (base : Word) :
    (balValueReverseFn p c r w).Spec base := by
  vcgen
  case balValueReverse.loop.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, -, ⟨hx7, hx5, hx6, hw, hA⟩, rfl, rfl⟩
    simp only [balValueReverseInitBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, hw, ?_⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x30),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x29),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28)]
      exact hx5
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28)]
      exact hx6
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x30),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28)]
      exact hx7
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29),
        RegFile.get_set_self _ _ _ (by decide), hx7]
      bv_omega
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30),
        RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx7,
        show signExtend12 (31 : BitVec 12) = (31 : Word) from by decide]
      bv_omega
    · rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx7,
        show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
    · rw [hA, reverseLoopWin_zero w hw]
  case balValueReverse.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rfb, wsb, hbLen, hpre, hrfb, hAb⟩
    rcases hpre with ⟨rf0, A0, win, rest, hwsLen, hreach, hsat, hR, hrfSwap, hASwap⟩
    obtain ⟨⟨hx5, hx6, hx7, hx28, hx29, hx30, hle, hw, hA0⟩, hcond⟩ := hreach
    obtain ⟨j, hj, hx7R, hx28R, hx29R, rfl, hwinLen, rfl, hlo, hhi⟩ := hR
    have hji : j = i := by
      rw [hx28] at hx28R
      bv_omega
    rw [hji] at hrfSwap hASwap hwinLen hlo hhi
    rw [hx7] at hrfSwap hASwap
    rw [balValueReverse_swap_engine _ _ _ _ i hlo hhi hwinLen hi] at hrfSwap hASwap
    dsimp only at hrfSwap hASwap
    subst rfb
    rw [balValueReverse_bump_engine] at hrfb hAb
    dsimp only at hrfb hAb
    subst rf'
    have hf5 : (bumpRf (swapRf rf0 (reverseLoopWin w i) i)).get .x5 = c := by
      rw [bumpSwap_get_x5, hx5]
    have hf6 : (bumpRf (swapRf rf0 (reverseLoopWin w i) i)).get .x6 = r := by
      rw [bumpSwap_get_x6, hx6]
    have hf7 : (bumpRf (swapRf rf0 (reverseLoopWin w i) i)).get .x7 = p := by
      rw [bumpSwap_get_x7, hx7]
    have hf28 : (bumpRf (swapRf rf0 (reverseLoopWin w i) i)).get .x28 =
        p + BitVec.ofNat 64 (i + 1) :=
      bumpSwap_get_x28_next p rf0 (reverseLoopWin w i) i hx28
    have hf29 : (bumpRf (swapRf rf0 (reverseLoopWin w i) i)).get .x29 =
        p + BitVec.ofNat 64 (31 - (i + 1)) :=
      bumpSwap_get_x29_next p rf0 (reverseLoopWin w i) i hi hx29
    have hf30 : (bumpRf (swapRf rf0 (reverseLoopWin w i) i)).get .x30 = p + 16 :=
      bumpSwap_get_x30_base p rf0 (reverseLoopWin w i) i hx7
    have hAfinal : A' = (⌜RwRegion.wf ⟨p, 32⟩⌝ ** bytesRegion p (reverseLoopWin w (i + 1))) := by
      rw [hASwap, sepConj_comm', reverseLoopWin_step w i hw hi]
    exact ⟨hf5, hf6, hf7, hf28, hf29, hf30, by omega, hw, hAfinal⟩
  case balValueReverse.loop.exhausted =>
    rintro rf ws A ⟨hx5, hx6, hx7, hx28, hx29, hx30, hle, hw, hA⟩
    simp only [Cond.holds]
    rw [hx28, hx30]
    intro h
    exact h rfl
  case balValueReverse.loop.body.swap.focus =>
    rintro rf ws A ⟨i, hi, ⟨hx5, hx6, hx7, hx28, hx29, hx30, hle, hw, hA⟩, hcond⟩ hApc hp hhp
    rw [hA] at hhp
    have hwf : RwRegion.wf ⟨p, 32⟩ := ((sepConj_pure_left hp).mp hhp).1
    refine ⟨reverseLoopWin w i, ⌜RwRegion.wf ⟨p, 32⟩⌝, ?_, ?_, pcFree_pure, ?_⟩
    · refine ⟨i, hi, hx7, hx28, hx29, rfl, ?_, rfl, ?_, ?_⟩
      · exact length_reverseLoopWin_of_le w i hw (by omega)
      · rw [hx28]
        exact cursor_addr_toNat p i (by omega) hwf
      · rw [hx29]
        exact cursor_addr_toNat p (31 - i) (by omega) hwf
    · rw [hx7]
      xperm_hyp hhp
    · rw [hx7, length_reverseLoopWin_of_le w i hw (by omega)]
      exact hwf
  case balValueReverse.loop.body.swap.mem =>
    rintro rf ws A win rest hws hreach hR hsat
    obtain ⟨i, hi, hx7, hx28, hx29, rfl, hwinLen, rfl, hlo, hhi⟩ := hR
    rw [hx7]
    exact balValueReverse_swap_blockVCs _ _ _ _ i hlo hhi hwinLen hi
  case balValueReverse.post =>
    intro rf ws A h
    obtain ⟨⟨i, hle, hx5, hx6, hx7, hx28, hx29, hx30, hiLe, hw, hA⟩, hnc⟩ := h
    have hi16 : i = 16 := by
      simp only [Cond.holds] at hnc
      by_contra hne
      have hcond : rf.get .x28 ≠ rf.get .x30 := by
        rw [hx28, hx30]
        intro heq
        bv_omega
      exact hnc hcond
    subst i
    exact ⟨hx5, hx6, by rw [hA, reverseLoopWin_16_eq_reverse w]⟩


end BalValueReverseSAsm

end EvmAsm.Codegen
