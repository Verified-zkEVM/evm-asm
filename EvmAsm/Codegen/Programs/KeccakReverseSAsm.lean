/-
  EvmAsm.Codegen.Programs.KeccakReverseSAsm

  Verified SAsm byte-reverse body for the KECCAK256 dispatcher tail.  The
  emitted program reverses the 32-byte cell at `a2` in place using only
  byte loads/stores and t2/t3 as temporaries.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.Stmt

namespace KeccakReverseSAsm

def byteSwapAt (lo hi : BitVec 12) : List Instr :=
  [.LBU .x7 .x12 lo,
   .LBU .x28 .x12 hi,
   .SB .x12 .x28 lo,
   .SB .x12 .x7 hi]

def byteReverse32Block : List Instr :=
  byteSwapAt 0 31 ++
  byteSwapAt 1 30 ++
  byteSwapAt 2 29 ++
  byteSwapAt 3 28 ++
  byteSwapAt 4 27 ++
  byteSwapAt 5 26 ++
  byteSwapAt 6 25 ++
  byteSwapAt 7 24 ++
  byteSwapAt 8 23 ++
  byteSwapAt 9 22 ++
  byteSwapAt 10 21 ++
  byteSwapAt 11 20 ++
  byteSwapAt 12 19 ++
  byteSwapAt 13 18 ++
  byteSwapAt 14 17 ++
  byteSwapAt 15 16

#guard byteReverse32Block.length = 64

def byteReverse32R (p : Word) (w : List (BitVec 8)) :
    RegFile -> List (BitVec 8) -> Assertion ->
      List (BitVec 8) -> Assertion -> Prop :=
  fun rf _ _ win rest =>
    rf.get .x12 = p ∧ win = w ∧ rest = ⌜RwRegion.wf ⟨p, 32⟩⌝

def byteReverse32Body (p : Word) (w : List (BitVec 8)) : Stmt :=
  .blockAt "rev" .x12 (byteReverse32R p w) byteReverse32Block

def byteReverse32Fn (p pc aux1 aux3 : Word) (w : List (BitVec 8)) : Fn where
  name := "keccakByteReverse"
  pre := fun rf _ A =>
    rf.get .x10 = pc ∧ rf.get .x11 = aux1 ∧ rf.get .x12 = p ∧
    rf.get .x13 = aux3 ∧ w.length = 32 ∧
    A = (⌜RwRegion.wf ⟨p, 32⟩⌝ ** bytesRegion p w)
  post := fun rf _ A =>
    rf.get .x10 = pc ∧ rf.get .x11 = aux1 ∧ rf.get .x12 = p ∧
    rf.get .x13 = aux3 ∧
    A = (⌜RwRegion.wf ⟨p, 32⟩⌝ ** bytesRegion p w.reverse)
  body := byteReverse32Body p w

def byteReverse32_verified : Program :=
  (byteReverse32Body 0 []).flatten 0

#guard (byteReverse32_verified : List Instr).length = 64

-- Position independence: the body has no PC-relative instructions.
#guard ((byteReverse32Body 0 []).flatten 0
  = (byteReverse32Body 0 []).flatten 0x80000000)

#guard ([0, 1, 2, 3, 4, 5, 6, 7] : List (BitVec 8)).reverse =
  [7, 6, 5, 4, 3, 2, 1, 0]

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
                                                                | cons b32 w => simp only [List.length_cons] at hw; omega

private theorem byteReverse32_off (b : Word) (ofs : BitVec 12) (k : Nat)
    (hofs : signExtend12 ofs = BitVec.ofNat 64 k) (hk : k < 2 ^ 12) :
    ((b + signExtend12 ofs) - b).toNat = k := by
  rw [hofs]
  bv_omega

private theorem byteReverse32_engine (reg : Region) (rf : RegFile)
    (b0 : BitVec 8) (b1 : BitVec 8) (b2 : BitVec 8) (b3 : BitVec 8) (b4 : BitVec 8) (b5 : BitVec 8) (b6 : BitVec 8) (b7 : BitVec 8) (b8 : BitVec 8) (b9 : BitVec 8) (b10 : BitVec 8) (b11 : BitVec 8) (b12 : BitVec 8) (b13 : BitVec 8) (b14 : BitVec 8) (b15 : BitVec 8) (b16 : BitVec 8) (b17 : BitVec 8) (b18 : BitVec 8) (b19 : BitVec 8) (b20 : BitVec 8) (b21 : BitVec 8) (b22 : BitVec 8) (b23 : BitVec 8) (b24 : BitVec 8) (b25 : BitVec 8) (b26 : BitVec 8) (b27 : BitVec 8) (b28 : BitVec 8) (b29 : BitVec 8) (b30 : BitVec 8) (b31 : BitVec 8) :
    execBlock reg (rf.get .x12) rf [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] byteReverse32Block
      = (((((((((((((((((((((((((((((((((rf.set .x7 (b0.zeroExtend 64)).set .x28 (b31.zeroExtend 64)).set .x7 (b1.zeroExtend 64)).set .x28 (b30.zeroExtend 64)).set .x7 (b2.zeroExtend 64)).set .x28 (b29.zeroExtend 64)).set .x7 (b3.zeroExtend 64)).set .x28 (b28.zeroExtend 64)).set .x7 (b4.zeroExtend 64)).set .x28 (b27.zeroExtend 64)).set .x7 (b5.zeroExtend 64)).set .x28 (b26.zeroExtend 64)).set .x7 (b6.zeroExtend 64)).set .x28 (b25.zeroExtend 64)).set .x7 (b7.zeroExtend 64)).set .x28 (b24.zeroExtend 64)).set .x7 (b8.zeroExtend 64)).set .x28 (b23.zeroExtend 64)).set .x7 (b9.zeroExtend 64)).set .x28 (b22.zeroExtend 64)).set .x7 (b10.zeroExtend 64)).set .x28 (b21.zeroExtend 64)).set .x7 (b11.zeroExtend 64)).set .x28 (b20.zeroExtend 64)).set .x7 (b12.zeroExtend 64)).set .x28 (b19.zeroExtend 64)).set .x7 (b13.zeroExtend 64)).set .x28 (b18.zeroExtend 64)).set .x7 (b14.zeroExtend 64)).set .x28 (b17.zeroExtend 64)).set .x7 (b15.zeroExtend 64)).set .x28 (b16.zeroExtend 64)), [b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0]) := by
  have h0 := byteReverse32_off (rf.get .x12) 0 0 (by decide) (by decide)
  have h1 := byteReverse32_off (rf.get .x12) 1 1 (by decide) (by decide)
  have h2 := byteReverse32_off (rf.get .x12) 2 2 (by decide) (by decide)
  have h3 := byteReverse32_off (rf.get .x12) 3 3 (by decide) (by decide)
  have h4 := byteReverse32_off (rf.get .x12) 4 4 (by decide) (by decide)
  have h5 := byteReverse32_off (rf.get .x12) 5 5 (by decide) (by decide)
  have h6 := byteReverse32_off (rf.get .x12) 6 6 (by decide) (by decide)
  have h7 := byteReverse32_off (rf.get .x12) 7 7 (by decide) (by decide)
  have h8 := byteReverse32_off (rf.get .x12) 8 8 (by decide) (by decide)
  have h9 := byteReverse32_off (rf.get .x12) 9 9 (by decide) (by decide)
  have h10 := byteReverse32_off (rf.get .x12) 10 10 (by decide) (by decide)
  have h11 := byteReverse32_off (rf.get .x12) 11 11 (by decide) (by decide)
  have h12 := byteReverse32_off (rf.get .x12) 12 12 (by decide) (by decide)
  have h13 := byteReverse32_off (rf.get .x12) 13 13 (by decide) (by decide)
  have h14 := byteReverse32_off (rf.get .x12) 14 14 (by decide) (by decide)
  have h15 := byteReverse32_off (rf.get .x12) 15 15 (by decide) (by decide)
  have h16 := byteReverse32_off (rf.get .x12) 16 16 (by decide) (by decide)
  have h17 := byteReverse32_off (rf.get .x12) 17 17 (by decide) (by decide)
  have h18 := byteReverse32_off (rf.get .x12) 18 18 (by decide) (by decide)
  have h19 := byteReverse32_off (rf.get .x12) 19 19 (by decide) (by decide)
  have h20 := byteReverse32_off (rf.get .x12) 20 20 (by decide) (by decide)
  have h21 := byteReverse32_off (rf.get .x12) 21 21 (by decide) (by decide)
  have h22 := byteReverse32_off (rf.get .x12) 22 22 (by decide) (by decide)
  have h23 := byteReverse32_off (rf.get .x12) 23 23 (by decide) (by decide)
  have h24 := byteReverse32_off (rf.get .x12) 24 24 (by decide) (by decide)
  have h25 := byteReverse32_off (rf.get .x12) 25 25 (by decide) (by decide)
  have h26 := byteReverse32_off (rf.get .x12) 26 26 (by decide) (by decide)
  have h27 := byteReverse32_off (rf.get .x12) 27 27 (by decide) (by decide)
  have h28 := byteReverse32_off (rf.get .x12) 28 28 (by decide) (by decide)
  have h29 := byteReverse32_off (rf.get .x12) 29 29 (by decide) (by decide)
  have h30 := byteReverse32_off (rf.get .x12) 30 30 (by decide) (by decide)
  have h31 := byteReverse32_off (rf.get .x12) 31 31 (by decide) (by decide)
  have hx12a : ∀ v : Word, (rf.set .x7 v).get .x12 = rf.get .x12 :=
    fun v => RegFile.get_set_ne _ _ _ _ (by decide)
  have hx12b : ∀ v w : Word, ((rf.set .x7 v).set .x28 w).get .x12
      = rf.get .x12 := fun v w => by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12a]
  rw [show byteReverse32Block = [.LBU .x7 .x12 0, .LBU .x28 .x12 31, .SB .x12 .x28 0, .SB .x12 .x7 31, .LBU .x7 .x12 1, .LBU .x28 .x12 30, .SB .x12 .x28 1, .SB .x12 .x7 30, .LBU .x7 .x12 2, .LBU .x28 .x12 29, .SB .x12 .x28 2, .SB .x12 .x7 29, .LBU .x7 .x12 3, .LBU .x28 .x12 28, .SB .x12 .x28 3, .SB .x12 .x7 28, .LBU .x7 .x12 4, .LBU .x28 .x12 27, .SB .x12 .x28 4, .SB .x12 .x7 27, .LBU .x7 .x12 5, .LBU .x28 .x12 26, .SB .x12 .x28 5, .SB .x12 .x7 26, .LBU .x7 .x12 6, .LBU .x28 .x12 25, .SB .x12 .x28 6, .SB .x12 .x7 25, .LBU .x7 .x12 7, .LBU .x28 .x12 24, .SB .x12 .x28 7, .SB .x12 .x7 24, .LBU .x7 .x12 8, .LBU .x28 .x12 23, .SB .x12 .x28 8, .SB .x12 .x7 23, .LBU .x7 .x12 9, .LBU .x28 .x12 22, .SB .x12 .x28 9, .SB .x12 .x7 22, .LBU .x7 .x12 10, .LBU .x28 .x12 21, .SB .x12 .x28 10, .SB .x12 .x7 21, .LBU .x7 .x12 11, .LBU .x28 .x12 20, .SB .x12 .x28 11, .SB .x12 .x7 20, .LBU .x7 .x12 12, .LBU .x28 .x12 19, .SB .x12 .x28 12, .SB .x12 .x7 19, .LBU .x7 .x12 13, .LBU .x28 .x12 18, .SB .x12 .x28 13, .SB .x12 .x7 18, .LBU .x7 .x12 14, .LBU .x28 .x12 17, .SB .x12 .x28 14, .SB .x12 .x7 17, .LBU .x7 .x12 15, .LBU .x28 .x12 16, .SB .x12 .x28 15, .SB .x12 .x7 16] from rfl]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 0 h0 (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 31
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7)]; exact h31) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 0
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h0)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 31
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h31)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 1 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h1) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 30
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h30) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 1
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h1)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 30
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h30)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 2 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h2) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 29
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h29) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 2
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h2)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 29
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h29)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 3 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h3) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 28
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h28) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 3
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h3)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 28
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h28)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 4 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h4) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 27
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h27) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 4
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h4)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 27
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h27)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 5 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h5) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 26
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h26) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 5
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h5)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 26
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h26)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 6 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h6) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 25
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h25) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 6
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h6)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 25
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h25)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 7 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h7) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 24
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h24) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 7
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h7)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 24
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h24)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 8 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h8) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 23
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h23) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 8
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h8)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 23
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h23)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 9 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h9) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 22
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h22) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 9
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h9)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 22
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h22)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 10 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h10) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 21
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h21) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 10
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h10)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 21
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h21)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 11 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h11) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 20
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h20) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 11
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h11)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 20
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h20)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 12 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h12) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 19
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h19) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 12
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h12)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 19
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h19)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 13 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h13) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 18
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h18) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 13
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h13)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 18
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h18)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 14 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h14) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 17
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h17) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 14
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h14)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 17
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h17)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 15 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h15) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 16
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h16) (by simp)]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 15
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h15)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 16
    (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h16)]
  dsimp only
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ, execBlock_nil]

set_option linter.unusedSimpArgs false in
private theorem byteReverse32_blockVCs (reg : Region) (rf : RegFile)
    (b0 : BitVec 8) (b1 : BitVec 8) (b2 : BitVec 8) (b3 : BitVec 8) (b4 : BitVec 8) (b5 : BitVec 8) (b6 : BitVec 8) (b7 : BitVec 8) (b8 : BitVec 8) (b9 : BitVec 8) (b10 : BitVec 8) (b11 : BitVec 8) (b12 : BitVec 8) (b13 : BitVec 8) (b14 : BitVec 8) (b15 : BitVec 8) (b16 : BitVec 8) (b17 : BitVec 8) (b18 : BitVec 8) (b19 : BitVec 8) (b20 : BitVec 8) (b21 : BitVec 8) (b22 : BitVec 8) (b23 : BitVec 8) (b24 : BitVec 8) (b25 : BitVec 8) (b26 : BitVec 8) (b27 : BitVec 8) (b28 : BitVec 8) (b29 : BitVec 8) (b30 : BitVec 8) (b31 : BitVec 8) :
    blockVCs reg (rf.get .x12) rf [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] byteReverse32Block := by
  have h0 := byteReverse32_off (rf.get .x12) 0 0 (by decide) (by decide)
  have h1 := byteReverse32_off (rf.get .x12) 1 1 (by decide) (by decide)
  have h2 := byteReverse32_off (rf.get .x12) 2 2 (by decide) (by decide)
  have h3 := byteReverse32_off (rf.get .x12) 3 3 (by decide) (by decide)
  have h4 := byteReverse32_off (rf.get .x12) 4 4 (by decide) (by decide)
  have h5 := byteReverse32_off (rf.get .x12) 5 5 (by decide) (by decide)
  have h6 := byteReverse32_off (rf.get .x12) 6 6 (by decide) (by decide)
  have h7 := byteReverse32_off (rf.get .x12) 7 7 (by decide) (by decide)
  have h8 := byteReverse32_off (rf.get .x12) 8 8 (by decide) (by decide)
  have h9 := byteReverse32_off (rf.get .x12) 9 9 (by decide) (by decide)
  have h10 := byteReverse32_off (rf.get .x12) 10 10 (by decide) (by decide)
  have h11 := byteReverse32_off (rf.get .x12) 11 11 (by decide) (by decide)
  have h12 := byteReverse32_off (rf.get .x12) 12 12 (by decide) (by decide)
  have h13 := byteReverse32_off (rf.get .x12) 13 13 (by decide) (by decide)
  have h14 := byteReverse32_off (rf.get .x12) 14 14 (by decide) (by decide)
  have h15 := byteReverse32_off (rf.get .x12) 15 15 (by decide) (by decide)
  have h16 := byteReverse32_off (rf.get .x12) 16 16 (by decide) (by decide)
  have h17 := byteReverse32_off (rf.get .x12) 17 17 (by decide) (by decide)
  have h18 := byteReverse32_off (rf.get .x12) 18 18 (by decide) (by decide)
  have h19 := byteReverse32_off (rf.get .x12) 19 19 (by decide) (by decide)
  have h20 := byteReverse32_off (rf.get .x12) 20 20 (by decide) (by decide)
  have h21 := byteReverse32_off (rf.get .x12) 21 21 (by decide) (by decide)
  have h22 := byteReverse32_off (rf.get .x12) 22 22 (by decide) (by decide)
  have h23 := byteReverse32_off (rf.get .x12) 23 23 (by decide) (by decide)
  have h24 := byteReverse32_off (rf.get .x12) 24 24 (by decide) (by decide)
  have h25 := byteReverse32_off (rf.get .x12) 25 25 (by decide) (by decide)
  have h26 := byteReverse32_off (rf.get .x12) 26 26 (by decide) (by decide)
  have h27 := byteReverse32_off (rf.get .x12) 27 27 (by decide) (by decide)
  have h28 := byteReverse32_off (rf.get .x12) 28 28 (by decide) (by decide)
  have h29 := byteReverse32_off (rf.get .x12) 29 29 (by decide) (by decide)
  have h30 := byteReverse32_off (rf.get .x12) 30 30 (by decide) (by decide)
  have h31 := byteReverse32_off (rf.get .x12) 31 31 (by decide) (by decide)
  rw [show byteReverse32Block = [.LBU .x7 .x12 0, .LBU .x28 .x12 31, .SB .x12 .x28 0, .SB .x12 .x7 31, .LBU .x7 .x12 1, .LBU .x28 .x12 30, .SB .x12 .x28 1, .SB .x12 .x7 30, .LBU .x7 .x12 2, .LBU .x28 .x12 29, .SB .x12 .x28 2, .SB .x12 .x7 29, .LBU .x7 .x12 3, .LBU .x28 .x12 28, .SB .x12 .x28 3, .SB .x12 .x7 28, .LBU .x7 .x12 4, .LBU .x28 .x12 27, .SB .x12 .x28 4, .SB .x12 .x7 27, .LBU .x7 .x12 5, .LBU .x28 .x12 26, .SB .x12 .x28 5, .SB .x12 .x7 26, .LBU .x7 .x12 6, .LBU .x28 .x12 25, .SB .x12 .x28 6, .SB .x12 .x7 25, .LBU .x7 .x12 7, .LBU .x28 .x12 24, .SB .x12 .x28 7, .SB .x12 .x7 24, .LBU .x7 .x12 8, .LBU .x28 .x12 23, .SB .x12 .x28 8, .SB .x12 .x7 23, .LBU .x7 .x12 9, .LBU .x28 .x12 22, .SB .x12 .x28 9, .SB .x12 .x7 22, .LBU .x7 .x12 10, .LBU .x28 .x12 21, .SB .x12 .x28 10, .SB .x12 .x7 21, .LBU .x7 .x12 11, .LBU .x28 .x12 20, .SB .x12 .x28 11, .SB .x12 .x7 20, .LBU .x7 .x12 12, .LBU .x28 .x12 19, .SB .x12 .x28 12, .SB .x12 .x7 19, .LBU .x7 .x12 13, .LBU .x28 .x12 18, .SB .x12 .x28 13, .SB .x12 .x7 18, .LBU .x7 .x12 14, .LBU .x28 .x12 17, .SB .x12 .x28 14, .SB .x12 .x7 17, .LBU .x7 .x12 15, .LBU .x28 .x12 16, .SB .x12 .x28 15, .SB .x12 .x7 16] from rfl]
  unfold blockVCs
  refine And.intro ?_ ?_
  · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
      List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
    rw [h0]
    trivial
  ·
    rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 0 (h0) (by simp)]
    dsimp only
    unfold blockVCs
    refine And.intro ?_ ?_
    · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
        List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
      rw [h31]
      trivial
    ·
      rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 31 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7)]; exact h31) (by simp)]
      dsimp only
      unfold blockVCs
      refine And.intro ?_ ?_
      · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
          List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
        rw [h0]
        trivial
      ·
        rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 0 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h0)]
        dsimp only
        rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
          truncate_zeroExtend_byte]
        unfold blockVCs
        refine And.intro ?_ ?_
        · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
            List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
          rw [h31]
          trivial
        ·
          rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 31 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h31)]
          dsimp only
          rw [RegFile.get_set_ne _ _ _ _ (by decide),
            RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
            truncate_zeroExtend_byte]
          simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
          unfold blockVCs
          refine And.intro ?_ ?_
          · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
              List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
            rw [h1]
            trivial
          ·
            rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 1 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h1) (by simp [execInstrRF_sb_snd])]
            dsimp only
            unfold blockVCs
            refine And.intro ?_ ?_
            · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
              rw [h30]
              trivial
            ·
              rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 30 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h30) (by simp [execInstrRF_sb_snd])]
              dsimp only
              unfold blockVCs
              refine And.intro ?_ ?_
              · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                  List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                rw [h1]
                trivial
              ·
                rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 1 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h1)]
                dsimp only
                rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                  truncate_zeroExtend_byte]
                unfold blockVCs
                refine And.intro ?_ ?_
                · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                    List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                  rw [h30]
                  trivial
                ·
                  rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 30 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h30)]
                  dsimp only
                  rw [RegFile.get_set_ne _ _ _ _ (by decide),
                    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                    truncate_zeroExtend_byte]
                  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                  unfold blockVCs
                  refine And.intro ?_ ?_
                  · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                      List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                    rw [h2]
                    trivial
                  ·
                    rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 2 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h2) (by simp [execInstrRF_sb_snd])]
                    dsimp only
                    unfold blockVCs
                    refine And.intro ?_ ?_
                    · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                        List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                      rw [h29]
                      trivial
                    ·
                      rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 29 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h29) (by simp [execInstrRF_sb_snd])]
                      dsimp only
                      unfold blockVCs
                      refine And.intro ?_ ?_
                      · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                          List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                        rw [h2]
                        trivial
                      ·
                        rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 2 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h2)]
                        dsimp only
                        rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                          truncate_zeroExtend_byte]
                        unfold blockVCs
                        refine And.intro ?_ ?_
                        · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                            List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                          rw [h29]
                          trivial
                        ·
                          rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 29 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h29)]
                          dsimp only
                          rw [RegFile.get_set_ne _ _ _ _ (by decide),
                            RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                            truncate_zeroExtend_byte]
                          simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                          unfold blockVCs
                          refine And.intro ?_ ?_
                          · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                              List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                            rw [h3]
                            trivial
                          ·
                            rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 3 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h3) (by simp [execInstrRF_sb_snd])]
                            dsimp only
                            unfold blockVCs
                            refine And.intro ?_ ?_
                            · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                              rw [h28]
                              trivial
                            ·
                              rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 28 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h28) (by simp [execInstrRF_sb_snd])]
                              dsimp only
                              unfold blockVCs
                              refine And.intro ?_ ?_
                              · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                  List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                rw [h3]
                                trivial
                              ·
                                rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 3 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h3)]
                                dsimp only
                                rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                  truncate_zeroExtend_byte]
                                unfold blockVCs
                                refine And.intro ?_ ?_
                                · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                    List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                  rw [h28]
                                  trivial
                                ·
                                  rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 28 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h28)]
                                  dsimp only
                                  rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                    truncate_zeroExtend_byte]
                                  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                  unfold blockVCs
                                  refine And.intro ?_ ?_
                                  · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                      List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                    rw [h4]
                                    trivial
                                  ·
                                    rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 4 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h4) (by simp [execInstrRF_sb_snd])]
                                    dsimp only
                                    unfold blockVCs
                                    refine And.intro ?_ ?_
                                    · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                        List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                      rw [h27]
                                      trivial
                                    ·
                                      rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 27 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h27) (by simp [execInstrRF_sb_snd])]
                                      dsimp only
                                      unfold blockVCs
                                      refine And.intro ?_ ?_
                                      · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                          List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                        rw [h4]
                                        trivial
                                      ·
                                        rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 4 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h4)]
                                        dsimp only
                                        rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                          truncate_zeroExtend_byte]
                                        unfold blockVCs
                                        refine And.intro ?_ ?_
                                        · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                            List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                          rw [h27]
                                          trivial
                                        ·
                                          rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 27 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h27)]
                                          dsimp only
                                          rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                            RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                            truncate_zeroExtend_byte]
                                          simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                          unfold blockVCs
                                          refine And.intro ?_ ?_
                                          · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                              List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                            rw [h5]
                                            trivial
                                          ·
                                            rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 5 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h5) (by simp [execInstrRF_sb_snd])]
                                            dsimp only
                                            unfold blockVCs
                                            refine And.intro ?_ ?_
                                            · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                              rw [h26]
                                              trivial
                                            ·
                                              rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 26 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h26) (by simp [execInstrRF_sb_snd])]
                                              dsimp only
                                              unfold blockVCs
                                              refine And.intro ?_ ?_
                                              · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                  List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                rw [h5]
                                                trivial
                                              ·
                                                rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 5 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h5)]
                                                dsimp only
                                                rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                  truncate_zeroExtend_byte]
                                                unfold blockVCs
                                                refine And.intro ?_ ?_
                                                · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                    List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                  rw [h26]
                                                  trivial
                                                ·
                                                  rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 26 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h26)]
                                                  dsimp only
                                                  rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                                    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                    truncate_zeroExtend_byte]
                                                  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                                  unfold blockVCs
                                                  refine And.intro ?_ ?_
                                                  · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                      List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                    rw [h6]
                                                    trivial
                                                  ·
                                                    rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 6 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h6) (by simp [execInstrRF_sb_snd])]
                                                    dsimp only
                                                    unfold blockVCs
                                                    refine And.intro ?_ ?_
                                                    · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                        List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                      rw [h25]
                                                      trivial
                                                    ·
                                                      rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 25 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h25) (by simp [execInstrRF_sb_snd])]
                                                      dsimp only
                                                      unfold blockVCs
                                                      refine And.intro ?_ ?_
                                                      · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                          List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                        rw [h6]
                                                        trivial
                                                      ·
                                                        rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 6 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h6)]
                                                        dsimp only
                                                        rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                          truncate_zeroExtend_byte]
                                                        unfold blockVCs
                                                        refine And.intro ?_ ?_
                                                        · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                            List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                          rw [h25]
                                                          trivial
                                                        ·
                                                          rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 25 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h25)]
                                                          dsimp only
                                                          rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                                            RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                            truncate_zeroExtend_byte]
                                                          simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                                          unfold blockVCs
                                                          refine And.intro ?_ ?_
                                                          · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                              List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                            rw [h7]
                                                            trivial
                                                          ·
                                                            rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 7 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h7) (by simp [execInstrRF_sb_snd])]
                                                            dsimp only
                                                            unfold blockVCs
                                                            refine And.intro ?_ ?_
                                                            · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                              rw [h24]
                                                              trivial
                                                            ·
                                                              rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 24 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h24) (by simp [execInstrRF_sb_snd])]
                                                              dsimp only
                                                              unfold blockVCs
                                                              refine And.intro ?_ ?_
                                                              · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                  List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                rw [h7]
                                                                trivial
                                                              ·
                                                                rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 7 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h7)]
                                                                dsimp only
                                                                rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                  truncate_zeroExtend_byte]
                                                                unfold blockVCs
                                                                refine And.intro ?_ ?_
                                                                · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                    List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                  rw [h24]
                                                                  trivial
                                                                ·
                                                                  rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 24 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h24)]
                                                                  dsimp only
                                                                  rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                                                    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                    truncate_zeroExtend_byte]
                                                                  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                                                  unfold blockVCs
                                                                  refine And.intro ?_ ?_
                                                                  · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                      List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                    rw [h8]
                                                                    trivial
                                                                  ·
                                                                    rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 8 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h8) (by simp [execInstrRF_sb_snd])]
                                                                    dsimp only
                                                                    unfold blockVCs
                                                                    refine And.intro ?_ ?_
                                                                    · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                        List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                      rw [h23]
                                                                      trivial
                                                                    ·
                                                                      rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 23 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h23) (by simp [execInstrRF_sb_snd])]
                                                                      dsimp only
                                                                      unfold blockVCs
                                                                      refine And.intro ?_ ?_
                                                                      · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                          List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                        rw [h8]
                                                                        trivial
                                                                      ·
                                                                        rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 8 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h8)]
                                                                        dsimp only
                                                                        rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                          truncate_zeroExtend_byte]
                                                                        unfold blockVCs
                                                                        refine And.intro ?_ ?_
                                                                        · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                            List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                          rw [h23]
                                                                          trivial
                                                                        ·
                                                                          rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 23 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h23)]
                                                                          dsimp only
                                                                          rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                                                            RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                            truncate_zeroExtend_byte]
                                                                          simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                                                          unfold blockVCs
                                                                          refine And.intro ?_ ?_
                                                                          · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                              List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                            rw [h9]
                                                                            trivial
                                                                          ·
                                                                            rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 9 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h9) (by simp [execInstrRF_sb_snd])]
                                                                            dsimp only
                                                                            unfold blockVCs
                                                                            refine And.intro ?_ ?_
                                                                            · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                              rw [h22]
                                                                              trivial
                                                                            ·
                                                                              rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 22 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h22) (by simp [execInstrRF_sb_snd])]
                                                                              dsimp only
                                                                              unfold blockVCs
                                                                              refine And.intro ?_ ?_
                                                                              · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                  List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                rw [h9]
                                                                                trivial
                                                                              ·
                                                                                rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 9 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h9)]
                                                                                dsimp only
                                                                                rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                  truncate_zeroExtend_byte]
                                                                                unfold blockVCs
                                                                                refine And.intro ?_ ?_
                                                                                · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                    List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                  rw [h22]
                                                                                  trivial
                                                                                ·
                                                                                  rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 22 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h22)]
                                                                                  dsimp only
                                                                                  rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                                                                    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                    truncate_zeroExtend_byte]
                                                                                  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                                                                  unfold blockVCs
                                                                                  refine And.intro ?_ ?_
                                                                                  · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                      List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                    rw [h10]
                                                                                    trivial
                                                                                  ·
                                                                                    rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 10 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h10) (by simp [execInstrRF_sb_snd])]
                                                                                    dsimp only
                                                                                    unfold blockVCs
                                                                                    refine And.intro ?_ ?_
                                                                                    · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                        List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                      rw [h21]
                                                                                      trivial
                                                                                    ·
                                                                                      rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 21 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h21) (by simp [execInstrRF_sb_snd])]
                                                                                      dsimp only
                                                                                      unfold blockVCs
                                                                                      refine And.intro ?_ ?_
                                                                                      · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                          List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                        rw [h10]
                                                                                        trivial
                                                                                      ·
                                                                                        rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 10 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h10)]
                                                                                        dsimp only
                                                                                        rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                          truncate_zeroExtend_byte]
                                                                                        unfold blockVCs
                                                                                        refine And.intro ?_ ?_
                                                                                        · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                            List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                          rw [h21]
                                                                                          trivial
                                                                                        ·
                                                                                          rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 21 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h21)]
                                                                                          dsimp only
                                                                                          rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                                                                            RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                            truncate_zeroExtend_byte]
                                                                                          simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                                                                          unfold blockVCs
                                                                                          refine And.intro ?_ ?_
                                                                                          · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                              List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                            rw [h11]
                                                                                            trivial
                                                                                          ·
                                                                                            rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 11 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h11) (by simp [execInstrRF_sb_snd])]
                                                                                            dsimp only
                                                                                            unfold blockVCs
                                                                                            refine And.intro ?_ ?_
                                                                                            · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                                List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                              rw [h20]
                                                                                              trivial
                                                                                            ·
                                                                                              rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 20 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h20) (by simp [execInstrRF_sb_snd])]
                                                                                              dsimp only
                                                                                              unfold blockVCs
                                                                                              refine And.intro ?_ ?_
                                                                                              · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                                  List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                rw [h11]
                                                                                                trivial
                                                                                              ·
                                                                                                rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 11 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h11)]
                                                                                                dsimp only
                                                                                                rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                                  truncate_zeroExtend_byte]
                                                                                                unfold blockVCs
                                                                                                refine And.intro ?_ ?_
                                                                                                · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                                    List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                  rw [h20]
                                                                                                  trivial
                                                                                                ·
                                                                                                  rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 20 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h20)]
                                                                                                  dsimp only
                                                                                                  rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                                                                                    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                                    truncate_zeroExtend_byte]
                                                                                                  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                                                                                  unfold blockVCs
                                                                                                  refine And.intro ?_ ?_
                                                                                                  · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                                      List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                    rw [h12]
                                                                                                    trivial
                                                                                                  ·
                                                                                                    rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 12 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h12) (by simp [execInstrRF_sb_snd])]
                                                                                                    dsimp only
                                                                                                    unfold blockVCs
                                                                                                    refine And.intro ?_ ?_
                                                                                                    · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                                        List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                      rw [h19]
                                                                                                      trivial
                                                                                                    ·
                                                                                                      rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 19 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h19) (by simp [execInstrRF_sb_snd])]
                                                                                                      dsimp only
                                                                                                      unfold blockVCs
                                                                                                      refine And.intro ?_ ?_
                                                                                                      · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                                          List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                        rw [h12]
                                                                                                        trivial
                                                                                                      ·
                                                                                                        rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 12 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h12)]
                                                                                                        dsimp only
                                                                                                        rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                                          truncate_zeroExtend_byte]
                                                                                                        unfold blockVCs
                                                                                                        refine And.intro ?_ ?_
                                                                                                        · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                                            List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                          rw [h19]
                                                                                                          trivial
                                                                                                        ·
                                                                                                          rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 19 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h19)]
                                                                                                          dsimp only
                                                                                                          rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                                                                                            RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                                            truncate_zeroExtend_byte]
                                                                                                          simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                                                                                          unfold blockVCs
                                                                                                          refine And.intro ?_ ?_
                                                                                                          · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                                              List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                            rw [h13]
                                                                                                            trivial
                                                                                                          ·
                                                                                                            rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 13 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h13) (by simp [execInstrRF_sb_snd])]
                                                                                                            dsimp only
                                                                                                            unfold blockVCs
                                                                                                            refine And.intro ?_ ?_
                                                                                                            · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                                                List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                              rw [h18]
                                                                                                              trivial
                                                                                                            ·
                                                                                                              rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 18 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h18) (by simp [execInstrRF_sb_snd])]
                                                                                                              dsimp only
                                                                                                              unfold blockVCs
                                                                                                              refine And.intro ?_ ?_
                                                                                                              · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                                                  List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                                rw [h13]
                                                                                                                trivial
                                                                                                              ·
                                                                                                                rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 13 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h13)]
                                                                                                                dsimp only
                                                                                                                rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                                                  truncate_zeroExtend_byte]
                                                                                                                unfold blockVCs
                                                                                                                refine And.intro ?_ ?_
                                                                                                                · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                                                    List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                                  rw [h18]
                                                                                                                  trivial
                                                                                                                ·
                                                                                                                  rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 18 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h18)]
                                                                                                                  dsimp only
                                                                                                                  rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                                                                                                    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                                                    truncate_zeroExtend_byte]
                                                                                                                  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                                                                                                  unfold blockVCs
                                                                                                                  refine And.intro ?_ ?_
                                                                                                                  · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                                                      List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                                    rw [h14]
                                                                                                                    trivial
                                                                                                                  ·
                                                                                                                    rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 14 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h14) (by simp [execInstrRF_sb_snd])]
                                                                                                                    dsimp only
                                                                                                                    unfold blockVCs
                                                                                                                    refine And.intro ?_ ?_
                                                                                                                    · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                                                        List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                                      rw [h17]
                                                                                                                      trivial
                                                                                                                    ·
                                                                                                                      rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 17 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h17) (by simp [execInstrRF_sb_snd])]
                                                                                                                      dsimp only
                                                                                                                      unfold blockVCs
                                                                                                                      refine And.intro ?_ ?_
                                                                                                                      · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                                                          List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                                        rw [h14]
                                                                                                                        trivial
                                                                                                                      ·
                                                                                                                        rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 14 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h14)]
                                                                                                                        dsimp only
                                                                                                                        rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                                                          truncate_zeroExtend_byte]
                                                                                                                        unfold blockVCs
                                                                                                                        refine And.intro ?_ ?_
                                                                                                                        · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                                                            List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                                          rw [h17]
                                                                                                                          trivial
                                                                                                                        ·
                                                                                                                          rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 17 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h17)]
                                                                                                                          dsimp only
                                                                                                                          rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                                                                                                            RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                                                            truncate_zeroExtend_byte]
                                                                                                                          simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                                                                                                          unfold blockVCs
                                                                                                                          refine And.intro ?_ ?_
                                                                                                                          · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                                                              List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                                            rw [h15]
                                                                                                                            trivial
                                                                                                                          ·
                                                                                                                            rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 15 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h15) (by simp [execInstrRF_sb_snd])]
                                                                                                                            dsimp only
                                                                                                                            unfold blockVCs
                                                                                                                            refine And.intro ?_ ?_
                                                                                                                            · simp only [loadSem, inRw, Region.loadOk, length_setBytes,
                                                                                                                                List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                                              rw [h16]
                                                                                                                              trivial
                                                                                                                            ·
                                                                                                                              rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 16 (by simp only [execInstrRF_sb_fst, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h16) (by simp [execInstrRF_sb_snd])]
                                                                                                                              dsimp only
                                                                                                                              unfold blockVCs
                                                                                                                              refine And.intro ?_ ?_
                                                                                                                              · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                                                                  List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                                                rw [h15]
                                                                                                                                trivial
                                                                                                                              ·
                                                                                                                                rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 15 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h15)]
                                                                                                                                dsimp only
                                                                                                                                rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                                                                  truncate_zeroExtend_byte]
                                                                                                                                unfold blockVCs
                                                                                                                                refine And.intro ?_ ?_
                                                                                                                                · simp only [loadSem, storeSem, inRw, length_setBytes, List.length_set,
                                                                                                                                    List.length_cons, List.length_nil, Nat.reduceAdd, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
                                                                                                                                  rw [h16]
                                                                                                                                  trivial
                                                                                                                                ·
                                                                                                                                  rw [execInstrRF_sb_byte _ _ _ _ _ _ _ 16 (by simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]; exact h16)]
                                                                                                                                  dsimp only
                                                                                                                                  rw [RegFile.get_set_ne _ _ _ _ (by decide),
                                                                                                                                    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
                                                                                                                                    truncate_zeroExtend_byte]
                                                                                                                                  simp only [List.set, List.getD_cons_zero, List.getD_cons_succ]
                                                                                                                                  unfold blockVCs
                                                                                                                                  trivial

theorem byteReverse32Fn_spec (p pc aux1 aux3 : Word) (w : List (BitVec 8))
    (base : Word) :
    (byteReverse32Fn p pc aux1 aux3 w).Spec base := by
  vcgen
  case keccakByteReverse.rev.focus =>
    rintro rf ws A ⟨hx10, hx11, hx12, hx13, hw, hA⟩ hApc hp hhp
    rw [hA] at hhp
    refine ⟨w, ⌜RwRegion.wf ⟨p, 32⟩⌝, ⟨hx12, rfl, rfl⟩, ?_, pcFree_pure, ?_⟩
    · rw [hx12]
      xperm_hyp hhp
    · rw [hx12, hw]
      exact ((sepConj_pure_left hp).mp hhp).1
  case keccakByteReverse.rev.mem =>
    rintro rf ws A win rest - ⟨-, -, -, -, hw, -⟩ ⟨hptr, rfl, rfl⟩ -
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩ := bytes32_of_length win hw
    exact byteReverse32_blockVCs _ rf b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31
  case keccakByteReverse.post =>
    rintro rf ws A ⟨rf₀, A₀, win, rest, -, ⟨hx10, hx11, hx12, hx13, hw, -⟩,
      -, ⟨hptr, rfl, rfl⟩, hrf, hA⟩
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩ := bytes32_of_length win hw
    rw [byteReverse32_engine] at hrf hA
    dsimp only at hrf hA
    subst hrf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x28)]
      exact hx10
    · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28)]
      exact hx11
    · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x28)]
      exact hx12
    · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x28)]
      exact hx13
    · rw [hA, hx12, sepConj_comm',
        show ([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] : List (BitVec 8)).reverse = [b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0] from rfl]

#print axioms byteReverse32Fn_spec

end KeccakReverseSAsm

end EvmAsm.Codegen
