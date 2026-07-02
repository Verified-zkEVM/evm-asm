/-
  EvmAsm.Codegen.Programs.KeccakReverseSAsm

  SAsm-shaped byte-reverse body for the KECCAK256 dispatcher tail.  The
  emitted program reverses the 32-byte cell at `a2` in place using only
  byte loads/stores and t2/t3 as temporaries.
-/

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

end KeccakReverseSAsm

end EvmAsm.Codegen
