/-
  EvmAsm.Evm64.Dup.Program

  256-bit EVM DUP1-16: generic duplication of nth stack element.
  9 instructions (1 ADDI + 4 × (LD + SD)).
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Rv64

/-- One limb pair for DUP: LD x7 from source offset, SD x7 to destination offset. -/
private def dup_one_limb (n i : Nat) : Program :=
  LD .x7 .x12 (BitVec.ofNat 12 (n * 32 + i * 8)) ;;
  SD .x12 .x7 (BitVec.ofNat 12 (i * 8))

/-- Generic DUPn program (1-indexed): push copy of nth stack element on top.
    n=1 copies the top, n=2 copies the second element, etc.
    Uses 9 instructions: 1 ADDI + 4 × (LD + SD). -/
def evm_dup (n : Nat) : Program :=
  ADDI .x12 .x12 (-32) ;;
  dup_one_limb n 0 ;; dup_one_limb n 1 ;; dup_one_limb n 2 ;; dup_one_limb n 3

/-- CodeReq for generic DUPn: 9 instructions = 36 bytes.
    Built as an explicit union chain because symbolic n prevents ofProg reduction. -/
abbrev evm_dup_code (base : Word) (n : Nat) : CodeReq :=
  CodeReq.singleton base (.ADDI .x12 .x12 (-32))
  |>.union (CodeReq.singleton (base + 4)  (.LD .x7 .x12 (BitVec.ofNat 12 (n*32))))
  |>.union (CodeReq.singleton (base + 8)  (.SD .x12 .x7 (BitVec.ofNat 12 0)))
  |>.union (CodeReq.singleton (base + 12) (.LD .x7 .x12 (BitVec.ofNat 12 (n*32+8))))
  |>.union (CodeReq.singleton (base + 16) (.SD .x12 .x7 (BitVec.ofNat 12 8)))
  |>.union (CodeReq.singleton (base + 20) (.LD .x7 .x12 (BitVec.ofNat 12 (n*32+16))))
  |>.union (CodeReq.singleton (base + 24) (.SD .x12 .x7 (BitVec.ofNat 12 16)))
  |>.union (CodeReq.singleton (base + 28) (.LD .x7 .x12 (BitVec.ofNat 12 (n*32+24))))
  |>.union (CodeReq.singleton (base + 32) (.SD .x12 .x7 (BitVec.ofNat 12 24)))

end EvmAsm.Rv64
