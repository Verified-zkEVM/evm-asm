/-
  EvmAsm.Evm64.Swap.Program

  256-bit EVM SWAP1-16: generic swap of top with nth stack element.
  16 instructions (4 × (LD + LD + SD + SD)).
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Rv64

/-- One limb quad for SWAP: LD x7 from top, LD x6 from nth, SD x6 to top, SD x7 to nth. -/
private def swap_one_limb (n i : Nat) : Program :=
  LD .x7 .x12 (BitVec.ofNat 12 (i * 8)) ;;
  LD .x6 .x12 (BitVec.ofNat 12 (n * 32 + i * 8)) ;;
  SD .x12 .x6 (BitVec.ofNat 12 (i * 8)) ;;
  SD .x12 .x7 (BitVec.ofNat 12 (n * 32 + i * 8))

/-- Generic SWAPn program (1-indexed): swap the top element with the nth stack element.
    n=1 swaps top with 2nd, n=2 swaps top with 3rd, etc.
    Uses 16 instructions: 4 × (LD + LD + SD + SD). -/
def evm_swap (n : Nat) : Program :=
  swap_one_limb n 0 ;; swap_one_limb n 1 ;; swap_one_limb n 2 ;; swap_one_limb n 3

/-- CodeReq for generic SWAPn: 16 instructions = 64 bytes.
    Built as an explicit union chain because symbolic n prevents ofProg reduction. -/
abbrev evm_swap_code (base : Word) (n : Nat) : CodeReq :=
  -- Limb 0
  CodeReq.singleton base (.LD .x7 .x12 (BitVec.ofNat 12 0))
  |>.union (CodeReq.singleton (base + 4)  (.LD .x6 .x12 (BitVec.ofNat 12 (n*32))))
  |>.union (CodeReq.singleton (base + 8)  (.SD .x12 .x6 (BitVec.ofNat 12 0)))
  |>.union (CodeReq.singleton (base + 12) (.SD .x12 .x7 (BitVec.ofNat 12 (n*32))))
  -- Limb 1
  |>.union (CodeReq.singleton (base + 16) (.LD .x7 .x12 (BitVec.ofNat 12 8)))
  |>.union (CodeReq.singleton (base + 20) (.LD .x6 .x12 (BitVec.ofNat 12 (n*32+8))))
  |>.union (CodeReq.singleton (base + 24) (.SD .x12 .x6 (BitVec.ofNat 12 8)))
  |>.union (CodeReq.singleton (base + 28) (.SD .x12 .x7 (BitVec.ofNat 12 (n*32+8))))
  -- Limb 2
  |>.union (CodeReq.singleton (base + 32) (.LD .x7 .x12 (BitVec.ofNat 12 16)))
  |>.union (CodeReq.singleton (base + 36) (.LD .x6 .x12 (BitVec.ofNat 12 (n*32+16))))
  |>.union (CodeReq.singleton (base + 40) (.SD .x12 .x6 (BitVec.ofNat 12 16)))
  |>.union (CodeReq.singleton (base + 44) (.SD .x12 .x7 (BitVec.ofNat 12 (n*32+16))))
  -- Limb 3
  |>.union (CodeReq.singleton (base + 48) (.LD .x7 .x12 (BitVec.ofNat 12 24)))
  |>.union (CodeReq.singleton (base + 52) (.LD .x6 .x12 (BitVec.ofNat 12 (n*32+24))))
  |>.union (CodeReq.singleton (base + 56) (.SD .x12 .x6 (BitVec.ofNat 12 24)))
  |>.union (CodeReq.singleton (base + 60) (.SD .x12 .x7 (BitVec.ofNat 12 (n*32+24))))

end EvmAsm.Rv64
