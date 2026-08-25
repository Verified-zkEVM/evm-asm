/-
  EvmAsm.Codegen.Programs.AssembleExecutionRequestsBase

  Shared geometry for the `assemble_execution_requests` whole-routine proof
  (#12206): symbolic base, `pc` indexing, the routine's own `CodeReq`, and the
  pc-arithmetic lemmas the five identical byte-copy loops need.

  `assembleExecutionRequests_prog` (AssembleExecutionRequests.lean) is 80
  instructions at `GuestAddrs.assemble_execution_requests` and calls NOTHING,
  so its `CodeReq` is `CodeReq.ofProg B aerProgL` with no callee union — the
  reason this routine is the tractable entry point of #12206.

  Index map (see the module docstring of AssembleExecutionRequests.lean):
    0–12   offset header: five little-endian u32 offsets at out+0,4,8,12,16
    13     x6 := out + 20 (the write cursor)
    14–22  copy loop 1 (deposits,       a0/a1)
    23–31  copy loop 2 (withdrawals,    a2/a3)
    32–40  copy loop 3 (consolidations, a4/a5)
    41–53  copy loop 4 (builder deposits, `aer_bd_*` globals)
    54–66  copy loop 5 (builder exits,    `aer_be_*` globals)
    67–78  return value a0 = 20 + a1 + a3 + a5 + bd_len + be_len
    79     JALR x0, 0(ra)

  The five loops' BEQ tops sit at indices 16, 25, 34, 47 and 60; each loop is
  the same seven instructions, which is why `AssembleExecutionRequestsCopy`
  proves the loop ONCE parameterised over the top index.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.LoopFuel
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.AssembleExecutionRequests

namespace EvmAsm.Codegen.AssembleExecutionRequestsBase

open EvmAsm.Rv64
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-- Symbolic entry address of `assemble_execution_requests`. -/
abbrev B : Word := BitVec.ofNat 64 GuestAddrs.assemble_execution_requests

/-- The routine's instruction list. -/
abbrev aerProgL : List Instr := assembleExecutionRequests_prog

theorem aerProgL_len : aerProgL.length = 80 := by
  simp only [aerProgL, assembleExecutionRequests_prog]; decide

theorem aerProgL_bound : 4 * aerProgL.length < 2 ^ 64 := by
  rw [aerProgL_len]; norm_num

/-- The routine's own `CodeReq`. No callee union: the routine calls nothing. -/
def aerCode : CodeReq := CodeReq.ofProg B aerProgL

/-- Address of instruction `k`. -/
def pc (k : Nat) : Word := B + BitVec.ofNat 64 (4 * k)

/-- Code membership for instruction `k` of the routine. -/
theorem mem_at (k : Nat) (ins : Instr) (a0 : Word)
    (hpc : a0 = B + BitVec.ofNat 64 (4 * k))
    (hk : k < aerProgL.length)
    (hins : aerProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton a0 ins a = some i → aerCode a = some i := by
  intro a i hs
  exact CodeReq.ofProg_mem_at B a0 aerProgL k ins hpc hk hins aerProgL_bound a i hs

/-! ## pc arithmetic

    All three lemmas are generic in the instruction index, so the copy-loop
    proof can be stated over an arbitrary loop-top index `b` and instantiated
    at 16 / 25 / 34 / 47 / 60. -/

private theorem word_shift (b : Word) (i j : Nat) :
    b + BitVec.ofNat 64 i + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem pc_add (k j : Nat) : (pc k : Word) + BitVec.ofNat 64 (4 * j) = pc (k + j) := by
  simp only [pc, word_shift, Nat.mul_add]

theorem pc_succ (k : Nat) : (pc k : Word) + 4 = pc (k + 1) := by
  have h : (4 : Word) = BitVec.ofNat 64 (4 * 1) := by decide
  rw [h, pc_add]

/-- The five loops' forward exit: `BEQ x28, x0, +28` skips the six-instruction
    body and lands on the instruction after the backward `JAL`. -/
theorem pc_beq_exit (k : Nat) :
    (pc k : Word) + signExtend13 (28 : BitVec 13) = pc (k + 7) := by
  have hs : signExtend13 (28 : BitVec 13) = BitVec.ofNat 64 (4 * 7) := by decide
  rw [hs, pc_add]

/-- The five loops' backward transfer: `JAL x0, -24` from the last body
    instruction returns to the loop's `BEQ` top. -/
theorem pc_jal_back (k : Nat) :
    (pc (k + 6) : Word) + signExtend21 (-24 : BitVec 21) = pc k := by
  have hs : signExtend21 (-24 : BitVec 21) = (-24 : Word) := by decide
  have h24 : (pc k : Word) + BitVec.ofNat 64 (4 * 6) = pc (k + 6) := pc_add k 6
  rw [hs, ← h24, BitVec.add_assoc,
    show (BitVec.ofNat 64 (4 * 6) + (-24 : Word)) = 0 from by decide]
  simp

end EvmAsm.Codegen.AssembleExecutionRequestsBase
