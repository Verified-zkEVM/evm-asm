/-
  EvmAsm.Codegen.Programs.RequestsHashVerifyBase

  Shared geometry for the `requests_hash_verify` whole-routine proof (#12206
  item 2): symbolic base, `pc` indexing, the routine's `CodeReq` (its own text
  UNIONED with `assemble_execution_requests`, whose whole-routine contract this
  proof composes), and the pc-arithmetic lemmas the six transfers need.

  `requestsHashVerify_prog` (AssembleExecutionRequests.lean:167) is 36
  instructions, ending with `JALR x0, 0(ra)` at 0x800543d8 — 144 bytes,
  re-derived from the linked guest ELF with `llvm-objdump -d`, not transcribed.
  The routine's single address anchor (every other address below is derived
  from it) is GuestAddrs.requests_hash_verify = 0x8005434c.

  Index map (addresses are the linked guest image):
    0–3    (entry)     prologue: sp -= 32; sd ra/s0/s1 at 0/8/16
    4      0x8005435c  s0 := a6   (caller's expected 32-byte hash pointer)
    5      0x80054360  s1 := a7   (scratch SSZ section buffer pointer)
    6      0x80054364  a6 := a7   (the section buffer becomes AER's `out`)
    7      0x80054368  jal ra, assemble_execution_requests
    8      0x8005436c  a1 := a0   (AER's return value: total section length)
    9      0x80054370  a0 := s1   (the section buffer)
    10–11  0x80054374  a2 := &rhv_hash                (auipc/addi)
    12     0x8005437c  jal ra, execution_requests_hash
    13     0x80054380  bnez a0, +68 → 30              (hash call failed ⇒ a0 = 2)
    14–15  0x80054384  t0 := &rhv_hash                (auipc/addi)
    16     0x8005438c  t1 := s0   (expected hash cursor)
    17     0x80054390  t2 := 32   (byte counter)
    18     0x80054394  beqz t2, +32 → 26              [compare-loop top]
    19–20  0x80054398  t3 := [t0]; t4 := [t1]
    21     0x800543a0  bne t3, t4, +28 → 28           (mismatch ⇒ a0 = 1)
    22–24  0x800543a4  t0 += 1; t1 += 1; t2 -= 1
    25     0x800543b0  j -28 → 18
    26–27  0x800543b4  a0 := 0 (match); j +16 → 31
    28–29  0x800543bc  a0 := 1 (mismatch); j +8 → 31
    30     0x800543c4  a0 := 2 (hash call failed)
    31–34  0x800543c8  epilogue: ld ra/s0/s1 from 0/8/16; sp += 32
    35     0x800543d8  jalr x0, 0(ra)

  The single backward transfer is the `j -28` at index 25; the compare loop is
  the same seven-instruction shape as `MptWalkLeafCmp` / `MptWalkExtCmp`
  (BEQ top / LBU / LBU / BNE / three ADDIs / JAL back), at different registers.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.SAsm.LoopFuel
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.AssembleExecutionRequests
import EvmAsm.Codegen.Programs.AssembleExecutionRequestsBase

namespace EvmAsm.Codegen.RequestsHashVerifyBase

open EvmAsm.Rv64
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-- Symbolic entry address of `requests_hash_verify` (see the anchor above). -/
abbrev B : Word := BitVec.ofNat 64 GuestAddrs.requests_hash_verify

/-- Symbolic entry address of the composed callee `assemble_execution_requests`. -/
abbrev AerB : Word := AssembleExecutionRequestsBase.B

/-- Symbolic entry address of the residual callee `execution_requests_hash`. -/
abbrev ErhB : Word := BitVec.ofNat 64 GuestAddrs.execution_requests_hash

/-- The 32-byte BSS scratch the callee `execution_requests_hash` writes its
    derived `requests_hash` into (`GuestAddrs.rhv_hash`, `.bss`). Owned by this
    footprint: the frame must account for those 32 bytes. -/
abbrev RhvHash : Word := BitVec.ofNat 64 GuestAddrs.rhv_hash

/-- The routine's instruction list. -/
abbrev rhvProgL : List Instr := requestsHashVerify_prog

theorem rhvProgL_len : rhvProgL.length = 36 := by
  simp only [rhvProgL, requestsHashVerify_prog]; decide

theorem rhvProgL_bound : 4 * rhvProgL.length < 2 ^ 64 := by
  rw [rhvProgL_len]; norm_num

/-- The routine's own text. -/
def rhvOwnCode : CodeReq := CodeReq.ofProg B rhvProgL

/-- `CodeReq` covering `requests_hash_verify` **and** the composed callee
    `assemble_execution_requests`. The `execution_requests_hash` text is NOT
    unioned in: that call is discharged from a named residual hypothesis
    (`ErhCallShape`), which carries its own `cr` obligation. -/
def rhvCode : CodeReq := rhvOwnCode.union AssembleExecutionRequestsBase.aerCode

/-- Address of instruction `k`. -/
def pc (k : Nat) : Word := B + BitVec.ofNat 64 (4 * k)

theorem rhv_aer_disjoint :
    rhvOwnCode.Disjoint AssembleExecutionRequestsBase.aerCode := by
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [rhvProgL_len]; decide
  · rw [AssembleExecutionRequestsBase.aerProgL_len]; decide
  · right
    rw [AssembleExecutionRequestsBase.aerProgL_len]; decide

/-- The composed callee's `CodeReq` is subsumed by this routine's. -/
theorem aer_sub_rhvCode :
    ∀ a i, AssembleExecutionRequestsBase.aerCode a = some i → rhvCode a = some i :=
  CodeReq.mono_union_right rhv_aer_disjoint (fun _ _ h => h)

/-- Code membership for instruction `k` of the routine. -/
theorem mem_at (k : Nat) (ins : Instr) (a0 : Word)
    (hpc : a0 = B + BitVec.ofNat 64 (4 * k))
    (hk : k < rhvProgL.length)
    (hins : rhvProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton a0 ins a = some i → rhvCode a = some i := by
  intro a i hs
  exact CodeReq.union_mono_left a i
    (CodeReq.ofProg_mem_at B a0 rhvProgL k ins hpc hk hins rhvProgL_bound a i hs)

/-! ## pc arithmetic

    Every offset below is read off the linked disassembly; the `decide`s are
    kernel-checked against the concrete `GuestAddrs` constants. -/

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

/-- `bnez a0, +68` at index 13 (0x80054380) lands on the `li a0, 2`
    hash-failure exit at index 30 (0x800543c4). -/
theorem pc_bne_hashfail : (pc 13 : Word) + signExtend13 (68 : BitVec 13) = pc 30 := by
  have hs : signExtend13 (68 : BitVec 13) = BitVec.ofNat 64 (4 * 17) := by decide
  rw [hs, pc_add]

/-- `beqz t2, +32` at the loop top, index 18 (0x80054394), lands on the
    `li a0, 0` match exit at index 26 (0x800543b4). -/
theorem pc_beq_match : (pc 18 : Word) + signExtend13 (32 : BitVec 13) = pc 26 := by
  have hs : signExtend13 (32 : BitVec 13) = BitVec.ofNat 64 (4 * 8) := by decide
  rw [hs, pc_add]

/-- `bne t3, t4, +28` at index 21 (0x800543a0) lands on the `li a0, 1`
    mismatch exit at index 28 (0x800543bc). -/
theorem pc_bne_mismatch : (pc 21 : Word) + signExtend13 (28 : BitVec 13) = pc 28 := by
  have hs : signExtend13 (28 : BitVec 13) = BitVec.ofNat 64 (4 * 7) := by decide
  rw [hs, pc_add]

/-- The routine's only backward transfer: `j -28` at index 25 (0x800543b0)
    returns to the loop top at index 18. -/
theorem pc_jal_back : (pc 25 : Word) + signExtend21 (-28 : BitVec 21) = pc 18 := by
  have hs : signExtend21 (-28 : BitVec 21) = (-28 : Word) := by decide
  have h : (pc 18 : Word) + BitVec.ofNat 64 (4 * 7) = pc 25 := pc_add 18 7
  rw [hs, ← h, BitVec.add_assoc,
    show (BitVec.ofNat 64 (4 * 7) + (-28 : Word)) = 0 from by decide]
  simp

/-- `j +16` at index 27 (0x800543b8) joins the epilogue at index 31. -/
theorem pc_jal_match_join : (pc 27 : Word) + signExtend21 (16 : BitVec 21) = pc 31 := by
  have hs : signExtend21 (16 : BitVec 21) = BitVec.ofNat 64 (4 * 4) := by decide
  rw [hs, pc_add]

/-- `j +8` at index 29 (0x800543c0) joins the epilogue at index 31. -/
theorem pc_jal_mismatch_join : (pc 29 : Word) + signExtend21 (8 : BitVec 21) = pc 31 := by
  have hs : signExtend21 (8 : BitVec 21) = BitVec.ofNat 64 (4 * 2) := by decide
  rw [hs, pc_add]

/-! ## Call targets -/

/-- The `jal ra, assemble_execution_requests` at index 7 (0x80054368)
    transfers to the callee's entry. -/
theorem pc_jal_aer :
    (pc 7 : Word) +
      signExtend21 (jalOff GuestAddrs.assemble_execution_requests
        (GuestAddrs.requests_hash_verify + 28)) = AerB := by
  unfold pc AerB AssembleExecutionRequestsBase.B B jalOff signExtend21
  decide

/-- The `jal ra, execution_requests_hash` at index 12 (0x8005437c)
    transfers to the callee's entry. -/
theorem pc_jal_erh :
    (pc 12 : Word) +
      signExtend21 (jalOff GuestAddrs.execution_requests_hash
        (GuestAddrs.requests_hash_verify + 48)) = ErhB := by
  unfold pc ErhB B jalOff signExtend21
  decide

/-- Both call sites' return addresses are 2-byte aligned, so the callees'
    `ret` (`jalr x0, 0(ra)`, which masks the low bit) lands exactly on them. -/
theorem ra_aer_aligned : ((pc 7 : Word) + 4 &&& ~~~(1 : Word)) = pc 7 + 4 := by
  rw [pc_succ]; unfold pc B; decide

theorem ra_erh_aligned : ((pc 12 : Word) + 4 &&& ~~~(1 : Word)) = pc 12 + 4 := by
  rw [pc_succ]; unfold pc B; decide

end EvmAsm.Codegen.RequestsHashVerifyBase
