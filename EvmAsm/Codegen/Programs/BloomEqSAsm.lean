/-
  EvmAsm.Codegen.Programs.BloomEqSAsm

  `bloom_eq` via the **single-exit accumulate loop**
  (`EvmAsm/Rv64/SAsm/AccumLoop.lean`, bead evm-asm-pr5lu) — the
  acceptance consumer.

  The routine compares two 256-byte bloom filters dword-by-dword with a
  constant cycle count (no early exit — timing invariance for gas-cost
  modeling): 32 iterations of `LD/LD/XOR/OR`, then the verdict
  `acc == 0` is materialized by `SLTIU` and stored to the u64 out cell.

  **Genuine post** (`bloomEq_spec`): the out dword is
  `if bsA = bsB then 1 else 0` — REAL byte-list equality of the two
  256-byte inputs (accumulator residue → per-slot facts → byte equality
  via `xorAcc_eq_zero_iff_bytes_eq`), `a0 = 0`, both inputs untouched.

  Byte-transparent: stated at the `#guard`-tied `GuestAddrs.bloom_eq`
  directly over the emitted `bloomEq_prog` (no byte change, no A/B).
-/

import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Rv64.SAsm.AccumLoop
import EvmAsm.Rv64.SAsm.RetForwardJoin
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.AccumLoop

namespace BloomEqSAsm

/-
  Layout (base GuestAddrs.bloom_eq):
    +0  GuestAddrs.bloom_eq  li   x5, 32
    +4  (GuestAddrs.bloom_eq + 4)  mv   x6, x10
    +8  (GuestAddrs.bloom_eq + 8)  mv   x7, x11
    +12 (GuestAddrs.bloom_eq + 12)  li   x30, 0
    +16 (GuestAddrs.bloom_eq + 16)  beq  x5, x0, +36  → (GuestAddrs.bloom_eq + 52)   [hdr]
    +20 (GuestAddrs.bloom_eq + 20)  ld   x28, 0(x6)
    +24 (GuestAddrs.bloom_eq + 24)  ld   x29, 0(x7)
    +28 (GuestAddrs.bloom_eq + 28)  xor  x28, x28, x29
    +32 (GuestAddrs.bloom_eq + 32)  or   x30, x30, x28
    +36 (GuestAddrs.bloom_eq + 36)  addi x6, x6, 8
    +40 (GuestAddrs.bloom_eq + 40)  addi x7, x7, 8
    +44 (GuestAddrs.bloom_eq + 44)  addi x5, x5, -1
    +48 (GuestAddrs.bloom_eq + 48)  jal  x0, -32      → (GuestAddrs.bloom_eq + 16)
    +52 (GuestAddrs.bloom_eq + 52)  sltiu x30, x30, 1
    +56 (GuestAddrs.bloom_eq + 56)  sd   x12, x30, 0
    +60 (GuestAddrs.bloom_eq + 60)  li   x10, 0
    +64 (GuestAddrs.bloom_eq + 64)  jalr x0, x1, 0
-/

section Scan

variable (aPtr bPtr outPtr ret : Word) (bsA bsB : List (BitVec 8))

private theorem ctr_dec (i : Nat) (hi : i < 32) :
    BitVec.ofNat 64 (32 - i) + signExtend12 (-1 : BitVec 12)
      = BitVec.ofNat 64 (32 - (i + 1)) := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
  omega

private theorem cursor_advance (p : Word) (i : Nat) :
    p + BitVec.ofNat 64 (8 * i) + signExtend12 (8 : BitVec 12)
      = p + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show ((8 : Word)).toNat = 8 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem ctr_ne_zero (i : Nat) (hi : i < 32) :
    ¬ (BitVec.ofNat 64 (32 - i) = (0 : Word)) := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, show ((0 : Word)).toNat = 0 from rfl] at this
  omega

/-- Loop invariant at the header after `i` dwords: counter `32 - i`,
    cursors at dword `i`, the accumulator at `xorAcc bsA bsB i` — a pure
    function of the inputs, no existential residue. -/
private def beInv (i : Nat) : Assertion :=
  ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
  ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * i))) **
  ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * i))) **
  ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB i) **
  ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
  ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x28 ** regOwn .x29 **
  bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr

/-- The genuine post: out dword = byte-list equality verdict, `a0 = 0`,
    inputs untouched. -/
private def bePost : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
  ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 **
  bytesRegion aPtr bsA ** bytesRegion bPtr bsB **
  (outPtr ↦ₘ (if bsA = bsB then (1 : Word) else (0 : Word)))

/-- One iteration: header guard (never taken), two cursor dword loads,
    XOR/OR accumulate, advance, loop back — invariant advanced. -/
private theorem beIter_spec
    (hlenA : bsA.length = 256) (hlenB : bsB.length = 256)
    (i : Nat) (hi : i < 32) :
    cpsTripleWithin 9 ((GuestAddrs.bloom_eq + 16) : Word) ((GuestAddrs.bloom_eq + 16) : Word)
      (CodeReq.ofProg (GuestAddrs.bloom_eq : Word) bloomEq_prog)
      (beInv aPtr bPtr outPtr ret bsA bsB i)
      (beInv aPtr bPtr outPtr ret bsA bsB (i + 1)) := by
  set CR := CodeReq.ofProg (GuestAddrs.bloom_eq : Word) bloomEq_prog with hCR
  unfold beInv
  -- peel this iteration's scratch registers x28, x29
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x28)
      (P := (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * i))) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * i))) **
        ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB i) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr) **
        regOwn .x29)
      (fun v28 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x29)
      (P := (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * i))) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * i))) **
        ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB i) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr) **
        ((.x28 : Reg) ↦ᵣ v28))
      (fun v29 => ?_))
  -- ---- the body instructions ----
  have hldA := liftCode (cr' := CR)
    (bytesRegion_ld_cursor_within .x28 .x6 aPtr v28 ((GuestAddrs.bloom_eq + 20) : Word)
      bsA i (by decide) (by omega))
    (by rw [hCR]; code_mem)
  rw [show ((GuestAddrs.bloom_eq + 20) : Word) + 4 = ((GuestAddrs.bloom_eq + 24) : Word) from by decide,
      show packBytes ((bsA.drop (8 * i)).take 8) = dwordSlot bsA i from rfl]
    at hldA
  have hldB := liftCode (cr' := CR)
    (bytesRegion_ld_cursor_within .x29 .x7 bPtr v29 ((GuestAddrs.bloom_eq + 24) : Word)
      bsB i (by decide) (by omega))
    (by rw [hCR]; code_mem)
  rw [show ((GuestAddrs.bloom_eq + 24) : Word) + 4 = ((GuestAddrs.bloom_eq + 28) : Word) from by decide,
      show packBytes ((bsB.drop (8 * i)).take 8) = dwordSlot bsB i from rfl]
    at hldB
  have hxor := liftCode (cr' := CR)
    (xor_spec_gen_rd_eq_rs1_within .x28 .x29 (dwordSlot bsA i)
      (dwordSlot bsB i) ((GuestAddrs.bloom_eq + 28) : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show ((GuestAddrs.bloom_eq + 28) : Word) + 4 = ((GuestAddrs.bloom_eq + 32) : Word) from by decide]
    at hxor
  have hor := liftCode (cr' := CR)
    (or_spec_gen_rd_eq_rs1_within .x30 .x28
      (xorAcc bsA bsB i) (dwordSlot bsA i ^^^ dwordSlot bsB i)
      ((GuestAddrs.bloom_eq + 32) : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show ((GuestAddrs.bloom_eq + 32) : Word) + 4 = ((GuestAddrs.bloom_eq + 36) : Word) from by decide]
    at hor
  have haddi6 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x6 (aPtr + BitVec.ofNat 64 (8 * i))
      (8 : BitVec 12) ((GuestAddrs.bloom_eq + 36) : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [cursor_advance aPtr i,
      show ((GuestAddrs.bloom_eq + 36) : Word) + 4 = ((GuestAddrs.bloom_eq + 40) : Word) from by decide]
    at haddi6
  have haddi7 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x7 (bPtr + BitVec.ofNat 64 (8 * i))
      (8 : BitVec 12) ((GuestAddrs.bloom_eq + 40) : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [cursor_advance bPtr i,
      show ((GuestAddrs.bloom_eq + 40) : Word) + 4 = ((GuestAddrs.bloom_eq + 44) : Word) from by decide]
    at haddi7
  have haddi5 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x5 (BitVec.ofNat 64 (32 - i))
      (-1 : BitVec 12) ((GuestAddrs.bloom_eq + 44) : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [ctr_dec i hi,
      show ((GuestAddrs.bloom_eq + 44) : Word) + 4 = ((GuestAddrs.bloom_eq + 48) : Word) from by decide]
    at haddi5
  have hjal := liftCode (cr' := CR)
    (jal_x0_spec_gen_within (-32 : BitVec 21) ((GuestAddrs.bloom_eq + 48) : Word))
    (by rw [hCR]; code_mem)
  rw [show ((GuestAddrs.bloom_eq + 48) : Word) + signExtend21 (-32 : BitVec 21)
    = ((GuestAddrs.bloom_eq + 16) : Word) from by decide] at hjal
  -- ---- frames + chain of the body (from (GuestAddrs.bloom_eq + 20)) ----
  have hldAF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * i))) **
      ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB i) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
      bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf) hldA
  have hldBF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * i))) **
      ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB i) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ dwordSlot bsA i) **
      bytesRegion aPtr bsA ** memOwn outPtr)
    (by pcf) hldB
  have hxorF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * i))) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * i))) **
      ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB i) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf) hxor
  have horF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * i))) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * i))) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x29 : Reg) ↦ᵣ dwordSlot bsB i) **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf) hor
  have haddi6F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * i))) **
      ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB (i + 1)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ (dwordSlot bsA i ^^^ dwordSlot bsB i)) **
      ((.x29 : Reg) ↦ᵣ dwordSlot bsB i) **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf) haddi6
  have haddi7F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * (i + 1)))) **
      ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB (i + 1)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ (dwordSlot bsA i ^^^ dwordSlot bsB i)) **
      ((.x29 : Reg) ↦ᵣ dwordSlot bsB i) **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf) haddi7
  have haddi5F := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * (i + 1)))) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * (i + 1)))) **
      ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB (i + 1)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ (dwordSlot bsA i ^^^ dwordSlot bsB i)) **
      ((.x29 : Reg) ↦ᵣ dwordSlot bsB i) **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf) haddi5
  have hjalF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
      ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * (i + 1)))) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * (i + 1)))) **
      ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB (i + 1)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ (dwordSlot bsA i ^^^ dwordSlot bsB i)) **
      ((.x29 : Reg) ↦ᵣ dwordSlot bsB i) **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf) hjal
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hldAF hldBF
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc1 hxorF
  have hc3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc2 horF
  have hc4 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [← xorAcc_succ] at hp
      xperm_hyp hp) hc3 haddi6F
  have hc5 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc4 haddi7F
  have hc6 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc5 haddi5F
  have hc7 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [sepConj_emp_left']
      xperm_hyp hp) hc6 hjalF
  -- ---- header guard station (never taken at i < 32) ----
  have hbrHdr := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * i))) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * i))) **
      ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB i) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x5 .x0 (36 : BitVec 13)
        (BitVec.ofNat 64 (32 - i)) (0 : Word) ((GuestAddrs.bloom_eq + 16) : Word))
      (hmono := by rw [hCR]; code_mem))
  rw [show ((GuestAddrs.bloom_eq + 16) : Word) + signExtend13 (36 : BitVec 13)
        = ((GuestAddrs.bloom_eq + 52) : Word) from by decide,
      show ((GuestAddrs.bloom_eq + 16) : Word) + 4 = ((GuestAddrs.bloom_eq + 20) : Word) from by decide]
    at hbrHdr
  -- the body must re-own x28/x29 into the invariant
  have hbody : cpsTripleWithin 8 ((GuestAddrs.bloom_eq + 20) : Word) ((GuestAddrs.bloom_eq + 16) : Word) CR
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * i))) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * i))) **
        ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB i) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
        bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
      (beInv aPtr bPtr outPtr ret bsA bsB (i + 1)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => ?_) hc7
    rw [sepConj_emp_left'] at hq
    unfold beInv
    have hq1 : (((.x28 : Reg) ↦ᵣ (dwordSlot bsA i ^^^ dwordSlot bsB i)) **
        (((.x29 : Reg) ↦ᵣ dwordSlot bsB i) **
          (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
           ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * (i + 1)))) **
           ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * (i + 1)))) **
           ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB (i + 1)) **
           ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
           ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion aPtr bsA ** bytesRegion bPtr bsB **
           memOwn outPtr))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x28 _)
      (sepConj_mono (regIs_to_regOwn .x29 _)
        (fun _ hh => hh)) h hq1
    xperm_hyp hq2
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (retJoinStation_spec
      (cond := (BitVec.ofNat 64 (32 - i) = (0 : Word)))
      (PT := ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * i))) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * i))) **
        ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB i) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
        bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
      (PF := ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * i))) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * i))) **
        ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB i) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
        bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
      hbrHdr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun hc => absurd hc (ctr_ne_zero i hi))
      (fun _ => cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) hbody))

/-- Exhaustion: header guard taken, `SLTIU` materializes the verdict,
    `SD` stores it, `a0 := 0`, `ret`. -/
private theorem beExh_spec
    (hlenA : bsA.length = 256) (hlenB : bsB.length = 256)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 5 ((GuestAddrs.bloom_eq + 16) : Word) ret
      (CodeReq.ofProg (GuestAddrs.bloom_eq : Word) bloomEq_prog)
      (beInv aPtr bPtr outPtr ret bsA bsB 32)
      (bePost aPtr bPtr outPtr ret bsA bsB) := by
  set CR := CodeReq.ofProg (GuestAddrs.bloom_eq : Word) bloomEq_prog with hCR
  unfold beInv
  have hflag : (if BitVec.ult (xorAcc bsA bsB 32) (1 : Word)
      then (1 : Word) else (0 : Word))
      = (if bsA = bsB then (1 : Word) else (0 : Word)) := by
    by_cases hEq : bsA = bsB
    · rw [if_pos hEq,
        (xorAcc_eq_zero_iff_bytes_eq bsA bsB 32 (by omega) (by omega)).mpr
          hEq]
      rw [if_pos (by decide)]
    · rw [if_neg hEq, if_neg ?_]
      intro hlt
      have hz : xorAcc bsA bsB 32 = 0 := by
        apply BitVec.eq_of_toNat_eq
        have h1 : (xorAcc bsA bsB 32).toNat < ((1 : Word)).toNat := by
          simpa [BitVec.ult, decide_eq_true_eq] using hlt
        rw [show ((1 : Word)).toNat = 1 from rfl] at h1
        rw [show ((0 : Word)).toNat = 0 from rfl]
        omega
      exact hEq
        ((xorAcc_eq_zero_iff_bytes_eq bsA bsB 32 (by omega) (by omega)).mp hz)
  -- sltiu x30, x30, 1
  have hsltiu := liftCode (cr' := CR)
    (sltiu_spec_gen_same_within .x30 (xorAcc bsA bsB 32) (1 : BitVec 12)
      ((GuestAddrs.bloom_eq + 52) : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      hflag,
      show ((GuestAddrs.bloom_eq + 52) : Word) + 4 = ((GuestAddrs.bloom_eq + 56) : Word) from by decide]
    at hsltiu
  -- sd x30, 0(x12)
  have hsd := liftCode (cr' := CR)
    (sd_spec_gen_own_within .x12 .x30 outPtr
      (if bsA = bsB then (1 : Word) else (0 : Word)) (0 : BitVec 12)
      ((GuestAddrs.bloom_eq + 56) : Word))
    (by rw [hCR]; code_mem)
  rw [show outPtr + signExtend12 (0 : BitVec 12) = outPtr from by
        rw [signExtend12_0]; bv_omega,
      show ((GuestAddrs.bloom_eq + 56) : Word) + 4 = ((GuestAddrs.bloom_eq + 60) : Word) from by decide]
    at hsd
  -- li a0, 0
  have hli := liftCode (cr' := CR)
    (li_spec_gen_within .x10 aPtr (0 : Word) ((GuestAddrs.bloom_eq + 60) : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show ((GuestAddrs.bloom_eq + 60) : Word) + 4 = ((GuestAddrs.bloom_eq + 64) : Word) from by decide]
    at hli
  -- ret
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' ((GuestAddrs.bloom_eq + 64) : Word) ret)
    (by rw [hCR]; code_mem)
  rw [halignRet] at hret
  -- frames
  have hsltiuF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
      ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * 32))) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * 32))) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf) hsltiu
  have hsdF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
      ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * 32))) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * 32))) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB)
    (by pcf) hsd
  have hliF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
      ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * 32))) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * 32))) **
      ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x30 : Reg) ↦ᵣ (if bsA = bsB then (1 : Word) else (0 : Word))) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB **
      (outPtr ↦ₘ (if bsA = bsB then (1 : Word) else (0 : Word))))
    (by pcf) hli
  have hretF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
      ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * 32))) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * 32))) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x30 : Reg) ↦ᵣ (if bsA = bsB then (1 : Word) else (0 : Word))) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB **
      (outPtr ↦ₘ (if bsA = bsB then (1 : Word) else (0 : Word))))
    (by pcf) hret
  -- tail chain
  have htail := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsltiuF hsdF
  have htail2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) htail hliF
  have htail3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) htail2 hretF
  -- the tail weakened into the genuine post
  have htailQ : cpsTripleWithin 4 ((GuestAddrs.bloom_eq + 52) : Word) ret CR
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * 32))) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * 32))) **
        ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB 32) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29 **
        bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
      (bePost aPtr bPtr outPtr ret bsA bsB) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => ?_) htail3
    unfold bePost
    have hq1 : (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        (((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * 32))) **
          (((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * 32))) **
            (((.x30 : Reg) ↦ᵣ (if bsA = bsB then (1 : Word) else (0 : Word))) **
              (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
               ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
               ((.x0 : Reg) ↦ᵣ (0 : Word)) **
               regOwn .x28 ** regOwn .x29 **
               bytesRegion aPtr bsA ** bytesRegion bPtr bsB **
               (outPtr ↦ₘ (if bsA = bsB then (1 : Word) else (0 : Word)))))))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x30 _)
            (fun _ hh => hh)))) h hq1
    xperm_hyp hq2
  -- header guard, taken (counter = 0)
  have hbrHdr := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * 32))) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * 32))) **
      ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB 32) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x5 .x0 (36 : BitVec 13)
        (BitVec.ofNat 64 (32 - 32)) (0 : Word) ((GuestAddrs.bloom_eq + 16) : Word))
      (hmono := by rw [hCR]; code_mem))
  rw [show ((GuestAddrs.bloom_eq + 16) : Word) + signExtend13 (36 : BitVec 13)
        = ((GuestAddrs.bloom_eq + 52) : Word) from by decide,
      show ((GuestAddrs.bloom_eq + 16) : Word) + 4 = ((GuestAddrs.bloom_eq + 20) : Word) from by decide]
    at hbrHdr
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (retJoinStation_spec
      (cond := (BitVec.ofNat 64 (32 - 32) = (0 : Word)))
      (PT := ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * 32))) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * 32))) **
        ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB 32) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29 **
        bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
      (PF := ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (8 * 32))) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (8 * 32))) **
        ((.x30 : Reg) ↦ᵣ xorAcc bsA bsB 32) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29 **
        bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
      hbrHdr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun _ => htailQ)
      (fun hc => absurd (by decide :
        (BitVec.ofNat 64 (32 - 32) : Word) = (0 : Word)) hc))

end Scan

-- ============================================================================
-- The whole routine
-- ============================================================================

/-- **`bloom_eq` at its linked address** (genuine post): the out dword is
    `1` iff the two 256-byte blooms are byte-equal, else `0`; `a0 = 0`;
    both inputs untouched. -/
theorem bloomEq_spec (aPtr bPtr outPtr ret : Word) (bsA bsB : List (BitVec 8))
    (hlenA : bsA.length = 256) (hlenB : bsB.length = 256)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 297 (GuestAddrs.bloom_eq : Word) ret
      (CodeReq.ofProg (GuestAddrs.bloom_eq : Word) bloomEq_prog)
      (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 **
        bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 **
        bytesRegion aPtr bsA ** bytesRegion bPtr bsB **
        (outPtr ↦ₘ (if bsA = bsB then (1 : Word) else (0 : Word)))) := by
  set CR := CodeReq.ofProg (GuestAddrs.bloom_eq : Word) bloomEq_prog with hCR
  -- peel x5, x6, x7, x30 for the init writes
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [regOwns_cons, regOwns_nil, sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns [.x5, .x6, .x7, .x30] (by decide)
      (P := ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 ** regOwn .x29 **
        bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
      (fun vf => ?_))
  simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
  -- ---- init: li x5, 32 ; mv x6, a0 ; mv x7, a1 ; li x30, 0 ----
  have hli5 := liftCode (cr' := CR)
    (li_spec_gen_within .x5 (vf .x5) (32 : Word) (GuestAddrs.bloom_eq : Word)
      (by decide))
    (by rw [hCR]; code_mem)
  rw [show (GuestAddrs.bloom_eq : Word) + 4 = ((GuestAddrs.bloom_eq + 4) : Word) from by decide]
    at hli5
  have hmv6 := liftCode (cr' := CR)
    (mv_spec_gen_within .x6 .x10 aPtr (vf .x6) ((GuestAddrs.bloom_eq + 4) : Word)
      (by decide))
    (by rw [hCR]; code_mem)
  rw [show ((GuestAddrs.bloom_eq + 4) : Word) + 4 = ((GuestAddrs.bloom_eq + 8) : Word) from by decide]
    at hmv6
  have hmv7 := liftCode (cr' := CR)
    (mv_spec_gen_within .x7 .x11 bPtr (vf .x7) ((GuestAddrs.bloom_eq + 8) : Word)
      (by decide))
    (by rw [hCR]; code_mem)
  rw [show ((GuestAddrs.bloom_eq + 8) : Word) + 4 = ((GuestAddrs.bloom_eq + 12) : Word) from by decide]
    at hmv7
  have hli30 := liftCode (cr' := CR)
    (li_spec_gen_within .x30 (vf .x30) (0 : Word) ((GuestAddrs.bloom_eq + 12) : Word)
      (by decide))
    (by rw [hCR]; code_mem)
  rw [show ((GuestAddrs.bloom_eq + 12) : Word) + 4 = ((GuestAddrs.bloom_eq + 16) : Word) from by decide]
    at hli30
  -- ---- the loop ----
  have hloop := retLoop_spec (hdr := ((GuestAddrs.bloom_eq + 16) : Word)) (ret := ret)
    (cr := CR) (Q := bePost aPtr bPtr outPtr ret bsA bsB) 32 9 5
    (beInv aPtr bPtr outPtr ret bsA bsB)
    (fun i hi => beIter_spec aPtr bPtr outPtr ret bsA bsB hlenA hlenB i hi)
    (beExh_spec aPtr bPtr outPtr ret bsA bsB hlenA hlenB halignRet)
  -- ---- frames + chain ----
  have hli5F := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ vf .x6) ** ((.x7 : Reg) ↦ᵣ vf .x7) **
      ((.x30 : Reg) ↦ᵣ vf .x30) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf) hli5
  have hmv6F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x7 : Reg) ↦ᵣ vf .x7) **
      ((.x30 : Reg) ↦ᵣ vf .x30) **
      ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf) hmv6
  have hmv7F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x6 : Reg) ↦ᵣ aPtr) **
      ((.x30 : Reg) ↦ᵣ vf .x30) **
      ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf) hmv7
  have hli30F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x6 : Reg) ↦ᵣ aPtr) **
      ((.x7 : Reg) ↦ᵣ bPtr) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr bsA ** bytesRegion bPtr bsB ** memOwn outPtr)
    (by pcf) hli30
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hli5F hmv6F
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc1 hmv7F
  have hc3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc2 hli30F
  have hc4 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold beInv
      rw [show (BitVec.ofNat 64 (32 - 0) : Word) = (32 : Word) from by decide,
          show aPtr + BitVec.ofNat 64 (8 * 0) = aPtr from by
            rw [show (BitVec.ofNat 64 (8 * 0) : Word) = (0 : Word) from rfl]
            bv_omega,
          show bPtr + BitVec.ofNat 64 (8 * 0) = bPtr from by
            rw [show (BitVec.ofNat 64 (8 * 0) : Word) = (0 : Word) from rfl]
            bv_omega,
          show xorAcc bsA bsB 0 = (0 : Word) from rfl]
      xperm_hyp hp) hc3 hloop
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by unfold bePost at hq; exact hq)
    (cpsTripleWithin_mono_nSteps (by omega) hc4)


end BloomEqSAsm

end EvmAsm.Codegen
