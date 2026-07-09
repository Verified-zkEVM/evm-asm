/-
  EvmAsm.Codegen.Programs.U256LtBeSAsm

  `u256_lt_be` via the **return-terminating two-break combinator with
  writable-output tails** (`EvmAsm/Rv64/SAsm/TwoBreakWritable.lean`,
  bead evm-asm-i177q) — the acceptance consumer.

  The routine byte-walks the two 32-byte big-endian operands with a
  countdown counter and advancing cursors, and routes THREE exits to TWO
  writable-output return tails:

  ```
        li   t0, 32 ; mv t1, a0 ; mv t2, a1
  hdr:  beq  t0, x0, .tail0            -- exhaustion (equal) → write 0
        lbu  x28, 0(t1) ; lbu x29, 0(t2)
        bltu x28, x29, .tail1          -- a[i] < b[i]        → write 1
        bltu x29, x28, .tail0          -- b[i] < a[i]        → write 0
        addi t1, t1, 1 ; addi t2, t2, 1 ; addi t0, t0, -1 ; j hdr
  .tail1: li x30, 1 ; sd x30, 0(a2) ; li a0, 0 ; ret
  .tail0:             sd x0,  0(a2) ; li a0, 0 ; ret
  ```

  Each tail is one `storeRetTail_spec` instance (distinct stored values:
  the `li`-loaded `1` vs the hardwired `x0` zero); each `bltu` is one
  `breakStation_spec`; the loop is one `twoBreakRetLoop_spec`.

  **Genuine post**: the output dword `[a2]` is
  `if beBytesToNat as < beBytesToNat bs then 1 else 0` — the REAL numeric
  less-than (big-endian lexicographic order IS numeric order, by
  `U256MinSAsm.beBytesToNat_lt_of_prefix_lt`), `a0 = 0`, both inputs
  untouched.

  Byte-transparent: the spec is stated at the `#guard`-tied
  `GuestAddrs.u256_lt_be` over the emitted `u256LtBe_prog` directly — no
  guest-byte change, no A/B run needed.

  Unblocks `secf_reduce_once` (bead evm-asm-4ch8f.38.2.4.1), whose closure
  calls `u256_lt_be`.
-/

import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.U256MinSAsm
import EvmAsm.Rv64.SAsm.TwoBreakWritable

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace U256LtBeSAsm

open U256MinSAsm (beBytesToNat_lt_of_prefix_lt bytes_eq_of_prefix_all)

-- Address anchor (fails the build if the guest link moves).
#guard GuestAddrs.u256_lt_be = 0x80005154

/-
  Emitted layout (base 0x80005154):
    +0  0x80005154  li   x5, 32
    +4  0x80005158  mv   x6, x10
    +8  0x8000515C  mv   x7, x11
    +12 0x80005160  beq  x5, x0, +52   → 0x80005194 (tail 0)   [hdr]
    +16 0x80005164  lbu  x28, 0(x6)
    +20 0x80005168  lbu  x29, 0(x7)
    +24 0x8000516C  bltu x28, x29, +24 → 0x80005184 (tail 1)
    +28 0x80005170  bltu x29, x28, +36 → 0x80005194 (tail 0)
    +32 0x80005174  addi x6, x6, 1
    +36 0x80005178  addi x7, x7, 1
    +40 0x8000517C  addi x5, x5, -1
    +44 0x80005180  jal  x0, -32       → 0x80005160
    +48 0x80005184  li   x30, 1                                [tail 1]
    +52 0x80005188  sd   x30, 0(x12)
    +56 0x8000518C  li   x10, 0
    +60 0x80005190  jalr x0, x1, 0
    +64 0x80005194  sd   x0, 0(x12)                            [tail 0]
    +68 0x80005198  li   x10, 0
    +72 0x8000519C  jalr x0, x1, 0
-/

-- ============================================================================
-- §1  Word-arithmetic helpers (countdown counter / advancing cursors)
-- ============================================================================

private theorem counter_dec (i : Nat) (hi : i < 32) :
    BitVec.ofNat 64 (32 - i) + signExtend12 (-1 : BitVec 12)
      = BitVec.ofNat 64 (32 - (i + 1)) := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
  omega

private theorem cursor_advance (p : Word) (i : Nat) :
    p + BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12)
      = p + BitVec.ofNat 64 (i + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show ((1 : Word)).toNat = 1 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem ctr_ne_zero (i : Nat) (hi : i < 32) :
    ¬ (BitVec.ofNat 64 (32 - i) = (0 : Word)) := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, show ((0 : Word)).toNat = 0 from rfl] at this
  omega

-- ============================================================================
-- §2  Invariant and genuine post
-- ============================================================================

section Scan

variable (aPtr bPtr outPtr ret : Word) (as bs : List (BitVec 8))

/-- Loop invariant at the header after `i` matched bytes: the counter holds
    `32 - i`, both cursors sit at byte `i`, the first `i` bytes agree
    (pure conjunct), the fixed registers and both input regions are
    untouched, and the output dword cell is still merely OWNED (no write
    has happened). -/
private def ltInv (i : Nat) : Assertion :=
  ⌜∀ j, j < i → as.getD j 0 = bs.getD j 0⌝ **
  ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
  ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
  ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
  ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
  ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
  bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr

/-- The genuine post: `a0 = 0`, the output dword `[a2]` is the REAL
    numeric less-than flag, both inputs untouched. -/
private def ltPost : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
  ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
  bytesRegion aPtr as ** bytesRegion bPtr bs **
  (outPtr ↦ₘ (if beBytesToNat as < beBytesToNat bs
    then (1 : Word) else (0 : Word)))

-- ============================================================================
-- §3  The two writable-output return tails
-- ============================================================================

/-- Tail 1 (`li x30, 1 ; sd x30, 0(a2) ; li a0, 0 ; ret`): writes the
    dword `1` to the owned output cell and returns `a0 = 0`. -/
private theorem tail1_spec (a0Old : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 4 (0x80005184 : Word) ret
      (CodeReq.ofProg (0x80005154 : Word) u256LtBe_prog)
      (regOwn .x30 ** ((.x12 : Reg) ↦ᵣ outPtr) ** memOwn outPtr **
        ((.x10 : Reg) ↦ᵣ a0Old) ** ((.x1 : Reg) ↦ᵣ ret))
      (((.x30 : Reg) ↦ᵣ (1 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        (outPtr ↦ₘ (1 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ ret)) := by
  set CR := CodeReq.ofProg (0x80005154 : Word) u256LtBe_prog with hCR
  have hli := liftCode (cr' := CR)
    (li_spec_gen_own_within .x30 (1 : Word) (0x80005184 : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (0x80005184 : Word) + 4 = (0x80005188 : Word) from by decide] at hli
  have htail := storeRetTail_spec CR (0x80005188 : Word) ret .x12 .x30 .x10
    (0 : BitVec 12) outPtr (1 : Word) a0Old (0 : Word) (by decide) halignRet
    (by rw [hCR]; code_mem) (by rw [hCR]; code_mem) (by rw [hCR]; code_mem)
  rw [show outPtr + signExtend12 (0 : BitVec 12) = outPtr from by
    rw [signExtend12_0]; bv_omega] at htail
  have hliF := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ outPtr) ** memOwn outPtr **
      ((.x10 : Reg) ↦ᵣ a0Old) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hli
  have hc := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hliF htail
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

/-- Tail 0 (`sd x0, 0(a2) ; li a0, 0 ; ret`): writes the dword `0` (the
    hardwired zero register is the stored source) and returns `a0 = 0`. -/
private theorem tail0_spec (a0Old : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 3 (0x80005194 : Word) ret
      (CodeReq.ofProg (0x80005154 : Word) u256LtBe_prog)
      (((.x12 : Reg) ↦ᵣ outPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        memOwn outPtr ** ((.x10 : Reg) ↦ᵣ a0Old) ** ((.x1 : Reg) ↦ᵣ ret))
      (((.x12 : Reg) ↦ᵣ outPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (outPtr ↦ₘ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ ret)) := by
  set CR := CodeReq.ofProg (0x80005154 : Word) u256LtBe_prog with hCR
  have htail := storeRetTail_spec CR (0x80005194 : Word) ret .x12 .x0 .x10
    (0 : BitVec 12) outPtr (0 : Word) a0Old (0 : Word) (by decide) halignRet
    (by rw [hCR]; code_mem) (by rw [hCR]; code_mem) (by rw [hCR]; code_mem)
  rw [show outPtr + signExtend12 (0 : BitVec 12) = outPtr from by
    rw [signExtend12_0]; bv_omega] at htail
  exact htail

-- ============================================================================
-- §4  One loop iteration (two break stations)
-- ============================================================================

/-- One iteration at the header with `i < 32` bytes known equal: either a
    `bltu` break fires and the corresponding writable-output tail RETURNS
    with the genuine post, or the iteration loops back to the header with
    the invariant advanced.  Exactly the `twoBreakRetLoop_spec` iteration
    shape, built from two nested `breakStation_spec`s. -/
private theorem ltIter_spec
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignA : aPtr.toNat % 8 = 0) (halignB : bPtr.toNat % 8 = 0)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 → isValidByteAccess (aPtr + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 → isValidByteAccess (bPtr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (i : Nat) (hi : i < 32) :
    cpsBranchWithin 9 (0x80005160 : Word)
      (CodeReq.ofProg (0x80005154 : Word) u256LtBe_prog)
      (ltInv aPtr bPtr outPtr ret as bs i)
      ret (ltPost aPtr bPtr outPtr ret as bs)
      (0x80005160 : Word) (ltInv aPtr bPtr outPtr ret as bs (i + 1)) := by
  set CR := CodeReq.ofProg (0x80005154 : Word) u256LtBe_prog with hCR
  have hia : i < as.length := by omega
  have hib : i < bs.length := by omega
  set aByte := (as[i]'hia).zeroExtend 64 with haByte
  set bByte := (bs[i]'hib).zeroExtend 64 with hbByte
  have haBN : aByte.toNat = (as[i]'hia).toNat := by
    rw [haByte]
    show (BitVec.setWidth 64 _).toNat = _
    rw [BitVec.toNat_setWidth]
    have := (as[i]'hia).isLt
    omega
  have hbBN : bByte.toNat = (bs[i]'hib).toNat := by
    rw [hbByte]
    show (BitVec.setWidth 64 _).toNat = _
    rw [BitVec.toNat_setWidth]
    have := (bs[i]'hib).isLt
    omega
  have hgdA : as.getD i 0 = as[i]'hia := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia]
    rfl
  have hgdB : bs.getD i 0 = bs[i]'hib := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hib]
    rfl
  -- strip the pure prefix fact
  unfold ltInv
  refine cpsBranchWithin_pure_pre (fun hpref => ?_)
  -- peel this iteration's scratch registers x28, x29
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x28)
      (P := (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr) **
        regOwn .x29)
      (fun v28 => ?_))
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x29)
      (P := (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr) **
        ((.x28 : Reg) ↦ᵣ v28))
      (fun v29 => ?_))
  -- canonical working set, x28/x29 concrete
  suffices hmain :
      cpsBranchWithin 9 (0x80005160 : Word) CR
        (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
         ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
         ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
         ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** regOwn .x30 **
         bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
        ret (ltPost aPtr bPtr outPtr ret as bs)
        (0x80005160 : Word) (ltInv aPtr bPtr outPtr ret as bs (i + 1)) by
    exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hmain
  -- ---- the two LBU loads (0x80005164, 0x80005168) ----
  have hlbuA := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x28 .x6 aPtr v28 (0x80005164 : Word) as i
      (by decide) halignA hia (by omega) (hvalidA i hi))
    (by rw [hCR]; code_mem)
  rw [show (0x80005164 : Word) + 4 = (0x80005168 : Word) from by decide] at hlbuA
  have hlbuB := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x29 .x7 bPtr v29 (0x80005168 : Word) bs i
      (by decide) halignB hib (by omega) (hvalidB i hi))
    (by rw [hCR]; code_mem)
  rw [show (0x80005168 : Word) + 4 = (0x8000516C : Word) from by decide] at hlbuB
  have hlbuAF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x29 : Reg) ↦ᵣ v29) ** regOwn .x30 **
      bytesRegion bPtr bs ** memOwn outPtr)
    (by pcf) hlbuA
  have hlbuBF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ aByte) ** regOwn .x30 **
      bytesRegion aPtr as ** memOwn outPtr)
    (by pcf) hlbuB
  have hpre1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlbuAF hlbuBF
  -- ---- the header BEQ station (0x80005160; never taken at i < 32) ----
  have hbrHdr := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** regOwn .x30 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x5 .x0 (52 : BitVec 13)
        (BitVec.ofNat 64 (32 - i)) (0 : Word) (0x80005160 : Word))
      (hmono := by rw [hCR]; code_mem))
  rw [show (0x80005160 : Word) + signExtend13 (52 : BitVec 13)
        = (0x80005194 : Word) from by decide,
      show (0x80005160 : Word) + 4 = (0x80005164 : Word) from by decide]
    at hbrHdr
  -- ---- break station A: bltu x28, x29 → tail 1 (0x8000516C) ----
  have hbrA := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x30 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bltu_spec_gen_within .x28 .x29 (24 : BitVec 13) aByte bByte
        (0x8000516C : Word))
      (hmono := by rw [hCR]; code_mem))
  rw [show (0x8000516C : Word) + signExtend13 (24 : BitVec 13)
        = (0x80005184 : Word) from by decide,
      show (0x8000516C : Word) + 4 = (0x80005170 : Word) from by decide]
    at hbrA
  -- ---- break station B: bltu x29, x28 → tail 0 (0x80005170) ----
  have hbrB := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x30 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bltu_spec_gen_within .x29 .x28 (36 : BitVec 13) bByte aByte
        (0x80005170 : Word))
      (hmono := by rw [hCR]; code_mem))
  rw [show (0x80005170 : Word) + signExtend13 (36 : BitVec 13)
        = (0x80005194 : Word) from by decide,
      show (0x80005170 : Word) + 4 = (0x80005174 : Word) from by decide]
    at hbrB
  -- the canonical post-load working set (used as both stations' PT/PF)
  set WSL : Assertion :=
    ((.x28 : Reg) ↦ᵣ aByte) ** ((.x29 : Reg) ↦ᵣ bByte) **
    ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
    ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
    ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
    ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
    ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x30 **
    bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr with hWSL
  -- ---- break arm A: tail 1 writes 1 (a < b decided) ----
  have htail1 : BitVec.ult aByte bByte →
      cpsTripleWithin 5 (0x80005184 : Word) ret CR WSL
        (ltPost aPtr bPtr outPtr ret as bs) := by
    intro hc
    have hltN : (as[i]'hia).toNat < (bs[i]'hib).toNat := by
      have hc' : aByte.toNat < bByte.toNat := by
        simpa [BitVec.ult, decide_eq_true_eq] using hc
      omega
    have hlt : beBytesToNat as < beBytesToNat bs :=
      beBytesToNat_lt_of_prefix_lt as bs (by omega) i hia hpref
        (by rw [hgdA, hgdB]; omega)
    have h := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ aByte) ** ((.x29 : Reg) ↦ᵣ bByte) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aPtr as ** bytesRegion bPtr bs)
      (by pcf) (tail1_spec outPtr ret aPtr halignRet)
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
        (fun h hq => ?_) h)
    unfold ltPost
    rw [if_pos hlt]
    have hq1 : (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        (((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
          (((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
            (((.x28 : Reg) ↦ᵣ aByte) ** (((.x29 : Reg) ↦ᵣ bByte) **
              (((.x30 : Reg) ↦ᵣ (1 : Word)) **
                (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
                 ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
                 ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                 bytesRegion aPtr as ** bytesRegion bPtr bs **
                 (outPtr ↦ₘ (1 : Word))))))))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x28 _)
            (sepConj_mono (regIs_to_regOwn .x29 _)
              (sepConj_mono (regIs_to_regOwn .x30 _)
                (fun _ hh => hh)))))) h hq1
    xperm_hyp hq2
  -- ---- break arm B: tail 0 writes 0 (b < a decided) ----
  have htail0 : BitVec.ult bByte aByte →
      cpsTripleWithin 4 (0x80005194 : Word) ret CR WSL
        (ltPost aPtr bPtr outPtr ret as bs) := by
    intro hc
    have hltN : (bs[i]'hib).toNat < (as[i]'hia).toNat := by
      have hc' : bByte.toNat < aByte.toNat := by
        simpa [BitVec.ult, decide_eq_true_eq] using hc
      omega
    have hnlt : ¬ (beBytesToNat as < beBytesToNat bs) := by
      have := beBytesToNat_lt_of_prefix_lt bs as (by omega) i hib
        (fun j hj => (hpref j hj).symm)
        (by rw [hgdA, hgdB]; omega)
      omega
    have h := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ aByte) ** ((.x29 : Reg) ↦ᵣ bByte) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs)
      (by pcf) (tail0_spec outPtr ret aPtr halignRet)
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
        (fun h hq => ?_) h)
    unfold ltPost
    rw [if_neg hnlt]
    have hq1 : (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        (((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
          (((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
            (((.x28 : Reg) ↦ᵣ aByte) ** (((.x29 : Reg) ↦ᵣ bByte) **
              (regOwn .x30 **
                (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
                 ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
                 ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                 bytesRegion aPtr as ** bytesRegion bPtr bs **
                 (outPtr ↦ₘ (0 : Word))))))))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x28 _)
            (sepConj_mono (regIs_to_regOwn .x29 _)
              (sepConj_mono (fun _ hh => hh)
                (fun _ hh => hh)))))) h hq1
    xperm_hyp hq2
  -- ---- continue segment: 3 × addi ; jal → header with inv (i+1) ----
  have hcont : ¬ BitVec.ult aByte bByte → ¬ BitVec.ult bByte aByte →
      cpsTripleWithin 4 (0x80005174 : Word) (0x80005160 : Word) CR WSL
        (ltInv aPtr bPtr outPtr ret as bs (i + 1)) := by
    intro hnAB hnBA
    have hEqByte : as[i]'hia = bs[i]'hib := by
      apply BitVec.eq_of_toNat_eq
      have h1 : ¬ aByte.toNat < bByte.toNat := by
        intro hlt
        exact hnAB (by simp [BitVec.ult, decide_eq_true_eq]; omega)
      have h2 : ¬ bByte.toNat < aByte.toNat := by
        intro hlt
        exact hnBA (by simp [BitVec.ult, decide_eq_true_eq]; omega)
      omega
    have hpref' : ∀ j, j < i + 1 → as.getD j 0 = bs.getD j 0 := by
      intro j hj
      by_cases hji : j < i
      · exact hpref j hji
      · have : j = i := by omega
        subst this
        rw [hgdA, hgdB, hEqByte]
    have haddi6 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x6 (aPtr + BitVec.ofNat 64 i) (1 : BitVec 12)
        (0x80005174 : Word) (by decide))
      (by rw [hCR]; code_mem)
    rw [cursor_advance aPtr i,
        show (0x80005174 : Word) + 4 = (0x80005178 : Word) from by decide]
      at haddi6
    have haddi7 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x7 (bPtr + BitVec.ofNat 64 i) (1 : BitVec 12)
        (0x80005178 : Word) (by decide))
      (by rw [hCR]; code_mem)
    rw [cursor_advance bPtr i,
        show (0x80005178 : Word) + 4 = (0x8000517C : Word) from by decide]
      at haddi7
    have haddi5 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x5 (BitVec.ofNat 64 (32 - i)) (-1 : BitVec 12)
        (0x8000517C : Word) (by decide))
      (by rw [hCR]; code_mem)
    rw [counter_dec i hi,
        show (0x8000517C : Word) + 4 = (0x80005180 : Word) from by decide]
      at haddi5
    have hjal := liftCode (cr' := CR)
      (jal_x0_spec_gen_within (-32 : BitVec 21) (0x80005180 : Word))
      (by rw [hCR]; code_mem)
    rw [show (0x80005180 : Word) + signExtend21 (-32 : BitVec 21)
          = (0x80005160 : Word) from by decide] at hjal
    have haddi6F := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x28 : Reg) ↦ᵣ aByte) ** ((.x29 : Reg) ↦ᵣ bByte) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
      (by pcf) haddi6
    have haddi7F := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x28 : Reg) ↦ᵣ aByte) ** ((.x29 : Reg) ↦ᵣ bByte) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
      (by pcf) haddi7
    have haddi5F := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x28 : Reg) ↦ᵣ aByte) ** ((.x29 : Reg) ↦ᵣ bByte) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
      (by pcf) haddi5
    have hjalF := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x28 : Reg) ↦ᵣ aByte) ** ((.x29 : Reg) ↦ᵣ bByte) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
      (by pcf) hjal
    have hc1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) haddi6F haddi7F
    have hc2 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hc1 haddi5F
    have hc3 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        rw [sepConj_emp_left']
        xperm_hyp hp) hc2 hjalF
    refine cpsTripleWithin_weaken
      (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
      (fun h hq => ?_) hc3
    rw [sepConj_emp_left'] at hq
    unfold ltInv
    refine (sepConj_pure_left h).2 ⟨hpref', ?_⟩
    have hq1 : (((.x28 : Reg) ↦ᵣ aByte) ** (((.x29 : Reg) ↦ᵣ bByte) **
        (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
         ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (i + 1))) **
         ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (i + 1))) **
         ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x30 **
         bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x28 _)
      (sepConj_mono (regIs_to_regOwn .x29 _)
        (fun _ hh => hh)) h hq1
    xperm_hyp hq2
  -- ---- station B (bltu x29, x28): break → tail 0, fall → continue ----
  have hstB : ¬ BitVec.ult aByte bByte →
      cpsBranchWithin (1 + 4) (0x80005170 : Word) CR WSL
        ret (ltPost aPtr bPtr outPtr ret as bs)
        (0x80005160 : Word) (ltInv aPtr bPtr outPtr ret as bs (i + 1)) :=
    fun hnAB =>
      breakStation_spec (cond := BitVec.ult bByte aByte)
        (PT := WSL) (PF := WSL)
        (cpsBranchWithin_weaken
          (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
          (fun _ hq => hq) (fun _ hq => hq) hbrB)
        (fun h hq => by rw [hWSL]; xperm_hyp hq)
        (fun h hq => by rw [hWSL]; xperm_hyp hq)
        (fun hc => htail0 hc)
        (fun hnBA => cpsTripleWithin_as_cpsBranchWithin_right ret
          (ltPost aPtr bPtr outPtr ret as bs) (hcont hnAB hnBA))
  -- ---- station A (bltu x28, x29): break → tail 1, fall → station B ----
  have hstA : cpsBranchWithin (1 + 5) (0x8000516C : Word) CR WSL
      ret (ltPost aPtr bPtr outPtr ret as bs)
      (0x80005160 : Word) (ltInv aPtr bPtr outPtr ret as bs (i + 1)) :=
    breakStation_spec (cond := BitVec.ult aByte bByte)
      (PT := WSL) (PF := WSL)
      (cpsBranchWithin_weaken
        (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
        (fun _ hq => hq) (fun _ hq => hq) hbrA)
      (fun h hq => by rw [hWSL]; xperm_hyp hq)
      (fun h hq => by rw [hWSL]; xperm_hyp hq)
      (fun hc => htail1 hc)
      (fun hnAB => hstB hnAB)
  -- ---- loads ; station A ----
  have hfallIter := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by rw [hWSL]; xperm_hyp hp) hpre1 hstA
  -- ---- the header BEQ station wraps it all ----
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (breakStation_spec (cond := (BitVec.ofNat 64 (32 - i) = (0 : Word)))
      (PT := ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
      (PF := ((((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
        ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion aPtr as) **
        (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x29 : Reg) ↦ᵣ v29) ** regOwn .x30 **
        bytesRegion bPtr bs ** memOwn outPtr)))
      hbrHdr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun hc => absurd hc (ctr_ne_zero i hi))
      (fun _ => hfallIter))

-- ============================================================================
-- §5  Loop exhaustion: all 32 bytes equal → tail 0 writes 0
-- ============================================================================

private theorem ltExh_spec
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 4 (0x80005160 : Word) ret
      (CodeReq.ofProg (0x80005154 : Word) u256LtBe_prog)
      (ltInv aPtr bPtr outPtr ret as bs 32)
      (ltPost aPtr bPtr outPtr ret as bs) := by
  set CR := CodeReq.ofProg (0x80005154 : Word) u256LtBe_prog with hCR
  unfold ltInv
  refine cpsTripleWithin_pure_pre (fun hpref => ?_)
  have hEq : as = bs := bytes_eq_of_prefix_all as bs (by omega)
    (fun j hj => hpref j (by omega))
  have hnlt : ¬ (beBytesToNat as < beBytesToNat bs) := by
    rw [hEq]; omega
  -- header BEQ, taken (counter = 0)
  have hbrHdr := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 32)) **
      ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 32)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x5 .x0 (52 : BitVec 13)
        (BitVec.ofNat 64 (32 - 32)) (0 : Word) (0x80005160 : Word))
      (hmono := by rw [hCR]; code_mem))
  rw [show (0x80005160 : Word) + signExtend13 (52 : BitVec 13)
        = (0x80005194 : Word) from by decide,
      show (0x80005160 : Word) + 4 = (0x80005164 : Word) from by decide]
    at hbrHdr
  -- taken arm: tail 0 writes 0 (framed, converted, if-resolved)
  have htail : cpsTripleWithin 3 (0x80005194 : Word) ret CR
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
       ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 32)) **
       ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 32)) **
       ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
      (ltPost aPtr bPtr outPtr ret as bs) := by
    have h := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 32)) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 32)) **
        ((.x11 : Reg) ↦ᵣ bPtr) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs)
      (by pcf) (tail0_spec outPtr ret aPtr halignRet)
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ?_) h
    unfold ltPost
    rw [if_neg hnlt]
    have hq1 : (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        (((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 32)) **
          (((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 32)) **
            (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
             ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
             ((.x0 : Reg) ↦ᵣ (0 : Word)) **
             regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             bytesRegion aPtr as ** bytesRegion bPtr bs **
             (outPtr ↦ₘ (0 : Word)))))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (fun _ hh => hh))) h hq1
    xperm_hyp hq2
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (retJoinStation_spec
      (cond := (BitVec.ofNat 64 (32 - 32) = (0 : Word)))
      (PT := (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 32)) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 32)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr))
      (PF := (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x6 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 32)) **
        ((.x7 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 32)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr))
      hbrHdr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun _ => htail)
      (fun hc => absurd (by decide :
        (BitVec.ofNat 64 (32 - 32) : Word) = (0 : Word)) hc))

end Scan

-- ============================================================================
-- §6  The whole routine
-- ============================================================================

/-- **`u256_lt_be` at its linked address** (genuine post): the output dword
    `[a2]` is `1` iff `a < b` numerically (big-endian bytes → `beBytesToNat`),
    else `0`; `a0 = 0`; both 32-byte inputs untouched. -/
theorem u256LtBe_spec (aPtr bPtr outPtr ret : Word) (as bs : List (BitVec 8))
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignA : aPtr.toNat % 8 = 0) (halignB : bPtr.toNat % 8 = 0)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 → isValidByteAccess (aPtr + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 → isValidByteAccess (bPtr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 295 (0x80005154 : Word) ret
      (CodeReq.ofProg (0x80005154 : Word) u256LtBe_prog)
      (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       bytesRegion aPtr as ** bytesRegion bPtr bs **
       (outPtr ↦ₘ (if beBytesToNat as < beBytesToNat bs
         then (1 : Word) else (0 : Word)))) := by
  set CR := CodeReq.ofProg (0x80005154 : Word) u256LtBe_prog with hCR
  -- peel the MV destinations x6, x7
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr) **
        regOwn .x7)
      (fun v6 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
      (P := (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr) **
        ((.x6 : Reg) ↦ᵣ v6))
      (fun v7 => ?_))
  -- ---- init: li x5, 32 ; mv x6, a0 ; mv x7, a1 ----
  have hli5 := liftCode (cr' := CR)
    (li_spec_gen_own_within .x5 (32 : Word) (0x80005154 : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (0x80005154 : Word) + 4 = (0x80005158 : Word) from by decide] at hli5
  have hmv6 := liftCode (cr' := CR)
    (mv_spec_gen_within .x6 .x10 aPtr v6 (0x80005158 : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (0x80005158 : Word) + 4 = (0x8000515C : Word) from by decide] at hmv6
  have hmv7 := liftCode (cr' := CR)
    (mv_spec_gen_within .x7 .x11 bPtr v7 (0x8000515C : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (0x8000515C : Word) + 4 = (0x80005160 : Word) from by decide] at hmv7
  -- ---- the two-break writable-output loop ----
  have hloop := twoBreakRetLoop_spec (hdr := (0x80005160 : Word)) (ret := ret)
    (cr := CR) (Q := ltPost aPtr bPtr outPtr ret as bs) 32 9 4
    (ltInv aPtr bPtr outPtr ret as bs)
    (fun i hi => ltIter_spec aPtr bPtr outPtr ret as bs hlenA hlenB
      halignA halignB hovA hovB hvalidA hvalidB halignRet i hi)
    (ltExh_spec aPtr bPtr outPtr ret as bs hlenA hlenB halignRet)
  -- ---- frames + chain ----
  have hli5F := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
    (by pcf) hli5
  have hmv6F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) **
      ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
    (by pcf) hmv6
  have hmv7F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x6 : Reg) ↦ᵣ aPtr) **
      ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
    (by pcf) hmv7
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hli5F hmv6F
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc1 hmv7F
  have hc3 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold ltInv
      refine (sepConj_pure_left h).2
        ⟨fun j hj => absurd hj (Nat.not_lt_zero j), ?_⟩
      rw [show (BitVec.ofNat 64 (32 - 0) : Word) = (32 : Word) from by decide,
          show aPtr + BitVec.ofNat 64 0 = aPtr from by
            rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
            bv_omega,
          show bPtr + BitVec.ofNat 64 0 = bPtr from by
            rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
            bv_omega]
      xperm_hyp hp) hc2 hloop
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by unfold ltPost at hq; exact hq)
    (cpsTripleWithin_mono_nSteps (by omega) hc3)

#print axioms u256LtBe_spec

end U256LtBeSAsm

end EvmAsm.Codegen
