/-
  EvmAsm.Codegen.Programs.Secp256k1FieldCmpPSAsm

  `secf_cmp_p` via the **three-outcome compare/store join**
  (`EvmAsm/Rv64/SAsm/TriCmpStoreJoin.lean`, bead evm-asm-4ch8f.38.2.2.3)
  — the acceptance consumer.

  The routine materializes the read-only global `secp256k1_p_be` with the
  `la` idiom (`auipc`+`addi`, PROVEN by `la_materialize_within` /
  `la_resolve` — only the decidable `laInRange` representability
  remains), byte-walks the 32-byte big-endian input against that constant
  with a countdown counter and advancing cursors, and routes THREE exits
  to THREE writable-output return tails:

  ```
        la   t0, secp256k1_p_be ; li t1, 32 ; mv t2, a0
  hdr:  beq  t1, x0, .tailEq            -- exhaustion (equal)  → write 1
        lbu  x28, 0(t2) ; lbu x29, 0(t0)
        bltu x28, x29, .tailLt          -- in[i] < p[i]        → write 0
        bltu x29, x28, .tailGt          -- p[i] < in[i]        → write 2
        addi t2, t2, 1 ; addi t0, t0, 1 ; addi t1, t1, -1 ; j hdr
  .tailLt:            sd x0, 0(a1) ; li a0, 0 ; ret
  .tailEq: li t0, 1 ; sd t0, 0(a1) ; li a0, 0 ; ret
  .tailGt: li t0, 2 ; sd t0, 0(a1) ; li a0, 0 ; ret
  ```

  The lt tail is one `storeRetTail_spec` instance (the hardwired `x0`
  zero is the stored source); the eq/gt tails are `liStoreRetTail_spec`
  instances at their distinct constants; the ordered `bltu` pair is one
  `triCmpStoreJoin_spec` station; the loop is one `twoBreakRetLoop_spec`
  (station-count-agnostic).

  **Genuine post**: the output dword `[a1]` is
  `if beBytesToNat in < beBytesToNat secp256k1PBytes then 0
   else if beBytesToNat in = beBytesToNat secp256k1PBytes then 1 else 2`
  — the REAL numeric three-way comparison against the secp256k1 field
  prime (big-endian lexicographic order IS numeric order, by
  `U256MinSAsm.beBytesToNat_lt_of_prefix_lt` in both directions and the
  all-equal bridge `bytes_eq_of_prefix_all`), `a0 = 0`, the input and the
  `globalConst` prime region untouched.

  Byte-transparent: the spec is stated at the `#guard`-tied symbolic
  `GuestAddrs.secf_cmp_p` over the emitted `secfCmpP_prog` directly — no
  guest-byte change, no A/B run needed.  No hardcoded PC literals (bead
  evm-asm-6agnq): the base and the constant's address are referenced
  through `GuestAddrs`, pinned by the `#guard`s below.
-/

import EvmAsm.Codegen.Programs.Secp256k1FieldReduceOnceSAsmSupport
import EvmAsm.Rv64.SAsm.TriCmpStoreJoin

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Secp256k1FieldCmpPSAsm

open U256MinSAsm (beBytesToNat_lt_of_prefix_lt bytes_eq_of_prefix_all)
open Secp256k1FieldReduceOnceSAsm (secp256k1PBytes)

/-- The routine base, symbolic (bead evm-asm-6agnq). -/
def cmpPBase : Word := (GuestAddrs.secf_cmp_p : Word)

/-- The read-only prime constant's link address, symbolic. -/
def pConstAddr : Word := (GuestAddrs.secp256k1_p_be : Word)

#guard secfCmpP_prog.length = 24

-- The constant bytes ARE the secp256k1 field prime p = 2^256 - 0x1000003d1.
#guard secp256k1PBytes.length = 32
#guard beBytesToNat secp256k1PBytes = 2 ^ 256 - 0x1000003d1

-- The `la` displacement is representable.
#guard decide (laInRange cmpPBase pConstAddr)

/-- The emitter's reloc immediates ARE the psABI `%pcrel_hi`/`%pcrel_lo`
    of the `la` resolution model at this pc/target (kernel-checked). -/
theorem cmpP_laHi_agree :
    Codegen.laHi GuestAddrs.secp256k1_p_be (GuestAddrs.secf_cmp_p + 0)
      = EvmAsm.Rv64.laHi cmpPBase pConstAddr := by decide

theorem cmpP_laLo_agree :
    Codegen.laLo GuestAddrs.secp256k1_p_be (GuestAddrs.secf_cmp_p + 0)
      = EvmAsm.Rv64.laLo cmpPBase pConstAddr := by decide

/-
  Emitted layout relative to `GuestAddrs.secf_cmp_p`:
    +0   auipc x5, %pcrel_hi(secp256k1_p_be)
    +4   addi  x5, x5, %pcrel_lo
    +8   li    x6, 32
    +12  mv    x7, x10
    +16  beq   x6, x0, +48  → +64 (eq tail)                    [hdr]
    +20  lbu   x28, 0(x7)
    +24  lbu   x29, 0(x5)
    +28  bltu  x28, x29, +24 → +52 (lt tail)
    +32  bltu  x29, x28, +48 → +80 (gt tail)
    +36  addi  x7, x7, 1
    +40  addi  x5, x5, 1
    +44  addi  x6, x6, -1
    +48  jal   x0, -32      → +16
    +52  sd    x11, x0, 0                                      [lt tail]
    +56  li    x10, 0
    +60  jalr  x0, x1, 0
    +64  li    x5, 1                                           [eq tail]
    +68  sd    x11, x5, 0
    +72  li    x10, 0
    +76  jalr  x0, x1, 0
    +80  li    x5, 2                                           [gt tail]
    +84  sd    x11, x5, 0
    +88  li    x10, 0
    +92  jalr  x0, x1, 0
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

/-- Every byte of the prime constant's region is a valid guest access. -/
private theorem pByte_valid (k : Nat) (hk : k < 32) :
    isValidByteAccess (pConstAddr + BitVec.ofNat 64 k) = true := by
  interval_cases k <;> decide

-- ============================================================================
-- §2  Invariant and genuine post
-- ============================================================================

section Scan

variable (inPtr outPtr ret : Word) (xs : List (BitVec 8))

/-- Loop invariant at the header after `i` matched bytes: the counter holds
    `32 - i`, both cursors sit at byte `i` (the const-side cursor walks the
    read-only prime region), the first `i` bytes agree with the prime
    (pure conjunct), the fixed registers, the input region and the
    constant region are untouched, and the output dword cell is still
    merely OWNED (no write has happened). -/
private def cmpInv (i : Nat) : Assertion :=
  ⌜∀ j, j < i → xs.getD j 0 = secp256k1PBytes.getD j 0⌝ **
  ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
  ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
  ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
  ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
  ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x28 ** regOwn .x29 **
  bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
  memOwn outPtr

/-- The genuine post: `a0 = 0`, the output dword `[a1]` is the REAL
    numeric three-way comparison against the prime, the input and the
    constant region untouched. -/
private def cmpPost : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
  ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 **
  bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
  (outPtr ↦ₘ (if beBytesToNat xs < beBytesToNat secp256k1PBytes
    then (0 : Word)
    else if beBytesToNat xs = beBytesToNat secp256k1PBytes
    then (1 : Word) else (2 : Word)))

-- ============================================================================
-- §3  The three writable-output return tails
-- ============================================================================

/-- Lt tail (`sd x0, 0(a1) ; li a0, 0 ; ret`): writes the dword `0` (the
    hardwired zero register is the stored source) and returns `a0 = 0`. -/
private theorem ltTail_spec (a0Old : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 3 (cmpPBase + 52) ret
      (CodeReq.ofProg cmpPBase secfCmpP_prog)
      (((.x11 : Reg) ↦ᵣ outPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        memOwn outPtr ** ((.x10 : Reg) ↦ᵣ a0Old) ** ((.x1 : Reg) ↦ᵣ ret))
      (((.x11 : Reg) ↦ᵣ outPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (outPtr ↦ₘ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ ret)) := by
  set CR := CodeReq.ofProg cmpPBase secfCmpP_prog with hCR
  have htail := storeRetTail_spec CR (cmpPBase + 52) ret .x11 .x0 .x10
    (0 : BitVec 12) outPtr (0 : Word) a0Old (0 : Word) (by decide) halignRet
    (by rw [hCR]; code_mem) (by rw [hCR]; code_mem) (by rw [hCR]; code_mem)
  rw [show outPtr + signExtend12 (0 : BitVec 12) = outPtr from by
    rw [signExtend12_0]; bv_omega] at htail
  exact htail

/-- Eq tail (`li x5, 1 ; sd x5, 0(a1) ; li a0, 0 ; ret`): writes the
    dword `1` to the owned output cell and returns `a0 = 0`. -/
private theorem eqTail_spec (a0Old : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 4 (cmpPBase + 64) ret
      (CodeReq.ofProg cmpPBase secfCmpP_prog)
      (regOwn .x5 ** ((.x11 : Reg) ↦ᵣ outPtr) ** memOwn outPtr **
        ((.x10 : Reg) ↦ᵣ a0Old) ** ((.x1 : Reg) ↦ᵣ ret))
      (((.x5 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        (outPtr ↦ₘ (1 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ ret)) := by
  set CR := CodeReq.ofProg cmpPBase secfCmpP_prog with hCR
  have htail := liStoreRetTail_spec CR (cmpPBase + 64) ret .x11 .x5 .x10
    (0 : BitVec 12) outPtr a0Old (1 : Word) (0 : Word)
    (by decide) (by decide) halignRet
    (by rw [hCR]; code_mem) (by rw [hCR]; code_mem)
    (by rw [hCR]; code_mem) (by rw [hCR]; code_mem)
  rw [show outPtr + signExtend12 (0 : BitVec 12) = outPtr from by
    rw [signExtend12_0]; bv_omega] at htail
  exact htail

/-- Gt tail (`li x5, 2 ; sd x5, 0(a1) ; li a0, 0 ; ret`): writes the
    dword `2` to the owned output cell and returns `a0 = 0`. -/
private theorem gtTail_spec (a0Old : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 4 (cmpPBase + 80) ret
      (CodeReq.ofProg cmpPBase secfCmpP_prog)
      (regOwn .x5 ** ((.x11 : Reg) ↦ᵣ outPtr) ** memOwn outPtr **
        ((.x10 : Reg) ↦ᵣ a0Old) ** ((.x1 : Reg) ↦ᵣ ret))
      (((.x5 : Reg) ↦ᵣ (2 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        (outPtr ↦ₘ (2 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ ret)) := by
  set CR := CodeReq.ofProg cmpPBase secfCmpP_prog with hCR
  have htail := liStoreRetTail_spec CR (cmpPBase + 80) ret .x11 .x5 .x10
    (0 : BitVec 12) outPtr a0Old (2 : Word) (0 : Word)
    (by decide) (by decide) halignRet
    (by rw [hCR]; code_mem) (by rw [hCR]; code_mem)
    (by rw [hCR]; code_mem) (by rw [hCR]; code_mem)
  rw [show outPtr + signExtend12 (0 : BitVec 12) = outPtr from by
    rw [signExtend12_0]; bv_omega] at htail
  exact htail

-- ============================================================================
-- §4  One loop iteration (the three-outcome join station)
-- ============================================================================

/-- One iteration at the header with `i < 32` bytes known equal: either a
    `bltu` break fires and the corresponding writable-output tail RETURNS
    with the genuine post, or the iteration loops back to the header with
    the invariant advanced.  Exactly the `twoBreakRetLoop_spec` iteration
    shape, built from one `triCmpStoreJoin_spec` station wrapped by the
    header `beq` `breakStation_spec`. -/
private theorem cmpIter_spec
    (hlenX : xs.length = 32)
    (halignIn : inPtr.toNat % 8 = 0)
    (hovIn : inPtr.toNat + 32 < 2 ^ 64)
    (hvalidIn : ∀ k, k < 32 → isValidByteAccess (inPtr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (i : Nat) (hi : i < 32) :
    cpsBranchWithin 9 (cmpPBase + 16)
      (CodeReq.ofProg cmpPBase secfCmpP_prog)
      (cmpInv inPtr outPtr ret xs i)
      ret (cmpPost inPtr outPtr ret xs)
      (cmpPBase + 16) (cmpInv inPtr outPtr ret xs (i + 1)) := by
  set CR := CodeReq.ofProg cmpPBase secfCmpP_prog with hCR
  have hplen : secp256k1PBytes.length = 32 := by decide
  have hix : i < xs.length := by omega
  have hip : i < secp256k1PBytes.length := by omega
  set xByte := (xs[i]'hix).zeroExtend 64 with hxByte
  set pByte := (secp256k1PBytes[i]'hip).zeroExtend 64 with hpByte
  have hxBN : xByte.toNat = (xs[i]'hix).toNat := by
    rw [hxByte]
    show (BitVec.setWidth 64 _).toNat = _
    rw [BitVec.toNat_setWidth]
    have := (xs[i]'hix).isLt
    omega
  have hpBN : pByte.toNat = (secp256k1PBytes[i]'hip).toNat := by
    rw [hpByte]
    show (BitVec.setWidth 64 _).toNat = _
    rw [BitVec.toNat_setWidth]
    have := (secp256k1PBytes[i]'hip).isLt
    omega
  have hgdX : xs.getD i 0 = xs[i]'hix := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hix]
    rfl
  have hgdP : secp256k1PBytes.getD i 0 = secp256k1PBytes[i]'hip := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hip]
    rfl
  -- strip the pure prefix fact
  unfold cmpInv
  refine cpsBranchWithin_pure_pre (fun hpref => ?_)
  -- peel this iteration's scratch registers x28, x29
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x28)
      (P := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
        memOwn outPtr) **
        regOwn .x29)
      (fun v28 => ?_))
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x29)
      (P := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
        memOwn outPtr) **
        ((.x28 : Reg) ↦ᵣ v28))
      (fun v29 => ?_))
  -- canonical working set, x28/x29 concrete
  suffices hmain :
      cpsBranchWithin 9 (cmpPBase + 16) CR
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
         ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
         ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
         ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
         bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
         memOwn outPtr)
        ret (cmpPost inPtr outPtr ret xs)
        (cmpPBase + 16) (cmpInv inPtr outPtr ret xs (i + 1)) by
    exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hmain
  -- ---- the two LBU loads (+20 input, +24 const) ----
  have hlbuX := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x28 .x7 inPtr v28 (cmpPBase + 20) xs i
      (by decide) halignIn hix (by omega) (hvalidIn i hi))
    (by rw [hCR]; code_mem)
  rw [show (cmpPBase + 20 : Word) + 4 = (cmpPBase + 24 : Word) from by decide]
    at hlbuX
  have hlbuP := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x29 .x5 pConstAddr v29 (cmpPBase + 24)
      secp256k1PBytes i (by decide) (by decide) hip
      (by have h : pConstAddr.toNat = 0xa3c052c0 := by decide
          omega)
      (pByte_valid i hi))
    (by rw [hCR]; code_mem)
  rw [show (cmpPBase + 24 : Word) + 4 = (cmpPBase + 28 : Word) from by decide]
    at hlbuP
  have hlbuXF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x29 : Reg) ↦ᵣ v29) **
      bytesRegion pConstAddr secp256k1PBytes ** memOwn outPtr)
    (by pcf) hlbuX
  have hlbuPF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ xByte) **
      bytesRegion inPtr xs ** memOwn outPtr)
    (by pcf) hlbuP
  have hpre1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlbuXF hlbuPF
  -- ---- the header BEQ station (+16; never taken at i < 32) ----
  have hbrHdr := cpsBranchWithin_frameR
    (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
      ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
      bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
      memOwn outPtr)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x6 .x0 (48 : BitVec 13)
        (BitVec.ofNat 64 (32 - i)) (0 : Word) (cmpPBase + 16))
      (hmono := by rw [hCR]; code_mem))
  rw [show (cmpPBase + 16 : Word) + signExtend13 (48 : BitVec 13)
        = (cmpPBase + 64 : Word) from by decide,
      show (cmpPBase + 16 : Word) + 4 = (cmpPBase + 20 : Word) from by decide]
    at hbrHdr
  -- ---- the ordered bltu pair, framed ----
  have hbrA := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
      ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
      memOwn outPtr)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bltu_spec_gen_within .x28 .x29 (24 : BitVec 13) xByte pByte
        (cmpPBase + 28))
      (hmono := by rw [hCR]; code_mem))
  rw [show (cmpPBase + 28 : Word) + signExtend13 (24 : BitVec 13)
        = (cmpPBase + 52 : Word) from by decide,
      show (cmpPBase + 28 : Word) + 4 = (cmpPBase + 32 : Word) from by decide]
    at hbrA
  have hbrB := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
      ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
      memOwn outPtr)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bltu_spec_gen_within .x29 .x28 (48 : BitVec 13) pByte xByte
        (cmpPBase + 32))
      (hmono := by rw [hCR]; code_mem))
  rw [show (cmpPBase + 32 : Word) + signExtend13 (48 : BitVec 13)
        = (cmpPBase + 80 : Word) from by decide,
      show (cmpPBase + 32 : Word) + 4 = (cmpPBase + 36 : Word) from by decide]
    at hbrB
  -- the canonical post-load working set (all three arms' currency)
  set WSL : Assertion :=
    ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
    ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
    ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
    ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
    ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
    ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
    memOwn outPtr with hWSL
  -- ---- break arm A: lt tail writes 0 (in < p decided) ----
  have htailLt : BitVec.ult xByte pByte →
      cpsTripleWithin 4 (cmpPBase + 52) ret CR WSL
        (cmpPost inPtr outPtr ret xs) := by
    intro hc
    have hltN : (xs[i]'hix).toNat < (secp256k1PBytes[i]'hip).toNat := by
      have hc' : xByte.toNat < pByte.toNat := by
        simpa [BitVec.ult, decide_eq_true_eq] using hc
      omega
    have hlt : beBytesToNat xs < beBytesToNat secp256k1PBytes :=
      beBytesToNat_lt_of_prefix_lt xs secp256k1PBytes (by omega) i hix hpref
        (by rw [hgdX, hgdP]; omega)
    have h := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes)
      (by pcf) (ltTail_spec outPtr ret inPtr halignRet)
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
        (fun h hq => ?_) h)
    unfold cmpPost
    rw [if_pos hlt]
    have hq1 : (((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
          (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
            (((.x28 : Reg) ↦ᵣ xByte) ** (((.x29 : Reg) ↦ᵣ pByte) **
              (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
               ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
               bytesRegion inPtr xs **
               bytesRegion pConstAddr secp256k1PBytes **
               (outPtr ↦ₘ (0 : Word)))))))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x28 _)
            (sepConj_mono (regIs_to_regOwn .x29 _)
              (fun _ hh => hh))))) h hq1
    xperm_hyp hq2
  -- ---- break arm B: gt tail writes 2 (p < in decided) ----
  have htailGt : ¬ BitVec.ult xByte pByte → BitVec.ult pByte xByte →
      cpsTripleWithin 4 (cmpPBase + 80) ret CR WSL
        (cmpPost inPtr outPtr ret xs) := by
    intro _ hc
    have hgtN : (secp256k1PBytes[i]'hip).toNat < (xs[i]'hix).toNat := by
      have hc' : pByte.toNat < xByte.toNat := by
        simpa [BitVec.ult, decide_eq_true_eq] using hc
      omega
    have hgt : beBytesToNat secp256k1PBytes < beBytesToNat xs :=
      beBytesToNat_lt_of_prefix_lt secp256k1PBytes xs (by omega) i hip
        (fun j hj => (hpref j hj).symm)
        (by rw [hgdX, hgdP]; omega)
    have hnlt : ¬ (beBytesToNat xs < beBytesToNat secp256k1PBytes) := by
      omega
    have hne : ¬ (beBytesToNat xs = beBytesToNat secp256k1PBytes) := by
      omega
    have h := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes)
      (by pcf) (gtTail_spec outPtr ret inPtr halignRet)
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) h
    · rw [hWSL] at hp
      have hp1 : (((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
          (((.x11 : Reg) ↦ᵣ outPtr) ** memOwn outPtr **
           ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
           ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
           ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
           ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion inPtr xs **
           bytesRegion pConstAddr secp256k1PBytes)) h := by
        xperm_hyp hp
      have hp2 := sepConj_mono (regIs_to_regOwn .x5 _)
        (fun _ hh => hh) h hp1
      xperm_hyp hp2
    · unfold cmpPost
      rw [if_neg hnlt, if_neg hne]
      have hq1 : (((.x5 : Reg) ↦ᵣ (2 : Word)) **
          (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
            (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
              (((.x28 : Reg) ↦ᵣ xByte) ** (((.x29 : Reg) ↦ᵣ pByte) **
                (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
                 ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                 bytesRegion inPtr xs **
                 bytesRegion pConstAddr secp256k1PBytes **
                 (outPtr ↦ₘ (2 : Word)))))))) h := by
        xperm_hyp hq
      have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
        (sepConj_mono (regIs_to_regOwn .x6 _)
          (sepConj_mono (regIs_to_regOwn .x7 _)
            (sepConj_mono (regIs_to_regOwn .x28 _)
              (sepConj_mono (regIs_to_regOwn .x29 _)
                (fun _ hh => hh))))) h hq1
      xperm_hyp hq2
  -- ---- continue segment: 3 × addi ; jal → header with inv (i+1) ----
  have hcont : ¬ BitVec.ult xByte pByte → ¬ BitVec.ult pByte xByte →
      cpsTripleWithin 4 (cmpPBase + 36) (cmpPBase + 16) CR WSL
        (cmpInv inPtr outPtr ret xs (i + 1)) := by
    intro hnXP hnPX
    have hEqByte : xs[i]'hix = secp256k1PBytes[i]'hip := by
      apply BitVec.eq_of_toNat_eq
      have h1 : ¬ xByte.toNat < pByte.toNat := by
        intro hlt
        exact hnXP (by simp [BitVec.ult, decide_eq_true_eq]; omega)
      have h2 : ¬ pByte.toNat < xByte.toNat := by
        intro hlt
        exact hnPX (by simp [BitVec.ult, decide_eq_true_eq]; omega)
      omega
    have hpref' : ∀ j, j < i + 1 → xs.getD j 0 = secp256k1PBytes.getD j 0 := by
      intro j hj
      by_cases hji : j < i
      · exact hpref j hji
      · have : j = i := by omega
        subst this
        rw [hgdX, hgdP, hEqByte]
    have haddi7 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x7 (inPtr + BitVec.ofNat 64 i) (1 : BitVec 12)
        (cmpPBase + 36) (by decide))
      (by rw [hCR]; code_mem)
    rw [cursor_advance inPtr i,
        show (cmpPBase + 36 : Word) + 4 = (cmpPBase + 40 : Word) from by decide]
      at haddi7
    have haddi5 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x5 (pConstAddr + BitVec.ofNat 64 i)
        (1 : BitVec 12) (cmpPBase + 40) (by decide))
      (by rw [hCR]; code_mem)
    rw [cursor_advance pConstAddr i,
        show (cmpPBase + 40 : Word) + 4 = (cmpPBase + 44 : Word) from by decide]
      at haddi5
    have haddi6 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (32 - i)) (-1 : BitVec 12)
        (cmpPBase + 44) (by decide))
      (by rw [hCR]; code_mem)
    rw [counter_dec i hi,
        show (cmpPBase + 44 : Word) + 4 = (cmpPBase + 48 : Word) from by decide]
      at haddi6
    have hjal := liftCode (cr' := CR)
      (jal_x0_spec_gen_within (-32 : BitVec 21) (cmpPBase + 48))
      (by rw [hCR]; code_mem)
    rw [show (cmpPBase + 48 : Word) + signExtend21 (-32 : BitVec 21)
          = (cmpPBase + 16 : Word) from by decide] at hjal
    have haddi7F := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
        memOwn outPtr)
      (by pcf) haddi7
    have haddi5F := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
        memOwn outPtr)
      (by pcf) haddi5
    have haddi6F := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 (i + 1))) **
        ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
        memOwn outPtr)
      (by pcf) haddi6
    have hjalF := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 (i + 1))) **
        ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
        memOwn outPtr)
      (by pcf) hjal
    have hc1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) haddi7F haddi5F
    have hc2 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hc1 haddi6F
    have hc3 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        rw [sepConj_emp_left']
        xperm_hyp hp) hc2 hjalF
    refine cpsTripleWithin_weaken
      (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
      (fun h hq => ?_) hc3
    rw [sepConj_emp_left'] at hq
    unfold cmpInv
    refine (sepConj_pure_left h).2 ⟨hpref', ?_⟩
    have hq1 : (((.x28 : Reg) ↦ᵣ xByte) ** (((.x29 : Reg) ↦ᵣ pByte) **
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
         ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 (i + 1))) **
         ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 (i + 1))) **
         ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
         memOwn outPtr))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x28 _)
      (sepConj_mono (regIs_to_regOwn .x29 _)
        (fun _ hh => hh)) h hq1
    xperm_hyp hq2
  -- ---- the ordered bltu pair as ONE three-outcome join station ----
  have hjoin : cpsBranchWithin (1 + (1 + 4)) (cmpPBase + 28) CR WSL
      ret (cmpPost inPtr outPtr ret xs)
      (cmpPBase + 16) (cmpInv inPtr outPtr ret xs (i + 1)) :=
    triCmpStoreJoin_spec
      (condLt := BitVec.ult xByte pByte) (condGt := BitVec.ult pByte xByte)
      (PLt := WSL) (PMid := WSL) (PGt := WSL) (PEq := WSL)
      (cpsBranchWithin_weaken
        (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
        (fun _ hq => hq) (fun _ hq => hq) hbrA)
      (fun h hq => by rw [hWSL]; xperm_hyp hq)
      (fun h hq => by rw [hWSL]; xperm_hyp hq)
      (fun hc => cpsTripleWithin_mono_nSteps (by omega) (htailLt hc))
      (fun _ => cpsBranchWithin_weaken
        (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
        (fun _ hq => hq) (fun _ hq => hq) hbrB)
      (fun h hq => by rw [hWSL]; xperm_hyp hq)
      (fun h hq => by rw [hWSL]; xperm_hyp hq)
      (fun hnXP hc => htailGt hnXP hc)
      (fun hnXP hnPX => cpsTripleWithin_as_cpsBranchWithin_right ret
        (cmpPost inPtr outPtr ret xs) (hcont hnXP hnPX))
  -- ---- loads ; join station ----
  have hfallIter := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by rw [hWSL]; xperm_hyp hp) hpre1 hjoin
  -- ---- the header BEQ station wraps it all ----
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (breakStation_spec (cond := (BitVec.ofNat 64 (32 - i) = (0 : Word)))
      (PT := ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
        memOwn outPtr)
      (PF := ((((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
        ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion inPtr xs) **
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x29 : Reg) ↦ᵣ v29) **
        bytesRegion pConstAddr secp256k1PBytes ** memOwn outPtr)))
      hbrHdr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun hc => absurd hc (ctr_ne_zero i hi))
      (fun _ => hfallIter))

-- ============================================================================
-- §5  Loop exhaustion: all 32 bytes equal → eq tail writes 1
-- ============================================================================

private theorem cmpExh_spec
    (hlenX : xs.length = 32)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 5 (cmpPBase + 16) ret
      (CodeReq.ofProg cmpPBase secfCmpP_prog)
      (cmpInv inPtr outPtr ret xs 32)
      (cmpPost inPtr outPtr ret xs) := by
  set CR := CodeReq.ofProg cmpPBase secfCmpP_prog with hCR
  have hplen : secp256k1PBytes.length = 32 := by decide
  unfold cmpInv
  refine cpsTripleWithin_pure_pre (fun hpref => ?_)
  have hEq : xs = secp256k1PBytes := bytes_eq_of_prefix_all xs secp256k1PBytes
    (by omega) (fun j hj => hpref j (by omega))
  have heqN : beBytesToNat xs = beBytesToNat secp256k1PBytes := by rw [hEq]
  have hnlt : ¬ (beBytesToNat xs < beBytesToNat secp256k1PBytes) := by omega
  -- header BEQ, taken (counter = 0)
  have hbrHdr := cpsBranchWithin_frameR
    (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 32)) **
      ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 32)) **
      ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
      memOwn outPtr)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x6 .x0 (48 : BitVec 13)
        (BitVec.ofNat 64 (32 - 32)) (0 : Word) (cmpPBase + 16))
      (hmono := by rw [hCR]; code_mem))
  rw [show (cmpPBase + 16 : Word) + signExtend13 (48 : BitVec 13)
        = (cmpPBase + 64 : Word) from by decide,
      show (cmpPBase + 16 : Word) + 4 = (cmpPBase + 20 : Word) from by decide]
    at hbrHdr
  -- taken arm: eq tail writes 1 (framed, converted, if-resolved)
  have htail : cpsTripleWithin 4 (cmpPBase + 64) ret CR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
       ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 32)) **
       ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 32)) **
       ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
       memOwn outPtr)
      (cmpPost inPtr outPtr ret xs) := by
    have h := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 32)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29 **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes)
      (by pcf) (eqTail_spec outPtr ret inPtr halignRet)
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) h
    · have hp1 : (((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 32)) **
          (((.x11 : Reg) ↦ᵣ outPtr) ** memOwn outPtr **
           ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
           ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
           ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 32)) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           regOwn .x28 ** regOwn .x29 **
           bytesRegion inPtr xs **
           bytesRegion pConstAddr secp256k1PBytes)) h := by
        xperm_hyp hp
      have hp2 := sepConj_mono (regIs_to_regOwn .x5 _)
        (fun _ hh => hh) h hp1
      xperm_hyp hp2
    · unfold cmpPost
      rw [if_neg hnlt, if_pos heqN]
      have hq1 : (((.x5 : Reg) ↦ᵣ (1 : Word)) **
          (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
            (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 32)) **
              (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
               ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
               regOwn .x28 ** regOwn .x29 **
               bytesRegion inPtr xs **
               bytesRegion pConstAddr secp256k1PBytes **
               (outPtr ↦ₘ (1 : Word)))))) h := by
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
      (PT := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 32)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 32)) **
        ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29 **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
        memOwn outPtr))
      (PF := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 32)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 32)) **
        ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29 **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
        memOwn outPtr))
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

/-- **`secf_cmp_p` at its linked address** (genuine post): the output
    dword `[a1]` is the REAL numeric three-way comparison of the 32-byte
    big-endian input against the secp256k1 field prime — `0` for `< p`,
    `1` for `= p`, `2` for `> p` (`beBytesToNat secp256k1PBytes` IS `p`,
    pinned by the `#guard` above); `a0 = 0`; the input and the read-only
    `globalConst` prime region untouched.  The `la` materialization of
    `secp256k1_p_be` is PROVEN (`la_materialize_within`), not assumed. -/
theorem secfCmpP_spec (inPtr outPtr ret : Word) (xs : List (BitVec 8))
    (hlenX : xs.length = 32)
    (halignIn : inPtr.toNat % 8 = 0)
    (hovIn : inPtr.toNat + 32 < 2 ^ 64)
    (hvalidIn : ∀ k, k < 32 → isValidByteAccess (inPtr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 297 cmpPBase ret
      (CodeReq.ofProg cmpPBase secfCmpP_prog)
      (((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion inPtr xs **
       globalConst pConstAddr secp256k1PBytes ** memOwn outPtr)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion inPtr xs **
       globalConst pConstAddr secp256k1PBytes **
       (outPtr ↦ₘ (if beBytesToNat xs < beBytesToNat secp256k1PBytes
         then (0 : Word)
         else if beBytesToNat xs = beBytesToNat secp256k1PBytes
         then (1 : Word) else (2 : Word)))) := by
  unfold globalConst
  set CR := CodeReq.ofProg cmpPBase secfCmpP_prog with hCR
  -- peel the la destination x5 and the MV destination x7
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** regOwn .x28 ** regOwn .x29 **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
        memOwn outPtr) **
        regOwn .x7)
      (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
      (P := (((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** regOwn .x28 ** regOwn .x29 **
        bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
        memOwn outPtr) **
        ((.x5 : Reg) ↦ᵣ v5))
      (fun v7 => ?_))
  -- ---- init: la x5, secp256k1_p_be ; li x6, 32 ; mv x7, a0 ----
  have hla := la_materialize_within .x5 v5 cmpPBase pConstAddr
    (cr := CR) (by decide) (by decide)
    (by rw [hCR]; code_mem) (by rw [hCR]; code_mem)
  have hli6 := liftCode (cr' := CR)
    (li_spec_gen_own_within .x6 (32 : Word) (cmpPBase + 8) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (cmpPBase + 8 : Word) + 4 = (cmpPBase + 12 : Word) from by decide]
    at hli6
  have hmv7 := liftCode (cr' := CR)
    (mv_spec_gen_within .x7 .x10 inPtr v7 (cmpPBase + 12) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (cmpPBase + 12 : Word) + 4 = (cmpPBase + 16 : Word) from by decide]
    at hmv7
  -- ---- the three-outcome writable-output loop ----
  have hloop := twoBreakRetLoop_spec (hdr := (cmpPBase + 16 : Word)) (ret := ret)
    (cr := CR) (Q := cmpPost inPtr outPtr ret xs) 32 9 5
    (cmpInv inPtr outPtr ret xs)
    (fun i hi => cmpIter_spec inPtr outPtr ret xs hlenX
      halignIn hovIn hvalidIn halignRet i hi)
    (cmpExh_spec inPtr outPtr ret xs hlenX halignRet)
  -- ---- frames + chain ----
  have hlaF := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ v7) **
      ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x6 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
      memOwn outPtr)
    (by pcf) hla
  have hli6F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ pConstAddr) ** ((.x7 : Reg) ↦ᵣ v7) **
      ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
      memOwn outPtr)
    (by pcf) hli6
  have hmv7F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ pConstAddr) ** ((.x6 : Reg) ↦ᵣ (32 : Word)) **
      ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion inPtr xs ** bytesRegion pConstAddr secp256k1PBytes **
      memOwn outPtr)
    (by pcf) hmv7
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlaF hli6F
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc1 hmv7F
  have hc3 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold cmpInv
      refine (sepConj_pure_left h).2
        ⟨fun j hj => absurd hj (Nat.not_lt_zero j), ?_⟩
      rw [show (BitVec.ofNat 64 (32 - 0) : Word) = (32 : Word) from by decide,
          show inPtr + BitVec.ofNat 64 0 = inPtr from by
            rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
            bv_omega,
          show pConstAddr + BitVec.ofNat 64 0 = pConstAddr from by decide]
      xperm_hyp hp) hc2 hloop
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by unfold cmpPost at hq; exact hq)
    (cpsTripleWithin_mono_nSteps (by omega) hc3)

#print axioms secfCmpP_spec

end Secp256k1FieldCmpPSAsm

end EvmAsm.Codegen
