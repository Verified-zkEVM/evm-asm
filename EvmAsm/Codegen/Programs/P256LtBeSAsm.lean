/-
  EvmAsm.Codegen.Programs.P256LtBeSAsm

  `p256_lt_be` — the 32-byte big-endian lexicographic comparator of the
  P256VERIFY range checks — via the three-outcome compare join
  (`EvmAsm/Rv64/SAsm/TriCmpStoreJoin.lean`) over SHARED `li a0, c ; ret`
  return tails (`sharedRetTail_spec`, `EvmAsm/Rv64/SAsm/RetForwardJoin.lean`).

  The routine byte-walks the two 32-byte big-endian operands (both
  caller-provided buffers — no global constant, no `la`, the program is
  position-independent) with a countdown counter and advancing cursors,
  and routes its THREE exits onto TWO `li`/`ret` tails:

  ```
        li   t2, 32 ; mv t0, a0 ; mv t1, a1
  hdr:  beq  t2, x0, .tailZero          -- exhaustion (equal)  → a0 = 0
        lbu  x28, 0(t0) ; lbu x29, 0(t1)
        bltu x28, x29, .tailOne         -- a[i] < b[i]         → a0 = 1
        bltu x29, x28, .tailZero        -- b[i] < a[i]         → a0 = 0
        addi t0, t0, 1 ; addi t1, t1, 1 ; addi t2, t2, -1 ; j hdr
  .tailOne:  li a0, 1 ; ret
  .tailZero: li a0, 0 ; ret
  ```

  Each tail is one `sharedRetTail_spec` instance (proven once per tail
  address); the ordered `bltu` pair is one `triCmpStoreJoin_spec`
  station; the loop is one `twoBreakRetLoop_spec`.  The `=` and `>`
  outcomes SHARE the zero tail — big-endian lexicographic order IS
  numeric order (`U256MinSAsm.beBytesToNat_lt_of_prefix_lt` in both
  directions, all-equal bridge `bytes_eq_of_prefix_all`).

  **Genuine post**: `a0 = if beBytesToNat as < beBytesToNat bs
  then 1 else 0` — the REAL numeric strict less-than of the two
  operands; both input regions untouched, `a1` preserved.

  Byte-transparent: the spec is stated at the `#guard`-tied symbolic
  `GuestAddrs.p256_lt_be` base (bead evm-asm-6agnq) over the emitted
  `p256LtBe_prog` directly — no guest-byte change, no A/B run needed.

  Resolves blocker bead evm-asm-4ch8f.58.2.7.1 (the "return-tail
  two-break loop" shape is exactly this composition — no new `Stmt`
  combinator was needed).  Bead: evm-asm-4ch8f.58.2.7.
-/

import EvmAsm.Codegen.Programs.P256Verify
import EvmAsm.Codegen.Programs.U256MinSAsm
import EvmAsm.Rv64.SAsm.TriCmpStoreJoin
import EvmAsm.Rv64.SAsm.RetForwardJoin

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace P256LtBeSAsm

open U256MinSAsm (beBytesToNat_lt_of_prefix_lt bytes_eq_of_prefix_all)

/-- The routine base, symbolic (bead evm-asm-6agnq). -/
def ltPBase : Word := (GuestAddrs.p256_lt_be : Word)

#guard p256LtBe_prog.length = 16
-- The comparator is position-independent (no PC-relative instruction).

/-
  Emitted layout relative to `GuestAddrs.p256_lt_be`:
    +0   li    x7, 32
    +4   mv    x5, x10
    +8   mv    x6, x11
    +12  beq   x7, x0, +44  → +56 (zero tail)                   [hdr]
    +16  lbu   x28, 0(x5)
    +20  lbu   x29, 0(x6)
    +24  bltu  x28, x29, +24 → +48 (one tail)
    +28  bltu  x29, x28, +28 → +56 (zero tail)
    +32  addi  x5, x5, 1
    +36  addi  x6, x6, 1
    +40  addi  x7, x7, -1
    +44  jal   x0, -32      → +12
    +48  li    x10, 1                                           [one tail]
    +52  jalr  x0, x1, 0
    +56  li    x10, 0                                           [zero tail]
    +60  jalr  x0, x1, 0
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

variable (aPtr bPtr ret : Word) (xs bs : List (BitVec 8))

/-- Loop invariant at the header after `i` matched bytes: the counter holds
    `32 - i`, both cursors sit at byte `i`, the first `i` bytes of the two
    operands agree (pure conjunct), the fixed registers and both input
    regions are untouched. -/
private def ltInv (i : Nat) : Assertion :=
  ⌜∀ j, j < i → xs.getD j 0 = bs.getD j 0⌝ **
  ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
  ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
  ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
  ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
  ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x28 ** regOwn .x29 **
  bytesRegion aPtr xs ** bytesRegion bPtr bs

/-- The genuine post: `a0` is the REAL numeric strict less-than of the
    two 32-byte big-endian operands; both input regions untouched, `a1`
    preserved. -/
private def ltPost : Assertion :=
  ((.x10 : Reg) ↦ᵣ (if beBytesToNat xs < beBytesToNat bs
    then (1 : Word) else (0 : Word))) **
  ((.x11 : Reg) ↦ᵣ bPtr) **
  ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x6 ** regOwn .x7 ** regOwn .x5 **
  regOwn .x28 ** regOwn .x29 **
  bytesRegion aPtr xs ** bytesRegion bPtr bs

-- ============================================================================
-- §3  One loop iteration (the three-outcome join station)
-- ============================================================================

/-- One iteration at the header with `i < 32` bytes known equal: either a
    `bltu` break fires and the corresponding shared `li`/`ret` tail
    RETURNS with the genuine post, or the iteration loops back to the
    header with the invariant advanced.  Exactly the
    `twoBreakRetLoop_spec` iteration shape, built from one
    `triCmpStoreJoin_spec` station wrapped by the header `beq`
    `breakStation_spec`. -/
private theorem ltIter_spec
    (hlenX : xs.length = 32) (hlenB : bs.length = 32)
    (halignA : aPtr.toNat % 8 = 0) (halignB : bPtr.toNat % 8 = 0)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 → isValidByteAccess (aPtr + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 → isValidByteAccess (bPtr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (i : Nat) (hi : i < 32) :
    cpsBranchWithin 9 (ltPBase + 12)
      (CodeReq.ofProg ltPBase p256LtBe_prog)
      (ltInv aPtr bPtr ret xs bs i)
      ret (ltPost aPtr bPtr ret xs bs)
      (ltPBase + 12) (ltInv aPtr bPtr ret xs bs (i + 1)) := by
  set CR := CodeReq.ofProg ltPBase p256LtBe_prog with hCR
  have hplen : bs.length = 32 := hlenB
  have hix : i < xs.length := by omega
  have hip : i < bs.length := by omega
  set xByte := (xs[i]'hix).zeroExtend 64 with hxByte
  set pByte := (bs[i]'hip).zeroExtend 64 with hpByte
  have hxBN : xByte.toNat = (xs[i]'hix).toNat := by
    rw [hxByte]
    show (BitVec.setWidth 64 _).toNat = _
    rw [BitVec.toNat_setWidth]
    have := (xs[i]'hix).isLt
    omega
  have hpBN : pByte.toNat = (bs[i]'hip).toNat := by
    rw [hpByte]
    show (BitVec.setWidth 64 _).toNat = _
    rw [BitVec.toNat_setWidth]
    have := (bs[i]'hip).isLt
    omega
  have hgdX : xs.getD i 0 = xs[i]'hix := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hix]
    rfl
  have hgdP : bs.getD i 0 = bs[i]'hip := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hip]
    rfl
  -- strip the pure prefix fact
  unfold ltInv
  refine cpsBranchWithin_pure_pre (fun hpref => ?_)
  -- peel this iteration's scratch registers x28, x29
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x28)
      (P := (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
        ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aPtr xs ** bytesRegion bPtr bs) **
        regOwn .x29)
      (fun v28 => ?_))
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x29)
      (P := (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
        ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aPtr xs ** bytesRegion bPtr bs) **
        ((.x28 : Reg) ↦ᵣ v28))
      (fun v29 => ?_))
  -- canonical working set, x28/x29 concrete
  suffices hmain :
      cpsBranchWithin 9 (ltPBase + 12) CR
        (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
         ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
         ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
         ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
         bytesRegion aPtr xs ** bytesRegion bPtr bs)
        ret (ltPost aPtr bPtr ret xs bs)
        (ltPBase + 12) (ltInv aPtr bPtr ret xs bs (i + 1)) by
    exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hmain
  -- ---- the two LBU loads (+20 input, +24 const) ----
  have hlbuX := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x28 .x5 aPtr v28 (ltPBase + 16) xs i
      (by decide) halignA hix (by omega) (hvalidA i hi))
    (by rw [hCR]; code_mem)
  rw [show (ltPBase + 16 : Word) + 4 = (ltPBase + 20 : Word) from by decide]
    at hlbuX
  have hlbuP := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x29 .x6 bPtr v29 (ltPBase + 20)
      bs i (by decide) halignB hip (by omega) (hvalidB i hi))
    (by rw [hCR]; code_mem)
  rw [show (ltPBase + 20 : Word) + 4 = (ltPBase + 24 : Word) from by decide]
    at hlbuP
  have hlbuXF := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x29 : Reg) ↦ᵣ v29) **
      bytesRegion bPtr bs)
    (by pcf) hlbuX
  have hlbuPF := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ xByte) **
      bytesRegion aPtr xs)
    (by pcf) hlbuP
  have hpre1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlbuXF hlbuPF
  -- ---- the header BEQ station (+16; never taken at i < 32) ----
  have hbrHdr := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
      ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
      bytesRegion aPtr xs ** bytesRegion bPtr bs)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x7 .x0 (44 : BitVec 13)
        (BitVec.ofNat 64 (32 - i)) (0 : Word) (ltPBase + 12))
      (hmono := by rw [hCR]; code_mem))
  rw [show (ltPBase + 12 : Word) + signExtend13 (44 : BitVec 13)
        = (ltPBase + 56 : Word) from by decide,
      show (ltPBase + 12 : Word) + 4 = (ltPBase + 16 : Word) from by decide]
    at hbrHdr
  -- ---- the ordered bltu pair, framed ----
  have hbrA := cpsBranchWithin_frameR
    (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
      ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion aPtr xs ** bytesRegion bPtr bs)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bltu_spec_gen_within .x28 .x29 (24 : BitVec 13) xByte pByte
        (ltPBase + 24))
      (hmono := by rw [hCR]; code_mem))
  rw [show (ltPBase + 24 : Word) + signExtend13 (24 : BitVec 13)
        = (ltPBase + 48 : Word) from by decide,
      show (ltPBase + 24 : Word) + 4 = (ltPBase + 28 : Word) from by decide]
    at hbrA
  have hbrB := cpsBranchWithin_frameR
    (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
      ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion aPtr xs ** bytesRegion bPtr bs)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bltu_spec_gen_within .x29 .x28 (28 : BitVec 13) pByte xByte
        (ltPBase + 28))
      (hmono := by rw [hCR]; code_mem))
  rw [show (ltPBase + 28 : Word) + signExtend13 (28 : BitVec 13)
        = (ltPBase + 56 : Word) from by decide,
      show (ltPBase + 28 : Word) + 4 = (ltPBase + 32 : Word) from by decide]
    at hbrB
  -- the canonical post-load working set (all three arms' currency)
  set WSL : Assertion :=
    ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
    ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
    ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
    ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
    ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
    ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    bytesRegion aPtr xs ** bytesRegion bPtr bs with hWSL
  -- ---- break arm A: one tail returns 1 (in < p decided) ----
  have htailOne : BitVec.ult xByte pByte →
      cpsTripleWithin 4 (ltPBase + 48) ret CR WSL
        (ltPost aPtr bPtr ret xs bs) := by
    intro hc
    have hltN : (xs[i]'hix).toNat < (bs[i]'hip).toNat := by
      have hc' : xByte.toNat < pByte.toNat := by
        simpa [BitVec.ult, decide_eq_true_eq] using hc
      omega
    have hlt : beBytesToNat xs < beBytesToNat bs :=
      beBytesToNat_lt_of_prefix_lt xs bs (by omega) i hix hpref
        (by rw [hgdX, hgdP]; omega)
    have h := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
        ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf)
      (sharedRetTail_spec CR (ltPBase + 48) ret .x10 (1 : Word) aPtr
        (bytesRegion aPtr xs ** bytesRegion bPtr bs)
        (by pcf) (by decide) halignRet
        (by rw [hCR]; code_mem) (by rw [hCR]; code_mem))
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) h)
    · rw [hWSL] at hp
      xperm_hyp hp
    · unfold ltPost
      rw [if_pos hlt]
      have hq1 : (((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
          (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
            (((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
              (((.x28 : Reg) ↦ᵣ xByte) ** (((.x29 : Reg) ↦ᵣ pByte) **
                (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
                 ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                 bytesRegion aPtr xs **
                 bytesRegion bPtr bs)))))) h := by
        xperm_hyp hq
      have hq2 := sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x5 _)
            (sepConj_mono (regIs_to_regOwn .x28 _)
              (sepConj_mono (regIs_to_regOwn .x29 _)
                (fun _ hh => hh))))) h hq1
      xperm_hyp hq2
  -- ---- break arm B: zero tail returns 0 (p < in decided) ----
  have htailZeroGt : ¬ BitVec.ult xByte pByte → BitVec.ult pByte xByte →
      cpsTripleWithin 4 (ltPBase + 56) ret CR WSL
        (ltPost aPtr bPtr ret xs bs) := by
    intro _ hc
    have hgtN : (bs[i]'hip).toNat < (xs[i]'hix).toNat := by
      have hc' : pByte.toNat < xByte.toNat := by
        simpa [BitVec.ult, decide_eq_true_eq] using hc
      omega
    have hgt : beBytesToNat bs < beBytesToNat xs :=
      beBytesToNat_lt_of_prefix_lt bs xs (by omega) i hip
        (fun j hj => (hpref j hj).symm)
        (by rw [hgdX, hgdP]; omega)
    have hnlt : ¬ (beBytesToNat xs < beBytesToNat bs) := by
      omega
    have h := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
        ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf)
      (sharedRetTail_spec CR (ltPBase + 56) ret .x10 (0 : Word) aPtr
        (bytesRegion aPtr xs ** bytesRegion bPtr bs)
        (by pcf) (by decide) halignRet
        (by rw [hCR]; code_mem) (by rw [hCR]; code_mem))
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) h)
    · rw [hWSL] at hp
      xperm_hyp hp
    · unfold ltPost
      rw [if_neg hnlt]
      have hq1 : (((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
          (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
            (((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
              (((.x28 : Reg) ↦ᵣ xByte) ** (((.x29 : Reg) ↦ᵣ pByte) **
                (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
                 ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                 bytesRegion aPtr xs **
                 bytesRegion bPtr bs)))))) h := by
        xperm_hyp hq
      have hq2 := sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x5 _)
            (sepConj_mono (regIs_to_regOwn .x28 _)
              (sepConj_mono (regIs_to_regOwn .x29 _)
                (fun _ hh => hh))))) h hq1
      xperm_hyp hq2
  -- ---- continue segment: 3 × addi ; jal → header with inv (i+1) ----
  have hcont : ¬ BitVec.ult xByte pByte → ¬ BitVec.ult pByte xByte →
      cpsTripleWithin 4 (ltPBase + 32) (ltPBase + 12) CR WSL
        (ltInv aPtr bPtr ret xs bs (i + 1)) := by
    intro hnXP hnPX
    have hEqByte : xs[i]'hix = bs[i]'hip := by
      apply BitVec.eq_of_toNat_eq
      have h1 : ¬ xByte.toNat < pByte.toNat := by
        intro hlt
        exact hnXP (by simp [BitVec.ult, decide_eq_true_eq]; omega)
      have h2 : ¬ pByte.toNat < xByte.toNat := by
        intro hlt
        exact hnPX (by simp [BitVec.ult, decide_eq_true_eq]; omega)
      omega
    have hpref' : ∀ j, j < i + 1 → xs.getD j 0 = bs.getD j 0 := by
      intro j hj
      by_cases hji : j < i
      · exact hpref j hji
      · have : j = i := by omega
        subst this
        rw [hgdX, hgdP, hEqByte]
    have haddi7 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x5 (aPtr + BitVec.ofNat 64 i) (1 : BitVec 12)
        (ltPBase + 32) (by decide))
      (by rw [hCR]; code_mem)
    rw [cursor_advance aPtr i,
        show (ltPBase + 32 : Word) + 4 = (ltPBase + 36 : Word) from by decide]
      at haddi7
    have haddi5 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x6 (bPtr + BitVec.ofNat 64 i)
        (1 : BitVec 12) (ltPBase + 36) (by decide))
      (by rw [hCR]; code_mem)
    rw [cursor_advance bPtr i,
        show (ltPBase + 36 : Word) + 4 = (ltPBase + 40 : Word) from by decide]
      at haddi5
    have haddi6 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x7 (BitVec.ofNat 64 (32 - i)) (-1 : BitVec 12)
        (ltPBase + 40) (by decide))
      (by rw [hCR]; code_mem)
    rw [counter_dec i hi,
        show (ltPBase + 40 : Word) + 4 = (ltPBase + 44 : Word) from by decide]
      at haddi6
    have hjal := liftCode (cr' := CR)
      (jal_x0_spec_gen_within (-32 : BitVec 21) (ltPBase + 44))
      (by rw [hCR]; code_mem)
    rw [show (ltPBase + 44 : Word) + signExtend21 (-32 : BitVec 21)
          = (ltPBase + 12 : Word) from by decide] at hjal
    have haddi7F := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aPtr xs ** bytesRegion bPtr bs)
      (by pcf) haddi7
    have haddi5F := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aPtr xs ** bytesRegion bPtr bs)
      (by pcf) haddi5
    have haddi6F := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aPtr xs ** bytesRegion bPtr bs)
      (by pcf) haddi6
    have hjalF := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
        ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aPtr xs ** bytesRegion bPtr bs)
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
    unfold ltInv
    refine (sepConj_pure_left h).2 ⟨hpref', ?_⟩
    have hq1 : (((.x28 : Reg) ↦ᵣ xByte) ** (((.x29 : Reg) ↦ᵣ pByte) **
        (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
         ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 (i + 1))) **
         ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 (i + 1))) **
         ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion aPtr xs ** bytesRegion bPtr bs))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x28 _)
      (sepConj_mono (regIs_to_regOwn .x29 _)
        (fun _ hh => hh)) h hq1
    xperm_hyp hq2
  -- ---- the ordered bltu pair as ONE three-outcome join station ----
  have hjoin : cpsBranchWithin (1 + (1 + 4)) (ltPBase + 24) CR WSL
      ret (ltPost aPtr bPtr ret xs bs)
      (ltPBase + 12) (ltInv aPtr bPtr ret xs bs (i + 1)) :=
    triCmpStoreJoin_spec
      (condLt := BitVec.ult xByte pByte) (condGt := BitVec.ult pByte xByte)
      (PLt := WSL) (PMid := WSL) (PGt := WSL) (PEq := WSL)
      (cpsBranchWithin_weaken
        (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
        (fun _ hq => hq) (fun _ hq => hq) hbrA)
      (fun h hq => by rw [hWSL]; xperm_hyp hq)
      (fun h hq => by rw [hWSL]; xperm_hyp hq)
      (fun hc => cpsTripleWithin_mono_nSteps (by omega) (htailOne hc))
      (fun _ => cpsBranchWithin_weaken
        (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
        (fun _ hq => hq) (fun _ hq => hq) hbrB)
      (fun h hq => by rw [hWSL]; xperm_hyp hq)
      (fun h hq => by rw [hWSL]; xperm_hyp hq)
      (fun hnXP hc => htailZeroGt hnXP hc)
      (fun hnXP hnPX => cpsTripleWithin_as_cpsBranchWithin_right ret
        (ltPost aPtr bPtr ret xs bs) (hcont hnXP hnPX))
  -- ---- loads ; join station ----
  have hfallIter := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by rw [hWSL]; xperm_hyp hp) hpre1 hjoin
  -- ---- the header BEQ station wraps it all ----
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (breakStation_spec (cond := (BitVec.ofNat 64 (32 - i) = (0 : Word)))
      (PT := ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
        ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
        bytesRegion aPtr xs ** bytesRegion bPtr bs)
      (PF := ((((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
        ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion aPtr xs) **
        (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x29 : Reg) ↦ᵣ v29) **
        bytesRegion bPtr bs)))
      hbrHdr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun hc => absurd hc (ctr_ne_zero i hi))
      (fun _ => hfallIter))

-- ============================================================================
-- §4  Loop exhaustion: all 32 bytes equal → zero tail returns 0
-- ============================================================================

private theorem ltExh_spec
    (hlenX : xs.length = 32) (hlenB : bs.length = 32)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 5 (ltPBase + 12) ret
      (CodeReq.ofProg ltPBase p256LtBe_prog)
      (ltInv aPtr bPtr ret xs bs 32)
      (ltPost aPtr bPtr ret xs bs) := by
  set CR := CodeReq.ofProg ltPBase p256LtBe_prog with hCR
  have hplen : bs.length = 32 := hlenB
  unfold ltInv
  refine cpsTripleWithin_pure_pre (fun hpref => ?_)
  have hEq : xs = bs := bytes_eq_of_prefix_all xs bs
    (by omega) (fun j hj => hpref j (by omega))
  have heqN : beBytesToNat xs = beBytesToNat bs := by rw [hEq]
  have hnlt : ¬ (beBytesToNat xs < beBytesToNat bs) := by omega
  -- header BEQ, taken (counter = 0)
  have hbrHdr := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 32)) **
      ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 32)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr xs ** bytesRegion bPtr bs)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x7 .x0 (44 : BitVec 13)
        (BitVec.ofNat 64 (32 - 32)) (0 : Word) (ltPBase + 12))
      (hmono := by rw [hCR]; code_mem))
  rw [show (ltPBase + 12 : Word) + signExtend13 (44 : BitVec 13)
        = (ltPBase + 56 : Word) from by decide,
      show (ltPBase + 12 : Word) + 4 = (ltPBase + 16 : Word) from by decide]
    at hbrHdr
  -- taken arm: zero tail returns 0 (framed, converted, if-resolved)
  have htail : cpsTripleWithin 4 (ltPBase + 56) ret CR
      (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
       ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 32)) **
       ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 32)) **
       ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion aPtr xs ** bytesRegion bPtr bs)
      (ltPost aPtr bPtr ret xs bs) := by
    have h := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 32)) **
        ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 32)) **
        ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29)
      (by pcf)
      (sharedRetTail_spec CR (ltPBase + 56) ret .x10 (0 : Word) aPtr
        (bytesRegion aPtr xs ** bytesRegion bPtr bs)
        (by pcf) (by decide) halignRet
        (by rw [hCR]; code_mem) (by rw [hCR]; code_mem))
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) h)
    · xperm_hyp hp
    · unfold ltPost
      rw [if_neg hnlt]
      have hq1 : (((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 32)) **
          (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
            (((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 32)) **
              (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
               ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
               regOwn .x28 ** regOwn .x29 **
               bytesRegion aPtr xs **
               bytesRegion bPtr bs)))) h := by
        xperm_hyp hq
      have hq2 := sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x5 _)
            (fun _ hh => hh))) h hq1
      xperm_hyp hq2
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (retJoinStation_spec
      (cond := (BitVec.ofNat 64 (32 - 32) = (0 : Word)))
      (PT := (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 32)) **
        ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 32)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29 **
        bytesRegion aPtr xs ** bytesRegion bPtr bs))
      (PF := (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x5 : Reg) ↦ᵣ (aPtr + BitVec.ofNat 64 32)) **
        ((.x6 : Reg) ↦ᵣ (bPtr + BitVec.ofNat 64 32)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29 **
        bytesRegion aPtr xs ** bytesRegion bPtr bs))
      hbrHdr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun _ => htail)
      (fun hc => absurd (by decide :
        (BitVec.ofNat 64 (32 - 32) : Word) = (0 : Word)) hc))

end Scan

-- ============================================================================
-- §5  The whole routine
-- ============================================================================

/-- **`p256_lt_be` at its linked address** (genuine post): `a0` is the
    REAL numeric strict less-than of the two 32-byte big-endian
    operands — `1` for `as < bs`, `0` otherwise (big-endian
    lexicographic order IS numeric order); both input regions
    untouched, `a1` preserved. -/
theorem p256LtBe_spec (aPtr bPtr ret : Word) (xs bs : List (BitVec 8))
    (hlenX : xs.length = 32) (hlenB : bs.length = 32)
    (halignA : aPtr.toNat % 8 = 0) (halignB : bPtr.toNat % 8 = 0)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 → isValidByteAccess (aPtr + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 → isValidByteAccess (bPtr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 296 ltPBase ret
      (CodeReq.ofProg ltPBase p256LtBe_prog)
      (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x5 **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion aPtr xs **
       bytesRegion bPtr bs)
      (((.x10 : Reg) ↦ᵣ (if beBytesToNat xs < beBytesToNat bs
         then (1 : Word) else (0 : Word))) **
       ((.x11 : Reg) ↦ᵣ bPtr) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x5 **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion aPtr xs **
       bytesRegion bPtr bs) := by
  set CR := CodeReq.ofProg ltPBase p256LtBe_prog with hCR
  -- peel the two MV destinations x5, x6 (the LI destination x7 is
  -- consumed as ownership by `li_spec_gen_own_within` directly)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        bytesRegion aPtr xs ** bytesRegion bPtr bs) **
        regOwn .x5)
      (fun v6 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        bytesRegion aPtr xs ** bytesRegion bPtr bs) **
        ((.x6 : Reg) ↦ᵣ v6))
      (fun v5 => ?_))
  -- ---- init: li x7, 32 ; mv x5, a0 ; mv x6, a1 ----
  have hli7 := liftCode (cr' := CR)
    (li_spec_gen_own_within .x7 (32 : Word) ltPBase (by decide))
    (by rw [hCR]; code_mem)
  have hmv5 := liftCode (cr' := CR)
    (mv_spec_gen_within .x5 .x10 aPtr v5 (ltPBase + 4) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (ltPBase + 4 : Word) + 4 = (ltPBase + 8 : Word) from by decide]
    at hmv5
  have hmv6 := liftCode (cr' := CR)
    (mv_spec_gen_within .x6 .x11 bPtr v6 (ltPBase + 8) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (ltPBase + 8 : Word) + 4 = (ltPBase + 12 : Word) from by decide]
    at hmv6
  -- ---- the three-outcome two-tail loop ----
  have hloop := twoBreakRetLoop_spec (hdr := (ltPBase + 12 : Word)) (ret := ret)
    (cr := CR) (Q := ltPost aPtr bPtr ret xs bs) 32 9 5
    (ltInv aPtr bPtr ret xs bs)
    (fun i hi => ltIter_spec aPtr bPtr ret xs bs hlenX hlenB
      halignA halignB hovA hovB hvalidA hvalidB halignRet i hi)
    (ltExh_spec aPtr bPtr ret xs bs hlenX hlenB halignRet)
  -- ---- frames + chain ----
  have hli7F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr xs ** bytesRegion bPtr bs)
    (by pcf) hli7
  have hmv5F := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr xs ** bytesRegion bPtr bs)
    (by pcf) hmv5
  have hmv6F := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x5 : Reg) ↦ᵣ aPtr) **
      ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr xs ** bytesRegion bPtr bs)
    (by pcf) hmv6
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hli7F hmv5F
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc1 hmv6F
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


end P256LtBeSAsm

end EvmAsm.Codegen
