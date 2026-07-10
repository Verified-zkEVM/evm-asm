/-
  EvmAsm.Codegen.Programs.Bn254FieldLtPSAsm

  `bnf_lt_p` — the EIP-196 BN254 coordinate range check — via the
  three-outcome compare join (`EvmAsm/Rv64/SAsm/TriCmpStoreJoin.lean`)
  over SHARED `li a0, c ; ret` return tails
  (`sharedRetTail_spec`, `EvmAsm/Rv64/SAsm/RetForwardJoin.lean`).

  The routine materializes the read-only global `bnf_p_be` with the
  `la` idiom (`auipc`+`addi`, PROVEN by `la_materialize_within` /
  `la_resolve` — only the decidable `laInRange` representability
  remains), byte-walks the 32-byte big-endian input against that
  constant with a countdown counter and advancing cursors, and routes
  its THREE exits onto TWO `li`/`ret` tails:

  ```
        la   t0, bnf_p_be ; li t1, 32 ; mv t2, a0
  hdr:  beq  t1, x0, .tailZero          -- exhaustion (equal)  → a0 = 0
        lbu  x28, 0(t2) ; lbu x29, 0(t0)
        bltu x28, x29, .tailOne         -- in[i] < p[i]        → a0 = 1
        bltu x29, x28, .tailZero        -- p[i] < in[i]        → a0 = 0
        addi t2, t2, 1 ; addi t0, t0, 1 ; addi t1, t1, -1 ; j hdr
  .tailOne:  li a0, 1 ; ret
  .tailZero: li a0, 0 ; ret
  ```

  Each tail is one `sharedRetTail_spec` instance (proven once per tail
  address); the ordered `bltu` pair is one `triCmpStoreJoin_spec`
  station; the loop is one `twoBreakRetLoop_spec`.  The `= p` and `> p`
  outcomes SHARE the zero tail — big-endian lexicographic order IS
  numeric order (`U256MinSAsm.beBytesToNat_lt_of_prefix_lt` in both
  directions, all-equal bridge `bytes_eq_of_prefix_all`).

  **Genuine post**: `a0 = if beBytesToNat in < beBytesToNat bn254PBytes
  then 1 else 0` — the REAL numeric strict comparison against the BN254
  base-field prime (pinned by `#guard` to
  `0x30644e72…fd47 = p_{BN254}`), the input and the `globalConst` prime
  region untouched.

  Byte-transparent: the spec is stated at the `#guard`-tied symbolic
  `GuestAddrs.bnf_lt_p` over the emitted `bnfLtP_prog` directly — no
  guest-byte change, no A/B run needed.  No hardcoded PC literals (bead
  evm-asm-6agnq): the base and the constant's address are referenced
  through `GuestAddrs`, pinned by the `#guard`s below.

  Bead: evm-asm-4ch8f.58.3.35.
-/

import EvmAsm.Codegen.Programs.Bn254Field
import EvmAsm.Codegen.Programs.U256MinSAsm
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.GlobalData
import EvmAsm.Rv64.SAsm.TriCmpStoreJoin
import EvmAsm.Rv64.SAsm.RetForwardJoin

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Bn254FieldLtPSAsm

open U256MinSAsm (beBytesToNat_lt_of_prefix_lt bytes_eq_of_prefix_all)

/-- The routine base, symbolic (bead evm-asm-6agnq). -/
def ltPBase : Word := (GuestAddrs.bnf_lt_p : Word)

/-- The read-only prime constant's link address, symbolic. -/
def pConstAddr : Word := (GuestAddrs.bnf_p_be : Word)

#guard bnfLtP_prog.length = 17

/-- BN254 base-field prime, as 32 big-endian bytes (mirrors the
    `bnf_p_be` data fragment in `Bn254Field.lean`). -/
def bn254PBytes : List (BitVec 8) :=
  [0x30, 0x64, 0x4e, 0x72, 0xe1, 0x31, 0xa0, 0x29,
   0xb8, 0x50, 0x45, 0xb6, 0x81, 0x81, 0x58, 0x5d,
   0x97, 0x81, 0x6a, 0x91, 0x68, 0x71, 0xca, 0x8d,
   0x3c, 0x20, 0x8c, 0x16, 0xd8, 0x7c, 0xfd, 0x47]

#guard bn254PBytes.length = 32

-- The constant bytes ARE the BN254 base-field prime.
#guard beBytesToNat bn254PBytes =
  0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

-- The `la` displacement is representable.
#guard decide (laInRange ltPBase pConstAddr)

/-- The emitter's reloc immediates ARE the psABI `%pcrel_hi`/`%pcrel_lo`
    of the `la` resolution model at this pc/target (kernel-checked). -/
theorem ltP_laHi_agree :
    Codegen.laHi GuestAddrs.bnf_p_be (GuestAddrs.bnf_lt_p + 0)
      = EvmAsm.Rv64.laHi ltPBase pConstAddr := by decide

theorem ltP_laLo_agree :
    Codegen.laLo GuestAddrs.bnf_p_be (GuestAddrs.bnf_lt_p + 0)
      = EvmAsm.Rv64.laLo ltPBase pConstAddr := by decide

/-
  Emitted layout relative to `GuestAddrs.bnf_lt_p`:
    +0   auipc x5, %pcrel_hi(bnf_p_be)
    +4   addi  x5, x5, %pcrel_lo
    +8   li    x6, 32
    +12  mv    x7, x10
    +16  beq   x6, x0, +44  → +60 (zero tail)                   [hdr]
    +20  lbu   x28, 0(x7)
    +24  lbu   x29, 0(x5)
    +28  bltu  x28, x29, +24 → +52 (one tail)
    +32  bltu  x29, x28, +28 → +60 (zero tail)
    +36  addi  x7, x7, 1
    +40  addi  x5, x5, 1
    +44  addi  x6, x6, -1
    +48  jal   x0, -32      → +16
    +52  li    x10, 1                                           [one tail]
    +56  jalr  x0, x1, 0
    +60  li    x10, 0                                           [zero tail]
    +64  jalr  x0, x1, 0
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

variable (inPtr ret : Word) (xs : List (BitVec 8))

/-- Loop invariant at the header after `i` matched bytes: the counter holds
    `32 - i`, both cursors sit at byte `i` (the const-side cursor walks the
    read-only prime region), the first `i` bytes agree with the prime
    (pure conjunct), the fixed registers, the input region and the
    constant region are untouched. -/
private def ltInv (i : Nat) : Assertion :=
  ⌜∀ j, j < i → xs.getD j 0 = bn254PBytes.getD j 0⌝ **
  ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
  ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
  ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
  ((.x10 : Reg) ↦ᵣ inPtr) **
  ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x28 ** regOwn .x29 **
  bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes

/-- The genuine post: `a0` is the REAL numeric strict comparison of the
    32-byte big-endian input against the prime; the input and the
    constant region untouched. -/
private def ltPost : Assertion :=
  ((.x10 : Reg) ↦ᵣ (if beBytesToNat xs < beBytesToNat bn254PBytes
    then (1 : Word) else (0 : Word))) **
  ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 **
  bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes

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
    (hlenX : xs.length = 32)
    (halignIn : inPtr.toNat % 8 = 0)
    (hovIn : inPtr.toNat + 32 < 2 ^ 64)
    (hvalidIn : ∀ k, k < 32 → isValidByteAccess (inPtr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (i : Nat) (hi : i < 32) :
    cpsBranchWithin 9 (ltPBase + 16)
      (CodeReq.ofProg ltPBase bnfLtP_prog)
      (ltInv inPtr ret xs i)
      ret (ltPost inPtr ret xs)
      (ltPBase + 16) (ltInv inPtr ret xs (i + 1)) := by
  set CR := CodeReq.ofProg ltPBase bnfLtP_prog with hCR
  have hplen : bn254PBytes.length = 32 := by decide
  have hix : i < xs.length := by omega
  have hip : i < bn254PBytes.length := by omega
  set xByte := (xs[i]'hix).zeroExtend 64 with hxByte
  set pByte := (bn254PBytes[i]'hip).zeroExtend 64 with hpByte
  have hxBN : xByte.toNat = (xs[i]'hix).toNat := by
    rw [hxByte]
    show (BitVec.setWidth 64 _).toNat = _
    rw [BitVec.toNat_setWidth]
    have := (xs[i]'hix).isLt
    omega
  have hpBN : pByte.toNat = (bn254PBytes[i]'hip).toNat := by
    rw [hpByte]
    show (BitVec.setWidth 64 _).toNat = _
    rw [BitVec.toNat_setWidth]
    have := (bn254PBytes[i]'hip).isLt
    omega
  have hgdX : xs.getD i 0 = xs[i]'hix := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hix]
    rfl
  have hgdP : bn254PBytes.getD i 0 = bn254PBytes[i]'hip := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hip]
    rfl
  -- strip the pure prefix fact
  unfold ltInv
  refine cpsBranchWithin_pure_pre (fun hpref => ?_)
  -- peel this iteration's scratch registers x28, x29
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x28)
      (P := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ inPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes) **
        regOwn .x29)
      (fun v28 => ?_))
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x29)
      (P := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ inPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes) **
        ((.x28 : Reg) ↦ᵣ v28))
      (fun v29 => ?_))
  -- canonical working set, x28/x29 concrete
  suffices hmain :
      cpsBranchWithin 9 (ltPBase + 16) CR
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
         ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
         ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
         ((.x10 : Reg) ↦ᵣ inPtr) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
         bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
        ret (ltPost inPtr ret xs)
        (ltPBase + 16) (ltInv inPtr ret xs (i + 1)) by
    exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hmain
  -- ---- the two LBU loads (+20 input, +24 const) ----
  have hlbuX := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x28 .x7 inPtr v28 (ltPBase + 20) xs i
      (by decide) halignIn hix (by omega) (hvalidIn i hi))
    (by rw [hCR]; code_mem)
  rw [show (ltPBase + 20 : Word) + 4 = (ltPBase + 24 : Word) from by decide]
    at hlbuX
  have hlbuP := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x29 .x5 pConstAddr v29 (ltPBase + 24)
      bn254PBytes i (by decide) (by decide) hip
      (by have h : pConstAddr.toNat = 0xbb565df0 := by decide
          omega)
      (pByte_valid i hi))
    (by rw [hCR]; code_mem)
  rw [show (ltPBase + 24 : Word) + 4 = (ltPBase + 28 : Word) from by decide]
    at hlbuP
  have hlbuXF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ inPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x29 : Reg) ↦ᵣ v29) **
      bytesRegion pConstAddr bn254PBytes)
    (by pcf) hlbuX
  have hlbuPF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ inPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ xByte) **
      bytesRegion inPtr xs)
    (by pcf) hlbuP
  have hpre1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlbuXF hlbuPF
  -- ---- the header BEQ station (+16; never taken at i < 32) ----
  have hbrHdr := cpsBranchWithin_frameR
    (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
      ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ inPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
      bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x6 .x0 (44 : BitVec 13)
        (BitVec.ofNat 64 (32 - i)) (0 : Word) (ltPBase + 16))
      (hmono := by rw [hCR]; code_mem))
  rw [show (ltPBase + 16 : Word) + signExtend13 (44 : BitVec 13)
        = (ltPBase + 60 : Word) from by decide,
      show (ltPBase + 16 : Word) + 4 = (ltPBase + 20 : Word) from by decide]
    at hbrHdr
  -- ---- the ordered bltu pair, framed ----
  have hbrA := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
      ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ inPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bltu_spec_gen_within .x28 .x29 (24 : BitVec 13) xByte pByte
        (ltPBase + 28))
      (hmono := by rw [hCR]; code_mem))
  rw [show (ltPBase + 28 : Word) + signExtend13 (24 : BitVec 13)
        = (ltPBase + 52 : Word) from by decide,
      show (ltPBase + 28 : Word) + 4 = (ltPBase + 32 : Word) from by decide]
    at hbrA
  have hbrB := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
      ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
      ((.x10 : Reg) ↦ᵣ inPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bltu_spec_gen_within .x29 .x28 (28 : BitVec 13) pByte xByte
        (ltPBase + 32))
      (hmono := by rw [hCR]; code_mem))
  rw [show (ltPBase + 32 : Word) + signExtend13 (28 : BitVec 13)
        = (ltPBase + 60 : Word) from by decide,
      show (ltPBase + 32 : Word) + 4 = (ltPBase + 36 : Word) from by decide]
    at hbrB
  -- the canonical post-load working set (all three arms' currency)
  set WSL : Assertion :=
    ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
    ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
    ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
    ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
    ((.x10 : Reg) ↦ᵣ inPtr) **
    ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes with hWSL
  -- ---- break arm A: one tail returns 1 (in < p decided) ----
  have htailOne : BitVec.ult xByte pByte →
      cpsTripleWithin 4 (ltPBase + 52) ret CR WSL
        (ltPost inPtr ret xs) := by
    intro hc
    have hltN : (xs[i]'hix).toNat < (bn254PBytes[i]'hip).toNat := by
      have hc' : xByte.toNat < pByte.toNat := by
        simpa [BitVec.ult, decide_eq_true_eq] using hc
      omega
    have hlt : beBytesToNat xs < beBytesToNat bn254PBytes :=
      beBytesToNat_lt_of_prefix_lt xs bn254PBytes (by omega) i hix hpref
        (by rw [hgdX, hgdP]; omega)
    have h := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf)
      (sharedRetTail_spec CR (ltPBase + 52) ret .x10 (1 : Word) inPtr
        (bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
        (by pcf) (by decide) halignRet
        (by rw [hCR]; code_mem) (by rw [hCR]; code_mem))
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) h)
    · rw [hWSL] at hp
      xperm_hyp hp
    · unfold ltPost
      rw [if_pos hlt]
      have hq1 : (((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
          (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
            (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
              (((.x28 : Reg) ↦ᵣ xByte) ** (((.x29 : Reg) ↦ᵣ pByte) **
                (((.x10 : Reg) ↦ᵣ (1 : Word)) **
                 ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                 bytesRegion inPtr xs **
                 bytesRegion pConstAddr bn254PBytes)))))) h := by
        xperm_hyp hq
      have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
        (sepConj_mono (regIs_to_regOwn .x6 _)
          (sepConj_mono (regIs_to_regOwn .x7 _)
            (sepConj_mono (regIs_to_regOwn .x28 _)
              (sepConj_mono (regIs_to_regOwn .x29 _)
                (fun _ hh => hh))))) h hq1
      xperm_hyp hq2
  -- ---- break arm B: zero tail returns 0 (p < in decided) ----
  have htailZeroGt : ¬ BitVec.ult xByte pByte → BitVec.ult pByte xByte →
      cpsTripleWithin 4 (ltPBase + 60) ret CR WSL
        (ltPost inPtr ret xs) := by
    intro _ hc
    have hgtN : (bn254PBytes[i]'hip).toNat < (xs[i]'hix).toNat := by
      have hc' : pByte.toNat < xByte.toNat := by
        simpa [BitVec.ult, decide_eq_true_eq] using hc
      omega
    have hgt : beBytesToNat bn254PBytes < beBytesToNat xs :=
      beBytesToNat_lt_of_prefix_lt bn254PBytes xs (by omega) i hip
        (fun j hj => (hpref j hj).symm)
        (by rw [hgdX, hgdP]; omega)
    have hnlt : ¬ (beBytesToNat xs < beBytesToNat bn254PBytes) := by
      omega
    have h := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf)
      (sharedRetTail_spec CR (ltPBase + 60) ret .x10 (0 : Word) inPtr
        (bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
        (by pcf) (by decide) halignRet
        (by rw [hCR]; code_mem) (by rw [hCR]; code_mem))
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) h)
    · rw [hWSL] at hp
      xperm_hyp hp
    · unfold ltPost
      rw [if_neg hnlt]
      have hq1 : (((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
          (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
            (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
              (((.x28 : Reg) ↦ᵣ xByte) ** (((.x29 : Reg) ↦ᵣ pByte) **
                (((.x10 : Reg) ↦ᵣ (0 : Word)) **
                 ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                 bytesRegion inPtr xs **
                 bytesRegion pConstAddr bn254PBytes)))))) h := by
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
      cpsTripleWithin 4 (ltPBase + 36) (ltPBase + 16) CR WSL
        (ltInv inPtr ret xs (i + 1)) := by
    intro hnXP hnPX
    have hEqByte : xs[i]'hix = bn254PBytes[i]'hip := by
      apply BitVec.eq_of_toNat_eq
      have h1 : ¬ xByte.toNat < pByte.toNat := by
        intro hlt
        exact hnXP (by simp [BitVec.ult, decide_eq_true_eq]; omega)
      have h2 : ¬ pByte.toNat < xByte.toNat := by
        intro hlt
        exact hnPX (by simp [BitVec.ult, decide_eq_true_eq]; omega)
      omega
    have hpref' : ∀ j, j < i + 1 → xs.getD j 0 = bn254PBytes.getD j 0 := by
      intro j hj
      by_cases hji : j < i
      · exact hpref j hji
      · have : j = i := by omega
        subst this
        rw [hgdX, hgdP, hEqByte]
    have haddi7 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x7 (inPtr + BitVec.ofNat 64 i) (1 : BitVec 12)
        (ltPBase + 36) (by decide))
      (by rw [hCR]; code_mem)
    rw [cursor_advance inPtr i,
        show (ltPBase + 36 : Word) + 4 = (ltPBase + 40 : Word) from by decide]
      at haddi7
    have haddi5 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x5 (pConstAddr + BitVec.ofNat 64 i)
        (1 : BitVec 12) (ltPBase + 40) (by decide))
      (by rw [hCR]; code_mem)
    rw [cursor_advance pConstAddr i,
        show (ltPBase + 40 : Word) + 4 = (ltPBase + 44 : Word) from by decide]
      at haddi5
    have haddi6 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (32 - i)) (-1 : BitVec 12)
        (ltPBase + 44) (by decide))
      (by rw [hCR]; code_mem)
    rw [counter_dec i hi,
        show (ltPBase + 44 : Word) + 4 = (ltPBase + 48 : Word) from by decide]
      at haddi6
    have hjal := liftCode (cr' := CR)
      (jal_x0_spec_gen_within (-32 : BitVec 21) (ltPBase + 48))
      (by rw [hCR]; code_mem)
    rw [show (ltPBase + 48 : Word) + signExtend21 (-32 : BitVec 21)
          = (ltPBase + 16 : Word) from by decide] at hjal
    have haddi7F := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x10 : Reg) ↦ᵣ inPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
      (by pcf) haddi7
    have haddi5F := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x10 : Reg) ↦ᵣ inPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
      (by pcf) haddi5
    have haddi6F := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 (i + 1))) **
        ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x10 : Reg) ↦ᵣ inPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
      (by pcf) haddi6
    have hjalF := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 (i + 1))) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 (i + 1))) **
        ((.x28 : Reg) ↦ᵣ xByte) ** ((.x29 : Reg) ↦ᵣ pByte) **
        ((.x10 : Reg) ↦ᵣ inPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
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
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
         ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 (i + 1))) **
         ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 (i + 1))) **
         ((.x10 : Reg) ↦ᵣ inPtr) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x28 _)
      (sepConj_mono (regIs_to_regOwn .x29 _)
        (fun _ hh => hh)) h hq1
    xperm_hyp hq2
  -- ---- the ordered bltu pair as ONE three-outcome join station ----
  have hjoin : cpsBranchWithin (1 + (1 + 4)) (ltPBase + 28) CR WSL
      ret (ltPost inPtr ret xs)
      (ltPBase + 16) (ltInv inPtr ret xs (i + 1)) :=
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
        (ltPost inPtr ret xs) (hcont hnXP hnPX))
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
        ((.x10 : Reg) ↦ᵣ inPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
        bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
      (PF := ((((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 i)) **
        ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion inPtr xs) **
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ inPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x29 : Reg) ↦ᵣ v29) **
        bytesRegion pConstAddr bn254PBytes)))
      hbrHdr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun hc => absurd hc (ctr_ne_zero i hi))
      (fun _ => hfallIter))

-- ============================================================================
-- §4  Loop exhaustion: all 32 bytes equal → zero tail returns 0
-- ============================================================================

private theorem ltExh_spec
    (hlenX : xs.length = 32)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 5 (ltPBase + 16) ret
      (CodeReq.ofProg ltPBase bnfLtP_prog)
      (ltInv inPtr ret xs 32)
      (ltPost inPtr ret xs) := by
  set CR := CodeReq.ofProg ltPBase bnfLtP_prog with hCR
  have hplen : bn254PBytes.length = 32 := by decide
  unfold ltInv
  refine cpsTripleWithin_pure_pre (fun hpref => ?_)
  have hEq : xs = bn254PBytes := bytes_eq_of_prefix_all xs bn254PBytes
    (by omega) (fun j hj => hpref j (by omega))
  have heqN : beBytesToNat xs = beBytesToNat bn254PBytes := by rw [hEq]
  have hnlt : ¬ (beBytesToNat xs < beBytesToNat bn254PBytes) := by omega
  -- header BEQ, taken (counter = 0)
  have hbrHdr := cpsBranchWithin_frameR
    (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 32)) **
      ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 32)) **
      ((.x10 : Reg) ↦ᵣ inPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x6 .x0 (44 : BitVec 13)
        (BitVec.ofNat 64 (32 - 32)) (0 : Word) (ltPBase + 16))
      (hmono := by rw [hCR]; code_mem))
  rw [show (ltPBase + 16 : Word) + signExtend13 (44 : BitVec 13)
        = (ltPBase + 60 : Word) from by decide,
      show (ltPBase + 16 : Word) + 4 = (ltPBase + 20 : Word) from by decide]
    at hbrHdr
  -- taken arm: zero tail returns 0 (framed, converted, if-resolved)
  have htail : cpsTripleWithin 4 (ltPBase + 60) ret CR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
       ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 32)) **
       ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 32)) **
       ((.x10 : Reg) ↦ᵣ inPtr) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
      (ltPost inPtr ret xs) := by
    have h := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 32)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 32)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29)
      (by pcf)
      (sharedRetTail_spec CR (ltPBase + 60) ret .x10 (0 : Word) inPtr
        (bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
        (by pcf) (by decide) halignRet
        (by rw [hCR]; code_mem) (by rw [hCR]; code_mem))
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) h)
    · xperm_hyp hp
    · unfold ltPost
      rw [if_neg hnlt]
      have hq1 : (((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 32)) **
          (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
            (((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 32)) **
              (((.x10 : Reg) ↦ᵣ (0 : Word)) **
               ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
               regOwn .x28 ** regOwn .x29 **
               bytesRegion inPtr xs **
               bytesRegion pConstAddr bn254PBytes)))) h := by
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
        ((.x10 : Reg) ↦ᵣ inPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29 **
        bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes))
      (PF := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - 32)) **
        ((.x7 : Reg) ↦ᵣ (inPtr + BitVec.ofNat 64 32)) **
        ((.x5 : Reg) ↦ᵣ (pConstAddr + BitVec.ofNat 64 32)) **
        ((.x10 : Reg) ↦ᵣ inPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** regOwn .x29 **
        bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes))
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

/-- **`bnf_lt_p` at its linked address** (genuine post): `a0` is the
    REAL numeric strict comparison of the 32-byte big-endian input
    against the BN254 base-field prime — `1` for `< p`, `0` otherwise
    (`beBytesToNat bn254PBytes` IS `p`, pinned by the `#guard` above);
    the input and the read-only `globalConst` prime region untouched.
    The `la` materialization of `bnf_p_be` is PROVEN
    (`la_materialize_within`), not assumed. -/
theorem bnfLtP_spec (inPtr ret : Word) (xs : List (BitVec 8))
    (hlenX : xs.length = 32)
    (halignIn : inPtr.toNat % 8 = 0)
    (hovIn : inPtr.toNat + 32 < 2 ^ 64)
    (hvalidIn : ∀ k, k < 32 → isValidByteAccess (inPtr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 297 ltPBase ret
      (CodeReq.ofProg ltPBase bnfLtP_prog)
      (((.x10 : Reg) ↦ᵣ inPtr) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion inPtr xs **
       globalConst pConstAddr bn254PBytes)
      (((.x10 : Reg) ↦ᵣ (if beBytesToNat xs < beBytesToNat bn254PBytes
         then (1 : Word) else (0 : Word))) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion inPtr xs **
       globalConst pConstAddr bn254PBytes) := by
  unfold globalConst
  set CR := CodeReq.ofProg ltPBase bnfLtP_prog with hCR
  -- peel the la destination x5 and the MV destination x7
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (((.x10 : Reg) ↦ᵣ inPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** regOwn .x28 ** regOwn .x29 **
        bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes) **
        regOwn .x7)
      (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
      (P := (((.x10 : Reg) ↦ᵣ inPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** regOwn .x28 ** regOwn .x29 **
        bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes) **
        ((.x5 : Reg) ↦ᵣ v5))
      (fun v7 => ?_))
  -- ---- init: la x5, bnf_p_be ; li x6, 32 ; mv x7, a0 ----
  have hla := la_materialize_within .x5 v5 ltPBase pConstAddr
    (cr := CR) (by decide) (by decide)
    (by rw [hCR]; code_mem) (by rw [hCR]; code_mem)
  have hli6 := liftCode (cr' := CR)
    (li_spec_gen_own_within .x6 (32 : Word) (ltPBase + 8) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (ltPBase + 8 : Word) + 4 = (ltPBase + 12 : Word) from by decide]
    at hli6
  have hmv7 := liftCode (cr' := CR)
    (mv_spec_gen_within .x7 .x10 inPtr v7 (ltPBase + 12) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (ltPBase + 12 : Word) + 4 = (ltPBase + 16 : Word) from by decide]
    at hmv7
  -- ---- the three-outcome two-tail loop ----
  have hloop := twoBreakRetLoop_spec (hdr := (ltPBase + 16 : Word)) (ret := ret)
    (cr := CR) (Q := ltPost inPtr ret xs) 32 9 5
    (ltInv inPtr ret xs)
    (fun i hi => ltIter_spec inPtr ret xs hlenX
      halignIn hovIn hvalidIn halignRet i hi)
    (ltExh_spec inPtr ret xs hlenX halignRet)
  -- ---- frames + chain ----
  have hlaF := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ v7) **
      ((.x10 : Reg) ↦ᵣ inPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x6 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
    (by pcf) hla
  have hli6F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ pConstAddr) ** ((.x7 : Reg) ↦ᵣ v7) **
      ((.x10 : Reg) ↦ᵣ inPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
    (by pcf) hli6
  have hmv7F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ pConstAddr) ** ((.x6 : Reg) ↦ᵣ (32 : Word)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x28 ** regOwn .x29 **
      bytesRegion inPtr xs ** bytesRegion pConstAddr bn254PBytes)
    (by pcf) hmv7
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlaF hli6F
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc1 hmv7F
  have hc3 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold ltInv
      refine (sepConj_pure_left h).2
        ⟨fun j hj => absurd hj (Nat.not_lt_zero j), ?_⟩
      rw [show (BitVec.ofNat 64 (32 - 0) : Word) = (32 : Word) from by decide,
          show inPtr + BitVec.ofNat 64 0 = inPtr from by
            rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
            bv_omega,
          show pConstAddr + BitVec.ofNat 64 0 = pConstAddr from by decide]
      xperm_hyp hp) hc2 hloop
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by unfold ltPost at hq; exact hq)
    (cpsTripleWithin_mono_nSteps (by omega) hc3)

#print axioms bnfLtP_spec

end Bn254FieldLtPSAsm

end EvmAsm.Codegen
