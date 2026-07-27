/-
  EvmAsm.Rv64.SAsm.DualReadByteScan

  The **dynamic-length byte dual-read equality scan** (bead evm-asm-v1ad3).

  `DualReadScan` (#10038) covers FIXED dword `LD` scans; comparison
  routines like `blsg2_eq_n` byte-walk two buffers with a DYNAMIC count
  (`a2 = length`), joining both loop exits at a counter-derived verdict:

  ```
  hdr:  beq  ctr, x0, .join        -- exhausted (all n bytes matched)
        lbu  tA, 0(pA)
        lbu  tB, 0(pB)
        bne  tA, tB, .join         -- first mismatch (ctr ≠ 0 here)
        addi pA, pA, 1 ; addi pB, pB, 1 ; addi ctr, ctr, -1 ; j hdr
  join: li   a0, 1
        beq  ctr, x0, .done        -- ctr = 0  ⟺  all n bytes matched
        li   a0, 0
  done: ret
  ```

  This module proves the scan ONCE, register- and length-agnostic, at
  `cpsTripleWithin` level (additive; no `Ast`/`Vc` changes):

  * `byteScanProg` — the 12-instruction generator (five generic scan
    registers; result in `a0`, return via `ra`), `rfl`-tied by consumers
    to the emitted bytes;

  * `bytes_eq_of_prefix_eq` — **the per-byte → byte-list bridge**: two
    `n`-byte lists agreeing at every position `< n` are EQUAL, which is
    what turns the loop's positional facts into the genuine post
    (the byte-level analogue of #10038's `bytes_eq_of_dwordSlots_eq`);

  * `scan_spec` — the whole scan: from the header with `ctr = n`, cursors
    at the two buffer bases, to `ret` with the GENUINE post
    `a0 = (if bsA = bsB then 1 else 0)`, both input regions untouched.
    The loop is one `twoBreakRetLoop_spec` (#10067) whose iterations route
    the `BNE` mismatch break and the `BEQ` exhaustion exit through the
    shared counter-verdict join (`joinNe_spec` / `joinEq_spec`).

  Also provides `CodeReq.ofProg_mem_at` — symbolic-base code membership
  (the `k`-th instruction of a program based at a SYMBOLIC address is in
  its `ofProg`), which `code_mem` cannot decide.

  Consumer: `blsg2_eq_n` (`Codegen/Programs/Bls12G2EqNSAsm.lean`) — the
  emitted `blsg2EqN_prog` IS `[mv;mv;mv] ++ byteScanProg x5 x28 x29 x6 x7`
  (kernel-checked), giving the byte-transparent `blsg2EqN_spec` with the
  real byte-equality post (superseding the `firstDiff`-shaped `Fn` post).
-/

import EvmAsm.Rv64.SAsm.TwoBreakWritable
import EvmAsm.Rv64.SAsm.RetForwardJoin

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

-- ============================================================================
-- §1  Symbolic-base code membership
-- ============================================================================

/-- The `k`-th instruction of `prog` based at a SYMBOLIC address is in its
    `ofProg` (per-instruction `CodeReq.singleton` subsumption; `code_mem`
    needs concrete bases and cannot close this). -/
theorem _root_.EvmAsm.Rv64.CodeReq.ofProg_mem_at (base A : Word)
    (prog : List Instr) (k : Nat) (ins : Instr)
    (hA : A = base + BitVec.ofNat 64 (4 * k))
    (hk : k < prog.length) (hins : prog[k]'hk = ins)
    (hbound : 4 * prog.length < 2 ^ 64) :
    ∀ a i, CodeReq.singleton A ins a = some i →
      CodeReq.ofProg base prog a = some i := by
  intro a i h
  rw [hA] at h
  refine CodeReq.ofProg_mono_sub base _ prog [ins] k rfl ?_ ?_ hbound a i ?_
  · rw [List.drop_eq_getElem_cons hk, hins]
    rfl
  · show k + 1 ≤ prog.length
    omega
  · rwa [CodeReq.ofProg_singleton]

-- ============================================================================
-- §2  The per-byte → byte-list equality bridge
-- ============================================================================

namespace DualReadByteScan

/-- **The bridge**: two `n`-byte lists agreeing at every position `< n`
    are equal — what turns per-position loop facts into genuine byte-list
    equality (byte-level analogue of `bytes_eq_of_dwordSlots_eq`). -/
theorem bytes_eq_of_prefix_eq (bsA bsB : List (BitVec 8)) (n : Nat)
    (hlenA : bsA.length = n) (hlenB : bsB.length = n)
    (hpref : ∀ j, j < n → bsA.getD j 0 = bsB.getD j 0) :
    bsA = bsB := by
  apply List.ext_getElem (by omega)
  intro j hj1 hj2
  have := hpref j (by omega)
  simpa [List.getD, List.getElem?_eq_getElem hj1,
    List.getElem?_eq_getElem hj2] using this

/-- Equal lists agree at every position (the trivial converse, used to
    refute equality at a mismatch). -/
theorem prefix_eq_of_bytes_eq {bsA bsB : List (BitVec 8)}
    (h : bsA = bsB) (j : Nat) : bsA.getD j 0 = bsB.getD j 0 := by
  rw [h]

-- ============================================================================
-- §3  The scan program generator
-- ============================================================================

/-- The 12-instruction dynamic-length byte dual-read equality scan.
    `ctr` counts down from `n`; `pA`/`pB` are advancing byte cursors;
    `tA`/`tB` the per-iteration loaded bytes; result in `a0`; return via
    `ra`.  Consumers `rfl`-tie this generator to their emitted bytes. -/
def byteScanProg (ctr tA tB pA pB : Reg) : List Instr :=
  [ .BEQ ctr .x0 (32 : BitVec 13),      -- +0   exhausted → join
    .LBU tA pA (0 : BitVec 12),         -- +4
    .LBU tB pB (0 : BitVec 12),         -- +8
    .BNE tA tB (20 : BitVec 13),        -- +12  mismatch → join
    .ADDI pA pA (1 : BitVec 12),        -- +16
    .ADDI pB pB (1 : BitVec 12),        -- +20
    .ADDI ctr ctr (-1 : BitVec 12),     -- +24
    .JAL .x0 (-28 : BitVec 21),         -- +28  → +0
    .LI .x10 (1 : Word),                -- +32  join
    .BEQ ctr .x0 (8 : BitVec 13),       -- +36  ctr = 0 → keep 1
    .LI .x10 (0 : Word),                -- +40
    .JALR .x0 .x1 (0 : BitVec 12) ]     -- +44  ret

private theorem scanProg_length (ctr tA tB pA pB : Reg) :
    (byteScanProg ctr tA tB pA pB).length = 12 := rfl

/-- Instruction-`k` membership in the scan program at a symbolic base
    (all side conditions discharged against the fixed 12-instruction
    generator). -/
private theorem mem_scanProg (ctr tA tB pA pB : Reg) (base A : Word)
    (k : Nat) (ins : Instr)
    (hA : A = base + BitVec.ofNat 64 (4 * k)) (hk : k < 12)
    (hins : ∀ h : k < (byteScanProg ctr tA tB pA pB).length,
      (byteScanProg ctr tA tB pA pB)[k]'h = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i →
      CodeReq.ofProg base (byteScanProg ctr tA tB pA pB) a = some i := by
  have hk' : k < (byteScanProg ctr tA tB pA pB).length := by
    rw [scanProg_length]; exact hk
  exact CodeReq.ofProg_mem_at base A _ k ins hA hk' (hins hk')
    (by rw [scanProg_length]; decide)

-- ============================================================================
-- §4  Word-arithmetic helpers (dynamic countdown / advancing cursors)
-- ============================================================================

private theorem ctr_dec (n i : Nat) (hi : i < n) (_hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (n - i) + signExtend12 (-1 : BitVec 12)
      = BitVec.ofNat 64 (n - (i + 1)) := by
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

private theorem ctr_ne_zero (n i : Nat) (hi : i < n) (hn : n < 2 ^ 64) :
    ¬ (BitVec.ofNat 64 (n - i) = (0 : Word)) := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, show ((0 : Word)).toNat = 0 from rfl] at this
  omega

-- ============================================================================
-- §5  Invariant, genuine post, and the counter-verdict join tails
-- ============================================================================

section Scan

variable (ctr tA tB pA pB : Reg) (base ret ptrA ptrB : Word)
variable (bsA bsB : List (BitVec 8)) (n : Nat)

/-- Loop invariant at the header after `i` matched bytes: counter `n - i`,
    cursors at byte `i`, the first `i` bytes agree (pure conjunct), result
    register still owned, both input regions untouched. -/
private def scanInv (i : Nat) : Assertion :=
  ⌜∀ j, j < i → bsA.getD j 0 = bsB.getD j 0⌝ **
  (ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
  (pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
  (pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
  ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
  regOwn tA ** regOwn tB **
  bytesRegion ptrA bsA ** bytesRegion ptrB bsB

/-- The genuine post: `a0` holds the byte-list equality verdict, both
    input regions untouched, the scan scratch registers merely owned. -/
private def scanPost : Assertion :=
  ((.x10 : Reg) ↦ᵣ (if bsA = bsB then (1 : Word) else (0 : Word))) **
  ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn ctr ** regOwn pA ** regOwn pB ** regOwn tA ** regOwn tB **
  bytesRegion ptrA bsA ** bytesRegion ptrB bsB

/-- The join entered with `ctr = 0` (exhaustion: all `n` bytes matched):
    `li a0, 1 ; beq ctr, x0, +8 (taken) ; ret` — verdict `1`. -/
private theorem joinEq_spec
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 3 (base + 32) ret
      (CodeReq.ofProg base (byteScanProg ctr tA tB pA pB))
      ((ctr ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 ** ((.x1 : Reg) ↦ᵣ ret))
      ((ctr ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (((.x10 : Reg)) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)) := by
  set CR := CodeReq.ofProg base (byteScanProg ctr tA tB pA pB) with hCR
  have hli := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mem_scanProg ctr tA tB pA pB base (base + 32) 8 _ rfl
        (by omega) (fun _ => rfl))
    (h := li_spec_gen_own_within .x10 (1 : Word) (base + 32) (by decide))
  rw [BitVec.add_assoc, show ((32 : Word) + 4) = (36 : Word) from by decide]
    at hli
  have hbr := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mem_scanProg ctr tA tB pA pB base (base + 36) 9 _ rfl
        (by omega) (fun _ => rfl))
    (h := beq_spec_gen_within ctr .x0 (8 : BitVec 13) (0 : Word) (0 : Word)
      (base + 36))
  rw [show (base + 36) + signExtend13 (8 : BitVec 13) = base + 44 from by
        rw [BitVec.add_assoc,
          show ((36 : Word) + signExtend13 (8 : BitVec 13)) = (44 : Word)
            from by decide],
      show (base + 36) + 4 = base + 40 from by
        rw [BitVec.add_assoc,
          show ((36 : Word) + (4 : Word)) = (40 : Word) from by decide]]
    at hbr
  have hret := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mem_scanProg ctr tA tB pA pB base (base + 44) 11 _ rfl
        (by omega) (fun _ => rfl))
    (h := EvmAsm.Evm64.ret_spec_within' (base + 44) ret)
  rw [halignRet] at hret
  -- frames
  have hliF := cpsTripleWithin_frameR
    ((ctr ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hli
  have hbrF := cpsBranchWithin_frameR
    ((((.x10 : Reg)) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hbr
  have hretF := cpsTripleWithin_frameR
    ((ctr ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (((.x10 : Reg)) ↦ᵣ (1 : Word)))
    (by pcf) hret
  have htakenT : cpsTripleWithin 1 (base + 44) ret CR
      ((ctr ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (((.x10 : Reg)) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
      ((ctr ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (((.x10 : Reg)) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hretF
  -- the branch station: cond (0 = 0) is true; fall-through is absurd
  have hstation := retJoinStation_spec (cond := ((0 : Word) = (0 : Word)))
    (PT := (ctr ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (((.x10 : Reg)) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
    (PF := (ctr ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (((.x10 : Reg)) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
    hbrF
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by xperm_hyp hq)
    (fun _ => htakenT)
    (fun hc => absurd rfl hc)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      hliF hstation)

/-- The join entered with `ctr = w ≠ 0` (mismatch break):
    `li a0, 1 ; beq ctr, x0, +8 (NOT taken) ; li a0, 0 ; ret` —
    verdict `0`. -/
private theorem joinNe_spec (w : Word) (hw : w ≠ (0 : Word))
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 4 (base + 32) ret
      (CodeReq.ofProg base (byteScanProg ctr tA tB pA pB))
      ((ctr ↦ᵣ w) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 ** ((.x1 : Reg) ↦ᵣ ret))
      ((ctr ↦ᵣ w) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (((.x10 : Reg)) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)) := by
  set CR := CodeReq.ofProg base (byteScanProg ctr tA tB pA pB) with hCR
  have hli := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mem_scanProg ctr tA tB pA pB base (base + 32) 8 _ rfl
        (by omega) (fun _ => rfl))
    (h := li_spec_gen_own_within .x10 (1 : Word) (base + 32) (by decide))
  rw [BitVec.add_assoc, show ((32 : Word) + 4) = (36 : Word) from by decide]
    at hli
  have hbr := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mem_scanProg ctr tA tB pA pB base (base + 36) 9 _ rfl
        (by omega) (fun _ => rfl))
    (h := beq_spec_gen_within ctr .x0 (8 : BitVec 13) w (0 : Word)
      (base + 36))
  rw [show (base + 36) + signExtend13 (8 : BitVec 13) = base + 44 from by
        rw [BitVec.add_assoc,
          show ((36 : Word) + signExtend13 (8 : BitVec 13)) = (44 : Word)
            from by decide],
      show (base + 36) + 4 = base + 40 from by
        rw [BitVec.add_assoc,
          show ((36 : Word) + (4 : Word)) = (40 : Word) from by decide]]
    at hbr
  have hli0 := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mem_scanProg ctr tA tB pA pB base (base + 40) 10 _ rfl
        (by omega) (fun _ => rfl))
    (h := li_spec_gen_within .x10 (1 : Word) (0 : Word) (base + 40)
      (by decide))
  rw [show (base + 40) + 4 = base + 44 from by
    rw [BitVec.add_assoc,
      show ((40 : Word) + (4 : Word)) = (44 : Word) from by decide]] at hli0
  have hret := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mem_scanProg ctr tA tB pA pB base (base + 44) 11 _ rfl
        (by omega) (fun _ => rfl))
    (h := EvmAsm.Evm64.ret_spec_within' (base + 44) ret)
  rw [halignRet] at hret
  -- frames
  have hliF := cpsTripleWithin_frameR
    ((ctr ↦ᵣ w) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hli
  have hbrF := cpsBranchWithin_frameR
    ((((.x10 : Reg)) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hbr
  have hli0F := cpsTripleWithin_frameR
    ((ctr ↦ᵣ w) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hli0
  have hretF := cpsTripleWithin_frameR
    ((ctr ↦ᵣ w) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (((.x10 : Reg)) ↦ᵣ (0 : Word)))
    (by pcf) hret
  -- fall arm: li a0, 0 ; ret
  have hfall : cpsTripleWithin 2 (base + 40) ret CR
      ((ctr ↦ᵣ w) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (((.x10 : Reg)) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
      ((ctr ↦ᵣ w) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (((.x10 : Reg)) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hli0F hretF)
  -- the branch station: cond (w = 0) is refuted by `hw`
  have hstation := retJoinStation_spec (cond := (w = (0 : Word)))
    (PT := (ctr ↦ᵣ w) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (((.x10 : Reg)) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
    (PF := (ctr ↦ᵣ w) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (((.x10 : Reg)) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
    hbrF
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by xperm_hyp hq)
    (fun hc => absurd hc hw)
    (fun _ => hfall)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      hliF hstation)

-- ============================================================================
-- §6  One loop iteration (mismatch break station + continue)
-- ============================================================================

private theorem scanIter_spec
    (hctr : ctr ≠ .x0) (htA : tA ≠ .x0) (htB : tB ≠ .x0)
    (hpA : pA ≠ .x0) (hpB : pB ≠ .x0)
    (hlenA : bsA.length = n) (hlenB : bsB.length = n)
    (halignA : ptrA.toNat % 8 = 0) (halignB : ptrB.toNat % 8 = 0)
    (hovA : ptrA.toNat + n < 2 ^ 64) (hovB : ptrB.toNat + n < 2 ^ 64)
    (hvalidA : ∀ k, k < n → isValidByteAccess (ptrA + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < n → isValidByteAccess (ptrB + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (i : Nat) (hi : i < n) :
    cpsBranchWithin 8 base
      (CodeReq.ofProg base (byteScanProg ctr tA tB pA pB))
      (scanInv ctr tA tB pA pB ret ptrA ptrB bsA bsB n i)
      ret (scanPost ctr tA tB pA pB ret ptrA ptrB bsA bsB)
      base (scanInv ctr tA tB pA pB ret ptrA ptrB bsA bsB n (i + 1)) := by
  set CR := CodeReq.ofProg base (byteScanProg ctr tA tB pA pB) with hCR
  have hn : n < 2 ^ 64 := by omega
  have hia : i < bsA.length := by omega
  have hib : i < bsB.length := by omega
  set aByte := (bsA[i]'hia).zeroExtend 64 with haByte
  set bByte := (bsB[i]'hib).zeroExtend 64 with hbByte
  have haBN : aByte.toNat = (bsA[i]'hia).toNat := by
    rw [haByte]
    show (BitVec.setWidth 64 _).toNat = _
    rw [BitVec.toNat_setWidth]
    have := (bsA[i]'hia).isLt
    omega
  have hbBN : bByte.toNat = (bsB[i]'hib).toNat := by
    rw [hbByte]
    show (BitVec.setWidth 64 _).toNat = _
    rw [BitVec.toNat_setWidth]
    have := (bsB[i]'hib).isLt
    omega
  have hgdA : bsA.getD i 0 = bsA[i]'hia := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia]
    rfl
  have hgdB : bsB.getD i 0 = bsB[i]'hib := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hib]
    rfl
  -- strip the pure prefix fact
  unfold scanInv
  refine cpsBranchWithin_pure_pre (fun hpref => ?_)
  -- peel this iteration's scratch registers tA, tB
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := tA)
      (P := ((ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
        (pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
        (pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB) **
        regOwn tB)
      (fun vA => ?_))
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := tB)
      (P := ((ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
        (pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
        (pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB) **
        (tA ↦ᵣ vA))
      (fun vB => ?_))
  -- canonical working set, tA/tB concrete
  suffices hmain :
      cpsBranchWithin 8 base CR
        ((ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
         (pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
         (pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         regOwn .x10 ** (tA ↦ᵣ vA) ** (tB ↦ᵣ vB) **
         bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
        ret (scanPost ctr tA tB pA pB ret ptrA ptrB bsA bsB)
        base (scanInv ctr tA tB pA pB ret ptrA ptrB bsA bsB n (i + 1)) by
    exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hmain
  -- ---- the two LBU loads (base+4, base+8) ----
  have hlbuA := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mem_scanProg ctr tA tB pA pB base (base + 4) 1 _ rfl
        (by omega) (fun _ => rfl))
    (h := bytesRegion_lbu_within tA pA ptrA vA (base + 4) bsA i
      htA halignA hia (by omega) (hvalidA i hi))
  rw [show (base + 4) + 4 = base + 8 from by
    rw [BitVec.add_assoc,
      show ((4 : Word) + (4 : Word)) = (8 : Word) from by decide]] at hlbuA
  have hlbuB := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mem_scanProg ctr tA tB pA pB base (base + 8) 2 _ rfl
        (by omega) (fun _ => rfl))
    (h := bytesRegion_lbu_within tB pB ptrB vB (base + 8) bsB i
      htB halignB hib (by omega) (hvalidB i hi))
  rw [show (base + 8) + 4 = base + 12 from by
    rw [BitVec.add_assoc,
      show ((8 : Word) + (4 : Word)) = (12 : Word) from by decide]] at hlbuB
  have hlbuAF := cpsTripleWithin_frameR
    ((ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
      (pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x10 ** (tB ↦ᵣ vB) **
      bytesRegion ptrB bsB)
    (by pcf) hlbuA
  have hlbuBF := cpsTripleWithin_frameR
    ((ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
      (pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x10 ** (tA ↦ᵣ aByte) **
      bytesRegion ptrA bsA)
    (by pcf) hlbuB
  have hpre1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlbuAF hlbuBF
  -- ---- the header BEQ (base; never taken at i < n) ----
  have hbrHdr := cpsBranchWithin_frameR
    ((pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
      (pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x10 **
      (tA ↦ᵣ vA) ** (tB ↦ᵣ vB) **
      bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mem_scanProg ctr tA tB pA pB base base 0 _ (by
          rw [show (4 : Nat) * 0 = 0 from rfl]
          rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
          bv_omega) (by omega) (fun _ => rfl))
      (h := beq_spec_gen_within ctr .x0 (32 : BitVec 13)
        (BitVec.ofNat 64 (n - i)) (0 : Word) base))
  rw [show base + signExtend13 (32 : BitVec 13) = base + 32 from by
        rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]]
    at hbrHdr
  -- ---- the mismatch BNE (base+12) ----
  have hbrNe := cpsBranchWithin_frameR
    ((ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
      (pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
      (pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x10 **
      bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mem_scanProg ctr tA tB pA pB base (base + 12) 3 _ rfl
          (by omega) (fun _ => rfl))
      (h := bne_spec_gen_within tA tB (20 : BitVec 13) aByte bByte
        (base + 12)))
  rw [show (base + 12) + signExtend13 (20 : BitVec 13) = base + 32 from by
        rw [BitVec.add_assoc,
          show ((12 : Word) + signExtend13 (20 : BitVec 13)) = (32 : Word)
            from by decide],
      show (base + 12) + 4 = base + 16 from by
        rw [BitVec.add_assoc,
          show ((12 : Word) + (4 : Word)) = (16 : Word) from by decide]]
    at hbrNe
  -- the canonical post-load working set
  set WSL : Assertion :=
    (tA ↦ᵣ aByte) ** (tB ↦ᵣ bByte) **
    (ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
    (pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
    (pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
    ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
    bytesRegion ptrA bsA ** bytesRegion ptrB bsB with hWSL
  -- ---- break arm: mismatch at byte i → join writes verdict 0 ----
  have htailNe : aByte ≠ bByte →
      cpsTripleWithin 4 (base + 32) ret CR WSL
        (scanPost ctr tA tB pA pB ret ptrA ptrB bsA bsB) := by
    intro hc
    have hneByte : bsA.getD i 0 ≠ bsB.getD i 0 := by
      rw [hgdA, hgdB]
      intro heq
      exact hc (by rw [haByte, hbByte, heq])
    have hNe : bsA ≠ bsB := fun hEq =>
      hneByte (prefix_eq_of_bytes_eq hEq i)
    have h := cpsTripleWithin_frameR
      ((tA ↦ᵣ aByte) ** (tB ↦ᵣ bByte) **
        (pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
        (pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
      (by pcf)
      (joinNe_spec ctr tA tB pA pB base ret (BitVec.ofNat 64 (n - i))
        (ctr_ne_zero n i hi hn) halignRet)
    refine cpsTripleWithin_weaken
      (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
      (fun h hq => ?_) h
    unfold scanPost
    rw [if_neg hNe]
    have hq1 : ((ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
        ((pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
          ((pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
            ((tA ↦ᵣ aByte) ** ((tB ↦ᵣ bByte) **
              ((((.x10 : Reg)) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
               ((.x0 : Reg) ↦ᵣ (0 : Word)) **
               bytesRegion ptrA bsA ** bytesRegion ptrB bsB)))))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn ctr _)
      (sepConj_mono (regIs_to_regOwn pA _)
        (sepConj_mono (regIs_to_regOwn pB _)
          (sepConj_mono (regIs_to_regOwn tA _)
            (sepConj_mono (regIs_to_regOwn tB _)
              (fun _ hh => hh))))) h hq1
    xperm_hyp hq2
  -- ---- continue segment: 3 × addi ; jal → header with inv (i+1) ----
  have hcont : aByte = bByte →
      cpsTripleWithin 4 (base + 16) base CR WSL
        (scanInv ctr tA tB pA pB ret ptrA ptrB bsA bsB n (i + 1)) := by
    intro hEqB
    have hEqByte : bsA[i]'hia = bsB[i]'hib := by
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hEqB
      omega
    have hpref' : ∀ j, j < i + 1 → bsA.getD j 0 = bsB.getD j 0 := by
      intro j hj
      by_cases hji : j < i
      · exact hpref j hji
      · have : j = i := by omega
        subst this
        rw [hgdA, hgdB, hEqByte]
    have haddiA := cpsTripleWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mem_scanProg ctr tA tB pA pB base (base + 16) 4 _ rfl
          (by omega) (fun _ => rfl))
      (h := addi_spec_gen_same_within pA (ptrA + BitVec.ofNat 64 i)
        (1 : BitVec 12) (base + 16) hpA)
    rw [cursor_advance ptrA i,
        show (base + 16) + 4 = base + 20 from by
          rw [BitVec.add_assoc,
            show ((16 : Word) + (4 : Word)) = (20 : Word) from by decide]]
      at haddiA
    have haddiB := cpsTripleWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mem_scanProg ctr tA tB pA pB base (base + 20) 5 _ rfl
          (by omega) (fun _ => rfl))
      (h := addi_spec_gen_same_within pB (ptrB + BitVec.ofNat 64 i)
        (1 : BitVec 12) (base + 20) hpB)
    rw [cursor_advance ptrB i,
        show (base + 20) + 4 = base + 24 from by
          rw [BitVec.add_assoc,
            show ((20 : Word) + (4 : Word)) = (24 : Word) from by decide]]
      at haddiB
    have haddiC := cpsTripleWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mem_scanProg ctr tA tB pA pB base (base + 24) 6 _ rfl
          (by omega) (fun _ => rfl))
      (h := addi_spec_gen_same_within ctr (BitVec.ofNat 64 (n - i))
        (-1 : BitVec 12) (base + 24) hctr)
    rw [ctr_dec n i hi hn,
        show (base + 24) + 4 = base + 28 from by
          rw [BitVec.add_assoc,
            show ((24 : Word) + (4 : Word)) = (28 : Word) from by decide]]
      at haddiC
    have hjal := cpsTripleWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mem_scanProg ctr tA tB pA pB base (base + 28) 7 _ rfl
          (by omega) (fun _ => rfl))
      (h := jal_x0_spec_gen_within (-28 : BitVec 21) (base + 28))
    rw [show (base + 28) + signExtend21 (-28 : BitVec 21) = base from by
      rw [BitVec.add_assoc,
        show ((28 : Word) + signExtend21 (-28 : BitVec 21)) = (0 : Word)
          from by decide]
      bv_omega] at hjal
    have haddiAF := cpsTripleWithin_frameR
      ((pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        (ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
        (tA ↦ᵣ aByte) ** (tB ↦ᵣ bByte) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
      (by pcf) haddiA
    have haddiBF := cpsTripleWithin_frameR
      ((pA ↦ᵣ (ptrA + BitVec.ofNat 64 (i + 1))) **
        (ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
        (tA ↦ᵣ aByte) ** (tB ↦ᵣ bByte) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
      (by pcf) haddiB
    have haddiCF := cpsTripleWithin_frameR
      ((pA ↦ᵣ (ptrA + BitVec.ofNat 64 (i + 1))) **
        (pB ↦ᵣ (ptrB + BitVec.ofNat 64 (i + 1))) **
        (tA ↦ᵣ aByte) ** (tB ↦ᵣ bByte) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
      (by pcf) haddiC
    have hjalF := cpsTripleWithin_frameR
      ((ctr ↦ᵣ BitVec.ofNat 64 (n - (i + 1))) **
        (pA ↦ᵣ (ptrA + BitVec.ofNat 64 (i + 1))) **
        (pB ↦ᵣ (ptrB + BitVec.ofNat 64 (i + 1))) **
        (tA ↦ᵣ aByte) ** (tB ↦ᵣ bByte) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
      (by pcf) hjal
    have hc1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) haddiAF haddiBF
    have hc2 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hc1 haddiCF
    have hc3 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        rw [sepConj_emp_left']
        xperm_hyp hp) hc2 hjalF
    refine cpsTripleWithin_weaken
      (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
      (fun h hq => ?_) hc3
    rw [sepConj_emp_left'] at hq
    unfold scanInv
    refine (sepConj_pure_left h).2 ⟨hpref', ?_⟩
    have hq1 : ((tA ↦ᵣ aByte) ** ((tB ↦ᵣ bByte) **
        ((ctr ↦ᵣ BitVec.ofNat 64 (n - (i + 1))) **
         (pA ↦ᵣ (ptrA + BitVec.ofNat 64 (i + 1))) **
         (pB ↦ᵣ (ptrB + BitVec.ofNat 64 (i + 1))) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         regOwn .x10 **
         bytesRegion ptrA bsA ** bytesRegion ptrB bsB))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn tA _)
      (sepConj_mono (regIs_to_regOwn tB _)
        (fun _ hh => hh)) h hq1
    xperm_hyp hq2
  -- ---- the mismatch BNE station ----
  have hstNe : cpsBranchWithin (1 + 4) (base + 12) CR WSL
      ret (scanPost ctr tA tB pA pB ret ptrA ptrB bsA bsB)
      base (scanInv ctr tA tB pA pB ret ptrA ptrB bsA bsB n (i + 1)) :=
    breakStation_spec (cond := (aByte ≠ bByte))
      (PT := WSL) (PF := WSL)
      (cpsBranchWithin_weaken
        (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
        (fun _ hq => hq) (fun _ hq => hq) hbrNe)
      (fun h hq => by rw [hWSL]; xperm_hyp hq)
      (fun h hq => by
        rw [hWSL]
        have hq1 : (⌜aByte = bByte⌝ **
            ((tA ↦ᵣ aByte) ** (tB ↦ᵣ bByte) **
             (ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
             (pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
             (pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
             ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
             regOwn .x10 **
             bytesRegion ptrA bsA ** bytesRegion ptrB bsB)) h := by
          xperm_hyp hq
        obtain ⟨heq, hrest⟩ := (sepConj_pure_left h).1 hq1
        exact (sepConj_pure_left h).2 ⟨fun hne => hne heq, hrest⟩)
      (fun hc => htailNe hc)
      (fun hnc => cpsTripleWithin_as_cpsBranchWithin_right ret
        (scanPost ctr tA tB pA pB ret ptrA ptrB bsA bsB)
        (hcont (not_ne_iff.mp hnc)))
  -- ---- loads ; BNE station ----
  have hfallIter := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by rw [hWSL]; xperm_hyp hp) hpre1 hstNe
  -- ---- the header BEQ station wraps it all ----
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (breakStation_spec (cond := (BitVec.ofNat 64 (n - i) = (0 : Word)))
      (PT := (ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
        (pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
        (pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 ** (tA ↦ᵣ vA) ** (tB ↦ᵣ vB) **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
      (PF := (((pA ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
        (tA ↦ᵣ vA) ** bytesRegion ptrA bsA) **
        ((ctr ↦ᵣ BitVec.ofNat 64 (n - i)) **
        (pB ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 ** (tB ↦ᵣ vB) **
        bytesRegion ptrB bsB)))
      hbrHdr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun hc => absurd hc (ctr_ne_zero n i hi hn))
      (fun _ => hfallIter))

-- ============================================================================
-- §7  Loop exhaustion: all n bytes matched → join writes verdict 1
-- ============================================================================

private theorem scanExh_spec
    (hlenA : bsA.length = n) (hlenB : bsB.length = n)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 4 base ret
      (CodeReq.ofProg base (byteScanProg ctr tA tB pA pB))
      (scanInv ctr tA tB pA pB ret ptrA ptrB bsA bsB n n)
      (scanPost ctr tA tB pA pB ret ptrA ptrB bsA bsB) := by
  set CR := CodeReq.ofProg base (byteScanProg ctr tA tB pA pB) with hCR
  unfold scanInv
  refine cpsTripleWithin_pure_pre (fun hpref => ?_)
  have hEq : bsA = bsB := bytes_eq_of_prefix_eq bsA bsB n hlenA hlenB
    (fun j hj => hpref j hj)
  have hc0 : BitVec.ofNat 64 (n - n) = (0 : Word) := by
    rw [Nat.sub_self]
    rfl
  -- header BEQ, taken (counter = 0)
  have hbrHdr := cpsBranchWithin_frameR
    ((pA ↦ᵣ (ptrA + BitVec.ofNat 64 n)) **
      (pB ↦ᵣ (ptrB + BitVec.ofNat 64 n)) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x10 **
      regOwn tA ** regOwn tB **
      bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mem_scanProg ctr tA tB pA pB base base 0 _ (by
          rw [show (4 : Nat) * 0 = 0 from rfl]
          rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
          bv_omega) (by omega) (fun _ => rfl))
      (h := beq_spec_gen_within ctr .x0 (32 : BitVec 13)
        (BitVec.ofNat 64 (n - n)) (0 : Word) base))
  rw [show base + signExtend13 (32 : BitVec 13) = base + 32 from by
        rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]]
    at hbrHdr
  -- taken arm: the counter-verdict join with ctr = 0
  have htail : cpsTripleWithin 3 (base + 32) ret CR
      ((ctr ↦ᵣ BitVec.ofNat 64 (n - n)) **
       (pA ↦ᵣ (ptrA + BitVec.ofNat 64 n)) **
       (pB ↦ᵣ (ptrB + BitVec.ofNat 64 n)) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x10 ** regOwn tA ** regOwn tB **
       bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
      (scanPost ctr tA tB pA pB ret ptrA ptrB bsA bsB) := by
    have h := cpsTripleWithin_frameR
      ((pA ↦ᵣ (ptrA + BitVec.ofNat 64 n)) **
        (pB ↦ᵣ (ptrB + BitVec.ofNat 64 n)) **
        regOwn tA ** regOwn tB **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
      (by pcf)
      (joinEq_spec ctr tA tB pA pB base ret halignRet)
    refine cpsTripleWithin_weaken
      (fun h hp => by rw [hc0] at hp; xperm_hyp hp)
      (fun h hq => ?_) h
    unfold scanPost
    rw [if_pos hEq]
    have hq1 : ((ctr ↦ᵣ (0 : Word)) **
        ((pA ↦ᵣ (ptrA + BitVec.ofNat 64 n)) **
          ((pB ↦ᵣ (ptrB + BitVec.ofNat 64 n)) **
            ((((.x10 : Reg)) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
             ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn tA ** regOwn tB **
             bytesRegion ptrA bsA ** bytesRegion ptrB bsB)))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn ctr _)
      (sepConj_mono (regIs_to_regOwn pA _)
        (sepConj_mono (regIs_to_regOwn pB _)
          (fun _ hh => hh))) h hq1
    xperm_hyp hq2
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (retJoinStation_spec
      (cond := (BitVec.ofNat 64 (n - n) = (0 : Word)))
      (PT := (ctr ↦ᵣ BitVec.ofNat 64 (n - n)) **
        (pA ↦ᵣ (ptrA + BitVec.ofNat 64 n)) **
        (pB ↦ᵣ (ptrB + BitVec.ofNat 64 n)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 ** regOwn tA ** regOwn tB **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
      (PF := (ctr ↦ᵣ BitVec.ofNat 64 (n - n)) **
        (pA ↦ᵣ (ptrA + BitVec.ofNat 64 n)) **
        (pB ↦ᵣ (ptrB + BitVec.ofNat 64 n)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 ** regOwn tA ** regOwn tB **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
      hbrHdr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun _ => htail)
      (fun hc => absurd hc0 hc))

-- ============================================================================
-- §8  The whole scan
-- ============================================================================

/-- **The dynamic-length byte dual-read equality scan, whole-routine.**
    Register-agnostic (five scan registers; result in `a0`, return via
    `ra`), length-agnostic (`n` from the counter register's entry value):
    from the header with `ctr = n` and cursors at the two buffer bases, to
    `ret` with the GENUINE post `a0 = (if bsA = bsB then 1 else 0)`, both
    `n`-byte input regions untouched. -/
theorem scan_spec
    (hctr : ctr ≠ .x0) (htA : tA ≠ .x0) (htB : tB ≠ .x0)
    (hpA : pA ≠ .x0) (hpB : pB ≠ .x0)
    (hlenA : bsA.length = n) (hlenB : bsB.length = n)
    (halignA : ptrA.toNat % 8 = 0) (halignB : ptrB.toNat % 8 = 0)
    (hovA : ptrA.toNat + n < 2 ^ 64) (hovB : ptrB.toNat + n < 2 ^ 64)
    (hvalidA : ∀ k, k < n → isValidByteAccess (ptrA + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < n → isValidByteAccess (ptrB + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (n * 8 + 4) base ret
      (CodeReq.ofProg base (byteScanProg ctr tA tB pA pB))
      ((ctr ↦ᵣ BitVec.ofNat 64 n) ** (pA ↦ᵣ ptrA) ** (pB ↦ᵣ ptrB) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x10 ** regOwn tA ** regOwn tB **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB)
      ((((.x10 : Reg)) ↦ᵣ (if bsA = bsB then (1 : Word) else (0 : Word))) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn ctr ** regOwn pA ** regOwn pB ** regOwn tA ** regOwn tB **
        bytesRegion ptrA bsA ** bytesRegion ptrB bsB) := by
  have hloop := twoBreakRetLoop_spec (hdr := base) (ret := ret)
    (cr := CodeReq.ofProg base (byteScanProg ctr tA tB pA pB))
    (Q := scanPost ctr tA tB pA pB ret ptrA ptrB bsA bsB) n 8 4
    (scanInv ctr tA tB pA pB ret ptrA ptrB bsA bsB n)
    (fun i hi => scanIter_spec ctr tA tB pA pB base ret ptrA ptrB bsA bsB n
      hctr htA htB hpA hpB hlenA hlenB halignA halignB hovA hovB
      hvalidA hvalidB halignRet i hi)
    (scanExh_spec ctr tA tB pA pB base ret ptrA ptrB bsA bsB n
      hlenA hlenB halignRet)
  refine cpsTripleWithin_weaken (fun h hp => ?_)
    (fun h hq => by unfold scanPost at hq; exact hq) hloop
  unfold scanInv
  refine (sepConj_pure_left h).2
    ⟨fun j hj => absurd hj (Nat.not_lt_zero j), ?_⟩
  rw [show (n : Nat) - 0 = n from rfl,
      show ptrA + BitVec.ofNat 64 0 = ptrA from by
        rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
        bv_omega,
      show ptrB + BitVec.ofNat 64 0 = ptrB from by
        rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
        bv_omega]
  xperm_hyp hp

end Scan


end DualReadByteScan

end EvmAsm.Rv64.SAsm
