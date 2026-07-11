/-
  EvmAsm.Codegen.Programs.RlpBytesEncodedSizeSAsm

  `rlp_bytes_encoded_size` — the RLP byte-string encoded size — the
  `rlp_list_encoded_size` shape (`RlpListEncodedSizeSAsm.lean`, #10082)
  prefixed by the single-byte prelude, all forward joins expressed with
  `retJoinStation_spec` (this resolves blocker bead
  evm-asm-4ch8f.15.5.1: the "return-if-with-fallthrough" it asked for
  IS a `retJoinStation` whose taken arm runs a `li`/`ret` tail and
  whose fall arm is the shared length-header continuation, proven once
  and consumed by BOTH the `len ≠ 1` branch and the `b0 ≥ 0x80`
  fall-through — no new `Stmt` node needed at `cpsTripleWithin` level).

      rlp_bytes_encoded_size:            -- a0 = ptr, a1 = len
        li   t0, 1
        bne  a1, t0, .hdr                -- len ≠ 1 → header path
        lbu  t1, 0(a0) ; li t2, 128
        bltu t1, t2, .one                -- single byte < 0x80 → size 1
      .hdr:
        li   t0, 56
        bgeu a1, t0, .long
        addi a0, a1, 1 ; ret             -- short form: 1-byte header
      .one:
        li   a0, 1 ; ret
      .long:
        mv   t0, a1 ; li t1, 0
      .len: beq t0, x0, .done            -- while (len >>> 8·i) ≠ 0
        srli t0, t0, 8 ; addi t1, t1, 1 ; j .len
      .done:
        add  a0, a1, t1 ; addi a0, a0, 1 ; ret

  **Genuine post** (`rlpBytesEncodedSize_spec`):
  `a0 = rbesSize xs len` — `1` when the string is a single byte below
  `0x80` (RLP encodes it as itself), else `len + 1` below 56, else
  `len + u64ByteLen len + 1`; the input region and `a1` untouched.
  The loop-exit index is tied to `u64ByteLen` by the #10082 shift
  bridges (`u64ByteLen_shift_zero` / `_ne`), reused as-is.

  Byte-transparent: stated at the `#guard`-tied symbolic
  `GuestAddrs.rlp_bytes_encoded_size` base (bead evm-asm-6agnq) over
  the emitted `rlpBytesEncodedSize_prog` — no guest-byte change, no
  A/B run needed.  Bead: evm-asm-4ch8f.15.5.
-/

import EvmAsm.Codegen.Programs.RlpListEncodedSizeSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace RlpBytesEncodedSizeSAsm

open RlpListEncodedSizeSAsm (u64ByteLen u64ByteLen_le u64ByteLen_shift_zero
  u64ByteLen_shift_ne)

/-- The routine base, symbolic (bead evm-asm-6agnq). -/
def rbesBase : Word := (GuestAddrs.rlp_bytes_encoded_size : Word)

-- Address anchor (fails the build if the guest link moves).
#guard GuestAddrs.rlp_bytes_encoded_size = 0x8000adcc
#guard rlpBytesEncodedSize_prog.length = 20
-- The routine is position-independent (no PC-relative instruction).

/-
  Layout relative to `GuestAddrs.rlp_bytes_encoded_size`:
    +0   li   x5, 1
    +4   bne  x11, x5, +16 → +20
    +8   lbu  x6, 0(x10)
    +12  li   x7, 128
    +16  bltu x6, x7, +20 → +36 (size-1 tail)
    +20  li   x5, 56
    +24  bgeu x11, x5, +20 → +44 (long)
    +28  addi x10, x11, 1
    +32  jalr (short ret)
    +36  li   x10, 1
    +40  jalr (size-1 ret)
    +44  mv   x5, x11
    +48  li   x6, 0
    +52  beq  x5, x0, +16 → +68   [hdr]
    +56  srli x5, x5, 8
    +60  addi x6, x6, 1
    +64  jal  x0, -12     → +52
    +68  add  x10, x11, x6
    +72  addi x10, x10, 1
    +76  jalr (long ret)
-/

/-- The RLP byte-string encoded size: a single byte below `0x80`
    encodes as itself (size 1); otherwise a 1-byte header below 56,
    else a `1 + length-of-length` header. -/
def rbesSize (xs : List (BitVec 8)) (len : Word) : Word :=
  if len = (1 : Word) ∧ (xs.getD 0 0).toNat < 128 then 1
  else if BitVec.ult len (56 : Word) then len + 1
  else (len + BitVec.ofNat 64 (u64ByteLen len)) + 1


/-- One `SRLI 8` advances the shift count by one byte (local copy of the
    #10082 private helper). -/
private theorem shift_step (v : Word) (i : Nat) :
    (v >>> (8 * i)) >>> ((8 : BitVec 6)).toNat = v >>> (8 * (i + 1)) := by
  rw [show ((8 : BitVec 6)).toNat = 8 from rfl]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
    BitVec.toNat_ushiftRight, ← Nat.shiftRight_add,
    show 8 * i + 8 = 8 * (i + 1) from by omega]

private theorem shift_zero_self (v : Word) : v >>> (8 * 0) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  rfl

private theorem cnt_step_up (n : Nat) (_h : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 n + signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 (n + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

section Routine

variable (ptr len ret : Word) (xs : List (BitVec 8))

/-- Loop invariant at iteration `i` (the `.len` byte-length loop):
    shift register, counter, and the riding inputs. -/
private def rbsInv (i : Nat) : Assertion :=
  ((.x5 : Reg) ↦ᵣ (len >>> (8 * i))) **
  ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
  ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
  ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x7 ** bytesRegion ptr xs

/-- The genuine routine post. -/
private def rbsPost : Assertion :=
  ((.x10 : Reg) ↦ᵣ rbesSize xs len) ** ((.x11 : Reg) ↦ᵣ len) **
  ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  bytesRegion ptr xs

/-- One `.len` iteration (`i < u64ByteLen len`). -/
private theorem rbsIter_spec (i : Nat) (hi : i < u64ByteLen len) :
    cpsBranchWithin 4 (rbesBase + 52)
      (CodeReq.ofProg rbesBase rlpBytesEncodedSize_prog)
      (rbsInv ptr len ret xs i)
      ret (rbsPost ptr len ret xs)
      (rbesBase + 52) (rbsInv ptr len ret xs (i + 1)) := by
  set CR := CodeReq.ofProg rbesBase rlpBytesEncodedSize_prog with hCR
  have hN8 := u64ByteLen_le len
  unfold rbsInv
  have hbr := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
      ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x7 ** bytesRegion ptr xs)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x5 .x0 (16 : BitVec 13) (len >>> (8 * i))
        (0 : Word) (rbesBase + 52))
      (hmono := by rw [hCR]; code_mem))
  rw [show (rbesBase + 52 : Word) + signExtend13 (16 : BitVec 13)
        = (rbesBase + 68 : Word) from by decide,
      show (rbesBase + 52 : Word) + 4 = (rbesBase + 56 : Word) from by decide]
    at hbr
  have hsrli := liftCode (cr' := CR)
    (srli_spec_gen_same_within .x5 (len >>> (8 * i)) (8 : BitVec 6)
      (rbesBase + 56) (by decide))
    (by rw [hCR]; code_mem)
  rw [shift_step len i,
      show (rbesBase + 56 : Word) + 4 = (rbesBase + 60 : Word) from by decide]
    at hsrli
  have haddi := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x6 (BitVec.ofNat 64 i) (1 : BitVec 12)
      (rbesBase + 60) (by decide))
    (by rw [hCR]; code_mem)
  rw [cnt_step_up i (by omega),
      show (rbesBase + 60 : Word) + 4 = (rbesBase + 64 : Word) from by decide]
    at haddi
  have hjal := liftCode (cr' := CR)
    (jal_x0_spec_gen_within (-12 : BitVec 21) (rbesBase + 64))
    (by rw [hCR]; code_mem)
  rw [show (rbesBase + 64 : Word) + signExtend21 (-12 : BitVec 21)
    = (rbesBase + 52 : Word) from by decide] at hjal
  have hsrliF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
      ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x7 ** bytesRegion ptr xs)
    (by pcf) hsrli
  have haddiF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (len >>> (8 * (i + 1)))) **
      ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x7 ** bytesRegion ptr xs)
    (by pcf) haddi
  have hjalF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (len >>> (8 * (i + 1)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) **
      ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x7 ** bytesRegion ptr xs)
    (by pcf) hjal
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsrliF haddiF
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [sepConj_emp_left']
      xperm_hyp hp) hc1 hjalF
  have hcont : cpsTripleWithin 3 (rbesBase + 56) (rbesBase + 52) CR
      (((.x5 : Reg) ↦ᵣ (len >>> (8 * i))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
        ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x7 ** bytesRegion ptr xs)
      (rbsInv ptr len ret xs (i + 1)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => ?_) hc2
    rw [sepConj_emp_left'] at hq
    unfold rbsInv
    xperm_hyp hq
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (breakStation_spec (cond := (len >>> (8 * i) = (0 : Word)))
    (PT := ((.x5 : Reg) ↦ᵣ (len >>> (8 * i))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
      ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x7 ** bytesRegion ptr xs)
    (PF := ((.x5 : Reg) ↦ᵣ (len >>> (8 * i))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
      ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x7 ** bytesRegion ptr xs)
    hbr
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by xperm_hyp hq)
    (fun hc => absurd hc (u64ByteLen_shift_ne len i hi))
    (fun _ => cpsTripleWithin_as_cpsBranchWithin_right ret
      (rbsPost ptr len ret xs) hcont))

/-- Exhaustion (`i = u64ByteLen len`): guard fires; under the two
    excluded cases the materialized `len + byteLen + 1` IS `rbesSize`. -/
private theorem rbsExh_spec
    (hnot1 : ¬ (len = (1 : Word) ∧ (xs.getD 0 0).toNat < 128))
    (hge : ¬ BitVec.ult len (56 : Word))
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 4 (rbesBase + 52) ret
      (CodeReq.ofProg rbesBase rlpBytesEncodedSize_prog)
      (rbsInv ptr len ret xs (u64ByteLen len))
      (rbsPost ptr len ret xs) := by
  set CR := CodeReq.ofProg rbesBase rlpBytesEncodedSize_prog with hCR
  unfold rbsInv
  have hbr := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) **
      ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x7 ** bytesRegion ptr xs)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x5 .x0 (16 : BitVec 13)
        (len >>> (8 * u64ByteLen len)) (0 : Word) (rbesBase + 52))
      (hmono := by rw [hCR]; code_mem))
  rw [show (rbesBase + 52 : Word) + signExtend13 (16 : BitVec 13)
        = (rbesBase + 68 : Word) from by decide,
      show (rbesBase + 52 : Word) + 4 = (rbesBase + 56 : Word) from by decide]
    at hbr
  -- add a0, a1, t1 ; addi a0, a0, 1 ; ret
  have hadd := liftCode (cr' := CR)
    (add_spec_gen_within .x10 .x11 .x6 len
      (BitVec.ofNat 64 (u64ByteLen len)) ptr (rbesBase + 68) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (rbesBase + 68 : Word) + 4 = (rbesBase + 72 : Word) from by decide]
    at hadd
  have haddi := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x10 (len + BitVec.ofNat 64 (u64ByteLen len))
      (1 : BitVec 12) (rbesBase + 72) (by decide))
    (by rw [hCR]; code_mem)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      show (rbesBase + 72 : Word) + 4 = (rbesBase + 76 : Word) from by decide]
    at haddi
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (rbesBase + 76) ret)
    (by rw [hCR]; code_mem)
  rw [halignRet] at hret
  have haddF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (len >>> (8 * u64ByteLen len))) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x7 ** bytesRegion ptr xs)
    (by pcf) hadd
  have haddiF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (len >>> (8 * u64ByteLen len))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) **
      ((.x11 : Reg) ↦ᵣ len) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x7 ** bytesRegion ptr xs)
    (by pcf) haddi
  have hretF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (len >>> (8 * u64ByteLen len))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) **
      ((.x10 : Reg) ↦ᵣ ((len + BitVec.ofNat 64 (u64ByteLen len)) + (1 : Word))) **
      ((.x11 : Reg) ↦ᵣ len) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x7 ** bytesRegion ptr xs)
    (by pcf) hret
  have htail1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) haddF haddiF
  have htail2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) htail1 hretF
  have htailQ : cpsTripleWithin 3 (rbesBase + 68) ret CR
      (((.x5 : Reg) ↦ᵣ (len >>> (8 * u64ByteLen len))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) **
        ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x7 ** bytesRegion ptr xs)
      (rbsPost ptr len ret xs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => ?_) htail2
    unfold rbsPost rbesSize
    rw [if_neg hnot1, if_neg hge]
    have hq1 : (((.x5 : Reg) ↦ᵣ (len >>> (8 * u64ByteLen len))) **
        ((((.x6 : Reg)) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) **
          (((.x10 : Reg) ↦ᵣ ((len + BitVec.ofNat 64 (u64ByteLen len)) + (1 : Word))) **
           ((.x11 : Reg) ↦ᵣ len) **
           ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           regOwn .x7 ** bytesRegion ptr xs))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hq1
    xperm_hyp hq2
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (retJoinStation_spec
      (cond := (len >>> (8 * u64ByteLen len) = (0 : Word)))
      (PT := ((.x5 : Reg) ↦ᵣ (len >>> (8 * u64ByteLen len))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) **
        ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x7 ** bytesRegion ptr xs)
      (PF := ((.x5 : Reg) ↦ᵣ (len >>> (8 * u64ByteLen len))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) **
        ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x7 ** bytesRegion ptr xs)
      hbr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun _ => htailQ)
      (fun hc => absurd (u64ByteLen_shift_zero len) hc))

/-- The shared length-header continuation (from `.hdr`, at `+20`),
    proven ONCE and consumed by both the `len ≠ 1` branch and the
    `b0 ≥ 0x80` fall-through.  `v6`/`v7` are whatever the two entry
    paths left in the scratch registers. -/
private theorem rbsHdr_spec (v6 v7 : Word)
    (hnot1 : ¬ (len = (1 : Word) ∧ (xs.getD 0 0).toNat < 128))
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 42 (rbesBase + 20) ret
      (CodeReq.ofProg rbesBase rlpBytesEncodedSize_prog)
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        bytesRegion ptr xs)
      (rbsPost ptr len ret xs) := by
  set CR := CodeReq.ofProg rbesBase rlpBytesEncodedSize_prog with hCR
  have hN8 := u64ByteLen_le len
  -- peel x5 (the li destination)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        bytesRegion ptr xs))
      (fun v5 => ?_))
  -- li x5, 56
  have hli := liftCode (cr' := CR)
    (li_spec_gen_within .x5 v5 (56 : Word) (rbesBase + 20) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (rbesBase + 20 : Word) + 4 = (rbesBase + 24 : Word) from by decide]
    at hli
  -- bgeu a1, t0 (the short/long dispatch)
  have hbr := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      bytesRegion ptr xs)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bgeu_spec_gen_within .x11 .x5 (20 : BitVec 13) len (56 : Word)
        (rbesBase + 24))
      (hmono := by rw [hCR]; code_mem))
  rw [show (rbesBase + 24 : Word) + signExtend13 (20 : BitVec 13)
        = (rbesBase + 44 : Word) from by decide,
      show (rbesBase + 24 : Word) + 4 = (rbesBase + 28 : Word) from by decide]
    at hbr
  -- short arm: addi a0, a1, 1 ; ret
  have hshort : BitVec.ult len (56 : Word) →
      cpsTripleWithin 40 (rbesBase + 28) ret CR
        (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (56 : Word)) **
          (((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
            bytesRegion ptr xs))
        (rbsPost ptr len ret xs) := by
    intro hlt
    have haddi := liftCode (cr' := CR)
      (addi_spec_gen_within .x10 .x11 ptr len (1 : BitVec 12)
        (rbesBase + 28) (by decide))
      (by rw [hCR]; code_mem)
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
        show (rbesBase + 28 : Word) + 4 = (rbesBase + 32 : Word) from by decide]
      at haddi
    have hret := liftCode (cr' := CR)
      (EvmAsm.Evm64.ret_spec_within' (rbesBase + 32) ret)
      (by rw [hCR]; code_mem)
    rw [halignRet] at hret
    have haddiF := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        bytesRegion ptr xs)
      (by pcf) haddi
    have hretF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (len + (1 : Word))) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        bytesRegion ptr xs)
      (by pcf) hret
    have hc := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) haddiF hretF
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun h hq => ?_) hc)
    unfold rbsPost rbesSize
    rw [if_neg hnot1, if_pos hlt]
    have hq1 : (((.x5 : Reg) ↦ᵣ (56 : Word)) ** (((.x6 : Reg) ↦ᵣ v6) **
        (((.x7 : Reg) ↦ᵣ v7) **
          (((.x10 : Reg) ↦ᵣ (len + (1 : Word))) ** ((.x11 : Reg) ↦ᵣ len) **
           ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion ptr xs)))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _) (fun _ hh => hh))) h hq1
    xperm_hyp hq2
  -- long arm: mv t0, a1 ; li t1, 0 ; the payload-dependent while
  have hlong : ¬ BitVec.ult len (56 : Word) →
      cpsTripleWithin 40 (rbesBase + 44) ret CR
        (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (56 : Word)) **
          (((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
            bytesRegion ptr xs))
        (rbsPost ptr len ret xs) := by
    intro hge
    have hmv := liftCode (cr' := CR)
      (mv_spec_gen_within .x5 .x11 len (56 : Word) (rbesBase + 44)
        (by decide))
      (by rw [hCR]; code_mem)
    rw [show (rbesBase + 44 : Word) + 4 = (rbesBase + 48 : Word) from by decide]
      at hmv
    have hli6 := liftCode (cr' := CR)
      (li_spec_gen_within .x6 v6 (0 : Word) (rbesBase + 48) (by decide))
      (by rw [hCR]; code_mem)
    rw [show (rbesBase + 48 : Word) + 4 = (rbesBase + 52 : Word) from by decide,
        show (0 : Word) = BitVec.ofNat 64 0 from rfl] at hli6
    have hloop := twoBreakRetLoop_spec (hdr := (rbesBase + 52 : Word))
      (ret := ret) (cr := CR) (Q := rbsPost ptr len ret xs) (u64ByteLen len) 4 4
      (rbsInv ptr len ret xs)
      (fun i hi => rbsIter_spec ptr len ret xs i hi)
      (rbsExh_spec ptr len ret xs hnot1 hge halignRet)
    have hmvF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        bytesRegion ptr xs)
      (by pcf) hmv
    have hli6F := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ len) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x11 : Reg) ↦ᵣ len) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) **
        bytesRegion ptr xs)
      (by pcf) hli6
    have hc1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hmvF hli6F
    have hc2 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        unfold rbsInv
        rw [shift_zero_self len]
        have hp1 : ((((.x7 : Reg) ↦ᵣ v7) **
            (((.x5 : Reg) ↦ᵣ len) **
             ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
             ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
             ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
             bytesRegion ptr xs))) h := by
          xperm_hyp hp
        have hp2 := sepConj_mono (regIs_to_regOwn .x7 _)
          (fun _ hh => hh) h hp1
        xperm_hyp hp2) hc1 hloop
    refine cpsTripleWithin_mono_nSteps ?hle
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) hc2)
    case hle => omega
  -- the dispatch station
  have hliF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      bytesRegion ptr xs)
    (by pcf) hli
  have hstation := retJoinStation_spec
    (cond := ¬ BitVec.ult len (56 : Word))
    (PT := ((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (56 : Word)) **
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        bytesRegion ptr xs))
    (PF := ((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (56 : Word)) **
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        bytesRegion ptr xs))
    hbr
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by
      have hq1 : (⌜BitVec.ult len (56 : Word)⌝ **
          (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (56 : Word)) **
           ((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
           bytesRegion ptr xs)) h := by
        xperm_hyp hq
      obtain ⟨hlt, hrest⟩ := (sepConj_pure_left h).1 hq1
      exact (sepConj_pure_left h).2 ⟨fun hn => hn hlt, hrest⟩)
    (fun hge => hlong hge)
    (fun hnge => hshort (not_not.mp hnge))
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hliF hstation
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hall)

/-- **`rlp_bytes_encoded_size` at its linked address** (genuine post):
    `a0 = rbesSize xs len` — the real RLP byte-string size formula;
    the input region and `a1` untouched. -/
theorem rlpBytesEncodedSize_spec
    (hlenXs : xs.length = len.toNat)
    (halignPtr : ptr.toNat % 8 = 0)
    (hvalidPtr : ∀ k, k < len.toNat →
      isValidByteAccess (ptr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 48 rbesBase ret
      (CodeReq.ofProg rbesBase rlpBytesEncodedSize_prog)
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        bytesRegion ptr xs)
      (((.x10 : Reg) ↦ᵣ rbesSize xs len) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        bytesRegion ptr xs) := by
  set CR := CodeReq.ofProg rbesBase rlpBytesEncodedSize_prog with hCR
  -- peel x5, x6, x7
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** regOwn .x7 ** bytesRegion ptr xs))
      (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x7 ** bytesRegion ptr xs) **
        ((.x5 : Reg) ↦ᵣ v5))
      (fun v6 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
      (P := (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion ptr xs) **
        ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6))
      (fun v7 => ?_))
  -- li x5, 1
  have hli := liftCode (cr' := CR)
    (li_spec_gen_within .x5 v5 (1 : Word) rbesBase (by decide))
    (by rw [hCR]; code_mem)
  -- bne a1, t0 (the single-byte prelude dispatch)
  have hbr := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      bytesRegion ptr xs)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bne_spec_gen_within .x11 .x5 (16 : BitVec 13) len (1 : Word)
        (rbesBase + 4))
      (hmono := by rw [hCR]; code_mem))
  rw [show (rbesBase + 4 : Word) + signExtend13 (16 : BitVec 13)
        = (rbesBase + 20 : Word) from by decide,
      show (rbesBase + 4 : Word) + 4 = (rbesBase + 8 : Word) from by decide]
    at hbr
  -- taken arm (len ≠ 1): straight to the shared header continuation
  have hne1 : len ≠ (1 : Word) →
      cpsTripleWithin 46 (rbesBase + 20) ret CR
        (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
          (((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
            bytesRegion ptr xs))
        (rbsPost ptr len ret xs) := by
    intro hne
    have hnot1 : ¬ (len = (1 : Word) ∧ (xs.getD 0 0).toNat < 128) :=
      fun hand => hne hand.1
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
        (rbsHdr_spec ptr len ret xs v6 v7 hnot1 halignRet))
    have hp1 : (((.x5 : Reg) ↦ᵣ (1 : Word)) **
        (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         bytesRegion ptr xs)) h := by
      xperm_hyp hp
    have hp2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (fun _ hh => hh) h hp1
    xperm_hyp hp2
  -- fall arm (len = 1): lbu ; li 128 ; the byte guard
  have heq1 : len = (1 : Word) →
      cpsTripleWithin 46 (rbesBase + 8) ret CR
        (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
          (((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
            bytesRegion ptr xs))
        (rbsPost ptr len ret xs) := by
    intro he1
    have hxlen : xs.length = 1 := by
      rw [hlenXs, he1]; rfl
    have h0lt : 0 < xs.length := by omega
    -- lbu t1, 0(a0): reads xs[0]
    have hlbu := liftCode (cr' := CR)
      (bytesRegion_lbu_within .x6 .x10 ptr v6 (rbesBase + 8) xs 0
        (by decide) halignPtr h0lt (by omega)
        (hvalidPtr 0 (by omega)))
      (by rw [hCR]; code_mem)
    rw [show ptr + BitVec.ofNat 64 0 = ptr from by
          rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
          bv_omega,
        show (rbesBase + 8 : Word) + 4 = (rbesBase + 12 : Word) from by decide]
      at hlbu
    set b0 := (xs[0]'h0lt).zeroExtend 64 with hb0
    have hgd0 : xs.getD 0 0 = xs[0]'h0lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0lt]
      rfl
    have hb0N : b0.toNat = (xs[0]'h0lt).toNat := by
      rw [hb0]
      show (BitVec.setWidth 64 _).toNat = _
      rw [BitVec.toNat_setWidth]
      have := (xs[0]'h0lt).isLt
      omega
    -- li t2, 128
    have hli7 := liftCode (cr' := CR)
      (li_spec_gen_within .x7 v7 (128 : Word) (rbesBase + 12) (by decide))
      (by rw [hCR]; code_mem)
    rw [show (rbesBase + 12 : Word) + 4 = (rbesBase + 16 : Word) from by decide]
      at hli7
    -- bltu t1, t2 (the byte guard)
    have hbrB := cpsBranchWithin_frameR
      (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
        ((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr xs)
      (by pcf)
      (cpsBranchWithin_extend_code (cr' := CR)
        (h := bltu_spec_gen_within .x6 .x7 (20 : BitVec 13) b0 (128 : Word)
          (rbesBase + 16))
        (hmono := by rw [hCR]; code_mem))
    rw [show (rbesBase + 16 : Word) + signExtend13 (20 : BitVec 13)
          = (rbesBase + 36 : Word) from by decide,
        show (rbesBase + 16 : Word) + 4 = (rbesBase + 20 : Word) from by decide]
      at hbrB
    -- taken: li a0, 1 ; ret — the size-1 tail
    have hone : BitVec.ult b0 (128 : Word) →
        cpsTripleWithin 43 (rbesBase + 36) ret CR
          (((.x6 : Reg) ↦ᵣ b0) ** ((.x7 : Reg) ↦ᵣ (128 : Word)) **
            (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
             ((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
             ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr xs))
          (rbsPost ptr len ret xs) := by
      intro hblt
      have hb0small : (xs.getD 0 0).toNat < 128 := by
        have : b0.toNat < 128 := by
          simpa [BitVec.ult, decide_eq_true_eq] using hblt
        rw [hgd0]
        omega
      have h := sharedRetTail_spec CR (rbesBase + 36) ret .x10 (1 : Word)
        ptr
        (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
          ((.x6 : Reg) ↦ᵣ b0) ** ((.x7 : Reg) ↦ᵣ (128 : Word)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr xs)
        (by pcf) (by decide) halignRet
        (by rw [hCR]; code_mem) (by rw [hCR]; code_mem)
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
          (fun h hq => ?_) h)
      unfold rbsPost rbesSize
      rw [if_pos ⟨he1, hb0small⟩]
      have hq1 : (((.x5 : Reg) ↦ᵣ (1 : Word)) ** (((.x6 : Reg) ↦ᵣ b0) **
          (((.x7 : Reg) ↦ᵣ (128 : Word)) **
            (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ len) **
             ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
             bytesRegion ptr xs)))) h := by
        xperm_hyp hq
      have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
        (sepConj_mono (regIs_to_regOwn .x6 _)
          (sepConj_mono (regIs_to_regOwn .x7 _) (fun _ hh => hh))) h hq1
      xperm_hyp hq2
    -- fall: the shared header continuation (b0 ≥ 0x80)
    have hbig : ¬ BitVec.ult b0 (128 : Word) →
        cpsTripleWithin 43 (rbesBase + 20) ret CR
          (((.x6 : Reg) ↦ᵣ b0) ** ((.x7 : Reg) ↦ᵣ (128 : Word)) **
            (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
             ((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
             ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr xs))
          (rbsPost ptr len ret xs) := by
      intro hnblt
      have hnot1 : ¬ (len = (1 : Word) ∧ (xs.getD 0 0).toNat < 128) := by
        rintro ⟨-, hsmall⟩
        apply hnblt
        have : b0.toNat < 128 := by rw [hb0N, ← hgd0]; omega
        simpa [BitVec.ult, decide_eq_true_eq] using this
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
          (rbsHdr_spec ptr len ret xs b0 (128 : Word) hnot1 halignRet))
      have hp1 : (((.x5 : Reg) ↦ᵣ (1 : Word)) **
          (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
           ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((.x6 : Reg) ↦ᵣ b0) ** ((.x7 : Reg) ↦ᵣ (128 : Word)) **
           bytesRegion ptr xs)) h := by
        xperm_hyp hp
      have hp2 := sepConj_mono (regIs_to_regOwn .x5 _)
        (fun _ hh => hh) h hp1
      xperm_hyp hp2
    -- the byte-guard station
    have hstB := retJoinStation_spec
      (cond := BitVec.ult b0 (128 : Word))
      (PT := ((.x6 : Reg) ↦ᵣ b0) ** ((.x7 : Reg) ↦ᵣ (128 : Word)) **
        (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
         ((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr xs))
      (PF := ((.x6 : Reg) ↦ᵣ b0) ** ((.x7 : Reg) ↦ᵣ (128 : Word)) **
        (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
         ((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr xs))
      hbrB
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun hblt => hone hblt)
      (fun hnblt => hbig hnblt)
    -- lbu ; li ; station
    have hlbuF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x7 : Reg) ↦ᵣ v7))
      (by pcf) hlbu
    have hli7F := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
        ((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ b0) **
        bytesRegion ptr xs)
      (by pcf) hli7
    have hc1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hlbuF hli7F
    have hc2 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hc1 hstB
    exact cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) hc2)
  -- the prelude station
  have hliF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      bytesRegion ptr xs)
    (by pcf) hli
  have hstation := retJoinStation_spec
    (cond := len ≠ (1 : Word))
    (PT := ((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        bytesRegion ptr xs))
    (PF := ((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        bytesRegion ptr xs))
    hbr
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by
      have hq1 : (⌜len = (1 : Word)⌝ **
          (((.x11 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
           ((.x10 : Reg) ↦ᵣ ptr) ** ((.x1 : Reg) ↦ᵣ ret) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
           bytesRegion ptr xs)) h := by
        xperm_hyp hq
      obtain ⟨he, hrest⟩ := (sepConj_pure_left h).1 hq1
      exact (sepConj_pure_left h).2 ⟨fun hn => hn he, hrest⟩)
    (fun hne => hne1 hne)
    (fun hnn => heq1 (not_not.mp hnn))
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hliF hstation
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      unfold rbsPost at hq
      xperm_hyp hq)
    (cpsTripleWithin_mono_nSteps (by omega) hall)

end Routine

#print axioms rlpBytesEncodedSize_spec

end RlpBytesEncodedSizeSAsm

end EvmAsm.Codegen
