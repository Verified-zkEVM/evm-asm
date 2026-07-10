/-
  EvmAsm.Codegen.Programs.RlpListEncodedSizeSAsm

  `rlp_list_encoded_size` — the **payload-dependent return-terminating
  routine** (bead evm-asm-8tw0t), ported WITHOUT new `retSound` split
  lemmas: at `cpsTripleWithin` level the "payload-dependent loop count"
  difficulty dissolves, because `twoBreakRetLoop_spec` (#10067) takes its
  iteration count as an ordinary `Nat` — instantiating it at the
  VALUE-DEPENDENT `u64ByteLen v` needs no new machinery.  The bead's
  "long-tail extraction relating the while exit index to `u64ByteLen`"
  is the pair of bridges `u64ByteLen_shift_zero` /
  `u64ByteLen_shift_ne` below: the byte-length is exactly the first
  shift count at which the payload length vanishes, which is what the
  loop's `BEQ` guard tests.

      rlp_list_encoded_size:
        li   t0, 56
        bgeu a0, t0, .long
        addi a0, a0, 1 ; ret          -- short form: 1-byte header
      .long:
        mv   t0, a0 ; li t1, 0
      .len: beq t0, x0, .done         -- while (v >>> 8·i) ≠ 0
        srli t0, t0, 8 ; addi t1, t1, 1 ; j .len
      .done:
        add  a0, a0, t1 ; addi a0, a0, 1 ; ret

  **Genuine post** (`rlpListEncodedSize_spec`): `a0 = (if v <u 56 then
  v + 1 else v + u64ByteLen v + 1)` — the real RLP list-header size
  formula (1-byte header below 56, else 1 + length-of-length bytes).
  Byte-transparent: at the `#guard`-tied
  `GuestAddrs.rlp_list_encoded_size` over the emitted
  `rlpListEncodedSize_prog` (no byte change, no A/B).
-/

import EvmAsm.Codegen.Programs.BlockRlpSize
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Rv64.SAsm.TwoBreakWritable
import EvmAsm.Rv64.SAsm.ContForwardJoin
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace RlpListEncodedSizeSAsm

-- Address anchor (fails the build if the guest link moves).
#guard GuestAddrs.rlp_list_encoded_size = 0x8000ae20

/-
  Layout (base 0x8000ae20):
    +0  0x8000ae20  li   x5, 56
    +4  0x8000ae24  bgeu x10, x5, +12 → 0x8000ae30
    +8  0x8000ae28  addi x10, x10, 1
    +12 0x8000ae2c  jalr (short ret)
    +16 0x8000ae30  mv   x5, x10
    +20 0x8000ae34  li   x6, 0
    +24 0x8000ae38  beq  x5, x0, +16 → 0x8000ae48   [hdr]
    +28 0x8000ae3c  srli x5, x5, 8
    +32 0x8000ae40  addi x6, x6, 1
    +36 0x8000ae44  jal  x0, -12     → 0x8000ae38
    +40 0x8000ae48  add  x10, x10, x6
    +44 0x8000ae4c  addi x10, x10, 1
    +48 0x8000ae50  jalr (long ret)
-/

-- ============================================================================
-- The byte length and its loop-exit bridges (the "long-tail extraction").
-- ============================================================================

/-- The minimal number of bytes needed to represent `v` — the routine's
    loop-iteration count (`0` for `v = 0`). -/
def u64ByteLen (v : Word) : Nat :=
  if v.toNat < 2 ^ 0 then 0
  else if v.toNat < 2 ^ 8 then 1
  else if v.toNat < 2 ^ 16 then 2
  else if v.toNat < 2 ^ 24 then 3
  else if v.toNat < 2 ^ 32 then 4
  else if v.toNat < 2 ^ 40 then 5
  else if v.toNat < 2 ^ 48 then 6
  else if v.toNat < 2 ^ 56 then 7
  else 8

theorem u64ByteLen_le (v : Word) : u64ByteLen v ≤ 8 := by
  unfold u64ByteLen
  split_ifs <;> omega

/-- A right shift vanishes exactly when the value fits below it. -/
private theorem shift_zero_iff (v : Word) (k : Nat) :
    v >>> k = (0 : Word) ↔ v.toNat < 2 ^ k := by
  constructor
  · intro h
    have hdiv := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show ((0 : Word)).toNat = 0 from rfl] at hdiv
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    rcases Nat.lt_or_ge v.toNat (2 ^ k) with hlt | hge
    · exact hlt
    · exfalso
      have hone := Nat.div_le_div_right (c := 2 ^ k) hge
      rw [Nat.div_self hpos] at hone
      omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show ((0 : Word)).toNat = 0 from rfl]
    exact Nat.div_eq_of_lt h

/-- **Exit bridge**: shifting by the byte length vanishes — the `BEQ`
    guard fires exactly at iteration `u64ByteLen v`. -/
theorem u64ByteLen_shift_zero (v : Word) :
    v >>> (8 * u64ByteLen v) = (0 : Word) := by
  rw [shift_zero_iff]
  have hlt := v.isLt
  unfold u64ByteLen
  split_ifs <;> (simp only [Nat.reduceMul]; omega)

private theorem u64ByteLen_ge (v : Word) (i : Nat) (hi : i < u64ByteLen v) :
    2 ^ (8 * i) ≤ v.toNat := by
  unfold u64ByteLen at hi
  split_ifs at hi <;>
    first
      | omega
      | (interval_cases i <;> (simp only [Nat.reduceMul]; omega))

/-- **Continuation bridge**: before the byte length, the shifted value is
    still nonzero — the `BEQ` guard cannot fire early. -/
theorem u64ByteLen_shift_ne (v : Word) (i : Nat) (hi : i < u64ByteLen v) :
    v >>> (8 * i) ≠ (0 : Word) := by
  intro h
  rw [shift_zero_iff] at h
  have := u64ByteLen_ge v i hi
  omega

/-- One `SRLI 8` advances the shift count by one byte. -/
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

-- ============================================================================
-- The while loop (payload-dependent count) and the whole routine.
-- ============================================================================

section Routine

variable (v ret : Word)

/-- Loop invariant at iteration `i`: the shift register holds
    `v >>> 8·i`, the counter `i`; the payload and return address ride
    unchanged. -/
private def rlsInv (i : Nat) : Assertion :=
  ((.x5 : Reg) ↦ᵣ (v >>> (8 * i))) **
  ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
  ((.x10 : Reg) ↦ᵣ v) ** ((.x1 : Reg) ↦ᵣ ret) **
  ((.x0 : Reg) ↦ᵣ (0 : Word))

/-- The long-arm post: `a0 = v + u64ByteLen v + 1`. -/
private def rlsPost : Assertion :=
  ((.x10 : Reg) ↦ᵣ ((v + BitVec.ofNat 64 (u64ByteLen v)) + (1 : Word))) **
  ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6

/-- One `while` iteration (`i < u64ByteLen v`): guard not taken, shift,
    bump, loop. -/
private theorem rlsIter_spec (i : Nat) (hi : i < u64ByteLen v) :
    cpsBranchWithin 4 (0x8000ae38 : Word)
      (CodeReq.ofProg (0x8000ae20 : Word) rlpListEncodedSize_prog)
      (rlsInv v ret i)
      ret (rlsPost v ret)
      (0x8000ae38 : Word) (rlsInv v ret (i + 1)) := by
  set CR := CodeReq.ofProg (0x8000ae20 : Word) rlpListEncodedSize_prog with hCR
  have hN8 := u64ByteLen_le v
  unfold rlsInv
  -- guard (never taken at i < byteLen)
  have hbr := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x10 : Reg) ↦ᵣ v) **
      ((.x1 : Reg) ↦ᵣ ret))
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x5 .x0 (16 : BitVec 13) (v >>> (8 * i))
        (0 : Word) (0x8000ae38 : Word))
      (hmono := by rw [hCR]; code_mem))
  rw [show (0x8000ae38 : Word) + signExtend13 (16 : BitVec 13)
        = (0x8000ae48 : Word) from by decide,
      show (0x8000ae38 : Word) + 4 = (0x8000ae3c : Word) from by decide]
    at hbr
  -- srli x5, x5, 8 ; addi x6, x6, 1 ; jal hdr
  have hsrli := liftCode (cr' := CR)
    (srli_spec_gen_same_within .x5 (v >>> (8 * i)) (8 : BitVec 6)
      (0x8000ae3c : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [shift_step v i,
      show (0x8000ae3c : Word) + 4 = (0x8000ae40 : Word) from by decide]
    at hsrli
  have haddi := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x6 (BitVec.ofNat 64 i) (1 : BitVec 12)
      (0x8000ae40 : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [cnt_step_up i (by omega),
      show (0x8000ae40 : Word) + 4 = (0x8000ae44 : Word) from by decide]
    at haddi
  have hjal := liftCode (cr' := CR)
    (jal_x0_spec_gen_within (-12 : BitVec 21) (0x8000ae44 : Word))
    (by rw [hCR]; code_mem)
  rw [show (0x8000ae44 : Word) + signExtend21 (-12 : BitVec 21)
    = (0x8000ae38 : Word) from by decide] at hjal
  have hsrliF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x10 : Reg) ↦ᵣ v) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hsrli
  have haddiF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (v >>> (8 * (i + 1)))) ** ((.x10 : Reg) ↦ᵣ v) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) haddi
  have hjalF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (v >>> (8 * (i + 1)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) ** ((.x10 : Reg) ↦ᵣ v) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hjal
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsrliF haddiF
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [sepConj_emp_left']
      xperm_hyp hp) hc1 hjalF
  have hcont : cpsTripleWithin 3 (0x8000ae3c : Word) (0x8000ae38 : Word) CR
      (((.x5 : Reg) ↦ᵣ (v >>> (8 * i))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x10 : Reg) ↦ᵣ v) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (rlsInv v ret (i + 1)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => ?_) hc2
    rw [sepConj_emp_left'] at hq
    unfold rlsInv
    xperm_hyp hq
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (breakStation_spec (cond := (v >>> (8 * i) = (0 : Word)))
    (PT := ((.x5 : Reg) ↦ᵣ (v >>> (8 * i))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x10 : Reg) ↦ᵣ v) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (PF := ((.x5 : Reg) ↦ᵣ (v >>> (8 * i))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x10 : Reg) ↦ᵣ v) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    hbr
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by xperm_hyp hq)
    (fun hc => absurd hc (u64ByteLen_shift_ne v i hi))
    (fun _ => cpsTripleWithin_as_cpsBranchWithin_right ret (rlsPost v ret)
      hcont))

/-- Exhaustion (`i = u64ByteLen v`): guard fires, the size is
    materialized and returned. -/
private theorem rlsExh_spec
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 4 (0x8000ae38 : Word) ret
      (CodeReq.ofProg (0x8000ae20 : Word) rlpListEncodedSize_prog)
      (rlsInv v ret (u64ByteLen v))
      (rlsPost v ret) := by
  set CR := CodeReq.ofProg (0x8000ae20 : Word) rlpListEncodedSize_prog with hCR
  unfold rlsInv
  -- guard, taken (shift vanished)
  have hbr := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen v)) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x5 .x0 (16 : BitVec 13)
        (v >>> (8 * u64ByteLen v)) (0 : Word) (0x8000ae38 : Word))
      (hmono := by rw [hCR]; code_mem))
  rw [show (0x8000ae38 : Word) + signExtend13 (16 : BitVec 13)
        = (0x8000ae48 : Word) from by decide,
      show (0x8000ae38 : Word) + 4 = (0x8000ae3c : Word) from by decide]
    at hbr
  -- add a0, a0, t1 ; addi a0, a0, 1 ; ret
  have hadd := liftCode (cr' := CR)
    (add_spec_gen_rd_eq_rs1_within .x10 .x6 v
      (BitVec.ofNat 64 (u64ByteLen v)) (0x8000ae48 : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (0x8000ae48 : Word) + 4 = (0x8000ae4c : Word) from by decide]
    at hadd
  have haddi := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x10 (v + BitVec.ofNat 64 (u64ByteLen v))
      (1 : BitVec 12) (0x8000ae4c : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      show (0x8000ae4c : Word) + 4 = (0x8000ae50 : Word) from by decide]
    at haddi
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (0x8000ae50 : Word) ret)
    (by rw [hCR]; code_mem)
  rw [halignRet] at hret
  have haddF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (v >>> (8 * u64ByteLen v))) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hadd
  have haddiF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (v >>> (8 * u64ByteLen v))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen v)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) haddi
  have hretF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (v >>> (8 * u64ByteLen v))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen v)) **
      ((.x10 : Reg) ↦ᵣ ((v + BitVec.ofNat 64 (u64ByteLen v)) + (1 : Word))) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hret
  have htail1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) haddF haddiF
  have htail2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) htail1 hretF
  have htailQ : cpsTripleWithin 3 (0x8000ae48 : Word) ret CR
      (((.x5 : Reg) ↦ᵣ (v >>> (8 * u64ByteLen v))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen v)) **
        ((.x10 : Reg) ↦ᵣ v) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (rlsPost v ret) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => ?_) htail2
    unfold rlsPost
    have hq1 : (((.x5 : Reg) ↦ᵣ (v >>> (8 * u64ByteLen v))) **
        ((((.x6 : Reg)) ↦ᵣ BitVec.ofNat 64 (u64ByteLen v)) **
          (((.x10 : Reg) ↦ᵣ ((v + BitVec.ofNat 64 (u64ByteLen v)) + (1 : Word))) **
           ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hq1
    xperm_hyp hq2
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (retJoinStation_spec
      (cond := (v >>> (8 * u64ByteLen v) = (0 : Word)))
      (PT := ((.x5 : Reg) ↦ᵣ (v >>> (8 * u64ByteLen v))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen v)) **
        ((.x10 : Reg) ↦ᵣ v) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (PF := ((.x5 : Reg) ↦ᵣ (v >>> (8 * u64ByteLen v))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen v)) **
        ((.x10 : Reg) ↦ᵣ v) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)))
      hbr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun _ => htailQ)
      (fun hc => absurd (u64ByteLen_shift_zero v) hc))

/-- **`rlp_list_encoded_size` at its linked address** (genuine post):
    `a0 = (if v <u 56 then v + 1 else v + u64ByteLen v + 1)` — the real
    RLP list-header size formula, the loop exit index tied to
    `u64ByteLen` by the shift bridges. -/
theorem rlpListEncodedSize_spec
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 40 (0x8000ae20 : Word) ret
      (CodeReq.ofProg (0x8000ae20 : Word) rlpListEncodedSize_prog)
      (((.x10 : Reg) ↦ᵣ v) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6)
      (((.x10 : Reg) ↦ᵣ (if BitVec.ult v (56 : Word) then v + (1 : Word)
          else (v + BitVec.ofNat 64 (u64ByteLen v)) + (1 : Word))) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6) := by
  set CR := CodeReq.ofProg (0x8000ae20 : Word) rlpListEncodedSize_prog with hCR
  have hN8 := u64ByteLen_le v
  -- peel x5, x6
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (((.x10 : Reg) ↦ᵣ v) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x6))
      (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (((.x10 : Reg) ↦ᵣ v) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5)))
      (fun v6 => ?_))
  -- li x5, 56
  have hli := liftCode (cr' := CR)
    (li_spec_gen_within .x5 v5 (56 : Word) (0x8000ae20 : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (0x8000ae20 : Word) + 4 = (0x8000ae24 : Word) from by decide] at hli
  -- bgeu a0, t0 (the short/long dispatch)
  have hbr := cpsBranchWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ v6))
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bgeu_spec_gen_within .x10 .x5 (12 : BitVec 13) v (56 : Word)
        (0x8000ae24 : Word))
      (hmono := by rw [hCR]; code_mem))
  rw [show (0x8000ae24 : Word) + signExtend13 (12 : BitVec 13)
        = (0x8000ae30 : Word) from by decide,
      show (0x8000ae24 : Word) + 4 = (0x8000ae28 : Word) from by decide]
    at hbr
  -- short arm: addi a0, a0, 1 ; ret
  have hshort : BitVec.ult v (56 : Word) →
      cpsTripleWithin 38 (0x8000ae28 : Word) ret CR
        (((.x10 : Reg) ↦ᵣ v) ** ((.x5 : Reg) ↦ᵣ (56 : Word)) **
          (((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ v6)))
        (((.x10 : Reg) ↦ᵣ (if BitVec.ult v (56 : Word) then v + (1 : Word)
            else (v + BitVec.ofNat 64 (u64ByteLen v)) + (1 : Word))) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6) := by
    intro hlt
    have haddi := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x10 v (1 : BitVec 12) (0x8000ae28 : Word)
        (by decide))
      (by rw [hCR]; code_mem)
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
        show (0x8000ae28 : Word) + 4 = (0x8000ae2c : Word) from by decide]
      at haddi
    have hret := liftCode (cr' := CR)
      (EvmAsm.Evm64.ret_spec_within' (0x8000ae2c : Word) ret)
      (by rw [hCR]; code_mem)
    rw [halignRet] at hret
    have haddiF := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ v6))
      (by pcf) haddi
    have hretF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (v + (1 : Word))) ** ((.x5 : Reg) ↦ᵣ (56 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ v6))
      (by pcf) hret
    have hc := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) haddiF hretF
    refine cpsTripleWithin_mono_nSteps ?hle
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun h hq => ?hpost) hc)
    case hle => omega
    case hpost =>
      rw [if_pos hlt]
      have hq1 : (((.x5 : Reg) ↦ᵣ (56 : Word)) ** (((.x6 : Reg) ↦ᵣ v6) **
          (((.x10 : Reg) ↦ᵣ (v + (1 : Word))) ** ((.x1 : Reg) ↦ᵣ ret) **
           ((.x0 : Reg) ↦ᵣ (0 : Word))))) h := by
        xperm_hyp hq
      have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
        (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hq1
      xperm_hyp hq2
  -- long arm: mv t0, a0 ; li t1, 0 ; the payload-dependent while
  have hlong : ¬ BitVec.ult v (56 : Word) →
      cpsTripleWithin 38 (0x8000ae30 : Word) ret CR
        (((.x10 : Reg) ↦ᵣ v) ** ((.x5 : Reg) ↦ᵣ (56 : Word)) **
          (((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ v6)))
        (((.x10 : Reg) ↦ᵣ (if BitVec.ult v (56 : Word) then v + (1 : Word)
            else (v + BitVec.ofNat 64 (u64ByteLen v)) + (1 : Word))) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6) := by
    intro hge
    have hmv := liftCode (cr' := CR)
      (mv_spec_gen_within .x5 .x10 v (56 : Word) (0x8000ae30 : Word)
        (by decide))
      (by rw [hCR]; code_mem)
    rw [show (0x8000ae30 : Word) + 4 = (0x8000ae34 : Word) from by decide]
      at hmv
    have hli6 := liftCode (cr' := CR)
      (li_spec_gen_within .x6 v6 (0 : Word) (0x8000ae34 : Word) (by decide))
      (by rw [hCR]; code_mem)
    rw [show (0x8000ae34 : Word) + 4 = (0x8000ae38 : Word) from by decide,
        show (0 : Word) = BitVec.ofNat 64 0 from rfl] at hli6
    -- the payload-dependent loop: N := u64ByteLen v
    have hloop := twoBreakRetLoop_spec (hdr := (0x8000ae38 : Word))
      (ret := ret) (cr := CR) (Q := rlsPost v ret) (u64ByteLen v) 4 4
      (rlsInv v ret)
      (fun i hi => rlsIter_spec v ret i hi)
      (rlsExh_spec v ret halignRet)
    have hmvF := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6))
      (by pcf) hmv
    have hli6F := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ v) ** ((.x10 : Reg) ↦ᵣ v) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf) hli6
    have hc1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hmvF hli6F
    have hc2 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        unfold rlsInv
        rw [shift_zero_self v]
        xperm_hyp hp) hc1 hloop
    refine cpsTripleWithin_mono_nSteps ?hle
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun h hq => ?hpost) hc2)
    case hle =>
      have := u64ByteLen_le v
      omega
    case hpost =>
      unfold rlsPost at hq
      rw [if_neg hge]
      xperm_hyp hq
  -- the dispatch station
  have hliF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ v) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ v6))
    (by pcf) hli
  have hstation := retJoinStation_spec
    (cond := ¬ BitVec.ult v (56 : Word))
    (PT := ((.x10 : Reg) ↦ᵣ v) ** ((.x5 : Reg) ↦ᵣ (56 : Word)) **
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6)))
    (PF := ((.x10 : Reg) ↦ᵣ v) ** ((.x5 : Reg) ↦ᵣ (56 : Word)) **
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6)))
    hbr
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by
      have hq1 : (⌜BitVec.ult v (56 : Word)⌝ **
          (((.x10 : Reg) ↦ᵣ v) ** ((.x5 : Reg) ↦ᵣ (56 : Word)) **
           ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((.x6 : Reg) ↦ᵣ v6))) h := by
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

end Routine

#print axioms u64ByteLen_shift_zero
#print axioms u64ByteLen_shift_ne
#print axioms rlpListEncodedSize_spec

end RlpListEncodedSizeSAsm

end EvmAsm.Codegen
