/-
  EvmAsm.Codegen.Programs.Bls12Fq12SetOneSAsm

  **A tactic-driven cross-call sp-frame port** (bead
  evm-asm-4ch8f.58.3.23, unblocked by the `abiFrameCall_spec` bridge and the
  `FramePort` automation): `blq_set_one`, byte-TRANSPARENT (the existing
  emitted `blqSetOne_prog` already IS an `abiFrameProg` flatten — no re-emit,
  no guest-byte change):

      blq_set_one:  addi sp, sp, -16
                    sd   ra, 0(sp)
                    sd   s0, 8(sp)
                    mv   s0, a0            -- clobbers callee-saved s0
                    jal  ra, blq_zero      -- zero all 72 dwords (clobbers ra!)
                    li   t0, 1
                    sd   t0 -> 0(s0)       -- coefficient 0 := 1
                    ld   ra, 0(sp)
                    ld   s0, 8(sp)
                    addi sp, sp, +16
                    ret

  The callee `blq_zero` gets a FLAT whole-routine contract
  (`blqZeroFlat_spec`) — the `cpsTripleWithin` shape `callWithin_spec`
  consumes — with its bottom-test store loop discharged by the new
  `countdownLoopBottom_spec` over the writable `dwordsIs` region and the
  genuine invariant "the first `72 - n` dwords are already zero".  (This is
  an independent flat derivation alongside the structured
  `Bls12Fq12ZeroSAsm.blqZeroFn_spec`; the flat form is what a frame-exposed
  caller body can compose — exactly the gap bead 4ch8f.58.3.23 recorded.)

  `blqSetOneFrame_spec` is the whole-routine ABI contract, wrapped by
  `abi_frame`: on return `sp`, `ra` (clobbered by the real `jal`!), and `s0`
  (clobbered by the body) are restored to entry, and the FQ12 at the entry
  `a0` holds ONE — dword 0 = 1, the other 71 dwords = 0 — the genuine,
  unweakened semantics.  `a0` itself ends at `dst + 576` (advanced by
  `blq_zero`), exactly as the machine leaves it.

  Byte-tie: `#guard`/`rfl` against the emitted `blqSetOne_prog` (including
  the concrete guest-linked `jalOff`) and the `GuestAddrs` anchors.
-/

import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.Bls12Fq12

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.Tactics

namespace Bls12Fq12SetOneSAsm

-- ============================================================================
-- Anchors and byte-ties.
-- ============================================================================

-- The two routines are adjacent in the guest text: `blq_zero` (6 slots)
-- immediately precedes `blq_set_one`.
#guard GuestAddrs.blq_zero = 0x80033e1c
#guard GuestAddrs.blq_set_one = 0x80033e34
#guard GuestAddrs.blq_zero + 4 * blqZero_prog.length = GuestAddrs.blq_set_one

/-- The caller's 2-slot frame: `ra` at 0, `s0` at 8. -/
def setOneFrame : FrameDesc := [(.x1, 0), (.x8, 8)]

/-- The caller body: pointer copy, the cross-call, the coefficient-0 store. -/
def setOneBody : List Instr :=
  [ .MV .x8 .x10,
    .JAL .x1 (jalOff GuestAddrs.blq_zero (GuestAddrs.blq_set_one + 16)),
    .LI .x5 (1 : Word),
    .SD .x8 .x5 (0 : BitVec 12) ]

-- Byte-transparency: the emitted `blqSetOne_prog` IS the abiFrameProg
-- flatten of this frame + body — verified == emitted, bytes unchanged.
#guard abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) setOneFrame setOneBody
  = blqSetOne_prog

/-- Byte-transparency, kernel-checked. -/
theorem setOneProg_eq :
    abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) setOneFrame setOneBody
      = blqSetOne_prog := rfl

/-- The verification `CodeReq`: both adjacent routines, at their guest
    addresses. -/
def blqCr : CodeReq :=
  CodeReq.ofProg (0x80033e1c : Word) (blqZero_prog ++ blqSetOne_prog)

-- ============================================================================
-- Word / list helpers.
-- ============================================================================

private theorem add_sext0 (x : Word) : x + signExtend12 (0 : BitVec 12) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show (signExtend12 (0 : BitVec 12)).toNat = 0 from by decide,
      Nat.add_zero, Nat.mod_eq_of_lt x.isLt]

private theorem add_ofNat_zero (x : Word) : x + BitVec.ofNat 64 0 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero,
      Nat.mod_eq_of_lt x.isLt]

private theorem addr_step8 (dst : Word) (p : Nat) :
    (dst + BitVec.ofNat 64 (8 * p)) + signExtend12 (8 : BitVec 12)
      = dst + BitVec.ofNat 64 (8 * (p + 1)) := by
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem cnt_step_down (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  have e1 : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1 := by
    rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e1, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide,
      BitVec.add_assoc, show (1 : Word) + (-1 : Word) = 0 from by decide]
  exact BitVec.add_zero _

/-- Zeroing the next dword extends the zero prefix. -/
private theorem zero_prefix_step (vs : List Word) (p : Nat) (hp : p < vs.length) :
    (List.replicate p (0 : Word) ++ vs.drop p).set p 0
      = List.replicate (p + 1) (0 : Word) ++ vs.drop (p + 1) := by
  induction p generalizing vs with
  | zero =>
    cases vs with
    | nil => exact absurd hp (by simp)
    | cons v t => rfl
  | succ k ih =>
    cases vs with
    | nil => exact absurd hp (by simp)
    | cons v t =>
      have hk : k < t.length := by simpa using hp
      show ((0 : Word) :: (List.replicate k 0 ++ t.drop k)).set (k + 1) 0
          = (0 : Word) :: (List.replicate (k + 1) 0 ++ t.drop (k + 1))
      rw [List.set_cons_succ, ih t hk]

-- ============================================================================
-- The callee: a FLAT whole-routine contract for `blq_zero`.
-- ============================================================================

/-- Loop invariant at remaining count `n`: the cursor has advanced past the
    `72 - n` dwords already zeroed. -/
def zeroInvF (dst : Word) (vs : List Word) (n : Nat) : Assertion :=
  (.x10 ↦ᵣ (dst + BitVec.ofNat 64 (8 * (72 - n))))
    ** dwordsIs dst (List.replicate (72 - n) (0 : Word) ++ vs.drop (72 - n))

theorem pcFree_zeroInvF (dst : Word) (vs : List Word) (n : Nat) :
    (zeroInvF dst vs n).pcFree := by
  unfold zeroInvF
  pcf

/-- The per-iteration body (`sd ; addi a0 ; addi ctr`, `0x80033e20 →
    0x80033e2C`): zero one dword, advance, decrement. -/
private theorem zeroLoopBody_spec (dst : Word) (vs : List Word)
    (hlen : vs.length = 72) (n : Nat) (hn : n < 72) :
    cpsTripleWithin 3 (0x80033e20 : Word) (0x80033e2C : Word) blqCr
      ((.x7 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** zeroInvF dst vs (n + 1))
      ((.x7 ↦ᵣ BitVec.ofNat 64 n) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** zeroInvF dst vs n) := by
  have hpn : 72 - n = (72 - (n + 1)) + 1 := by omega
  set p := 72 - (n + 1) with hp
  set L := List.replicate p (0 : Word) ++ vs.drop p with hL
  have hLlen : p < L.length := by
    rw [hL]
    simp only [List.length_append, List.length_replicate, List.length_drop, hlen]
    omega
  obtain ⟨front, rest, hf, hr, heq1, heq2⟩ := dwordsIs_at_set dst L p 0 hLlen
  have hset : L.set p 0
      = List.replicate (p + 1) (0 : Word) ++ vs.drop (p + 1) := by
    rw [hL]
    exact zero_prefix_step vs p (by omega)
  simp only [zeroInvF, hpn, ← hp, ← hL]
  rw [heq1, ← hset, heq2]
  have hsd := sd_x0_spec_gen_within .x10 (dst + BitVec.ofNat 64 (8 * p))
    (L.getD p 0) (0 : BitVec 12) (0x80033e20 : Word)
  rw [add_sext0] at hsd
  rw [show (0x80033e20 : Word) + 4 = (0x80033e24 : Word) from by decide] at hsd
  have hsdC := liftCode (cr' := blqCr) hsd (by code_mem)
  have ha1 := addi_spec_gen_same_within .x10 (dst + BitVec.ofNat 64 (8 * p))
    (8 : BitVec 12) (0x80033e24 : Word) (by decide)
  rw [addr_step8] at ha1
  rw [show (0x80033e24 : Word) + 4 = (0x80033e28 : Word) from by decide] at ha1
  have ha1C := liftCode (cr' := blqCr) ha1 (by code_mem)
  have ha2 := addi_spec_gen_same_within .x7 (BitVec.ofNat 64 (n + 1))
    (-1 : BitVec 12) (0x80033e28 : Word) (by decide)
  rw [cnt_step_down] at ha2
  rw [show (0x80033e28 : Word) + 4 = (0x80033e2C : Word) from by decide] at ha2
  have ha2C := liftCode (cr' := blqCr) ha2 (by code_mem)
  have hFrontRest : (front ** rest).pcFree := pcFree_sepConj hf hr
  have hsdF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word)) ** front ** rest)
    (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hf
        | exact hr) hsdC
  have ha1F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** ((dst + BitVec.ofNat 64 (8 * p)) ↦ₘ (0 : Word)) ** front ** rest)
    (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact hf
        | exact hr) ha1C
  have ha2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (dst + BitVec.ofNat 64 (8 * (p + 1))))
      ** (Reg.x0 ↦ᵣ (0 : Word))
      ** ((dst + BitVec.ofNat 64 (8 * p)) ↦ₘ (0 : Word)) ** front ** rest)
    (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact hf
        | exact hr) ha2C
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsdF ha1F
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 ha2F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) s2

/-- **The flat whole-routine contract for `blq_zero`** — the exact
    `cpsTripleWithin` shape `callWithin_spec` consumes: entered at its guest
    address with any aligned return address in `ra`, a buffer pointer in
    `a0`, and 72 owned dwords, it returns with all 72 dwords zero, `a0`
    advanced past the buffer, and `ra` intact. -/
theorem blqZeroFlat_spec (ret dst v7 : Word) (vs : List Word)
    (hlen : vs.length = 72)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (1 + 72 * (3 + 1) + 1) (0x80033e1c : Word) ret blqCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** (.x7 ↦ᵣ v7)
        ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs dst vs)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ (dst + BitVec.ofNat 64 576))
        ** (.x7 ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** dwordsIs dst (List.replicate 72 (0 : Word))) := by
  -- init: li x7, 72
  have hli := li_spec_gen_within .x7 v7 (72 : Word) (0x80033e1c : Word) (by decide)
  rw [show (72 : Word) = BitVec.ofNat 64 72 from rfl] at hli
  rw [show (0x80033e1c : Word) + 4 = (0x80033e20 : Word) from by decide] at hli
  have hliC := liftCode (cr' := blqCr) hli (by code_mem)
  have hliF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs dst vs)
    (by pcf) hliC
  -- the loop, endpoints presented at 72 / 0
  have hloop : cpsTripleWithin (72 * (3 + 1)) (0x80033e20 : Word) (0x80033e30 : Word)
      blqCr
      ((.x7 ↦ᵣ BitVec.ofNat 64 72) ** (Reg.x0 ↦ᵣ (0 : Word)) ** zeroInvF dst vs 72)
      ((.x7 ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word)) ** zeroInvF dst vs 0) := by
    have h := countdownLoopBottom_spec blqCr (0x80033e20 : Word) (0x80033e2C : Word)
      .x7 (-12 : BitVec 13) 3 72 (zeroInvF dst vs)
      (by decide) (by omega) (by omega) (by decide)
      (fun n => pcFree_zeroInvF dst vs n)
      (by code_mem)
      (fun n hn => zeroLoopBody_spec dst vs hlen n hn)
    rw [show (0x80033e2C : Word) + 4 = (0x80033e30 : Word) from by decide] at h
    exact h
  have hstart : zeroInvF dst vs 72
      = ((.x10 ↦ᵣ dst) ** dwordsIs dst vs) := by
    unfold zeroInvF
    rw [show (72 - 72 : Nat) = 0 from rfl, show (8 * 0 : Nat) = 0 from rfl,
        add_ofNat_zero, List.replicate_zero, List.drop_zero, List.nil_append]
  have hend : zeroInvF dst vs 0
      = ((.x10 ↦ᵣ (dst + BitVec.ofNat 64 576))
          ** dwordsIs dst (List.replicate 72 (0 : Word))) := by
    unfold zeroInvF
    rw [show (72 - 0 : Nat) = 72 from rfl, show (8 * 72 : Nat) = 576 from rfl,
        show vs.drop 72 = [] from by rw [← hlen]; exact List.drop_length,
        List.append_nil]
  rw [hstart, hend] at hloop
  have hloopF := cpsTripleWithin_frameR ((.x1 : Reg) ↦ᵣ ret) (by pcf) hloop
  -- ret
  have hret := Fn.jalr_ret_spec (0x80033e30 : Word) ret halign
    (P := (.x10 ↦ᵣ (dst + BitVec.ofNat 64 576)) ** (.x7 ↦ᵣ BitVec.ofNat 64 0)
      ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs dst (List.replicate 72 (0 : Word)))
    (by pcf)
  have hretC := liftCode (cr' := blqCr) hret (by code_mem)
  -- chain
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hloopF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hretC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) s2

-- ============================================================================
-- The caller: `blq_set_one` via the frame + cross-call composition.
-- ============================================================================

/-- Entry values of the saved registers. -/
def setOneVals (ret arb8 : Word) : Reg → Word :=
  fun r => match r with | .x1 => ret | .x8 => arb8 | _ => 0

/-- Post-body values: `ra` holds the call's link address (genuinely
    clobbered by the `jal`; the epilogue restores it from the slot), `s0`
    the buffer pointer. -/
def setOneVals' (dst : Word) : Reg → Word :=
  fun r => match r with | .x1 => (0x80033e48 : Word) | .x8 => dst | _ => 0

/-- **The whole-routine ABI contract for `blq_set_one`.**  On return `sp`,
    `ra`, and `s0` are restored to ENTRY values (`ra` was clobbered by the
    real cross-call; `s0` by the body), and the FQ12 at the entry `a0` holds
    ONE: dword 0 = 1, dwords 1–71 = 0 — the genuine, unweakened semantics.
    `a0` ends at `dst + 576` exactly as `blq_zero` leaves it. -/
theorem blqSetOneFrame_spec (sp0 ret dst arb8 v5 v7 : Word) (vs : List Word)
    (hlen : vs.length = 72)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      (1 + setOneFrame.length + (1 + (1 + (1 + 72 * (3 + 1) + 1)) + 1 + 1)
        + setOneFrame.length + 1 + 1)
      (0x80033e34 : Word) ret blqCr
      ((.x2 ↦ᵣ sp0) ** regsAt setOneFrame (setOneVals ret arb8)
        ** frameSlotsOwn setOneFrame (sp0 + signExtend12 (-16 : BitVec 12))
        ** ((.x10 ↦ᵣ dst) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7)
          ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs dst vs))
      ((.x2 ↦ᵣ sp0) ** regsAt setOneFrame (setOneVals ret arb8)
        ** frameSlotsSaved setOneFrame (sp0 + signExtend12 (-16 : BitVec 12))
            (setOneVals ret arb8)
        ** ((.x10 ↦ᵣ (dst + BitVec.ofNat 64 576)) ** regOwn .x5 ** regOwn .x7
          ** (Reg.x0 ↦ᵣ (0 : Word))
          ** dwordsIs dst ((1 : Word) :: List.replicate 71 (0 : Word)))) := by
  -- ---- the single-exit body: mv ; call ; li ; sd ----
  -- mv s0, a0 (0x80033e40)
  have hmv := mv_spec_gen_within .x8 .x10 dst arb8 (0x80033e40 : Word) (by decide)
  rw [show (0x80033e40 : Word) + 4 = (0x80033e44 : Word) from by decide] at hmv
  have hmvC := liftCode (cr' := blqCr) hmv (by code_mem)
  have hmvF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** dwordsIs dst vs)
    (by pcf) hmvC
  -- jal ra, blq_zero (0x80033e44): the cross-call.
  have hcallee := blqZeroFlat_spec ((0x80033e44 : Word) + 4) dst v7 vs hlen (by decide)
  have hcall := callWithin_spec (0x80033e44 : Word) (0x80033e1c : Word) ret
    (jalOff GuestAddrs.blq_zero (GuestAddrs.blq_set_one + 16)) (1 + 72 * (3 + 1) + 1)
    (by decide) (by code_mem) (by pcf) hcallee
  rw [show (0x80033e44 : Word) + 4 = (0x80033e48 : Word) from by decide] at hcall
  have hcallF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ dst) ** (.x5 ↦ᵣ v5)) (by pcf) hcall
  -- li t0, 1 (0x80033e48)
  have hli := li_spec_gen_within .x5 v5 (1 : Word) (0x80033e48 : Word) (by decide)
  rw [show (0x80033e48 : Word) + 4 = (0x80033e4C : Word) from by decide] at hli
  have hliC := liftCode (cr' := blqCr) hli (by code_mem)
  have hliF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ (0x80033e48 : Word)) ** (.x8 ↦ᵣ dst)
      ** (.x10 ↦ᵣ (dst + BitVec.ofNat 64 576)) ** (.x7 ↦ᵣ BitVec.ofNat 64 0)
      ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs dst (List.replicate 72 (0 : Word)))
    (by pcf) hliC
  -- sd t0 -> 0(s0) (0x80033e4C): coefficient 0 := 1.
  obtain ⟨front, rest, hf, hr, heq1, heq2⟩ :=
    dwordsIs_at_set dst (List.replicate 72 (0 : Word)) 0 1 (by decide)
  have hcell0 : dst + BitVec.ofNat 64 (8 * 0) = dst := by
    rw [show (8 * 0 : Nat) = 0 from rfl]
    exact add_ofNat_zero dst
  rw [hcell0] at heq1 heq2
  have hone : (List.replicate 72 (0 : Word)).set 0 1
      = ((1 : Word) :: List.replicate 71 (0 : Word)) := by decide
  rw [hone] at heq2
  have hsd := sd_spec_gen_within .x8 .x5 dst (1 : Word)
    ((List.replicate 72 (0 : Word)).getD 0 0) (0 : BitVec 12) (0x80033e4C : Word)
  rw [add_sext0] at hsd
  rw [show (0x80033e4C : Word) + 4 = (0x80033e50 : Word) from by decide] at hsd
  have hsdC := liftCode (cr' := blqCr) hsd (by code_mem)
  have hsdF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ (0x80033e48 : Word))
      ** (.x10 ↦ᵣ (dst + BitVec.ofNat 64 576)) ** (.x7 ↦ᵣ BitVec.ofNat 64 0)
      ** (Reg.x0 ↦ᵣ (0 : Word)) ** front ** rest)
    (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hf
        | exact hr) hsdC
  -- chain: mv ; call ; li ; sd
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmvF hcallF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hliF
  have s3 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [heq1] at hp; xperm_hyp hp) s2 hsdF
  -- the single-exit body triple, in `abiFrame_spec` shape
  have hbody : cpsTripleWithin (1 + (1 + (1 + 72 * (3 + 1) + 1)) + 1 + 1)
      ((0x80033e34 : Word) + BitVec.ofNat 64 (4 * (1 + setOneFrame.length)))
      ((0x80033e34 : Word)
        + BitVec.ofNat 64 (4 * (1 + setOneFrame.length + setOneBody.length)))
      blqCr
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-16 : BitVec 12)))
        ** regsAt setOneFrame (setOneVals ret arb8)
        ** frameSlotsSaved setOneFrame (sp0 + signExtend12 (-16 : BitVec 12))
            (setOneVals ret arb8)
        ** ((.x10 ↦ᵣ dst) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7)
          ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs dst vs))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-16 : BitVec 12)))
        ** regsAt setOneFrame (setOneVals' dst)
        ** frameSlotsSaved setOneFrame (sp0 + signExtend12 (-16 : BitVec 12))
            (setOneVals ret arb8)
        ** ((.x10 ↦ᵣ (dst + BitVec.ofNat 64 576)) ** regOwn .x5 ** regOwn .x7
          ** (Reg.x0 ↦ᵣ (0 : Word))
          ** dwordsIs dst ((1 : Word) :: List.replicate 71 (0 : Word)))) := by
    have hentry : (0x80033e34 : Word) + BitVec.ofNat 64 (4 * (1 + setOneFrame.length))
        = (0x80033e40 : Word) := by decide
    have hexit : (0x80033e34 : Word)
          + BitVec.ofNat 64 (4 * (1 + setOneFrame.length + setOneBody.length))
        = (0x80033e50 : Word) := by decide
    rw [hentry, hexit]
    simp only [setOneFrame, regsAt, frameSlotsSaved, setOneVals, setOneVals',
      List.foldr_cons, List.foldr_nil, sepConj_emp_right']
    have hchainF := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-16 : BitVec 12)))
        ** (((sp0 + signExtend12 (-16 : BitVec 12))
              + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
        ** (((sp0 + signExtend12 (-16 : BitVec 12))
              + signExtend12 (8 : BitVec 12)) ↦ₘ arb8))
      (by pcf) s3
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_)
      hchainF
    -- release t0 (`↦ 1`) and the drained counter (`↦ 0`) to ownership;
    -- reassemble the ONE array from the extracted cell.
    have hq1 : ((.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ BitVec.ofNat 64 0)
        ** ((.x1 : Reg) ↦ᵣ (0x80033e48 : Word)) ** (.x8 ↦ᵣ dst)
        ** (.x10 ↦ᵣ (dst + BitVec.ofNat 64 576)) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** dwordsIs dst ((1 : Word) :: List.replicate 71 (0 : Word))
        ** (.x2 ↦ᵣ (sp0 + signExtend12 (-16 : BitVec 12)))
        ** (((sp0 + signExtend12 (-16 : BitVec 12))
              + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
        ** (((sp0 + signExtend12 (-16 : BitVec 12))
              + signExtend12 (8 : BitVec 12)) ↦ₘ arb8)) h := by
      rw [heq2]
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x7 _) (fun _ hh => hh)) h hq1
    xperm_hyp hq2
  rw [show (1 + setOneFrame.length + (1 + (1 + (1 + 72 * (3 + 1) + 1)) + 1 + 1)
        + setOneFrame.length + 1 + 1 : Nat)
      = 1 + setOneFrame.length + (1 + (1 + (1 + 72 * (3 + 1) + 1)) + 1 + 1)
        + setOneFrame.length + 1 + 1 from rfl]
  abi_frame (16 : BitVec 12) halign hbody


end Bls12Fq12SetOneSAsm

end EvmAsm.Codegen
