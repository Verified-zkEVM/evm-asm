/-
  EvmAsm.Codegen.Programs.Bn254CallAllotmentSAsm

  `bn254_call_allotment` — the EIP-150 child gas allotment for a
  precompile call — via TWO `retJoinStation_spec` forward joins to the
  routine's single shared `ret` (`EvmAsm/Rv64/SAsm/RetForwardJoin.lean`).

  The routine (see `Bn254Curve.lean`):

  ```
        ld   a7, 568(s4)              -- remaining = dispatcher gas cell
        srli s6, a7, 6
        sub  s6, a7, s6               -- cap = remaining - remaining/64
        ld   s7, 8(a2) ; ld s8, 16(a2) ; or s7, s7, s8
        ld   s8, 24(a2) ; or s7, s7, s8   -- high-limb OR of the gas word
        bne  s7, x0, .ret             -- any high limb set → keep cap
        ld   s7, 0(a2)                -- low limb
        bgeu s7, s6, .ret             -- low ≥ cap → keep cap
        mv   s6, s7                   -- else allot the requested gas
  .ret: ret
  ```

  Both guards jump FORWARD to the one shared `ret` — each is one
  `retJoinStation_spec`; the straight-line prefix is per-instruction
  `spec_gen` lemmas over the five owned dword cells (the 32-byte
  LE-limb stack word at `a2` and the dispatcher gas cell at `568(s4)`).

  **Genuine post**: `x22 = bn254Allotment w0 w1 w2 w3 rem` — the REAL
  EIP-150 rule `min(gas word, remaining - remaining/64)` where any
  nonzero high limb caps at the 63/64 send limit; `a2`/`s4` and all
  five memory cells untouched (`x17`/`x23`/`x24` are the documented
  clobbers).

  Byte-transparent: stated at the `#guard`-tied symbolic
  `GuestAddrs.bn254_call_allotment` base (bead evm-asm-6agnq) over the
  emitted `bn254CallAllotment_prog` directly — no guest-byte change,
  no A/B run needed.

  Bead: evm-asm-4ch8f.57.3.
-/

import EvmAsm.Codegen.Programs.Bn254Curve
import EvmAsm.Rv64.SAsm.RetForwardJoin
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace Bn254CallAllotmentSAsm

/-- The routine base, symbolic (bead evm-asm-6agnq). -/
def allotBase : Word := (GuestAddrs.bn254_call_allotment : Word)

#guard bn254CallAllotment_prog.length = 13
-- The routine is position-independent (no PC-relative instruction).

/-
  Emitted layout relative to `GuestAddrs.bn254_call_allotment`:
    +0   ld    x17, 568(x20)
    +4   srli  x22, x17, 6
    +8   sub   x22, x17, x22
    +12  ld    x23, 8(x12)
    +16  ld    x24, 16(x12)
    +20  or    x23, x23, x24
    +24  ld    x24, 24(x12)
    +28  or    x23, x23, x24
    +32  bne   x23, x0, +16 → +48 (ret)
    +36  ld    x23, 0(x12)
    +40  bgeu  x23, x22, +8 → +48 (ret)
    +44  mv    x22, x23
    +48  jalr  x0, x1, 0
-/

/-! ## The routine's semantics -/

/-- The EIP-150 63/64 send limit: `remaining - remaining/64`. -/
def allotCap (rem : Word) : Word := rem - (rem >>> 6)

/-- The child allotment: the requested gas word (LE u64 limbs
    `w0 … w3`) capped at the 63/64 limit — any nonzero high limb, or a
    low limb at/above the cap, allots the cap; otherwise the request. -/
def bn254Allotment (w0 w1 w2 w3 rem : Word) : Word :=
  if (w1 ||| w2) ||| w3 = 0 then
    (if BitVec.ult w0 (allotCap rem) then w0 else allotCap rem)
  else allotCap rem

/-! ## The whole routine -/

/-- **`bn254_call_allotment` at its linked address** (genuine post):
    `x22 = bn254Allotment w0 w1 w2 w3 rem`; the gas-word pointer `a2`,
    the dispatcher base `s4` and all five memory cells untouched;
    `x17`/`x23`/`x24` are the documented clobbers (returned as owned). -/
theorem bn254CallAllotment_spec (gp sp ret : Word) (w0 w1 w2 w3 rem : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 13 allotBase ret
      (CodeReq.ofProg allotBase bn254CallAllotment_prog)
      (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x17 ** regOwn .x22 ** regOwn .x23 ** regOwn .x24 **
       ((gp + 568) ↦ₘ rem) **
       (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
       ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
      (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x17 ** ((.x22 : Reg) ↦ᵣ bn254Allotment w0 w1 w2 w3 rem) **
       regOwn .x23 ** regOwn .x24 **
       ((gp + 568) ↦ₘ rem) **
       (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
       ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3)) := by
  set CR := CodeReq.ofProg allotBase bn254CallAllotment_prog with hCR
  set cap := allotCap rem with hcap
  set hi := (w1 ||| w2) ||| w3 with hhi
  -- peel the scratch registers
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [regOwns_cons, regOwns_nil, sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns [.x17, .x22, .x23, .x24] (by decide)
      (P := ((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((gp + 568) ↦ₘ rem) **
        (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
        ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
      (fun vf => ?_))
  simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
  -- the shared post, reached by every arm
  set POST : Assertion :=
    ((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
    ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    regOwn .x17 ** ((.x22 : Reg) ↦ᵣ bn254Allotment w0 w1 w2 w3 rem) **
    regOwn .x23 ** regOwn .x24 **
    ((gp + 568) ↦ₘ rem) **
    (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
    ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3) with hPOST
  -- ---- straight-line prefix (+0 … +28) ----
  have hld17 := liftCode (cr' := CR)
    (ld_spec_gen_within .x17 .x20 gp (vf .x17) rem (568 : BitVec 12)
      allotBase (by decide))
    (by rw [hCR]; code_mem)
  rw [show signExtend12 (568 : BitVec 12) = (568 : Word) from by decide,
      show (allotBase : Word) + 4 = (allotBase + 4 : Word) from by decide]
    at hld17
  have hsrli := liftCode (cr' := CR)
    (srli_spec_gen_within .x22 .x17 (vf .x22) rem (6 : BitVec 6)
      (allotBase + 4) (by decide))
    (by rw [hCR]; code_mem)
  rw [show ((6 : BitVec 6)).toNat = 6 from rfl,
      show (allotBase + 4 : Word) + 4 = (allotBase + 8 : Word) from by decide]
    at hsrli
  have hsub := liftCode (cr' := CR)
    (sub_spec_gen_rd_eq_rs2_within .x22 .x17 rem (rem >>> 6)
      (allotBase + 8) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (allotBase + 8 : Word) + 4 = (allotBase + 12 : Word) from by decide]
    at hsub
  have hld23 := liftCode (cr' := CR)
    (ld_spec_gen_within .x23 .x12 sp (vf .x23) w1 (8 : BitVec 12)
      (allotBase + 12) (by decide))
    (by rw [hCR]; code_mem)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
      show (allotBase + 12 : Word) + 4 = (allotBase + 16 : Word) from by decide]
    at hld23
  have hld24 := liftCode (cr' := CR)
    (ld_spec_gen_within .x24 .x12 sp (vf .x24) w2 (16 : BitVec 12)
      (allotBase + 16) (by decide))
    (by rw [hCR]; code_mem)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
      show (allotBase + 16 : Word) + 4 = (allotBase + 20 : Word) from by decide]
    at hld24
  have hor1 := liftCode (cr' := CR)
    (or_spec_gen_rd_eq_rs1_within .x23 .x24 w1 w2
      (allotBase + 20) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (allotBase + 20 : Word) + 4 = (allotBase + 24 : Word) from by decide]
    at hor1
  have hld24b := liftCode (cr' := CR)
    (ld_spec_gen_within .x24 .x12 sp w2 w3 (24 : BitVec 12)
      (allotBase + 24) (by decide))
    (by rw [hCR]; code_mem)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
      show (allotBase + 24 : Word) + 4 = (allotBase + 28 : Word) from by decide]
    at hld24b
  have hor2 := liftCode (cr' := CR)
    (or_spec_gen_rd_eq_rs1_within .x23 .x24 (w1 ||| w2) w3
      (allotBase + 28) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (allotBase + 28 : Word) + 4 = (allotBase + 32 : Word) from by decide]
    at hor2
  -- frames for the prefix
  have hld17F := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ sp) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x22 : Reg) ↦ᵣ vf .x22) ** ((.x23 : Reg) ↦ᵣ vf .x23) **
      ((.x24 : Reg) ↦ᵣ vf .x24) **
      (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
      ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
    (by pcf) hld17
  have hsrliF := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x23 : Reg) ↦ᵣ vf .x23) ** ((.x24 : Reg) ↦ᵣ vf .x24) **
      ((gp + 568) ↦ₘ rem) **
      (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
      ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
    (by pcf) hsrli
  have hsubF := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x23 : Reg) ↦ᵣ vf .x23) ** ((.x24 : Reg) ↦ᵣ vf .x24) **
      ((gp + 568) ↦ₘ rem) **
      (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
      ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
    (by pcf) hsub
  have hld23F := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ gp) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
      ((.x24 : Reg) ↦ᵣ vf .x24) **
      ((gp + 568) ↦ₘ rem) **
      (sp ↦ₘ w0) ** ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
    (by pcf) hld23
  have hld24F := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ gp) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
      ((.x23 : Reg) ↦ᵣ w1) **
      ((gp + 568) ↦ₘ rem) **
      (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) ** ((sp + 24) ↦ₘ w3))
    (by pcf) hld24
  have hor1F := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
      ((gp + 568) ↦ₘ rem) **
      (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
      ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
    (by pcf) hor1
  have hld24bF := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ gp) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
      ((.x23 : Reg) ↦ᵣ (w1 ||| w2)) **
      ((gp + 568) ↦ₘ rem) **
      (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) ** ((sp + 16) ↦ₘ w2))
    (by pcf) hld24b
  have hor2F := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
      ((gp + 568) ↦ₘ rem) **
      (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
      ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
    (by pcf) hor2
  -- ---- the shared ret (+48), one arm per x22 value ----
  have hret : ∀ x22v x23v x24v : Word,
      x22v = bn254Allotment w0 w1 w2 w3 rem →
      cpsTripleWithin 1 (allotBase + 48) ret CR
        (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ x22v) **
          ((.x23 : Reg) ↦ᵣ x23v) ** ((.x24 : Reg) ↦ᵣ x24v) **
          ((gp + 568) ↦ₘ rem) **
          (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
          ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
        POST := by
    intro x22v x23v x24v hx22
    have h := cpsTripleWithin_extend_code (cr' := CR)
      (hmono := by rw [hCR]; code_mem)
      (h := EvmAsm.Evm64.ret_spec_within' (allotBase + 48) ret)
    rw [halignRet] at h
    have hF := cpsTripleWithin_frameR
      (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ x22v) **
        ((.x23 : Reg) ↦ᵣ x23v) ** ((.x24 : Reg) ↦ᵣ x24v) **
        ((gp + 568) ↦ₘ rem) **
        (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
        ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
      (by pcf) h
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ?_) hF
    rw [hPOST, ← hx22]
    have hq1 : (((.x17 : Reg) ↦ᵣ rem) ** (((.x23 : Reg) ↦ᵣ x23v) **
        (((.x24 : Reg) ↦ᵣ x24v) **
          (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
           ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((.x22 : Reg) ↦ᵣ x22v) **
           ((gp + 568) ↦ₘ rem) **
           (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
           ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x17 _)
      (sepConj_mono (regIs_to_regOwn .x23 _)
        (sepConj_mono (regIs_to_regOwn .x24 _)
          (fun _ hh => hh))) h hq1
    xperm_hyp hq2
  -- ---- the low-limb guard (+36 … +44) into the shared ret ----
  have hlow : hi = 0 →
      cpsTripleWithin 4 (allotBase + 36) ret CR
        (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
          ((.x23 : Reg) ↦ᵣ hi) ** ((.x24 : Reg) ↦ᵣ w3) **
          ((gp + 568) ↦ₘ rem) **
          (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
          ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
        POST := by
    intro hhiz
    -- ld x23, 0(x12)
    have hld := liftCode (cr' := CR)
      (ld_spec_gen_within .x23 .x12 sp hi w0 (0 : BitVec 12)
        (allotBase + 36) (by decide))
      (by rw [hCR]; code_mem)
    rw [show sp + signExtend12 (0 : BitVec 12) = sp from by
          rw [signExtend12_0]; bv_omega,
        show (allotBase + 36 : Word) + 4 = (allotBase + 40 : Word) from by decide]
      at hld
    have hldF := cpsTripleWithin_frameR
      (((.x20 : Reg) ↦ᵣ gp) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
        ((.x24 : Reg) ↦ᵣ w3) **
        ((gp + 568) ↦ₘ rem) **
        ((sp + 8) ↦ₘ w1) ** ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
      (by pcf) hld
    -- bgeu x23, x22 (+40)
    have hbrGe := cpsBranchWithin_frameR
      (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x17 : Reg) ↦ᵣ rem) ** ((.x24 : Reg) ↦ᵣ w3) **
        ((gp + 568) ↦ₘ rem) **
        (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
        ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
      (by pcf)
      (cpsBranchWithin_extend_code (cr' := CR)
        (h := bgeu_spec_gen_within .x23 .x22 (8 : BitVec 13) w0
          (rem - rem >>> 6) (allotBase + 40))
        (hmono := by rw [hCR]; code_mem))
    rw [show (allotBase + 40 : Word) + signExtend13 (8 : BitVec 13)
          = (allotBase + 48 : Word) from by decide,
        show (allotBase + 40 : Word) + 4 = (allotBase + 44 : Word) from by decide]
      at hbrGe
    -- ge arm: keep the cap
    have hge : ¬ BitVec.ult w0 (rem - rem >>> 6) →
        cpsTripleWithin 2 (allotBase + 48) ret CR
          (((.x23 : Reg) ↦ᵣ w0) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
            (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
             ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
             ((.x17 : Reg) ↦ᵣ rem) ** ((.x24 : Reg) ↦ᵣ w3) **
             ((gp + 568) ↦ₘ rem) **
             (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
             ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3)))
          POST := by
      intro hnlt
      have hx22 : (rem - rem >>> 6) = bn254Allotment w0 w1 w2 w3 rem := by
        unfold bn254Allotment allotCap
        rw [← hhi, if_pos hhiz, if_neg hnlt]
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
          (fun _ hq => hq)
          (hret (rem - rem >>> 6) w0 w3 hx22))
    -- lt arm: mv x22, x23 then ret
    have hlt : BitVec.ult w0 (rem - rem >>> 6) →
        cpsTripleWithin 2 (allotBase + 44) ret CR
          (((.x23 : Reg) ↦ᵣ w0) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
            (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
             ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
             ((.x17 : Reg) ↦ᵣ rem) ** ((.x24 : Reg) ↦ᵣ w3) **
             ((gp + 568) ↦ₘ rem) **
             (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
             ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3)))
          POST := by
      intro hltc
      have hmv := liftCode (cr' := CR)
        (mv_spec_gen_within .x22 .x23 w0 (rem - rem >>> 6)
          (allotBase + 44) (by decide))
        (by rw [hCR]; code_mem)
      rw [show (allotBase + 44 : Word) + 4 = (allotBase + 48 : Word) from by decide]
        at hmv
      have hmvF := cpsTripleWithin_frameR
        (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x17 : Reg) ↦ᵣ rem) ** ((.x24 : Reg) ↦ᵣ w3) **
          ((gp + 568) ↦ₘ rem) **
          (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
          ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
        (by pcf) hmv
      have hx22 : w0 = bn254Allotment w0 w1 w2 w3 rem := by
        unfold bn254Allotment allotCap
        rw [← hhi, if_pos hhiz, if_pos hltc]
      have hc := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hmvF
        (hret w0 w0 w3 hx22)
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) hc
    -- the low-limb station
    have hstGe := retJoinStation_spec
      (cond := ¬ BitVec.ult w0 (rem - rem >>> 6))
      (PT := ((.x23 : Reg) ↦ᵣ w0) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
        (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         ((.x17 : Reg) ↦ᵣ rem) ** ((.x24 : Reg) ↦ᵣ w3) **
         ((gp + 568) ↦ₘ rem) **
         (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
         ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3)))
      (PF := ((.x23 : Reg) ↦ᵣ w0) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
        (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         ((.x17 : Reg) ↦ᵣ rem) ** ((.x24 : Reg) ↦ᵣ w3) **
         ((gp + 568) ↦ₘ rem) **
         (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
         ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3)))
      hbrGe
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by
        have hq1 : (⌜BitVec.ult w0 (rem - rem >>> 6)⌝ **
            (((.x23 : Reg) ↦ᵣ w0) **
             ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
             ((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
             ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
             ((.x17 : Reg) ↦ᵣ rem) ** ((.x24 : Reg) ↦ᵣ w3) **
             ((gp + 568) ↦ₘ rem) **
             (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
             ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))) h := by
          xperm_hyp hq
        obtain ⟨hltc, hrest⟩ := (sepConj_pure_left h).1 hq1
        exact (sepConj_pure_left h).2 ⟨fun hn => hn hltc, hrest⟩)
      (fun hnlt => hge hnlt)
      (fun hnn => hlt (not_not.mp hnn))
    -- ld ; station
    have hc := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hldF hstGe
    exact cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) hc)
  -- ---- the high-limb guard (BNE at +32) ----
  have hbrHi := cpsBranchWithin_frameR
    (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
      ((.x1 : Reg) ↦ᵣ ret) **
      ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
      ((.x24 : Reg) ↦ᵣ w3) **
      ((gp + 568) ↦ₘ rem) **
      (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
      ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bne_spec_gen_within .x23 .x0 (16 : BitVec 13) hi (0 : Word)
        (allotBase + 32))
      (hmono := by rw [hCR]; code_mem))
  rw [show (allotBase + 32 : Word) + signExtend13 (16 : BitVec 13)
        = (allotBase + 48 : Word) from by decide,
      show (allotBase + 32 : Word) + 4 = (allotBase + 36 : Word) from by decide]
    at hbrHi
  -- taken arm: keep the cap
  have hhiTail : hi ≠ 0 →
      cpsTripleWithin 4 (allotBase + 48) ret CR
        (((.x23 : Reg) ↦ᵣ hi) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
           ((.x1 : Reg) ↦ᵣ ret) **
           ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
           ((.x24 : Reg) ↦ᵣ w3) **
           ((gp + 568) ↦ₘ rem) **
           (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
           ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3)))
        POST := by
    intro hne
    have hx22 : (rem - rem >>> 6) = bn254Allotment w0 w1 w2 w3 rem := by
      unfold bn254Allotment allotCap
      rw [← hhi, if_neg hne]
    exact cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ hq => hq)
        (hret (rem - rem >>> 6) hi w3 hx22))
  -- the high-limb station
  have hstHi := retJoinStation_spec
    (cond := hi ≠ (0 : Word))
    (PT := ((.x23 : Reg) ↦ᵣ hi) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((.x1 : Reg) ↦ᵣ ret) **
       ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
       ((.x24 : Reg) ↦ᵣ w3) **
       ((gp + 568) ↦ₘ rem) **
       (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
       ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3)))
    (PF := ((.x23 : Reg) ↦ᵣ hi) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((.x1 : Reg) ↦ᵣ ret) **
       ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
       ((.x24 : Reg) ↦ᵣ w3) **
       ((gp + 568) ↦ₘ rem) **
       (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
       ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3)))
    hbrHi
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by
      have hq1 : (⌜hi = (0 : Word)⌝ **
          (((.x23 : Reg) ↦ᵣ hi) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((.x20 : Reg) ↦ᵣ gp) ** ((.x12 : Reg) ↦ᵣ sp) **
           ((.x1 : Reg) ↦ᵣ ret) **
           ((.x17 : Reg) ↦ᵣ rem) ** ((.x22 : Reg) ↦ᵣ (rem - rem >>> 6)) **
           ((.x24 : Reg) ↦ᵣ w3) **
           ((gp + 568) ↦ₘ rem) **
           (sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
           ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3))) h := by
        xperm_hyp hq
      obtain ⟨hz, hrest⟩ := (sepConj_pure_left h).1 hq1
      exact (sepConj_pure_left h).2 ⟨fun hn => hn hz, hrest⟩)
    (fun hne => hhiTail hne)
    (fun hnn => by
      have hz : hi = 0 := not_not.mp hnn
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ hq => hq) (hlow hz))
  -- ---- assemble the straight-line prefix into the station ----
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hld17F hsrliF
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc1 hsubF
  have hc3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc2 hld23F
  have hc4 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc3 hld24F
  have hc5 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc4 hor1F
  have hc6 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc5 hld24bF
  have hc7 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc6 hor2F
  have hc8 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by rw [hhi]; xperm_hyp hp) hc7 hstHi
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by rw [hPOST] at hq; xperm_hyp hq)
    (cpsTripleWithin_mono_nSteps (by omega) hc8)


end Bn254CallAllotmentSAsm

end EvmAsm.Codegen
