/-
  EvmAsm.Codegen.Programs.Secp256k1PointDoubleSAsm

  `secp256k1_point_double` via the **multi-RW-subwindow callee adapter**
  plus the **inline CSR-2052 curve accelerator** (bead evm-asm-4ch8f.38.5,
  closing the inline-CSRS half; the converter+arithMod half landed as
  `bnf_mul_mod_p`, #10069).

  The routine is an sp-frame (`ra`/`s0`/`s1`) with ONE branch: after
  `secf_is_zero32` on the input `y` coordinate it either

  ```
    (y = 0, the 2-torsion / infinity case)
      secf_zero32(out) ; secf_zero32(out+32) ; a0 := 1
    (y ≠ 0, the accelerator case)
      secf_be_to_le(in,    secc_le_p1)        -- stage x, LE
      secf_be_to_le(in+32, secc_le_p1+32)     -- stage y, LE
      csrs 2052, &secc_le_p1                  -- Secp256k1Dbl in place
      secf_le_to_be(secc_le_p1,    out)       -- out.x, BE
      secf_le_to_be(secc_le_p1+32, out+32)    -- out.y, BE
      a0 := 0
  ```

  both paths re-joining at the shared epilogue.  Because the two paths
  exit the body with different `ra` values, the proof CASE-SPLITS on the
  (decidable) branch condition `beBytesToNat yBE = 0`: under either
  hypothesis the branch resolves deterministically
  (`cpsBranchWithin_takenPath`/`_ntakenPath` — the dead side carries a
  contradictory pure fact), the body is a straight line, and one
  `abiFrame_spec` instance per case closes the SAME whole-routine
  conclusion with a disjunctive genuine post.

  **Genuine post** (`pointDouble_spec`): either `y = 0` and the output is
  the 64-byte zero point with `a0 = 1` (staging arena untouched), or
  `y ≠ 0` and the output BE-encodes `Accel.curveDbl secpP x y` — the REAL
  tangent-doubling semantic of the ziskemu accelerator — with `a0 = 0`
  and the staging arena holding the accelerator's LE wire image.
  `sp`/`ra`/`s0`/`s1` restored; inputs framed.  Byte-transparent: the
  emitted `secp256k1PointDouble_prog` IS `abiFrameProg (-32)/(+32)` over
  the body (kernel-checked `rfl`, `pdProg_tie`), at the `#guard`-tied
  `GuestAddrs`.
-/

import EvmAsm.Codegen.Programs.Secp256k1PointDoubleSAsmReg

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Secp256k1PointDoubleSAsm

open Secp256k1FieldConvSAsm (secfBeToLeFn)
open Secp256k1FieldLeToBeSAsm (secfLeToBeFn)
open Secp256k1FieldIsZeroSAsm (secfIsZero32Fn)
open Secp256k1FieldLeavesSAsm (secfZero32Fn)
open EvmAsm.Rv64.SAsm.WhileBreakDemo (nlz nlz_le nlz_spec nlz_boundary)

-- ============================================================================
-- The whole-routine contract
-- ============================================================================

/-- **`secp256k1_point_double` at its linked address** (genuine post):
    either the input `y` is zero and the output is the zeroed point with
    `a0 = 1` (staging arena untouched), or `y ≠ 0` and the output
    BE-encodes `Accel.curveDbl secpP x y` — the accelerator's real affine
    tangent doubling — with `a0 = 0` and the arena holding its LE wire
    image.  `sp`/`ra`/`s0`/`s1` restored to entry; inputs framed.  The
    `x0 ↦ᵣ 0` atom rides through (the branch reads it). -/
theorem pointDouble_spec (sp0 inPtr outPtr ret v8 v9 : Word)
    (xBE yBE oX oY ws : List (BitVec 8))
    (hxlen : xBE.length = 32) (hylen : yBE.length = 32)
    (hoXlen : oX.length = 32) (hoYlen : oY.length = 32)
    (hwslen : ws.length = 64)
    (hwfX : Region.wf ⟨inPtr, xBE⟩) (hwfY : Region.wf ⟨inPtr + 32, yBE⟩)
    (hoal : outPtr.toNat % 8 = 0) (hoov : outPtr.toNat + 64 < 2 ^ 64)
    (hovalid : ∀ k, k < 64 → isValidMemAddr (outPtr + BitVec.ofNat 64 k) = true)
    (harval : ∀ j, j < 64 → isValidMemAddr (arenaB + BitVec.ofNat 64 j) = true)
    (hdIn : inPtr.toNat + 64 ≤ (0xa3c05618 : Nat)
      ∨ (0xa3c05658 : Nat) ≤ inPtr.toNat)
    (hdOut : outPtr.toNat + 64 ≤ (0xa3c05618 : Nat)
      ∨ (0xa3c05658 : Nat) ≤ outPtr.toNat)
    (hxlt : beBytesToNat xBE < Accel.secpP)
    (hylt : beBytesToNat yBE < Accel.secpP)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      (1 + pdFrame.length
        + (27 + ((secfIsZero32Fn 0 []).body.steps + 1)
            + ((secfBeToLeFn 0 0 [] []).body.steps + 1) * 2
            + ((secfLeToBeFn 0 0 [] []).body.steps + 1) * 2
            + ((secfZero32Fn 0 []).body.steps + 1) * 2)
        + pdFrame.length + 1 + 1)
      (GuestAddrs.secp256k1_point_double : Word) ret pdCr
      ((.x2 ↦ᵣ sp0) ** regsAt pdFrame (pdVals ret v8 v9)
        ** frameSlotsOwn pdFrame (sp0 + signExtend12 (-32 : BitVec 12))
        ** (((.x0 : Reg) ↦ᵣ (0 : Word))
          ** ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr)
          ** regOwns convScratch
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
          ** bytesRegion arenaB ws))
      ((.x2 ↦ᵣ sp0) ** regsAt pdFrame (pdVals ret v8 v9)
        ** frameSlotsSaved pdFrame (sp0 + signExtend12 (-32 : BitVec 12))
            (pdVals ret v8 v9)
        ** (fun hp =>
            ((⌜beBytesToNat yBE = 0⌝
              ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word))
              ** regOwns a0Rest
              ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
              ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))
              ** bytesRegion (outPtr + 32) (List.replicate 32 (0 : BitVec 8))
              ** bytesRegion arenaB ws) hp)
            ∨ (∃ oX' oY',
              ((⌜beBytesToNat yBE ≠ 0
                ∧ beBytesToNat oX' = (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)).1
                ∧ oX'.length = 32
                ∧ beBytesToNat oY' = (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)).2
                ∧ oY'.length = 32⌝
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word))
                ** regOwns a0Rest
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion outPtr oX' ** bytesRegion (outPtr + 32) oY'
                ** bytesRegion arenaB
                  (pairBytes 4 (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)))) hp)))) := by
  -- shared arithmetic facts
  have hinB : inPtr.toNat + 32 < 2 ^ 64 := by
    have h := hwfX.2.1
    rwa [hxlen] at h
  have hinT : ((inPtr + 32 : Word)).toNat = inPtr.toNat + 32 := by bv_omega
  have hin32B : ((inPtr + 32 : Word)).toNat + 32 < 2 ^ 64 := by
    have h := hwfY.2.1
    rwa [hylen] at h
  have houtT : ((outPtr + 32 : Word)).toNat = outPtr.toNat + 32 := by bv_omega
  have hrwwOut : RwRegion.wf ⟨outPtr, 32⟩ := by
    refine ⟨hoal, ?_, ?_⟩
    · show outPtr.toNat + 32 < 2 ^ 64
      omega
    · intro k hk
      have hk' : k < 32 := hk
      exact hovalid k (by omega)
  have hrwwOut32 : RwRegion.wf ⟨outPtr + 32, 32⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · show ((outPtr + 32 : Word)).toNat % 8 = 0
      rw [houtT]
      omega
    · show ((outPtr + 32 : Word)).toNat + 32 < 2 ^ 64
      rw [houtT]
      omega
    · intro k hk
      have hk' : k < 32 := hk
      rw [show (outPtr + 32 : Word) + BitVec.ofNat 64 k
          = outPtr + BitVec.ofNat 64 (32 + k) from by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
          show ((32 : Word)).toNat = 32 from rfl]
        omega]
      exact hovalid (32 + k) (by omega)
  by_cases hy0 : beBytesToNat yBE = 0
  · -- ======================================================================
    -- INFINITY PATH: y = 0 — zero the output, return 1, arena untouched.
    -- ======================================================================
    have hnlz : nlz yBE 32 = 32 := (nlz32_iff_zero yBE hylen).mpr hy0
    have hbody : cpsTripleWithin
        (27 + ((secfIsZero32Fn 0 []).body.steps + 1)
          + ((secfBeToLeFn 0 0 [] []).body.steps + 1) * 2
          + ((secfLeToBeFn 0 0 [] []).body.steps + 1) * 2
          + ((secfZero32Fn 0 []).body.steps + 1) * 2)
        ((GuestAddrs.secp256k1_point_double : Word) + BitVec.ofNat 64 (4 * (1 + pdFrame.length)))
        ((GuestAddrs.secp256k1_point_double : Word)
          + BitVec.ofNat 64 (4 * (1 + pdFrame.length + pdBody.length)))
        pdCr
        ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
          ** regsAt pdFrame (pdVals ret v8 v9)
          ** frameSlotsSaved pdFrame (sp0 + signExtend12 (-32 : BitVec 12))
              (pdVals ret v8 v9)
          ** (((.x0 : Reg) ↦ᵣ (0 : Word))
            ** ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr)
            ** regOwns convScratch
            ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
            ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
            ** bytesRegion arenaB ws))
        ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
          ** regsAt pdFrame (pdValsInf inPtr outPtr)
          ** frameSlotsSaved pdFrame (sp0 + signExtend12 (-32 : BitVec 12))
              (pdVals ret v8 v9)
          ** (fun hp =>
              ((⌜beBytesToNat yBE = 0⌝
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word))
                ** regOwns a0Rest
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))
                ** bytesRegion (outPtr + 32) (List.replicate 32 (0 : BitVec 8))
                ** bytesRegion arenaB ws) hp)
              ∨ (∃ oX' oY',
                ((⌜beBytesToNat yBE ≠ 0
                  ∧ beBytesToNat oX' = (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).1
                  ∧ oX'.length = 32
                  ∧ beBytesToNat oY' = (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).2
                  ∧ oY'.length = 32⌝
                  ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word))
                  ** regOwns a0Rest
                  ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                  ** bytesRegion outPtr oX' ** bytesRegion (outPtr + 32) oY'
                  ** bytesRegion arenaB
                    (pairBytes 4 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)))) hp)))) := by
      have hentry : (GuestAddrs.secp256k1_point_double : Word)
            + BitVec.ofNat 64 (4 * (1 + pdFrame.length))
          = ((GuestAddrs.secp256k1_point_double + 16) : Word) := by decide
      have hexit : (GuestAddrs.secp256k1_point_double : Word)
            + BitVec.ofNat 64 (4 * (1 + pdFrame.length + pdBody.length))
          = ((GuestAddrs.secp256k1_point_double + 148) : Word) := by decide
      rw [hentry, hexit]
      -- ---- mv s0,a0 ; mv s1,a1 ; addi a0,s0,32 ----
      have hm1 := liftCode (cr' := pdCr)
        (mv_spec_gen_within .x8 .x10 inPtr v8 ((GuestAddrs.secp256k1_point_double + 16) : Word) (by decide))
        (by code_mem)
      rw [show ((GuestAddrs.secp256k1_point_double + 16) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 20) : Word) from by decide]
        at hm1
      have hm2 := liftCode (cr' := pdCr)
        (mv_spec_gen_within .x9 .x11 outPtr v9 ((GuestAddrs.secp256k1_point_double + 20) : Word) (by decide))
        (by code_mem)
      rw [show ((GuestAddrs.secp256k1_point_double + 20) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 24) : Word) from by decide]
        at hm2
      have haddi := liftCode (cr' := pdCr)
        (addi_spec_gen_within .x10 .x8 inPtr inPtr (32 : BitVec 12)
          ((GuestAddrs.secp256k1_point_double + 24) : Word) (by decide))
        (by code_mem)
      rw [show ((GuestAddrs.secp256k1_point_double + 24) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 28) : Word) from by decide,
        show inPtr + signExtend12 (32 : BitVec 12) = inPtr + 32 from by
          rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]]
        at haddi
      -- ---- call secf_is_zero32(in+32) — verdict a0 = 1 (y = 0) ----
      have hcall1 := callWithin_spec ((GuestAddrs.secp256k1_point_double + 28) : Word) (GuestAddrs.secf_is_zero32 : Word)
        ret
        (jalOff GuestAddrs.secf_is_zero32 (GuestAddrs.secp256k1_point_double + 28))
        ((secfIsZero32Fn (inPtr + 32) yBE).body.steps + 1)
        (by decide) (by code_mem) (by pcf)
        (secfIsZero32Flat_spec ((GuestAddrs.secp256k1_point_double + 32) : Word) (inPtr + 32) yBE hylen
          hwfY (by omega) (by decide))
      rw [show ((GuestAddrs.secp256k1_point_double + 28) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 32) : Word) from by decide,
        show (secfIsZero32Fn (inPtr + 32) yBE).body.steps
          = (secfIsZero32Fn 0 []).body.steps from rfl,
        if_pos hnlz] at hcall1
      -- ---- beq a0, x0 — NOT taken (a0 = 1 ≠ 0) ----
      have hbeq := cpsBranchWithin_ntakenPath
        (cpsBranchWithin_extend_code (cr' := pdCr) (by code_mem)
          (beq_spec_gen_within .x10 .x0 (28 : BitVec 13) (1 : Word) (0 : Word)
            ((GuestAddrs.secp256k1_point_double + 32) : Word)))
        (fun hp hq => by
          have hq1 : ((⌜(1 : Word) = (0 : Word)⌝ : Assertion)
              ** ((.x10 ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))) hp := by
            xperm_hyp hq
          exact absurd ((sepConj_pure_left hp).mp hq1).1 (by decide))
      rw [show ((GuestAddrs.secp256k1_point_double + 32) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 36) : Word) from by decide]
        at hbeq
      -- ---- mv a0, s1 ; call secf_zero32(out) ----
      have hm3 := liftCode (cr' := pdCr)
        (mv_spec_gen_within .x10 .x9 outPtr (1 : Word) ((GuestAddrs.secp256k1_point_double + 36) : Word)
          (by decide))
        (by code_mem)
      rw [show ((GuestAddrs.secp256k1_point_double + 36) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 40) : Word) from by decide]
        at hm3
      have hcall2 := callWithin_spec ((GuestAddrs.secp256k1_point_double + 40) : Word) (GuestAddrs.secf_zero32 : Word)
        ((GuestAddrs.secp256k1_point_double + 32) : Word)
        (jalOff GuestAddrs.secf_zero32 (GuestAddrs.secp256k1_point_double + 40))
        ((secfZero32Fn 0 []).body.steps + 1)
        (by decide) (by code_mem) (by pcf)
        (secfZero32Flat_spec ((GuestAddrs.secp256k1_point_double + 44) : Word) outPtr oX hoXlen hrwwOut
          (by decide))
      rw [show ((GuestAddrs.secp256k1_point_double + 40) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 44) : Word) from by decide]
        at hcall2
      -- ---- addi a0, s1, 32 ; call secf_zero32(out+32) ----
      -- x10 comes back only owned — peel it for the addi
      have haddi2 : cpsTripleWithin 1 ((GuestAddrs.secp256k1_point_double + 44) : Word) ((GuestAddrs.secp256k1_point_double + 48) : Word)
          pdCr
          (((.x9 : Reg) ↦ᵣ outPtr) ** regOwns [.x10])
          (((.x9 : Reg) ↦ᵣ outPtr) ** (.x10 ↦ᵣ (outPtr + 32))) := by
        refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq)
          (cpsTripleWithin_peel_regOwns [.x10] (by decide)
            (P := ((.x9 : Reg) ↦ᵣ outPtr)) (fun vf => ?_))
        have h := liftCode (cr' := pdCr)
          (addi_spec_gen_within .x10 .x9 (vf .x10) outPtr (32 : BitVec 12)
            ((GuestAddrs.secp256k1_point_double + 44) : Word) (by decide))
          (by code_mem)
        rw [show ((GuestAddrs.secp256k1_point_double + 44) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 48) : Word) from by decide,
          show outPtr + signExtend12 (32 : BitVec 12) = outPtr + 32 from by
            rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]]
          at h
        refine cpsTripleWithin_weaken (fun _ hp => by
            simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
              at hp
            xperm_hyp hp)
          (fun _ hq => by xperm_hyp hq) h
      have hcall3 := callWithin_spec ((GuestAddrs.secp256k1_point_double + 48) : Word) (GuestAddrs.secf_zero32 : Word)
        ((GuestAddrs.secp256k1_point_double + 44) : Word)
        (jalOff GuestAddrs.secf_zero32 (GuestAddrs.secp256k1_point_double + 48))
        ((secfZero32Fn 0 []).body.steps + 1)
        (by decide) (by code_mem) (by pcf)
        (secfZero32Flat_spec ((GuestAddrs.secp256k1_point_double + 52) : Word) (outPtr + 32) oY hoYlen
          hrwwOut32 (by decide))
      rw [show ((GuestAddrs.secp256k1_point_double + 48) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 52) : Word) from by decide]
        at hcall3
      -- ---- li a0, 1 ; j (epilogue) ----
      have hli : cpsTripleWithin 1 ((GuestAddrs.secp256k1_point_double + 52) : Word) ((GuestAddrs.secp256k1_point_double + 56) : Word)
          pdCr (regOwns [.x10]) ((.x10 : Reg) ↦ᵣ (1 : Word)) := by
        refine cpsTripleWithin_weaken
          (fun _ hp => by
            simp only [regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp
            exact hp)
          (fun _ hq => hq) ?_
        have h := liftCode (cr' := pdCr)
          (li_spec_gen_own_within .x10 (1 : Word) ((GuestAddrs.secp256k1_point_double + 52) : Word)
            (by decide))
          (by code_mem)
        rwa [show ((GuestAddrs.secp256k1_point_double + 52) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 56) : Word) from by decide]
          at h
      have hjmp := liftCode (cr' := pdCr)
        (jal_x0_spec_gen_within (92 : BitVec 21) ((GuestAddrs.secp256k1_point_double + 56) : Word))
        (by code_mem)
      rw [show ((GuestAddrs.secp256k1_point_double + 56) : Word) + signExtend21 (92 : BitVec 21)
          = ((GuestAddrs.secp256k1_point_double + 148) : Word) from by decide] at hjmp
      -- ---- frames + chain (all posts deterministic) ----
      have hm1F := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ v9)
          ** (.x11 ↦ᵣ outPtr) ** regOwns convScratch
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
          ** bytesRegion arenaB ws)
        (by pcf) hm1
      have hm2F := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
          ** (.x10 ↦ᵣ inPtr) ** regOwns convScratch
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
          ** bytesRegion arenaB ws)
        (by pcf) hm2
      have haddiF := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ outPtr)
          ** (.x11 ↦ᵣ outPtr) ** regOwns convScratch
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
          ** bytesRegion arenaB ws)
        (by pcf) haddi
      have hcall1F := cpsTripleWithin_frameR
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
          ** bytesRegion inPtr xBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
          ** bytesRegion arenaB ws)
        (by pcf) hcall1
      have hbeqF := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 32) : Word)) ** (.x8 ↦ᵣ inPtr)
          ** (.x9 ↦ᵣ outPtr) ** regOwns a0Rest
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
          ** bytesRegion arenaB ws)
        (by pcf) hbeq
      have hm3F := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 32) : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))
          ** (.x8 ↦ᵣ inPtr) ** regOwns a0Rest
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
          ** bytesRegion arenaB ws)
        (by pcf) hm3
      have hcall2F := cpsTripleWithin_frameR
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion (outPtr + 32) oY ** bytesRegion arenaB ws)
        (by pcf) hcall2
      have haddi2F := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 44) : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))
          ** (.x8 ↦ᵣ inPtr) ** regOwns a0Rest
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))
          ** bytesRegion (outPtr + 32) oY ** bytesRegion arenaB ws)
        (by pcf) haddi2
      have hcall3F := cpsTripleWithin_frameR
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))
          ** bytesRegion arenaB ws)
        (by pcf) hcall3
      have hliF := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 52) : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))
          ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr) ** regOwns a0Rest
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))
          ** bytesRegion (outPtr + 32) (List.replicate 32 (0 : BitVec 8))
          ** bytesRegion arenaB ws)
        (by pcf) hli
      have hjmpF := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 52) : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))
          ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
          ** ((.x10 : Reg) ↦ᵣ (1 : Word)) ** regOwns a0Rest
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))
          ** bytesRegion (outPtr + 32) (List.replicate 32 (0 : BitVec 8))
          ** bytesRegion arenaB ws)
        (by pcf) hjmp
      rw [sepConj_emp_left'] at hjmpF
      have hc1 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hm1F hm2F
      have hc2 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hc1 haddiF
      have hc3 := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          -- release a1 into the callee scratch: a0Rest = x11 :: convScratch
          have hp1 : ((.x11 ↦ᵣ outPtr)
              ** (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ (inPtr + 32))
                ** regOwns convScratch ** bytesRegion (inPtr + 32) yBE
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
                ** (.x9 ↦ᵣ outPtr) ** bytesRegion inPtr xBE
                ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
                ** bytesRegion arenaB ws)) h := by
            xperm_hyp hp
          have hp2 := sepConj_mono (regIs_to_regOwn .x11 outPtr)
            (fun _ hh => hh) h hp1
          have hp3 : (regOwns a0Rest
              ** (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ (inPtr + 32))
                ** bytesRegion (inPtr + 32) yBE
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
                ** (.x9 ↦ᵣ outPtr) ** bytesRegion inPtr xBE
                ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
                ** bytesRegion arenaB ws)) h := by
            rw [ownsA0Split11]
            xperm_hyp hp2
          xperm_hyp hp3) hc2 hcall1F
      have hc4 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hc3 hbeqF
      have hc5 := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          -- strip the branch verdict pure fact
          have hp1 : ((⌜(1 : Word) ≠ (0 : Word)⌝ : Assertion)
              ** ((.x9 ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ (1 : Word))
                ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 32) : Word))
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
                ** regOwns a0Rest
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
                ** bytesRegion arenaB ws)) h := by
            xperm_hyp hp
          have hp2 := ((sepConj_pure_left h).mp hp1).2
          xperm_hyp hp2) hc4 hm3F
      have hc6 := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          -- release the stale a0 copy into the callee scratch
          have hp1 : ((.x10 ↦ᵣ outPtr)
              ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 32) : Word)) ** regOwns a0Rest
                ** bytesRegion outPtr oX
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
                ** (.x9 ↦ᵣ outPtr) ** bytesRegion inPtr xBE
                ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion (outPtr + 32) oY
                ** bytesRegion arenaB ws)) h := by
            xperm_hyp hp
          have hp2 := sepConj_mono (regIs_to_regOwn .x10 outPtr)
            (fun _ hh => hh) h hp1
          -- x10 is consumed by the callee's a0 slot; keep a0Rest intact
          have hp3 : (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 32) : Word))
              ** ((.x10 : Reg) ↦ᵣ outPtr) ** regOwns a0Rest
              ** bytesRegion outPtr oX
              ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
                ** (.x9 ↦ᵣ outPtr) ** bytesRegion inPtr xBE
                ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion (outPtr + 32) oY
                ** bytesRegion arenaB ws)) h := by
            xperm_hyp hp
          xperm_hyp hp3) hc5 hcall2F
      have hc7 := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          -- x10 back as owned: exposedRegs = [x10] ++ a0Rest
          rw [ownsSplitA0] at hp
          xperm_hyp hp) hc6 haddi2F
      have hc8 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hc7 hcall3F
      have hc9 := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          rw [ownsSplitA0] at hp
          xperm_hyp hp) hc8 hliF
      have hc10 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hc9 hjmpF
      have hcF := cpsTripleWithin_frameR
        ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
          ** ((sp0 + signExtend12 (-32 : BitVec 12)
                + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
          ** ((sp0 + signExtend12 (-32 : BitVec 12)
                + signExtend12 (8 : BitVec 12)) ↦ₘ v8)
          ** ((sp0 + signExtend12 (-32 : BitVec 12)
                + signExtend12 (16 : BitVec 12)) ↦ₘ v9))
        (by pcf) hc10
      refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun h hq => ?_)
        (cpsTripleWithin_mono_nSteps (by omega) hcF)
      · simp only [pdFrame, regsAt, frameSlotsSaved, pdVals,
          List.foldr_cons, List.foldr_nil, sepConj_emp_right'] at hp
        xperm_hyp hp
      · simp only [pdFrame, regsAt, frameSlotsSaved, pdVals, pdValsInf,
          List.foldr_cons, List.foldr_nil, sepConj_emp_right']
        have hfin : ((((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 52) : Word)) ** (.x8 ↦ᵣ inPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** ((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
            ** ((sp0 + signExtend12 (-32 : BitVec 12)
                  + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
            ** ((sp0 + signExtend12 (-32 : BitVec 12)
                  + signExtend12 (8 : BitVec 12)) ↦ₘ v8)
            ** ((sp0 + signExtend12 (-32 : BitVec 12)
                  + signExtend12 (16 : BitVec 12)) ↦ₘ v9))
            ** ((⌜beBytesToNat yBE = 0⌝ : Assertion)
              ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word))
                ** regOwns a0Rest
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))
                ** bytesRegion (outPtr + 32) (List.replicate 32 (0 : BitVec 8))
                ** bytesRegion arenaB ws))) h := by
          have hq' : ((((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 52) : Word)) ** (.x8 ↦ᵣ inPtr)
              ** (.x9 ↦ᵣ outPtr)
              ** ((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
              ** ((sp0 + signExtend12 (-32 : BitVec 12)
                    + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
              ** ((sp0 + signExtend12 (-32 : BitVec 12)
                    + signExtend12 (8 : BitVec 12)) ↦ₘ v8)
              ** ((sp0 + signExtend12 (-32 : BitVec 12)
                    + signExtend12 (16 : BitVec 12)) ↦ₘ v9))
              ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word))
                ** regOwns a0Rest
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))
                ** bytesRegion (outPtr + 32) (List.replicate 32 (0 : BitVec 8))
                ** bytesRegion arenaB ws)) h := by
            xperm_hyp hq
          exact sepConj_mono_right
            (fun h' hh => (sepConj_pure_left h').mpr ⟨hy0, hh⟩) h hq'
        have hout : ((((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 52) : Word)) ** (.x8 ↦ᵣ inPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** ((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
            ** ((sp0 + signExtend12 (-32 : BitVec 12)
                  + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
            ** ((sp0 + signExtend12 (-32 : BitVec 12)
                  + signExtend12 (8 : BitVec 12)) ↦ₘ v8)
            ** ((sp0 + signExtend12 (-32 : BitVec 12)
                  + signExtend12 (16 : BitVec 12)) ↦ₘ v9))
            ** (fun hp =>
              ((⌜beBytesToNat yBE = 0⌝
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word))
                ** regOwns a0Rest
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))
                ** bytesRegion (outPtr + 32) (List.replicate 32 (0 : BitVec 8))
                ** bytesRegion arenaB ws) hp)
              ∨ (∃ oX' oY',
                ((⌜beBytesToNat yBE ≠ 0
                  ∧ beBytesToNat oX' = (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).1
                  ∧ oX'.length = 32
                  ∧ beBytesToNat oY' = (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).2
                  ∧ oY'.length = 32⌝
                  ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word))
                  ** regOwns a0Rest
                  ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                  ** bytesRegion outPtr oX' ** bytesRegion (outPtr + 32) oY'
                  ** bytesRegion arenaB
                    (pairBytes 4 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)))) hp)))
            : Assertion) h :=
          sepConj_mono_right (fun h' hh => Or.inl hh) h hfin
        xperm_hyp hout
    exact abiFrame_spec
      (posImm := (32 : BitVec 12))
      (hframe := rfl)
      (hne := by decide)
      (hbound := by decide)
      (hprogBound := by decide)
      (hret := rfl)
      (halign := halign)
      (hframeRestore := sext_frameRestore _ _ _ (by decide))
      (hcpF := by pcf)
      (hcpF' := pcFree_or (by pcf)
        (pcFree_exists2 (fun oX' oY' => by pcf)))
      (hsub := by code_mem)
      (hbody := hbody)
  · -- ======================================================================
    -- ACCELERATOR PATH: y ≠ 0 — the staged doubling body, split out into
    -- `Secp256k1PointDoubleSAsmReg.pointDoubleRegBody_spec`.
    -- ======================================================================
    exact abiFrame_spec
      (posImm := (32 : BitVec 12))
      (hframe := rfl)
      (hne := by decide)
      (hbound := by decide)
      (hprogBound := by decide)
      (hret := rfl)
      (halign := halign)
      (hframeRestore := sext_frameRestore _ _ _ (by decide))
      (hcpF := by pcf)
      (hcpF' := pcFree_or (by pcf)
        (pcFree_exists2 (fun oX' oY' => by pcf)))
      (hsub := by code_mem)
      (hbody := pointDoubleRegBody_spec sp0 inPtr outPtr ret v8 v9
        xBE yBE oX oY ws hxlen hylen hoXlen hoYlen hwslen hwfX hwfY
        hoal hoov hovalid harval hdIn hdOut hxlt hylt hy0)

#print axioms pointDouble_spec
#print axioms pointDoubleRegBody_spec
#print axioms curveStep_spec
#print axioms secfBeToLeFlat_spec
#print axioms secfLeToBeFlat_spec
#print axioms secfIsZero32Flat_spec
#print axioms secfZero32Flat_spec

end Secp256k1PointDoubleSAsm

end EvmAsm.Codegen
