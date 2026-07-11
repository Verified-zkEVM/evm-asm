/-
  EvmAsm.Codegen.Programs.Secp256k1PointDoubleSAsmReg

  The accelerator-path (`y ≠ 0`) single-exit body triple of
  `secp256k1_point_double`, split out of `Secp256k1PointDoubleSAsm.lean`
  (file-size guardrail): stage both coordinates LE via `secf_be_to_le`
  into their own `secc_le_p1` subwindows (multi-RW-subwindow adapter),
  run the inline CSR-2052 tangent doubling in place, convert both halves
  back out via `secf_le_to_be`, `a0 := 0`.  Consumed by `abiFrame_spec`
  in `Secp256k1PointDoubleSAsm.pointDouble_spec`.
-/

import EvmAsm.Codegen.Programs.Secp256k1PointDoubleSAsmBody

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Secp256k1PointDoubleSAsm

open Secp256k1FieldConvSAsm (secfBeToLeFn)
open Secp256k1FieldConvSAsm (secfLeToBeFn)
open Secp256k1FieldIsZeroSAsm (secfIsZero32Fn)
open Secp256k1FieldLeavesSAsm (secfZero32Fn)
open EvmAsm.Rv64.SAsm.WhileBreakDemo (nlz)

/-- The accelerator-path body triple, in `abiFrame_spec` shape. -/
theorem pointDoubleRegBody_spec (sp0 inPtr outPtr ret v8 v9 : Word)
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
    (hy0 : beBytesToNat yBE ≠ 0) :
    cpsTripleWithin
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
      ** regsAt pdFrame (pdValsReg inPtr outPtr)
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
  have hnlz : nlz yBE 32 ≠ 32 := fun h => hy0 ((nlz32_iff_zero yBE hylen).mp h)
  have hwfArena1 : ∀ bs : List (BitVec 8), bs.length = 32 →
      Region.wf ⟨(GuestAddrs.secc_le_p1 : Word), bs⟩ := by
    intro bs hbs
    refine ⟨?_, ?_, ?_⟩
    · show ((GuestAddrs.secc_le_p1 : Word)).toNat % 8 = 0
      decide
    · show ((GuestAddrs.secc_le_p1 : Word)).toNat + bs.length < 2 ^ 64
      rw [hbs]
      decide
    · intro k hk
      rw [hbs] at hk
      rw [show (GuestAddrs.secc_le_p1 : Word) = arenaB from by decide]
      exact harval k (by omega)
  have hwfArena2 : ∀ bs : List (BitVec 8), bs.length = 32 →
      Region.wf ⟨(arenaB + 32), bs⟩ := by
    intro bs hbs
    refine ⟨?_, ?_, ?_⟩
    · show ((arenaB + 32)).toNat % 8 = 0
      decide
    · show ((arenaB + 32)).toNat + bs.length < 2 ^ 64
      rw [hbs]
      decide
    · intro k hk
      rw [hbs] at hk
      rw [show (arenaB + 32) + BitVec.ofNat 64 k
          = arenaB + BitVec.ofNat 64 (32 + k) from by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [show (32 : Word).toNat = 32 from by decide]
        norm_num [arenaB, GuestAddrs.secc_le_p1]
        omega]
      exact harval (32 + k) (by omega)
  have hrwwA : RwRegion.wf ⟨(GuestAddrs.secc_le_p1 : Word), 32⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · show ((GuestAddrs.secc_le_p1 : Word)).toNat % 8 = 0
      decide
    · show ((GuestAddrs.secc_le_p1 : Word)).toNat + 32 < 2 ^ 64
      decide
    intro k hk
    have hk' : k < 32 := hk
    rw [show (GuestAddrs.secc_le_p1 : Word) = arenaB from by decide]
    exact harval k (by omega)
  have hrwwA2 : RwRegion.wf ⟨(arenaB + 32), 32⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · show ((arenaB + 32)).toNat % 8 = 0
      decide
    · show ((arenaB + 32)).toNat + 32 < 2 ^ 64
      decide
    intro k hk
    have hk' : k < 32 := hk
    rw [show (arenaB + 32) + BitVec.ofNat 64 k
        = arenaB + BitVec.ofNat 64 (32 + k) from by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [show (32 : Word).toNat = 32 from by decide]
      norm_num [arenaB, GuestAddrs.secc_le_p1]
      omega]
    exact harval (32 + k) (by omega)
  have hdstA : ((GuestAddrs.secc_le_p1 : Word)).toNat = 0xa3c05618 := by decide
  have hdstA2 : ((arenaB + 32)).toNat = 0xa3c05638 := by decide
  have hentry : (GuestAddrs.secp256k1_point_double : Word)
        + BitVec.ofNat 64 (4 * (1 + pdFrame.length))
      = ((GuestAddrs.secp256k1_point_double + 16) : Word) := by decide
  have hexit : (GuestAddrs.secp256k1_point_double : Word)
        + BitVec.ofNat 64 (4 * (1 + pdFrame.length + pdBody.length))
      = ((GuestAddrs.secp256k1_point_double + 148) : Word) := by decide
  rw [hentry, hexit]
  -- ---- the post-first-conversion continuation (per written `_x` LE) ----
  have hB1 : ∀ ws₁ : List (BitVec 8),
      cpsTripleWithin
        ((5 + ((secfBeToLeFn 0 0 [] []).body.steps + 1))
          + ((7 + ((secfLeToBeFn 0 0 [] []).body.steps + 1))
            + ((6 + ((secfLeToBeFn 0 0 [] []).body.steps + 1)) + 1)))
        ((GuestAddrs.secp256k1_point_double + 76) : Word) ((GuestAddrs.secp256k1_point_double + 148) : Word) pdCr
        (⌜wsNat256 ws₁ 0 = beBytesToNat xBE ∧ ws₁.length = 32⌝
          ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 76) : Word)) ** regOwns exposedRegs
          ** bytesRegion (GuestAddrs.secc_le_p1 : Word) ws₁ ** bytesRegion inPtr xBE
          ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
          ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
          ** windowRest arenaB ws 0 32)
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word)) ** (.x8 ↦ᵣ inPtr)
          ** (.x9 ↦ᵣ outPtr)
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
                ** ((.x0 : Reg) ↦ᵣ (0 : Word))
                ** ((.x10 : Reg) ↦ᵣ (0 : Word))
                ** regOwns a0Rest
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion outPtr oX' ** bytesRegion (outPtr + 32) oY'
                ** bytesRegion arenaB
                  (pairBytes 4 (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)))) hp)))) := by
    intro ws₁
    refine cpsTripleWithin_pure_pre (fun hf1 => ?_)
    obtain ⟨hf1a, hf1b⟩ := hf1
    -- ---- the post-second-conversion continuation (per written `_y` LE) --
    have hB2 : ∀ ws₂ : List (BitVec 8),
        cpsTripleWithin
          ((7 + ((secfLeToBeFn 0 0 [] []).body.steps + 1))
            + ((6 + ((secfLeToBeFn 0 0 [] []).body.steps + 1)) + 1))
          ((GuestAddrs.secp256k1_point_double + 96) : Word) ((GuestAddrs.secp256k1_point_double + 148) : Word) pdCr
          (⌜wsNat256 ws₂ 0 = beBytesToNat yBE ∧ ws₂.length = 32⌝
            ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word)) ** regOwns exposedRegs
            ** bytesRegion (arenaB + 32) ws₂
            ** bytesRegion (inPtr + 32) yBE
            ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion inPtr xBE
            ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
            ** windowRest arenaB (setBytes ws 0 ws₁) 0x20 32)
          (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word)) ** (.x8 ↦ᵣ inPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** (fun hp =>
              ((⌜beBytesToNat yBE = 0⌝
                ** ((.x0 : Reg) ↦ᵣ (0 : Word))
                ** ((.x10 : Reg) ↦ᵣ (1 : Word))
                ** regOwns a0Rest
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))
                ** bytesRegion (outPtr + 32)
                    (List.replicate 32 (0 : BitVec 8))
                ** bytesRegion arenaB ws) hp)
              ∨ (∃ oX' oY',
                ((⌜beBytesToNat yBE ≠ 0
                  ∧ beBytesToNat oX' = (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).1
                  ∧ oX'.length = 32
                  ∧ beBytesToNat oY' = (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).2
                  ∧ oY'.length = 32⌝
                  ** ((.x0 : Reg) ↦ᵣ (0 : Word))
                  ** ((.x10 : Reg) ↦ᵣ (0 : Word))
                  ** regOwns a0Rest
                  ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                  ** bytesRegion outPtr oX'
                  ** bytesRegion (outPtr + 32) oY'
                  ** bytesRegion arenaB
                    (pairBytes 4 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)))) hp)))) := by
      intro ws₂
      refine cpsTripleWithin_pure_pre (fun hf2 => ?_)
      obtain ⟨hf2a, hf2b⟩ := hf2
      -- decode the accumulated staging image at the accelerator operands
      have e0 : wsNat256 (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0
          = beBytesToNat xBE := by
        rw [wsNat256_setBytes_low (by omega),
          wsNat256_setBytes_inside hf1b (by omega), hf1a]
      have e1 : wsNat256 (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0x20
          = beBytesToNat yBE := by
        rw [wsNat256_setBytes_inside hf2b (by rw [length_setBytes]; omega),
          hf2a]
      -- ---- the post-doubling out.x conversion continuation ----
      have hC : ∀ oX' : List (BitVec 8),
          cpsTripleWithin
            ((6 + ((secfLeToBeFn 0 0 [] []).body.steps + 1)) + 1)
            ((GuestAddrs.secp256k1_point_double + 124) : Word) ((GuestAddrs.secp256k1_point_double + 148) : Word) pdCr
            (⌜beBytesToNat oX' = wsNat256 (leBytes32 (Accel.curveDbl
                Accel.secpP (beBytesToNat xBE) (beBytesToNat yBE)).1) 0
              ∧ oX'.length = 32⌝
              ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 124) : Word)) ** regOwns exposedRegs
              ** bytesRegion outPtr oX'
              ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                  (leBytes32 (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)).1)
              ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
              ** (.x9 ↦ᵣ outPtr)
              ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
              ** bytesRegion (outPtr + 32) oY
              ** bytesRegion (arenaB + 32)
                  (leBytes32 (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)).2))
            (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word)) ** (.x8 ↦ᵣ inPtr)
              ** (.x9 ↦ᵣ outPtr)
              ** (fun hp =>
                ((⌜beBytesToNat yBE = 0⌝
                  ** ((.x0 : Reg) ↦ᵣ (0 : Word))
                  ** ((.x10 : Reg) ↦ᵣ (1 : Word))
                  ** regOwns a0Rest
                  ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                  ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))
                  ** bytesRegion (outPtr + 32)
                      (List.replicate 32 (0 : BitVec 8))
                  ** bytesRegion arenaB ws) hp)
                ∨ (∃ oX'' oY'',
                  ((⌜beBytesToNat yBE ≠ 0
                    ∧ beBytesToNat oX'' = (Accel.curveDbl Accel.secpP
                        (beBytesToNat xBE) (beBytesToNat yBE)).1
                    ∧ oX''.length = 32
                    ∧ beBytesToNat oY'' = (Accel.curveDbl Accel.secpP
                        (beBytesToNat xBE) (beBytesToNat yBE)).2
                    ∧ oY''.length = 32⌝
                    ** ((.x0 : Reg) ↦ᵣ (0 : Word))
                    ** ((.x10 : Reg) ↦ᵣ (0 : Word))
                    ** regOwns a0Rest
                    ** bytesRegion inPtr xBE
                    ** bytesRegion (inPtr + 32) yBE
                    ** bytesRegion outPtr oX''
                    ** bytesRegion (outPtr + 32) oY''
                    ** bytesRegion arenaB
                      (pairBytes 4 (Accel.curveDbl Accel.secpP
                        (beBytesToNat xBE) (beBytesToNat yBE)))) hp)))) := by
        intro oX'
        refine cpsTripleWithin_pure_pre (fun hfX => ?_)
        obtain ⟨hfXa, hfXb⟩ := hfX
        -- ---- the out.y conversion continuation (per written out.y) ----
        have hD : ∀ oY' : List (BitVec 8),
            cpsTripleWithin 1 ((GuestAddrs.secp256k1_point_double + 144) : Word) ((GuestAddrs.secp256k1_point_double + 148) : Word) pdCr
              (⌜beBytesToNat oY' = wsNat256 (leBytes32 (Accel.curveDbl
                  Accel.secpP (beBytesToNat xBE) (beBytesToNat yBE)).2) 0
                ∧ oY'.length = 32⌝
                ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word))
                ** regOwns exposedRegs
                ** bytesRegion (outPtr + 32) oY'
                ** bytesRegion (arenaB + 32)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).2)
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
                ** (.x9 ↦ᵣ outPtr)
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion outPtr oX'
                ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).1))
              (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word)) ** (.x8 ↦ᵣ inPtr)
                ** (.x9 ↦ᵣ outPtr)
                ** (fun hp =>
                  ((⌜beBytesToNat yBE = 0⌝
                    ** ((.x0 : Reg) ↦ᵣ (0 : Word))
                    ** ((.x10 : Reg) ↦ᵣ (1 : Word))
                    ** regOwns a0Rest
                    ** bytesRegion inPtr xBE
                    ** bytesRegion (inPtr + 32) yBE
                    ** bytesRegion outPtr
                        (List.replicate 32 (0 : BitVec 8))
                    ** bytesRegion (outPtr + 32)
                        (List.replicate 32 (0 : BitVec 8))
                    ** bytesRegion arenaB ws) hp)
                  ∨ (∃ oX'' oY'',
                    ((⌜beBytesToNat yBE ≠ 0
                      ∧ beBytesToNat oX'' = (Accel.curveDbl Accel.secpP
                          (beBytesToNat xBE) (beBytesToNat yBE)).1
                      ∧ oX''.length = 32
                      ∧ beBytesToNat oY'' = (Accel.curveDbl Accel.secpP
                          (beBytesToNat xBE) (beBytesToNat yBE)).2
                      ∧ oY''.length = 32⌝
                      ** ((.x0 : Reg) ↦ᵣ (0 : Word))
                      ** ((.x10 : Reg) ↦ᵣ (0 : Word))
                      ** regOwns a0Rest
                      ** bytesRegion inPtr xBE
                      ** bytesRegion (inPtr + 32) yBE
                      ** bytesRegion outPtr oX''
                      ** bytesRegion (outPtr + 32) oY''
                      ** bytesRegion arenaB
                        (pairBytes 4 (Accel.curveDbl Accel.secpP
                          (beBytesToNat xBE) (beBytesToNat yBE)))) hp)))) := by
          intro oY'
          refine cpsTripleWithin_pure_pre (fun hfY => ?_)
          obtain ⟨hfYa, hfYb⟩ := hfY
          -- li a0, 0
          have hli : cpsTripleWithin 1 ((GuestAddrs.secp256k1_point_double + 144) : Word)
              ((GuestAddrs.secp256k1_point_double + 148) : Word) pdCr
              (regOwns [.x10]) ((.x10 : Reg) ↦ᵣ (0 : Word)) := by
            refine cpsTripleWithin_weaken
              (fun _ hp => by
                simp only [regOwns_cons, regOwns_nil, sepConj_emp_right']
                  at hp
                exact hp)
              (fun _ hq => hq) ?_
            have h := liftCode (cr' := pdCr)
              (li_spec_gen_own_within .x10 (0 : Word) ((GuestAddrs.secp256k1_point_double + 144) : Word)
                (by decide))
              (by code_mem)
            rwa [show ((GuestAddrs.secp256k1_point_double + 144) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 148) : Word)
              from by decide] at h
          have hliF := cpsTripleWithin_frameR
            (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word))
              ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
              ** (.x9 ↦ᵣ outPtr) ** regOwns a0Rest
              ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
              ** bytesRegion outPtr oX' ** bytesRegion (outPtr + 32) oY'
              ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                  (leBytes32 (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)).1)
              ** bytesRegion (arenaB + 32)
                  (leBytes32 (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)).2))
            (by pcf) hli
          refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
            hliF
          · rw [ownsSplitA0] at hp
            xperm_hyp hp
          · -- rebuild the disjunctive post (inr, with merged staging point)
            have hfXa' : beBytesToNat oX' = (Accel.curveDbl Accel.secpP
                (beBytesToNat xBE) (beBytesToNat yBE)).1 := by
              rw [hfXa, wsNat256_leBytes32 _
                (curveDbl_lt (beBytesToNat xBE) (beBytesToNat yBE)).1]
            have hfYa' : beBytesToNat oY' = (Accel.curveDbl Accel.secpP
                (beBytesToNat xBE) (beBytesToNat yBE)).2 := by
              rw [hfYa, wsNat256_leBytes32 _
                (curveDbl_lt (beBytesToNat xBE) (beBytesToNat yBE)).2]
            have hq1 : ((((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word))
                ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr))
                ** (((.x0 : Reg) ↦ᵣ (0 : Word))
                  ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns a0Rest
                  ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                  ** bytesRegion outPtr oX'
                  ** bytesRegion (outPtr + 32) oY'
                  ** (bytesRegion (GuestAddrs.secc_le_p1 : Word)
                      (leBytes32 (Accel.curveDbl Accel.secpP
                        (beBytesToNat xBE) (beBytesToNat yBE)).1)
                    ** bytesRegion (arenaB + 32)
                      (leBytes32 (Accel.curveDbl Accel.secpP
                        (beBytesToNat xBE) (beBytesToNat yBE)).2)))) h := by
              xperm_hyp hq
            rw [← arena_pair] at hq1
            have hfin : ((((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word))
                ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr))
                ** (⌜beBytesToNat yBE ≠ 0
                  ∧ beBytesToNat oX' = (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).1
                  ∧ oX'.length = 32
                  ∧ beBytesToNat oY' = (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).2
                  ∧ oY'.length = 32⌝
                  ** ((.x0 : Reg) ↦ᵣ (0 : Word))
                  ** ((.x10 : Reg) ↦ᵣ (0 : Word))
                  ** regOwns a0Rest
                  ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                  ** bytesRegion outPtr oX'
                  ** bytesRegion (outPtr + 32) oY'
                  ** bytesRegion arenaB
                    (pairBytes 4 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE))))) h :=
              sepConj_mono_right (fun h' hh =>
                (sepConj_pure_left h').mpr
                  ⟨⟨hy0, hfXa', hfXb, hfYa', hfYb⟩, hh⟩) h hq1
            have hout : ((((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word))
                ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr))
                ** (fun hp =>
                  ((⌜beBytesToNat yBE = 0⌝
                    ** ((.x0 : Reg) ↦ᵣ (0 : Word))
                    ** ((.x10 : Reg) ↦ᵣ (1 : Word))
                    ** regOwns a0Rest
                    ** bytesRegion inPtr xBE
                    ** bytesRegion (inPtr + 32) yBE
                    ** bytesRegion outPtr
                        (List.replicate 32 (0 : BitVec 8))
                    ** bytesRegion (outPtr + 32)
                        (List.replicate 32 (0 : BitVec 8))
                    ** bytesRegion arenaB ws) hp)
                  ∨ (∃ oX'' oY'',
                    ((⌜beBytesToNat yBE ≠ 0
                      ∧ beBytesToNat oX'' = (Accel.curveDbl Accel.secpP
                          (beBytesToNat xBE) (beBytesToNat yBE)).1
                      ∧ oX''.length = 32
                      ∧ beBytesToNat oY'' = (Accel.curveDbl Accel.secpP
                          (beBytesToNat xBE) (beBytesToNat yBE)).2
                      ∧ oY''.length = 32⌝
                      ** ((.x0 : Reg) ↦ᵣ (0 : Word))
                      ** ((.x10 : Reg) ↦ᵣ (0 : Word))
                      ** regOwns a0Rest
                      ** bytesRegion inPtr xBE
                      ** bytesRegion (inPtr + 32) yBE
                      ** bytesRegion outPtr oX''
                      ** bytesRegion (outPtr + 32) oY''
                      ** bytesRegion arenaB
                        (pairBytes 4 (Accel.curveDbl Accel.secpP
                          (beBytesToNat xBE) (beBytesToNat yBE)))) hp)))
                : Assertion) h :=
              sepConj_mono_right
                (fun h' hh => Or.inr ⟨oX', oY', hh⟩) h hfin
            xperm_hyp hout
        -- ---- la a0, secc_le_p1 ; a0 += 32 ; a1 := s1 + 32 ; call ----
        have hla10 := la_own_within .x10 (fun vOld =>
          la_materialize_within .x10 vOld ((GuestAddrs.secp256k1_point_double + 124) : Word)
            (GuestAddrs.secc_le_p1 : Word) (by decide) (by decide)
            (by code_mem) (by code_mem))
        rw [show ((GuestAddrs.secp256k1_point_double + 124) : Word) + 8 = ((GuestAddrs.secp256k1_point_double + 132) : Word) from by decide]
          at hla10
        have haddiS := liftCode (cr' := pdCr)
          (addi_spec_gen_same_within .x10 (GuestAddrs.secc_le_p1 : Word)
            (32 : BitVec 12) ((GuestAddrs.secp256k1_point_double + 132) : Word) (by decide))
          (by code_mem)
        rw [show ((GuestAddrs.secp256k1_point_double + 132) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 136) : Word) from by decide,
          show (GuestAddrs.secc_le_p1 : Word) + signExtend12 (32 : BitVec 12)
            = (arenaB + 32) from by decide] at haddiS
        have haddi11 := liftCode (cr' := pdCr)
          (addi_own_within .x11 .x9 outPtr (32 : BitVec 12)
            ((GuestAddrs.secp256k1_point_double + 136) : Word) (by decide))
          (by code_mem)
        rw [show ((GuestAddrs.secp256k1_point_double + 136) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 140) : Word) from by decide,
          show outPtr + signExtend12 (32 : BitVec 12) = outPtr + 32 from by
            rw [show signExtend12 (32 : BitVec 12) = (32 : Word)
              from by decide]] at haddi11
        have hflatL2 := secfLeToBeFlat_spec ((GuestAddrs.secp256k1_point_double + 144) : Word)
          (arenaB + 32) (outPtr + 32)
          (leBytes32 (Accel.curveDbl Accel.secpP
            (beBytesToNat xBE) (beBytesToNat yBE)).2) oY
          (by rw [length_leBytes32]) hoYlen
          (hwfArena2 _ (by rw [length_leBytes32])) hrwwOut32
          (by decide) (by rw [houtT]; omega)
          (by
            rw [hdstA2, houtT]
            rcases hdOut with h | h
            · right
              omega
            · left
              omega)
          (by decide)
        have hcalleeL2 : cpsTripleWithin
            ((secfLeToBeFn (arenaB + 32) (outPtr + 32)
              (leBytes32 (Accel.curveDbl Accel.secpP
                (beBytesToNat xBE) (beBytesToNat yBE)).2) oY).body.steps + 1)
            (GuestAddrs.secf_le_to_be : Word) ((GuestAddrs.secp256k1_point_double + 144) : Word) pdCr
            (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word))
              ** ((.x10 ↦ᵣ (arenaB + 32)) ** (.x11 ↦ᵣ (outPtr + 32))
                ** regOwns convScratch ** bytesRegion (outPtr + 32) oY
                ** bytesRegion (arenaB + 32)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).2)))
            (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word))
              ** (fun hp => ∃ ws',
                ((⌜beBytesToNat ws' = wsNat256 (leBytes32 (Accel.curveDbl
                      Accel.secpP (beBytesToNat xBE) (beBytesToNat yBE)).2) 0
                  ∧ ws'.length = 32⌝
                  ** regOwns exposedRegs ** bytesRegion (outPtr + 32) ws'
                  ** bytesRegion (arenaB + 32)
                      (leBytes32 (Accel.curveDbl Accel.secpP
                        (beBytesToNat xBE) (beBytesToNat yBE)).2))) hp)) := by
          refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
            (fun h hq => ?_) hflatL2
          obtain ⟨ws', hin⟩ := hq
          refine exists_pull h ⟨ws', ?_⟩
          xperm_hyp hin
        have hcallL2 := callWithin_spec ((GuestAddrs.secp256k1_point_double + 140) : Word)
          (GuestAddrs.secf_le_to_be : Word) ((GuestAddrs.secp256k1_point_double + 124) : Word)
          (jalOff GuestAddrs.secf_le_to_be
            (GuestAddrs.secp256k1_point_double + 140))
          ((secfLeToBeFn (arenaB + 32) (outPtr + 32)
            (leBytes32 (Accel.curveDbl Accel.secpP
              (beBytesToNat xBE) (beBytesToNat yBE)).2) oY).body.steps + 1)
          (by decide) (by code_mem) (by pcf) hcalleeL2
        rw [show ((GuestAddrs.secp256k1_point_double + 140) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 144) : Word) from by decide,
          show (secfLeToBeFn (arenaB + 32) (outPtr + 32)
              (leBytes32 (Accel.curveDbl Accel.secpP
                (beBytesToNat xBE) (beBytesToNat yBE)).2) oY).body.steps
            = (secfLeToBeFn 0 0 [] []).body.steps from rfl] at hcallL2
        -- ---- frames + chain ----
        have hla10F := cpsTripleWithin_frameR
          (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 124) : Word)) ** regOwn .x11
            ** regOwns convScratch
            ** bytesRegion outPtr oX'
            ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                (leBytes32 (Accel.curveDbl Accel.secpP
                  (beBytesToNat xBE) (beBytesToNat yBE)).1)
            ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
            ** bytesRegion (outPtr + 32) oY
            ** bytesRegion (arenaB + 32)
                (leBytes32 (Accel.curveDbl Accel.secpP
                  (beBytesToNat xBE) (beBytesToNat yBE)).2))
          (by pcf) hla10
        have haddiSF := cpsTripleWithin_frameR
          (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 124) : Word)) ** regOwn .x11
            ** regOwns convScratch
            ** bytesRegion outPtr oX'
            ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                (leBytes32 (Accel.curveDbl Accel.secpP
                  (beBytesToNat xBE) (beBytesToNat yBE)).1)
            ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
            ** bytesRegion (outPtr + 32) oY
            ** bytesRegion (arenaB + 32)
                (leBytes32 (Accel.curveDbl Accel.secpP
                  (beBytesToNat xBE) (beBytesToNat yBE)).2))
          (by pcf) haddiS
        have haddi11F := cpsTripleWithin_frameR
          (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 124) : Word))
            ** ((.x10 : Reg) ↦ᵣ (arenaB + 32))
            ** regOwns convScratch
            ** bytesRegion outPtr oX'
            ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                (leBytes32 (Accel.curveDbl Accel.secpP
                  (beBytesToNat xBE) (beBytesToNat yBE)).1)
            ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
            ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
            ** bytesRegion (outPtr + 32) oY
            ** bytesRegion (arenaB + 32)
                (leBytes32 (Accel.curveDbl Accel.secpP
                  (beBytesToNat xBE) (beBytesToNat yBE)).2))
          (by pcf) haddi11
        have hcallL2F := cpsTripleWithin_frameR
          (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
            ** bytesRegion outPtr oX'
            ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                (leBytes32 (Accel.curveDbl Accel.secpP
                  (beBytesToNat xBE) (beBytesToNat yBE)).1))
          (by pcf) hcallL2
        have hd1 := cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by xperm_hyp hp) hla10F haddiSF
        have hd2 := cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by xperm_hyp hp) hd1 haddi11F
        have hd3 := cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by xperm_hyp hp) hd2 hcallL2F
        have hd3' : cpsTripleWithin
            (6 + ((secfLeToBeFn 0 0 [] []).body.steps + 1))
            ((GuestAddrs.secp256k1_point_double + 124) : Word) ((GuestAddrs.secp256k1_point_double + 144) : Word) pdCr
            ((regOwn .x10)
              ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 124) : Word)) ** regOwn .x11
                ** regOwns convScratch
                ** bytesRegion outPtr oX'
                ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).1)
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
                ** (.x9 ↦ᵣ outPtr)
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion (outPtr + 32) oY
                ** bytesRegion (arenaB + 32)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).2)))
            (fun hp => ∃ oY',
              ((⌜beBytesToNat oY' = wsNat256 (leBytes32 (Accel.curveDbl
                  Accel.secpP (beBytesToNat xBE) (beBytesToNat yBE)).2) 0
                ∧ oY'.length = 32⌝
                ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word))
                ** regOwns exposedRegs
                ** bytesRegion (outPtr + 32) oY'
                ** bytesRegion (arenaB + 32)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).2)
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
                ** (.x9 ↦ᵣ outPtr)
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion outPtr oX'
                ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).1))) hp) := by
          refine cpsTripleWithin_mono_nSteps (by omega)
            (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
              (fun h hq => ?_) hd3)
          have hq1 : ((fun hp => ∃ ws',
              ((⌜beBytesToNat ws' = wsNat256 (leBytes32 (Accel.curveDbl
                    Accel.secpP (beBytesToNat xBE) (beBytesToNat yBE)).2) 0
                ∧ ws'.length = 32⌝
                ** regOwns exposedRegs ** bytesRegion (outPtr + 32) ws'
                ** bytesRegion (arenaB + 32)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).2))) hp)
              ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 144) : Word))
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
                ** (.x9 ↦ᵣ outPtr)
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion outPtr oX'
                ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).1))
              : Assertion) h := by
            xperm_hyp hq
          obtain ⟨oY', hin⟩ := (sepConj_exists_left h).mp hq1
          exact ⟨oY', by xperm_hyp hin⟩
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
          (cpsTripleWithin_seq_exists_same_cr hd3' hD)
        rw [ownsSplit1011] at hp
        simp only [regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp
        xperm_hyp hp
      -- ---- la t0 ; csrs 2052 ; la a0 ; a1 := s1 ; call le_to_be ----
      have hla5 := la_own_within .x5 (fun vOld =>
        la_materialize_within .x5 vOld ((GuestAddrs.secp256k1_point_double + 96) : Word)
          (GuestAddrs.secc_le_p1 : Word) (by decide) (by decide)
          (by code_mem) (by code_mem))
      rw [show ((GuestAddrs.secp256k1_point_double + 96) : Word) + 8 = ((GuestAddrs.secp256k1_point_double + 104) : Word) from by decide]
        at hla5
      have hcurve := curveStep_spec
        (setBytes (setBytes ws 0 ws₁) 0x20 ws₂)
        (by rw [length_setBytes, length_setBytes]; exact hwslen)
        harval
        (by rw [e0]; exact hxlt)
        (by rw [e1]; exact hylt)
        (by rw [e1]; exact hy0)
      rw [e0, e1,
        setBytes_cover (setBytes (setBytes ws 0 ws₁) 0x20 ws₂)
          (pairBytes 4 (Accel.curveDbl Accel.secpP
            (beBytesToNat xBE) (beBytesToNat yBE)))
          (by rw [length_pairBytes, length_setBytes, length_setBytes,
            hwslen]),
        arena_pair] at hcurve
      have hla10' := la_own_within .x10 (fun vOld =>
        la_materialize_within .x10 vOld ((GuestAddrs.secp256k1_point_double + 108) : Word)
          (GuestAddrs.secc_le_p1 : Word) (by decide) (by decide)
          (by code_mem) (by code_mem))
      rw [show ((GuestAddrs.secp256k1_point_double + 108) : Word) + 8 = ((GuestAddrs.secp256k1_point_double + 116) : Word) from by decide]
        at hla10'
      have hmv11 := liftCode (cr' := pdCr)
        (mv_own_within .x11 .x9 outPtr ((GuestAddrs.secp256k1_point_double + 116) : Word) (by decide))
        (by code_mem)
      rw [show ((GuestAddrs.secp256k1_point_double + 116) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 120) : Word) from by decide]
        at hmv11
      have hflatL1 := secfLeToBeFlat_spec ((GuestAddrs.secp256k1_point_double + 124) : Word)
        (GuestAddrs.secc_le_p1 : Word) outPtr
        (leBytes32 (Accel.curveDbl Accel.secpP
          (beBytesToNat xBE) (beBytesToNat yBE)).1) oX
        (by rw [length_leBytes32]) hoXlen
        (hwfArena1 _ (by rw [length_leBytes32])) hrwwOut
        (by decide) (by omega)
        (by
          rw [hdstA]
          rcases hdOut with h | h
          · right
            omega
          · left
            omega)
        (by decide)
      have hcalleeL1 : cpsTripleWithin
          ((secfLeToBeFn (GuestAddrs.secc_le_p1 : Word) outPtr
            (leBytes32 (Accel.curveDbl Accel.secpP
              (beBytesToNat xBE) (beBytesToNat yBE)).1) oX).body.steps + 1)
          (GuestAddrs.secf_le_to_be : Word) ((GuestAddrs.secp256k1_point_double + 124) : Word) pdCr
          (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 124) : Word))
            ** ((.x10 ↦ᵣ (GuestAddrs.secc_le_p1 : Word)) ** (.x11 ↦ᵣ outPtr)
              ** regOwns convScratch ** bytesRegion outPtr oX
              ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                  (leBytes32 (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)).1)))
          (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 124) : Word))
            ** (fun hp => ∃ ws',
              ((⌜beBytesToNat ws' = wsNat256 (leBytes32 (Accel.curveDbl
                    Accel.secpP (beBytesToNat xBE) (beBytesToNat yBE)).1) 0
                ∧ ws'.length = 32⌝
                ** regOwns exposedRegs ** bytesRegion outPtr ws'
                ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).1))) hp)) := by
        refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun h hq => ?_) hflatL1
        obtain ⟨ws', hin⟩ := hq
        refine exists_pull h ⟨ws', ?_⟩
        xperm_hyp hin
      have hcallL1 := callWithin_spec ((GuestAddrs.secp256k1_point_double + 120) : Word)
        (GuestAddrs.secf_le_to_be : Word) ((GuestAddrs.secp256k1_point_double + 96) : Word)
        (jalOff GuestAddrs.secf_le_to_be
          (GuestAddrs.secp256k1_point_double + 120))
        ((secfLeToBeFn (GuestAddrs.secc_le_p1 : Word) outPtr
          (leBytes32 (Accel.curveDbl Accel.secpP
            (beBytesToNat xBE) (beBytesToNat yBE)).1) oX).body.steps + 1)
        (by decide) (by code_mem) (by pcf) hcalleeL1
      rw [show ((GuestAddrs.secp256k1_point_double + 120) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 124) : Word) from by decide,
        show (secfLeToBeFn (GuestAddrs.secc_le_p1 : Word) outPtr
            (leBytes32 (Accel.curveDbl Accel.secpP
              (beBytesToNat xBE) (beBytesToNat yBE)).1) oX).body.steps
          = (secfLeToBeFn 0 0 [] []).body.steps from rfl] at hcallL1
      -- ---- frames + chain ----
      have hla5F := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word)) ** regOwns csrsRest
          ** bytesRegion arenaB (setBytes (setBytes ws 0 ws₁) 0x20 ws₂)
          ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY)
        (by pcf) hla5
      have hcurveF := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word))
          ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY)
        (by pcf) hcurve
      have hla10'F := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word))
          ** ((.x5 : Reg) ↦ᵣ (GuestAddrs.secc_le_p1 : Word)) ** regOwn .x11
          ** regOwns csrsScratch
          ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
              (leBytes32 (Accel.curveDbl Accel.secpP
                (beBytesToNat xBE) (beBytesToNat yBE)).1)
          ** bytesRegion (arenaB + 32)
              (leBytes32 (Accel.curveDbl Accel.secpP
                (beBytesToNat xBE) (beBytesToNat yBE)).2)
          ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY)
        (by pcf) hla10'
      have hmv11F := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word))
          ** ((.x5 : Reg) ↦ᵣ (GuestAddrs.secc_le_p1 : Word))
          ** ((.x10 : Reg) ↦ᵣ (GuestAddrs.secc_le_p1 : Word))
          ** regOwns csrsScratch
          ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
              (leBytes32 (Accel.curveDbl Accel.secpP
                (beBytesToNat xBE) (beBytesToNat yBE)).1)
          ** bytesRegion (arenaB + 32)
              (leBytes32 (Accel.curveDbl Accel.secpP
                (beBytesToNat xBE) (beBytesToNat yBE)).2)
          ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY)
        (by pcf) hmv11
      have hcallL1F := cpsTripleWithin_frameR
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion (outPtr + 32) oY
          ** bytesRegion (arenaB + 32)
              (leBytes32 (Accel.curveDbl Accel.secpP
                (beBytesToNat xBE) (beBytesToNat yBE)).2))
        (by pcf) hcallL1
      have he1 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hla5F hcurveF
      have he2 := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          rw [ownsCsrs1011] at hp
          simp only [regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp
          xperm_hyp hp) he1 hla10'F
      have he3 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) he2 hmv11F
      have he4 := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          -- release t0 into the callee scratch
          have hp1 : (((.x5 : Reg) ↦ᵣ (GuestAddrs.secc_le_p1 : Word))
              ** ((((.x1 : Reg)) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word))
                ** ((.x10 : Reg) ↦ᵣ (GuestAddrs.secc_le_p1 : Word))
                ** ((.x11 : Reg) ↦ᵣ outPtr) ** regOwns csrsScratch
                ** bytesRegion outPtr oX
                ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).1)
                ** bytesRegion (arenaB + 32)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).2)
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
                ** (.x9 ↦ᵣ outPtr)
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion (outPtr + 32) oY)) h := by
            xperm_hyp hp
          have hp2 := sepConj_mono (regIs_to_regOwn .x5 _)
            (fun _ hh => hh) h hp1
          have hp3 : (regOwns convScratch
              ** ((((.x1 : Reg)) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word))
                ** ((.x10 : Reg) ↦ᵣ (GuestAddrs.secc_le_p1 : Word))
                ** ((.x11 : Reg) ↦ᵣ outPtr)
                ** bytesRegion outPtr oX
                ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).1)
                ** bytesRegion (arenaB + 32)
                    (leBytes32 (Accel.curveDbl Accel.secpP
                      (beBytesToNat xBE) (beBytesToNat yBE)).2)
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
                ** (.x9 ↦ᵣ outPtr)
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion (outPtr + 32) oY)) h := by
            rw [ownsConvSplit5]
            xperm_hyp hp2
          xperm_hyp hp3) he3 hcallL1F
      have he4' : cpsTripleWithin
          (7 + ((secfLeToBeFn 0 0 [] []).body.steps + 1))
          ((GuestAddrs.secp256k1_point_double + 96) : Word) ((GuestAddrs.secp256k1_point_double + 124) : Word) pdCr
          ((regOwn .x5)
            ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word)) ** regOwns csrsRest
              ** bytesRegion arenaB (setBytes (setBytes ws 0 ws₁) 0x20 ws₂)
              ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
              ** (.x9 ↦ᵣ outPtr)
              ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
              ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY))
          (fun hp => ∃ oX',
            ((⌜beBytesToNat oX' = wsNat256 (leBytes32 (Accel.curveDbl
                Accel.secpP (beBytesToNat xBE) (beBytesToNat yBE)).1) 0
              ∧ oX'.length = 32⌝
              ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 124) : Word)) ** regOwns exposedRegs
              ** bytesRegion outPtr oX'
              ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                  (leBytes32 (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)).1)
              ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
              ** (.x9 ↦ᵣ outPtr)
              ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
              ** bytesRegion (outPtr + 32) oY
              ** bytesRegion (arenaB + 32)
                  (leBytes32 (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)).2))) hp) := by
        refine cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
            (fun h hq => ?_) he4)
        have hq1 : ((fun hp => ∃ ws',
            ((⌜beBytesToNat ws' = wsNat256 (leBytes32 (Accel.curveDbl
                  Accel.secpP (beBytesToNat xBE) (beBytesToNat yBE)).1) 0
              ∧ ws'.length = 32⌝
              ** regOwns exposedRegs ** bytesRegion outPtr ws'
              ** bytesRegion (GuestAddrs.secc_le_p1 : Word)
                  (leBytes32 (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)).1))) hp)
            ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 124) : Word))
              ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
              ** (.x9 ↦ᵣ outPtr)
              ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
              ** bytesRegion (outPtr + 32) oY
              ** bytesRegion (arenaB + 32)
                  (leBytes32 (Accel.curveDbl Accel.secpP
                    (beBytesToNat xBE) (beBytesToNat yBE)).2))
            : Assertion) h := by
          xperm_hyp hq
        obtain ⟨oX', hin⟩ := (sepConj_exists_left h).mp hq1
        exact ⟨oX', by xperm_hyp hin⟩
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
        (cpsTripleWithin_seq_exists_same_cr he4' hC)
      -- reassemble the staging point around the written `_y` window,
      -- and split off `t0` ownership
      rw [ownsSplit5] at hp
      have hp1 : ((regOwns [.x5])
          ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word)) ** regOwns csrsRest
            ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
            ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
            ** (bytesRegion (arenaB + BitVec.ofNat 64 0x20) ws₂
              ** windowRest arenaB (setBytes ws 0 ws₁) 0x20 32))) h := by
        rw [show arenaB + BitVec.ofNat 64 0x20 = (arenaB + 32)
          from by decide]
        xperm_hyp hp
      rw [← bytesRegion_window_update arenaB (setBytes ws 0 ws₁) ws₂ 0x20 32
        (by rw [length_setBytes]; omega) (by norm_num) (by norm_num)
        hf2b] at hp1
      simp only [regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp1
      xperm_hyp hp1
    -- ---- a0 := s0 + 32 ; la a1, _y ; call secf_be_to_le ----
    have haddi10 := liftCode (cr' := pdCr)
      (addi_own_within .x10 .x8 inPtr (32 : BitVec 12) ((GuestAddrs.secp256k1_point_double + 76) : Word)
        (by decide))
      (by code_mem)
    rw [show ((GuestAddrs.secp256k1_point_double + 76) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 80) : Word) from by decide,
      show inPtr + signExtend12 (32 : BitVec 12) = inPtr + 32 from by
        rw [show signExtend12 (32 : BitVec 12) = (32 : Word)
          from by decide]] at haddi10
    have hla11' := la_own_within .x11 (fun vOld =>
      la_materialize_within .x11 vOld ((GuestAddrs.secp256k1_point_double + 80) : Word)
        (GuestAddrs.secc_le_p1 : Word) (by decide) (by decide)
        (by code_mem) (by code_mem))
    rw [show ((GuestAddrs.secp256k1_point_double + 80) : Word) + 8 = ((GuestAddrs.secp256k1_point_double + 88) : Word) from by decide]
      at hla11'
    have haddiS11 := liftCode (cr' := pdCr)
      (addi_spec_gen_same_within .x11 (GuestAddrs.secc_le_p1 : Word) (32 : BitVec 12)
        ((GuestAddrs.secp256k1_point_double + 88) : Word) (by decide))
      (by code_mem)
    rw [show ((GuestAddrs.secp256k1_point_double + 88) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 92) : Word) from by decide,
      show (GuestAddrs.secc_le_p1 : Word) + signExtend12 (32 : BitVec 12)
        = (arenaB + 32) from by decide] at haddiS11
    have hflatB2 := secfBeToLeFlat_spec ((GuestAddrs.secp256k1_point_double + 96) : Word) (inPtr + 32)
      (arenaB + 32) yBE
      (((setBytes ws 0 ws₁).drop 0x20).take 32)
      hylen
      (by
        rw [List.length_take, List.length_drop, length_setBytes, hwslen]
        omega)
      hwfY hrwwA2
      (by rw [hinT]; omega) (by decide)
      (by
        rw [hdstA2, hinT]
        rcases hdIn with h | h
        · left
          omega
        · right
          omega)
      (by decide)
    have hcalleeB2 : cpsTripleWithin
        ((secfBeToLeFn (inPtr + 32) (arenaB + 32) yBE
          (((setBytes ws 0 ws₁).drop 0x20).take 32)).body.steps + 1)
        (GuestAddrs.secf_be_to_le : Word) ((GuestAddrs.secp256k1_point_double + 96) : Word) pdCr
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word))
          ** ((.x10 ↦ᵣ (inPtr + 32)) ** (.x11 ↦ᵣ (arenaB + 32))
            ** regOwns convScratch
            ** bytesRegion (arenaB + 32)
                (((setBytes ws 0 ws₁).drop 0x20).take 32)
            ** bytesRegion (inPtr + 32) yBE))
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word))
          ** (fun hp => ∃ ws',
            ((⌜wsNat256 ws' 0 = beBytesToNat yBE ∧ ws'.length = 32⌝
              ** regOwns exposedRegs
              ** bytesRegion (arenaB + 32) ws'
              ** bytesRegion (inPtr + 32) yBE)) hp)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun h hq => ?_) hflatB2
      obtain ⟨ws', hin⟩ := hq
      refine exists_pull h ⟨ws', ?_⟩
      xperm_hyp hin
    have hcallB2 := callWithin_spec ((GuestAddrs.secp256k1_point_double + 92) : Word) (GuestAddrs.secf_be_to_le : Word)
      ((GuestAddrs.secp256k1_point_double + 76) : Word)
      (jalOff GuestAddrs.secf_be_to_le
        (GuestAddrs.secp256k1_point_double + 92))
      ((secfBeToLeFn (inPtr + 32) (arenaB + 32) yBE
        (((setBytes ws 0 ws₁).drop 0x20).take 32)).body.steps + 1)
      (by decide) (by code_mem) (by pcf) hcalleeB2
    rw [show ((GuestAddrs.secp256k1_point_double + 92) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 96) : Word) from by decide,
      show (secfBeToLeFn (inPtr + 32) (arenaB + 32) yBE
          (((setBytes ws 0 ws₁).drop 0x20).take 32)).body.steps
        = (secfBeToLeFn 0 0 [] []).body.steps from rfl] at hcallB2
    -- ---- frames + chain ----
    have haddi10F := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 76) : Word)) ** regOwn .x11
        ** regOwns convScratch
        ** bytesRegion (GuestAddrs.secc_le_p1 : Word) ws₁ ** bytesRegion inPtr xBE
        ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ outPtr)
        ** bytesRegion (inPtr + 32) yBE
        ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
        ** windowRest arenaB ws 0 32)
      (by
        exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regOwn
          (pcFree_sepConj (pcFree_regOwns _)
            (pcFree_sepConj (bytesRegion_pcFree _ _)
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj (bytesRegion_pcFree _ _)
                    (pcFree_sepConj (bytesRegion_pcFree _ _)
                      (pcFree_sepConj (bytesRegion_pcFree _ _)
                        (pcFree_windowRest _ _ _ _)))))))))))
      haddi10
    have hla11'F := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 76) : Word))
        ** ((.x10 : Reg) ↦ᵣ (inPtr + 32)) ** regOwns convScratch
        ** bytesRegion (GuestAddrs.secc_le_p1 : Word) ws₁ ** bytesRegion inPtr xBE
        ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
        ** bytesRegion (inPtr + 32) yBE
        ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
        ** windowRest arenaB ws 0 32)
      (by
        exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (pcFree_regOwns _)
            (pcFree_sepConj (bytesRegion_pcFree _ _)
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs
                    (pcFree_sepConj (bytesRegion_pcFree _ _)
                      (pcFree_sepConj (bytesRegion_pcFree _ _)
                        (pcFree_sepConj (bytesRegion_pcFree _ _)
                          (pcFree_windowRest _ _ _ _))))))))))))
      hla11'
    have haddiS11F := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 76) : Word))
        ** ((.x10 : Reg) ↦ᵣ (inPtr + 32)) ** regOwns convScratch
        ** bytesRegion (GuestAddrs.secc_le_p1 : Word) ws₁ ** bytesRegion inPtr xBE
        ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
        ** bytesRegion (inPtr + 32) yBE
        ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
        ** windowRest arenaB ws 0 32)
      (by
        exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (pcFree_regOwns _)
            (pcFree_sepConj (bytesRegion_pcFree _ _)
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs
                    (pcFree_sepConj (bytesRegion_pcFree _ _)
                      (pcFree_sepConj (bytesRegion_pcFree _ _)
                        (pcFree_sepConj (bytesRegion_pcFree _ _)
                          (pcFree_windowRest _ _ _ _))))))))))))
      haddiS11
    have hcallB2F := cpsTripleWithin_frameR
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
        ** bytesRegion inPtr xBE
        ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
        ** windowRest arenaB (setBytes ws 0 ws₁) 0x20 32)
      (by
        exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj (bytesRegion_pcFree _ _)
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (pcFree_sepConj (bytesRegion_pcFree _ _)
                  (pcFree_windowRest _ _ _ _)))))))
      hcallB2
    have hf1' := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) haddi10F hla11'F
    have hf2' := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hf1' haddiS11F
    have hf3' := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        -- reassemble the `_x` splice, then focus the `_y` window out of it
        have hp1 : (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 76) : Word))
            ** ((.x10 : Reg) ↦ᵣ (inPtr + 32))
            ** ((.x11 : Reg) ↦ᵣ (arenaB + 32))
            ** regOwns convScratch ** bytesRegion inPtr xBE
            ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion (inPtr + 32) yBE
            ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
            ** (bytesRegion (arenaB + BitVec.ofNat 64 0) ws₁
              ** windowRest arenaB ws 0 32)) h := by
          rw [show arenaB + BitVec.ofNat 64 0 = (GuestAddrs.secc_le_p1 : Word)
            from by decide]
          xperm_hyp hp
        rw [← bytesRegion_window_update arenaB ws ws₁ 0 32 (by omega)
          (by norm_num) (by norm_num) hf1b] at hp1
        rw [bytesRegion_window_focus arenaB (setBytes ws 0 ws₁) 0x20 32
              (by rw [length_setBytes]; omega) (by norm_num) (by norm_num),
            show arenaB + BitVec.ofNat 64 0x20 = (arenaB + 32)
              from by decide] at hp1
        xperm_hyp hp1) hf2' hcallB2F
    have hf3'' : cpsTripleWithin
        (5 + ((secfBeToLeFn 0 0 [] []).body.steps + 1))
        ((GuestAddrs.secp256k1_point_double + 76) : Word) ((GuestAddrs.secp256k1_point_double + 96) : Word) pdCr
        ((regOwn .x10)
          ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 76) : Word)) ** regOwn .x11
            ** regOwns convScratch
            ** bytesRegion (GuestAddrs.secc_le_p1 : Word) ws₁ ** bytesRegion inPtr xBE
            ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion (inPtr + 32) yBE
            ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
            ** windowRest arenaB ws 0 32))
        (fun hp => ∃ ws₂,
          ((⌜wsNat256 ws₂ 0 = beBytesToNat yBE ∧ ws₂.length = 32⌝
            ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word)) ** regOwns exposedRegs
            ** bytesRegion (arenaB + 32) ws₂
            ** bytesRegion (inPtr + 32) yBE
            ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion inPtr xBE
            ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
            ** windowRest arenaB (setBytes ws 0 ws₁) 0x20 32)) hp) := by
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun h hq => ?_) hf3')
      have hq1 : ((fun hp => ∃ ws',
          ((⌜wsNat256 ws' 0 = beBytesToNat yBE ∧ ws'.length = 32⌝
            ** regOwns exposedRegs
            ** bytesRegion (arenaB + 32) ws'
            ** bytesRegion (inPtr + 32) yBE)) hp)
          ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 96) : Word))
            ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion inPtr xBE
            ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
            ** windowRest arenaB (setBytes ws 0 ws₁) 0x20 32)
          : Assertion) h := by
        xperm_hyp hq
      obtain ⟨ws₂, hin⟩ := (sepConj_exists_left h).mp hq1
      exact ⟨ws₂, by xperm_hyp hin⟩
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
      (cpsTripleWithin_seq_exists_same_cr hf3'' hB2)
    rw [ownsSplit1011] at hp
    simp only [regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp
    xperm_hyp hp
  -- ---- prefix: mv;mv;addi ; call is_zero (verdict 0) ; beq TAKEN ;
  --      mv a0,s0 ; la a1,_x ; call secf_be_to_le ----
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
    if_neg hnlz] at hcall1
  -- ---- beq a0, x0 — TAKEN (a0 = 0) ----
  have hbeq := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code (cr' := pdCr) (by code_mem)
      (beq_spec_gen_within .x10 .x0 (28 : BitVec 13) (0 : Word) (0 : Word)
        ((GuestAddrs.secp256k1_point_double + 32) : Word)))
    (fun hp hq => by
      have hq1 : ((⌜(0 : Word) ≠ (0 : Word)⌝ : Assertion)
          ** ((.x10 ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))) hp := by
        xperm_hyp hq
      exact absurd rfl ((sepConj_pure_left hp).mp hq1).1)
  rw [show ((GuestAddrs.secp256k1_point_double + 32) : Word) + signExtend13 (28 : BitVec 13)
      = ((GuestAddrs.secp256k1_point_double + 60) : Word) from by decide] at hbeq
  -- ---- mv a0, s0 ; la a1, secc_le_p1 ----
  have hm3 := liftCode (cr' := pdCr)
    (mv_spec_gen_within .x10 .x8 inPtr (0 : Word) ((GuestAddrs.secp256k1_point_double + 60) : Word)
      (by decide))
    (by code_mem)
  rw [show ((GuestAddrs.secp256k1_point_double + 60) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 64) : Word) from by decide]
    at hm3
  have hla11 := la_own_within .x11 (fun vOld =>
    la_materialize_within .x11 vOld ((GuestAddrs.secp256k1_point_double + 64) : Word) (GuestAddrs.secc_le_p1 : Word)
      (by decide) (by decide) (by code_mem) (by code_mem))
  rw [show ((GuestAddrs.secp256k1_point_double + 64) : Word) + 8 = ((GuestAddrs.secp256k1_point_double + 72) : Word) from by decide]
    at hla11
  -- ---- call secf_be_to_le(in, secc_le_p1) ----
  have hflatB1 := secfBeToLeFlat_spec ((GuestAddrs.secp256k1_point_double + 76) : Word) inPtr
    (GuestAddrs.secc_le_p1 : Word) xBE ((ws.drop 0).take 32)
    hxlen
    (by
      rw [List.length_take, List.length_drop, hwslen]
      omega)
    hwfX hrwwA
    (by omega) (by decide)
    (by
      rw [hdstA]
      rcases hdIn with h | h
      · left
        omega
      · right
        omega)
    (by decide)
  have hcalleeB1 : cpsTripleWithin
      ((secfBeToLeFn inPtr (GuestAddrs.secc_le_p1 : Word) xBE
        ((ws.drop 0).take 32)).body.steps + 1)
      (GuestAddrs.secf_be_to_le : Word) ((GuestAddrs.secp256k1_point_double + 76) : Word) pdCr
      (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 76) : Word))
        ** ((.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ (GuestAddrs.secc_le_p1 : Word))
          ** regOwns convScratch
          ** bytesRegion (GuestAddrs.secc_le_p1 : Word) ((ws.drop 0).take 32)
          ** bytesRegion inPtr xBE))
      (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 76) : Word))
        ** (fun hp => ∃ ws',
          ((⌜wsNat256 ws' 0 = beBytesToNat xBE ∧ ws'.length = 32⌝
            ** regOwns exposedRegs
            ** bytesRegion (GuestAddrs.secc_le_p1 : Word) ws'
            ** bytesRegion inPtr xBE)) hp)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => ?_) hflatB1
    obtain ⟨ws', hin⟩ := hq
    refine exists_pull h ⟨ws', ?_⟩
    xperm_hyp hin
  have hcallB1 := callWithin_spec ((GuestAddrs.secp256k1_point_double + 72) : Word) (GuestAddrs.secf_be_to_le : Word)
    ((GuestAddrs.secp256k1_point_double + 32) : Word)
    (jalOff GuestAddrs.secf_be_to_le
      (GuestAddrs.secp256k1_point_double + 72))
    ((secfBeToLeFn inPtr (GuestAddrs.secc_le_p1 : Word) xBE
      ((ws.drop 0).take 32)).body.steps + 1)
    (by decide) (by code_mem) (by pcf) hcalleeB1
  rw [show ((GuestAddrs.secp256k1_point_double + 72) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 76) : Word) from by decide,
    show (secfBeToLeFn inPtr (GuestAddrs.secc_le_p1 : Word) xBE
        ((ws.drop 0).take 32)).body.steps
      = (secfBeToLeFn 0 0 [] []).body.steps from rfl] at hcallB1
  -- ---- frames + chain ----
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
      ** (.x9 ↦ᵣ outPtr) ** regOwn .x11 ** regOwns convScratch
      ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
      ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
      ** bytesRegion arenaB ws)
    (by pcf) hm3
  have hla11F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 32) : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))
      ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr) ** (.x10 ↦ᵣ inPtr)
      ** regOwns convScratch
      ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
      ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
      ** bytesRegion arenaB ws)
    (by pcf) hla11
  have hcallB1F := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ outPtr)
      ** bytesRegion (inPtr + 32) yBE
      ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
      ** windowRest arenaB ws 0 32)
    (by
      exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (bytesRegion_pcFree _ _)
            (pcFree_sepConj (bytesRegion_pcFree _ _)
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (pcFree_windowRest _ _ _ _)))))))
    hcallB1
  have hg1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hm1F hm2F
  have hg2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hg1 haddiF
  have hg3 := cpsTripleWithin_seq_perm_same_cr
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
      xperm_hyp hp3) hg2 hcall1F
  have hg4 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hg3 hbeqF
  have hg5 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      -- strip the branch verdict, split x10/x11 back out of a0Rest
      have hp1 : ((⌜(0 : Word) = (0 : Word)⌝ : Assertion)
          ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))
            ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 32) : Word)) ** (.x8 ↦ᵣ inPtr)
            ** (.x9 ↦ᵣ outPtr) ** regOwns a0Rest
            ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
            ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
            ** bytesRegion arenaB ws)) h := by
        xperm_hyp hp
      have hp2 := ((sepConj_pure_left h).mp hp1).2
      rw [ownsA0Split11] at hp2
      xperm_hyp hp2) hg4 hm3F
  have hg6 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hg5 hla11F
  have hg7 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      -- carve the `_x` window out of the staging point
      rw [bytesRegion_window_focus arenaB ws 0 32 (by omega) (by norm_num)
            (by norm_num),
          show arenaB + BitVec.ofNat 64 0 = (GuestAddrs.secc_le_p1 : Word)
            from by decide] at hp
      xperm_hyp hp) hg6 hcallB1F
  have hg7' : cpsTripleWithin
      (10 + ((secfIsZero32Fn 0 []).body.steps + 1)
        + ((secfBeToLeFn 0 0 [] []).body.steps + 1))
      ((GuestAddrs.secp256k1_point_double + 16) : Word) ((GuestAddrs.secp256k1_point_double + 76) : Word) pdCr
      (((.x10 ↦ᵣ inPtr) ** (.x8 ↦ᵣ v8))
        ** (((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))
          ** (.x9 ↦ᵣ v9) ** (.x11 ↦ᵣ outPtr) ** regOwns convScratch
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
          ** bytesRegion arenaB ws))
      (fun hp => ∃ ws₁,
        ((⌜wsNat256 ws₁ 0 = beBytesToNat xBE ∧ ws₁.length = 32⌝
          ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 76) : Word)) ** regOwns exposedRegs
          ** bytesRegion (GuestAddrs.secc_le_p1 : Word) ws₁ ** bytesRegion inPtr xBE
          ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
          ** (.x9 ↦ᵣ outPtr)
          ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
          ** windowRest arenaB ws 0 32)) hp) := by
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun h hq => ?_) hg7)
    have hq1 : ((fun hp => ∃ ws',
        ((⌜wsNat256 ws' 0 = beBytesToNat xBE ∧ ws'.length = 32⌝
          ** regOwns exposedRegs
          ** bytesRegion (GuestAddrs.secc_le_p1 : Word) ws'
          ** bytesRegion inPtr xBE)) hp)
        ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secp256k1_point_double + 76) : Word))
          ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ inPtr)
          ** (.x9 ↦ᵣ outPtr)
          ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
          ** windowRest arenaB ws 0 32)
        : Assertion) h := by
      xperm_hyp hq
    obtain ⟨ws₁, hin⟩ := (sepConj_exists_left h).mp hq1
    exact ⟨ws₁, by xperm_hyp hin⟩
  have hcore := cpsTripleWithin_seq_exists_same_cr hg7' hB1
  have hcoreF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
      ** ((sp0 + signExtend12 (-32 : BitVec 12)
            + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
      ** ((sp0 + signExtend12 (-32 : BitVec 12)
            + signExtend12 (8 : BitVec 12)) ↦ₘ v8)
      ** ((sp0 + signExtend12 (-32 : BitVec 12)
            + signExtend12 (16 : BitVec 12)) ↦ₘ v9))
    (by pcf) hcore
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun h hq => ?_)
    (cpsTripleWithin_mono_nSteps (by omega) hcoreF)
  · simp only [pdFrame, regsAt, frameSlotsSaved, pdVals,
      List.foldr_cons, List.foldr_nil, sepConj_emp_right'] at hp
    xperm_hyp hp
  · simp only [pdFrame, regsAt, frameSlotsSaved, pdVals, pdValsReg,
      List.foldr_cons, List.foldr_nil, sepConj_emp_right']
    xperm_hyp hq

end Secp256k1PointDoubleSAsm

end EvmAsm.Codegen
