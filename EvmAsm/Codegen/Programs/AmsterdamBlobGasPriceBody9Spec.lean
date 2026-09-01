
/-
Tail window part 2b: the copy arm (`tail_copyarm`), extracted from the core
composition for the file-size cap. Same namespace as part 1.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody7Spec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody5Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody6Spec

set_option maxRecDepth 8000

private theorem cpsTripleWithin_add_pure_post {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {fact : Prop}
    (h : cpsTripleWithin n entry exit_ cr P Q)
    (hpre_fact : ∀ h, P h → fact) :
    cpsTripleWithin n entry exit_ cr P (Q ** ⌜fact⌝) := by
  intro R hR s hcr hPR hpc
  have hPRcopy := hPR
  obtain ⟨hstate, hcompat, hPR'⟩ := hPR
  obtain ⟨hPstate, hRstate, hd, hu, hP, hRstate'⟩ := hPR'
  have hfact : fact := hpre_fact hPstate hP
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h R hR s hcr hPRcopy hpc
  obtain ⟨hpost, hpostcomp, hQR'⟩ := hQR
  refine ⟨k, hk, s', hstep, hpc', ?_⟩
  have hPureQR : (⌜fact⌝ ** (Q ** R)).holdsFor s' := by
    exact ⟨hpost, hpostcomp, (sepConj_pure_left hpost).2 ⟨hfact, hQR'⟩⟩
  exact holdsFor_sepConj_pull_second.mpr hPureQR

/-- The copy arm: li t5, 0; 31 byte rounds; the final round; li a0, 0; j B+968.
Extracted from `tail_core` (file-size cap); consumes the bne fall post `FP`
and produces the status-0 exit shape. -/
theorem tail_copyarm (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (_v6 v7 v18 v19 v20 v28 v29 v30 v31 : Word)
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 291 (PriceK + 916) (PriceK + 968) priceCode
      ((((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) = (0 : Word)⌝) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x6 ↦ᵣ q5) ** frameSlotsSaved priceFrame newSp vals **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ o0) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) ** ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) **
       FR))) (((.x10 ↦ᵣ (0 : Word)) **       ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) ** (.x29 ↦ᵣ (32 : Word)) **
       (.x30 ↦ᵣ BitVec.ofNat 64 32) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q0 (0)).zeroExtend 64).truncate 8))) ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ (vals .x1)) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
       (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR))) := by
  have hFRARG0 : (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR).pcFree := by unfold tailFR0; pcFree; exact hFR
  have hFRARG1 : (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR).pcFree := by unfold tailFR1; pcFree; exact hFR
  have hFRARG2 : (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR).pcFree := by unfold tailFR2; pcFree; exact hFR
  have hFRARG3 : (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR).pcFree := by unfold tailFR3; pcFree; exact hFR
  -- copy arm: li t5, 0 ; 31 byte rounds ; final round ; li a0, 0 ; j 968
  have hLIl := li_spec_gen_within .x30 v30 (0 : Word) (PriceK + 916) (by decide)
  have hLIlF : cpsTripleWithin 1 (PriceK + 916) (PriceK + 920) priceCode
      ((.x30 ↦ᵣ v30) **
        (((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) = (0 : Word)⌝) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x31 ↦ᵣ v31) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) ** ((outPtr + BitVec.ofNat 64 0) ↦ₘ o0) **
       ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) ** ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR))) ((.x30 ↦ᵣ (0 : Word)) **
        (((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) = (0 : Word)⌝) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x31 ↦ᵣ v31) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) ** ((outPtr + BitVec.ofNat 64 0) ↦ₘ o0) **
       ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) ** ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR))) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hLIl)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[229]'(by decide) = .LI .x30 (0 : Word) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 916) amsterdamBlobGasPriceU256_prog
      229 (.LI .x30 (0 : Word)) (by decide) (by decide) hins (by decide) a i hi
  have hLIlF' : cpsTripleWithin 1 (PriceK + 916) (PriceK + 920) priceCode
      ((((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) = (0 : Word)⌝) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x6 ↦ᵣ q5) ** frameSlotsSaved priceFrame newSp vals **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ o0) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) ** ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) **
       FR))) ((.x30 ↦ᵣ (0 : Word)) **
        (((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) = (0 : Word)⌝) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x31 ↦ᵣ v31) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) ** ((outPtr + BitVec.ofNat 64 0) ↦ₘ o0) **
       ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) ** ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hLIlF
  have hENTRY : cpsTripleWithin 1 (PriceK + 916) (PriceK + 920) priceCode
      ((((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) = (0 : Word)⌝) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x6 ↦ᵣ q5) ** frameSlotsSaved priceFrame newSp vals **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ o0) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) ** ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) **
       FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr v7 v28 v29 q3 (o0) 24 0 0
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) := by
    refine cpsTripleWithin_weaken (fun _ hx => hx) ?_ hLIlF'
    intro h hx
    rw [preS_eq]
    rw [tailFR0_eq]
    obtain ⟨h1, h2, hd, hu, hx30, hfli⟩ := hx
    have hfli2 : (((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word))) **
              ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x31 ↦ᵣ v31) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) ** ((outPtr + BitVec.ofNat 64 0) ↦ₘ o0) **
       ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) ** ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR)) h2 :=
      pure_drop_mid _ hfli
    obtain ⟨g50, gtail, gd50t, gu50t, hg50, hgtail⟩ := hfli2
    obtain ⟨g5, g0, gd50, gu50, hg5, hg0⟩ := hg50
    obtain ⟨gq4, gq5t, gdq, guq, hq4, hq5t⟩ := hgtail
    obtain ⟨gq5, gt, gdq5, guq5, hq5, hgt⟩ := hq5t
    have hv4 : ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12))
        = ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) := by
      rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
        show (32 : Word) = BitVec.ofNat 64 32 from rfl]
    have hq4' : (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) gq4 := by
      rw [← hv4]; exact hq4
    have hv5 : ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12))
        = ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) := by
      rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide,
        show (40 : Word) = BitVec.ofNat 64 40 from rfl]
    have hq5' : (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) gq5 := by
      rw [← hv5]; exact hq5
    have hx2 : ((.x30 ↦ᵣ BitVec.ofNat 64 0) ** (((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word))) ** ((((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** ((((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
              ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x31 ↦ᵣ v31) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) ** ((outPtr + BitVec.ofNat 64 0) ↦ₘ o0) **
       ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) ** ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR))))) h :=
      ⟨h1, h2, hd, hu, hx30, ⟨g50, gtail, gd50t, gu50t, ⟨g5, g0, gd50, gu50, hg5, hg0⟩,
        ⟨gq4, gq5t, gdq, guq, hq4', ⟨gq5, gt, gdq5, guq5, hq5', hgt⟩⟩⟩⟩
    xperm_hyp hx2
  have hR0 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      0 24 0 (by omega) (by decide) (by decide) q3 (o0)
      v7 v28 v29 (by decide) (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG0
  have hT0 := cpsBranchWithin_takenPath hR0 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep0 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr v7 v28 v29 q3 (o0) 24 0 0
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (7)).zeroExtend 64) (outPtr + BitVec.ofNat 64 0) (32 : Word) q3 ((replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8))) 24 0 1
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 0 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (0 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT0
  have hR1 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      1 24 0 (by omega) (by decide) (by decide) q3 ((replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)))
      ((extractByte q3 (7)).zeroExtend 64) (outPtr + BitVec.ofNat 64 0) (32 : Word) (by decide) (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG0
  have hT1 := cpsBranchWithin_takenPath hR1 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep1 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (7)).zeroExtend 64) (outPtr + BitVec.ofNat 64 0) (32 : Word) q3 ((replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8))) 24 0 1
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (6)).zeroExtend 64) (outPtr + BitVec.ofNat 64 1) (32 : Word) q3 ((replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8))) 24 0 2
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 1 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (1 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT1
  have hR2 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      2 24 0 (by omega) (by decide) (by decide) q3 ((replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)))
      ((extractByte q3 (6)).zeroExtend 64) (outPtr + BitVec.ofNat 64 1) (32 : Word) (by decide) (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG0
  have hT2 := cpsBranchWithin_takenPath hR2 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep2 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (6)).zeroExtend 64) (outPtr + BitVec.ofNat 64 1) (32 : Word) q3 ((replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8))) 24 0 2
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (5)).zeroExtend 64) (outPtr + BitVec.ofNat 64 2) (32 : Word) q3 ((replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8))) 24 0 3
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 2 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (2 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT2
  have hR3 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      3 24 0 (by omega) (by decide) (by decide) q3 ((replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)))
      ((extractByte q3 (5)).zeroExtend 64) (outPtr + BitVec.ofNat 64 2) (32 : Word) (by decide) (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG0
  have hT3 := cpsBranchWithin_takenPath hR3 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep3 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (5)).zeroExtend 64) (outPtr + BitVec.ofNat 64 2) (32 : Word) q3 ((replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8))) 24 0 3
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (4)).zeroExtend 64) (outPtr + BitVec.ofNat 64 3) (32 : Word) q3 ((replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8))) 24 0 4
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 3 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (3 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT3
  have hR4 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      4 24 0 (by omega) (by decide) (by decide) q3 ((replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)))
      ((extractByte q3 (4)).zeroExtend 64) (outPtr + BitVec.ofNat 64 3) (32 : Word) (by decide) (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG0
  have hT4 := cpsBranchWithin_takenPath hR4 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep4 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (4)).zeroExtend 64) (outPtr + BitVec.ofNat 64 3) (32 : Word) q3 ((replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8))) 24 0 4
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (3)).zeroExtend 64) (outPtr + BitVec.ofNat 64 4) (32 : Word) q3 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8))) 24 0 5
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 4 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (4 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT4
  have hR5 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      5 24 0 (by omega) (by decide) (by decide) q3 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)))
      ((extractByte q3 (3)).zeroExtend 64) (outPtr + BitVec.ofNat 64 4) (32 : Word) (by decide) (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG0
  have hT5 := cpsBranchWithin_takenPath hR5 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep5 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (3)).zeroExtend 64) (outPtr + BitVec.ofNat 64 4) (32 : Word) q3 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8))) 24 0 5
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (2)).zeroExtend 64) (outPtr + BitVec.ofNat 64 5) (32 : Word) q3 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8))) 24 0 6
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 5 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (5 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT5
  have hR6 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      6 24 0 (by omega) (by decide) (by decide) q3 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)))
      ((extractByte q3 (2)).zeroExtend 64) (outPtr + BitVec.ofNat 64 5) (32 : Word) (by decide) (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG0
  have hT6 := cpsBranchWithin_takenPath hR6 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep6 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (2)).zeroExtend 64) (outPtr + BitVec.ofNat 64 5) (32 : Word) q3 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8))) 24 0 6
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (1)).zeroExtend 64) (outPtr + BitVec.ofNat 64 6) (32 : Word) q3 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8))) 24 0 7
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 6 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (6 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT6
  have hR7 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      7 24 0 (by omega) (by decide) (by decide) q3 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)))
      ((extractByte q3 (1)).zeroExtend 64) (outPtr + BitVec.ofNat 64 6) (32 : Word) (by decide) (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG0
  have hT7 := cpsBranchWithin_takenPath hR7 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep7 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (1)).zeroExtend 64) (outPtr + BitVec.ofNat 64 6) (32 : Word) q3 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8))) 24 0 7
      (tailFR0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (0)).zeroExtend 64) (outPtr + BitVec.ofNat 64 7) (32 : Word) q2 (o1) 16 8 8
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 7 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (7 + 1) from by decide) _ hx
      rw [preS_eq]
      rw [tailFR0_eq] at hx'
      rw [tailFR1_eq]
      xperm_hyp hx') hT7
  have hR8 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      8 16 8 (by omega) (by decide) (by decide) q2 (o1)
      ((extractByte q3 (0)).zeroExtend 64) (outPtr + BitVec.ofNat 64 7) (32 : Word) (by decide) (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG1
  have hT8 := cpsBranchWithin_takenPath hR8 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep8 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q3 (0)).zeroExtend 64) (outPtr + BitVec.ofNat 64 7) (32 : Word) q2 (o1) 16 8 8
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (7)).zeroExtend 64) (outPtr + BitVec.ofNat 64 8) (32 : Word) q2 ((replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8))) 16 8 9
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 8 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (8 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT8
  have hR9 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      9 16 8 (by omega) (by decide) (by decide) q2 ((replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)))
      ((extractByte q2 (7)).zeroExtend 64) (outPtr + BitVec.ofNat 64 8) (32 : Word) (by decide) (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG1
  have hT9 := cpsBranchWithin_takenPath hR9 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep9 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (7)).zeroExtend 64) (outPtr + BitVec.ofNat 64 8) (32 : Word) q2 ((replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8))) 16 8 9
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (6)).zeroExtend 64) (outPtr + BitVec.ofNat 64 9) (32 : Word) q2 ((replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8))) 16 8 10
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 9 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (9 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT9
  have hR10 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      10 16 8 (by omega) (by decide) (by decide) q2 ((replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)))
      ((extractByte q2 (6)).zeroExtend 64) (outPtr + BitVec.ofNat 64 9) (32 : Word) (by decide) (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG1
  have hT10 := cpsBranchWithin_takenPath hR10 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep10 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (6)).zeroExtend 64) (outPtr + BitVec.ofNat 64 9) (32 : Word) q2 ((replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8))) 16 8 10
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (5)).zeroExtend 64) (outPtr + BitVec.ofNat 64 10) (32 : Word) q2 ((replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8))) 16 8 11
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 10 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (10 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT10
  have hR11 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      11 16 8 (by omega) (by decide) (by decide) q2 ((replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)))
      ((extractByte q2 (5)).zeroExtend 64) (outPtr + BitVec.ofNat 64 10) (32 : Word) (by decide) (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG1
  have hT11 := cpsBranchWithin_takenPath hR11 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep11 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (5)).zeroExtend 64) (outPtr + BitVec.ofNat 64 10) (32 : Word) q2 ((replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8))) 16 8 11
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (4)).zeroExtend 64) (outPtr + BitVec.ofNat 64 11) (32 : Word) q2 ((replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8))) 16 8 12
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 11 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (11 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT11
  have hR12 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      12 16 8 (by omega) (by decide) (by decide) q2 ((replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)))
      ((extractByte q2 (4)).zeroExtend 64) (outPtr + BitVec.ofNat 64 11) (32 : Word) (by decide) (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG1
  have hT12 := cpsBranchWithin_takenPath hR12 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep12 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (4)).zeroExtend 64) (outPtr + BitVec.ofNat 64 11) (32 : Word) q2 ((replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8))) 16 8 12
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (3)).zeroExtend 64) (outPtr + BitVec.ofNat 64 12) (32 : Word) q2 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8))) 16 8 13
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 12 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (12 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT12
  have hR13 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      13 16 8 (by omega) (by decide) (by decide) q2 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)))
      ((extractByte q2 (3)).zeroExtend 64) (outPtr + BitVec.ofNat 64 12) (32 : Word) (by decide) (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG1
  have hT13 := cpsBranchWithin_takenPath hR13 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep13 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (3)).zeroExtend 64) (outPtr + BitVec.ofNat 64 12) (32 : Word) q2 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8))) 16 8 13
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (2)).zeroExtend 64) (outPtr + BitVec.ofNat 64 13) (32 : Word) q2 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8))) 16 8 14
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 13 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (13 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT13
  have hR14 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      14 16 8 (by omega) (by decide) (by decide) q2 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)))
      ((extractByte q2 (2)).zeroExtend 64) (outPtr + BitVec.ofNat 64 13) (32 : Word) (by decide) (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG1
  have hT14 := cpsBranchWithin_takenPath hR14 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep14 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (2)).zeroExtend 64) (outPtr + BitVec.ofNat 64 13) (32 : Word) q2 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8))) 16 8 14
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (1)).zeroExtend 64) (outPtr + BitVec.ofNat 64 14) (32 : Word) q2 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8))) 16 8 15
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 14 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (14 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT14
  have hR15 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      15 16 8 (by omega) (by decide) (by decide) q2 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)))
      ((extractByte q2 (1)).zeroExtend 64) (outPtr + BitVec.ofNat 64 14) (32 : Word) (by decide) (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG1
  have hT15 := cpsBranchWithin_takenPath hR15 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep15 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (1)).zeroExtend 64) (outPtr + BitVec.ofNat 64 14) (32 : Word) q2 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8))) 16 8 15
      (tailFR1 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (0)).zeroExtend 64) (outPtr + BitVec.ofNat 64 15) (32 : Word) q1 (o2) 8 16 16
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 15 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (15 + 1) from by decide) _ hx
      rw [preS_eq]
      rw [tailFR1_eq] at hx'
      rw [tailFR2_eq]
      xperm_hyp hx') hT15
  have hR16 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      16 8 16 (by omega) (by decide) (by decide) q1 (o2)
      ((extractByte q2 (0)).zeroExtend 64) (outPtr + BitVec.ofNat 64 15) (32 : Word) (by decide) (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG2
  have hT16 := cpsBranchWithin_takenPath hR16 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep16 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q2 (0)).zeroExtend 64) (outPtr + BitVec.ofNat 64 15) (32 : Word) q1 (o2) 8 16 16
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (7)).zeroExtend 64) (outPtr + BitVec.ofNat 64 16) (32 : Word) q1 ((replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8))) 8 16 17
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 16 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (16 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT16
  have hR17 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      17 8 16 (by omega) (by decide) (by decide) q1 ((replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)))
      ((extractByte q1 (7)).zeroExtend 64) (outPtr + BitVec.ofNat 64 16) (32 : Word) (by decide) (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG2
  have hT17 := cpsBranchWithin_takenPath hR17 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep17 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (7)).zeroExtend 64) (outPtr + BitVec.ofNat 64 16) (32 : Word) q1 ((replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8))) 8 16 17
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (6)).zeroExtend 64) (outPtr + BitVec.ofNat 64 17) (32 : Word) q1 ((replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8))) 8 16 18
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 17 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (17 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT17
  have hR18 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      18 8 16 (by omega) (by decide) (by decide) q1 ((replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)))
      ((extractByte q1 (6)).zeroExtend 64) (outPtr + BitVec.ofNat 64 17) (32 : Word) (by decide) (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG2
  have hT18 := cpsBranchWithin_takenPath hR18 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep18 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (6)).zeroExtend 64) (outPtr + BitVec.ofNat 64 17) (32 : Word) q1 ((replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8))) 8 16 18
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (5)).zeroExtend 64) (outPtr + BitVec.ofNat 64 18) (32 : Word) q1 ((replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8))) 8 16 19
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 18 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (18 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT18
  have hR19 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      19 8 16 (by omega) (by decide) (by decide) q1 ((replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)))
      ((extractByte q1 (5)).zeroExtend 64) (outPtr + BitVec.ofNat 64 18) (32 : Word) (by decide) (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG2
  have hT19 := cpsBranchWithin_takenPath hR19 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep19 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (5)).zeroExtend 64) (outPtr + BitVec.ofNat 64 18) (32 : Word) q1 ((replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8))) 8 16 19
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (4)).zeroExtend 64) (outPtr + BitVec.ofNat 64 19) (32 : Word) q1 ((replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8))) 8 16 20
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 19 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (19 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT19
  have hR20 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      20 8 16 (by omega) (by decide) (by decide) q1 ((replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)))
      ((extractByte q1 (4)).zeroExtend 64) (outPtr + BitVec.ofNat 64 19) (32 : Word) (by decide) (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG2
  have hT20 := cpsBranchWithin_takenPath hR20 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep20 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (4)).zeroExtend 64) (outPtr + BitVec.ofNat 64 19) (32 : Word) q1 ((replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8))) 8 16 20
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (3)).zeroExtend 64) (outPtr + BitVec.ofNat 64 20) (32 : Word) q1 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8))) 8 16 21
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 20 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (20 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT20
  have hR21 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      21 8 16 (by omega) (by decide) (by decide) q1 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)))
      ((extractByte q1 (3)).zeroExtend 64) (outPtr + BitVec.ofNat 64 20) (32 : Word) (by decide) (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG2
  have hT21 := cpsBranchWithin_takenPath hR21 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep21 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (3)).zeroExtend 64) (outPtr + BitVec.ofNat 64 20) (32 : Word) q1 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8))) 8 16 21
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (2)).zeroExtend 64) (outPtr + BitVec.ofNat 64 21) (32 : Word) q1 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8))) 8 16 22
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 21 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (21 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT21
  have hR22 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      22 8 16 (by omega) (by decide) (by decide) q1 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)))
      ((extractByte q1 (2)).zeroExtend 64) (outPtr + BitVec.ofNat 64 21) (32 : Word) (by decide) (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG2
  have hT22 := cpsBranchWithin_takenPath hR22 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep22 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (2)).zeroExtend 64) (outPtr + BitVec.ofNat 64 21) (32 : Word) q1 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8))) 8 16 22
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (1)).zeroExtend 64) (outPtr + BitVec.ofNat 64 22) (32 : Word) q1 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8))) 8 16 23
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 22 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (22 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT22
  have hR23 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      23 8 16 (by omega) (by decide) (by decide) q1 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)))
      ((extractByte q1 (1)).zeroExtend 64) (outPtr + BitVec.ofNat 64 22) (32 : Word) (by decide) (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG2
  have hT23 := cpsBranchWithin_takenPath hR23 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep23 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (1)).zeroExtend 64) (outPtr + BitVec.ofNat 64 22) (32 : Word) q1 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8))) 8 16 23
      (tailFR2 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (0)).zeroExtend 64) (outPtr + BitVec.ofNat 64 23) (32 : Word) q0 (o3) 0 24 24
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 23 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (23 + 1) from by decide) _ hx
      rw [preS_eq]
      rw [tailFR2_eq] at hx'
      rw [tailFR3_eq]
      xperm_hyp hx') hT23
  have hR24 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      24 0 24 (by omega) (by decide) (by decide) q0 (o3)
      ((extractByte q1 (0)).zeroExtend 64) (outPtr + BitVec.ofNat 64 23) (32 : Word) (by decide) (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG3
  have hT24 := cpsBranchWithin_takenPath hR24 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep24 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q1 (0)).zeroExtend 64) (outPtr + BitVec.ofNat 64 23) (32 : Word) q0 (o3) 0 24 24
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (7)).zeroExtend 64) (outPtr + BitVec.ofNat 64 24) (32 : Word) q0 ((replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8))) 0 24 25
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 24 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (24 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT24
  have hR25 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      25 0 24 (by omega) (by decide) (by decide) q0 ((replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)))
      ((extractByte q0 (7)).zeroExtend 64) (outPtr + BitVec.ofNat 64 24) (32 : Word) (by decide) (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG3
  have hT25 := cpsBranchWithin_takenPath hR25 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep25 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (7)).zeroExtend 64) (outPtr + BitVec.ofNat 64 24) (32 : Word) q0 ((replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8))) 0 24 25
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (6)).zeroExtend 64) (outPtr + BitVec.ofNat 64 25) (32 : Word) q0 ((replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8))) 0 24 26
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 25 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (25 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT25
  have hR26 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      26 0 24 (by omega) (by decide) (by decide) q0 ((replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)))
      ((extractByte q0 (6)).zeroExtend 64) (outPtr + BitVec.ofNat 64 25) (32 : Word) (by decide) (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG3
  have hT26 := cpsBranchWithin_takenPath hR26 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep26 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (6)).zeroExtend 64) (outPtr + BitVec.ofNat 64 25) (32 : Word) q0 ((replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8))) 0 24 26
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (5)).zeroExtend 64) (outPtr + BitVec.ofNat 64 26) (32 : Word) q0 ((replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8))) 0 24 27
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 26 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (26 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT26
  have hR27 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      27 0 24 (by omega) (by decide) (by decide) q0 ((replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)))
      ((extractByte q0 (5)).zeroExtend 64) (outPtr + BitVec.ofNat 64 26) (32 : Word) (by decide) (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG3
  have hT27 := cpsBranchWithin_takenPath hR27 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep27 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (5)).zeroExtend 64) (outPtr + BitVec.ofNat 64 26) (32 : Word) q0 ((replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8))) 0 24 27
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (4)).zeroExtend 64) (outPtr + BitVec.ofNat 64 27) (32 : Word) q0 ((replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8))) 0 24 28
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 27 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (27 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT27
  have hR28 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      28 0 24 (by omega) (by decide) (by decide) q0 ((replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)))
      ((extractByte q0 (4)).zeroExtend 64) (outPtr + BitVec.ofNat 64 27) (32 : Word) (by decide) (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG3
  have hT28 := cpsBranchWithin_takenPath hR28 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep28 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (4)).zeroExtend 64) (outPtr + BitVec.ofNat 64 27) (32 : Word) q0 ((replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8))) 0 24 28
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (3)).zeroExtend 64) (outPtr + BitVec.ofNat 64 28) (32 : Word) q0 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8))) 0 24 29
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 28 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (28 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT28
  have hR29 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      29 0 24 (by omega) (by decide) (by decide) q0 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)))
      ((extractByte q0 (3)).zeroExtend 64) (outPtr + BitVec.ofNat 64 28) (32 : Word) (by decide) (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG3
  have hT29 := cpsBranchWithin_takenPath hR29 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep29 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (3)).zeroExtend 64) (outPtr + BitVec.ofNat 64 28) (32 : Word) q0 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8))) 0 24 29
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (2)).zeroExtend 64) (outPtr + BitVec.ofNat 64 29) (32 : Word) q0 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8))) 0 24 30
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 29 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (29 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT29
  have hR30 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      30 0 24 (by omega) (by decide) (by decide) q0 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)))
      ((extractByte q0 (2)).zeroExtend 64) (outPtr + BitVec.ofNat 64 29) (32 : Word) (by decide) (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG3
  have hT30 := cpsBranchWithin_takenPath hR30 (by
      intro hp hx
      obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
      obtain ⟨_, _, _, _, _, h29p⟩ := hlead
      obtain ⟨_, _, _, _, _, hgP⟩ := h29p
      obtain ⟨_, hPp⟩ := hgP
      exact absurd hPp (by decide))
  have hstep30 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 920) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (2)).zeroExtend 64) (outPtr + BitVec.ofNat 64 29) (32 : Word) q0 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8))) 0 24 30
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (1)).zeroExtend 64) (outPtr + BitVec.ofNat 64 30) (32 : Word) q0 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8))) 0 24 31
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 30 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 (30 + 1) from by decide) _ hx
      rw [preS_eq]
      xperm_hyp hx') hT30
  have hR31 := tail_byteround (newSp + signExtend12 (160 : BitVec 12)) outPtr hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
      31 0 24 (by omega) (by decide) (by decide) q0 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8)))
      ((extractByte q0 (1)).zeroExtend 64) (outPtr + BitVec.ofNat 64 30) (32 : Word) (by decide) (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) hFRARG3
  have hT31 := cpsBranchWithin_ntakenPath hR31
      (by
        intro hp hx
        obtain ⟨h1, h2, hd, hu, hlead, hrest⟩ := hx
        obtain ⟨_, _, _, _, _, h29p⟩ := hlead
        obtain ⟨_, _, _, _, _, hgP⟩ := h29p
        obtain ⟨_, hPp⟩ := hgP
        exact absurd hPp (by decide))
  have hfin31 : cpsTripleWithin 9 (PriceK + 920) (PriceK + 956) priceCode
      ((preS (newSp + signExtend12 (160 : BitVec 12)) outPtr ((extractByte q0 (1)).zeroExtend 64) (outPtr + BitVec.ofNat 64 30) (32 : Word) q0 ((replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8))) 0 24 31
      (tailFR3 newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR))) (      ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) ** (.x29 ↦ᵣ (32 : Word)) **
       (.x30 ↦ᵣ BitVec.ofNat 64 32) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q0 (0)).zeroExtend 64).truncate 8)))) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
       (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR)) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by
      intro h hx
      have hx' := link_fix (show (BitVec.ofNat 64 31 + signExtend12 (1 : BitVec 12)) = BitVec.ofNat 64 32 from by decide) _ hx
      rw [tailFR3_eq] at hx'
      xperm_hyp hx') hT31
  have hc1 := cpsTripleWithin_seq_same_cr hENTRY hstep0
  have hc2 := cpsTripleWithin_seq_same_cr hc1 hstep1
  have hc3 := cpsTripleWithin_seq_same_cr hc2 hstep2
  have hc4 := cpsTripleWithin_seq_same_cr hc3 hstep3
  have hc5 := cpsTripleWithin_seq_same_cr hc4 hstep4
  have hc6 := cpsTripleWithin_seq_same_cr hc5 hstep5
  have hc7 := cpsTripleWithin_seq_same_cr hc6 hstep6
  have hc8 := cpsTripleWithin_seq_same_cr hc7 hstep7
  have hc9 := cpsTripleWithin_seq_same_cr hc8 hstep8
  have hc10 := cpsTripleWithin_seq_same_cr hc9 hstep9
  have hc11 := cpsTripleWithin_seq_same_cr hc10 hstep10
  have hc12 := cpsTripleWithin_seq_same_cr hc11 hstep11
  have hc13 := cpsTripleWithin_seq_same_cr hc12 hstep12
  have hc14 := cpsTripleWithin_seq_same_cr hc13 hstep13
  have hc15 := cpsTripleWithin_seq_same_cr hc14 hstep14
  have hc16 := cpsTripleWithin_seq_same_cr hc15 hstep15
  have hc17 := cpsTripleWithin_seq_same_cr hc16 hstep16
  have hc18 := cpsTripleWithin_seq_same_cr hc17 hstep17
  have hc19 := cpsTripleWithin_seq_same_cr hc18 hstep18
  have hc20 := cpsTripleWithin_seq_same_cr hc19 hstep19
  have hc21 := cpsTripleWithin_seq_same_cr hc20 hstep20
  have hc22 := cpsTripleWithin_seq_same_cr hc21 hstep21
  have hc23 := cpsTripleWithin_seq_same_cr hc22 hstep22
  have hc24 := cpsTripleWithin_seq_same_cr hc23 hstep23
  have hc25 := cpsTripleWithin_seq_same_cr hc24 hstep24
  have hc26 := cpsTripleWithin_seq_same_cr hc25 hstep25
  have hc27 := cpsTripleWithin_seq_same_cr hc26 hstep26
  have hc28 := cpsTripleWithin_seq_same_cr hc27 hstep27
  have hc29 := cpsTripleWithin_seq_same_cr hc28 hstep28
  have hc30 := cpsTripleWithin_seq_same_cr hc29 hstep29
  have hc31 := cpsTripleWithin_seq_same_cr hc30 hstep30
  have hc32 := cpsTripleWithin_seq_same_cr hc31 hfin31
  -- copy arm tail: li a0, 0 ; j B+968
  have hLIa := li_spec_gen_within .x10 excess (0 : Word) (PriceK + 956) (by decide)
  have hLIaF : cpsTripleWithin 1 (PriceK + 956) (PriceK + 960) priceCode
      ((.x10 ↦ᵣ excess) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) ** (.x29 ↦ᵣ (32 : Word)) **
       (.x30 ↦ᵣ BitVec.ofNat 64 32) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q0 (0)).zeroExtend 64).truncate 8))) ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ (vals .x1)) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
       (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR)) ((.x10 ↦ᵣ (0 : Word)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) ** (.x29 ↦ᵣ (32 : Word)) **
       (.x30 ↦ᵣ BitVec.ofNat 64 32) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q0 (0)).zeroExtend 64).truncate 8))) ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ (vals .x1)) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
       (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hLIa)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[239]'(by decide) = .LI .x10 (0 : Word) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 956) amsterdamBlobGasPriceU256_prog
      239 (.LI .x10 (0 : Word)) (by decide) (by decide) hins (by decide) a i hi
  have hLIaF' : cpsTripleWithin 1 (PriceK + 956) (PriceK + 960) priceCode
      (      ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) ** (.x29 ↦ᵣ (32 : Word)) **
       (.x30 ↦ᵣ BitVec.ofNat 64 32) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q0 (0)).zeroExtend 64).truncate 8)))) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
       (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR)) ((.x10 ↦ᵣ (0 : Word)) **
              ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) ** (.x29 ↦ᵣ (32 : Word)) **
       (.x30 ↦ᵣ BitVec.ofNat 64 32) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q0 (0)).zeroExtend 64).truncate 8))) ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ (vals .x1)) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
       (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hLIaF
  have hj := jal_x0_spec_gen_within (8 : BitVec 21) (PriceK + 960)
  rw [show (PriceK + 960 : Word) + signExtend21 (8 : BitVec 21) = PriceK + 968 from by
      rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
      decide] at hj
  have hJALF : cpsTripleWithin 1 (PriceK + 960) (PriceK + 968) priceCode
      (empAssertion ** ((.x10 ↦ᵣ (0 : Word)) **       ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) ** (.x29 ↦ᵣ (32 : Word)) **
       (.x30 ↦ᵣ BitVec.ofNat 64 32) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q0 (0)).zeroExtend 64).truncate 8))) ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ (vals .x1)) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
       (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR))) (empAssertion ** ((.x10 ↦ᵣ (0 : Word)) **       ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) ** (.x29 ↦ᵣ (32 : Word)) **
       (.x30 ↦ᵣ BitVec.ofNat 64 32) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q0 (0)).zeroExtend 64).truncate 8))) ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ (vals .x1)) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
       (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR))) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hj)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[240]'(by decide) = .JAL .x0 (8 : BitVec 21) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 960) amsterdamBlobGasPriceU256_prog
      240 (.JAL .x0 (8 : BitVec 21)) (by decide) (by decide) hins (by decide) a i hi
  have hJALF' : cpsTripleWithin 1 (PriceK + 960) (PriceK + 968) priceCode
      (((.x10 ↦ᵣ (0 : Word)) **       ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) ** (.x29 ↦ᵣ (32 : Word)) **
       (.x30 ↦ᵣ BitVec.ofNat 64 32) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q0 (0)).zeroExtend 64).truncate 8))) ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ (vals .x1)) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
       (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR))) (((.x10 ↦ᵣ (0 : Word)) **       ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
       (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) ** (.x29 ↦ᵣ (32 : Word)) **
       (.x30 ↦ᵣ BitVec.ofNat 64 32) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o3 0 (((extractByte q0 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q0 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q0 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q0 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q0 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q0 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q0 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q0 (0)).zeroExtend 64).truncate 8))) ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ (vals .x1)) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
       (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o0 0 (((extractByte q3 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q3 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q3 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q3 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q3 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q3 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q3 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q3 (0)).zeroExtend 64).truncate 8))) ** ((outPtr + BitVec.ofNat 64 8) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o1 0 (((extractByte q2 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q2 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q2 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q2 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q2 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q2 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q2 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q2 (0)).zeroExtend 64).truncate 8))) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; rw [sepConj_emp_left']; exact hx)
      (by
        intro h hx
        obtain ⟨h1, h2, hd, hu, he, hX⟩ := hx
        have h1e : h1 = PartialState.empty := he
        rw [h1e, PartialState.union_empty_left] at hu
        rw [hu] at hX
        exact hX) hJALF
  have hca := cpsTripleWithin_seq_same_cr hc32 hLIaF'
  have hCOPY := cpsTripleWithin_seq_same_cr hca hJALF'
  exact hCOPY

set_option linter.defProp false in
def tail_copyarm_with_qzero (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (v6 v7 v18 v19 v20 v28 v29 v30 v31 : Word)
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (FR : Assertion) (hFR : FR.pcFree) :=
  cpsTripleWithin_add_pure_post
    (tail_copyarm newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v6 v7 v18 v19 v20 v28 v29 v30 v31
      hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid FR hFR)
    (by
      intro h hp
      obtain ⟨h12, hRest, hd, hu, h12p, hRestp⟩ := hp
      obtain ⟨h5, h0pure, hd5, hu5, h5p, h0purep⟩ := h12p
      exact ((sepConj_pure_right h0pure).mp h0purep).2)

#print axioms tail_copyarm
