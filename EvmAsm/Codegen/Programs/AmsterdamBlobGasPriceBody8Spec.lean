/-
Tail window core (instrs 225..241): composition of the check phase, overflow arm,
and the 32-round copy loop from AmsterdamBlobGasPriceBody7Spec into the
whole-window contract. Part 2 of the tail window; same namespace as part 1.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody7Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody9Spec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody5Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody6Spec

set_option maxRecDepth 8000

/-- Tail window: instrs 225..241 @ PriceK+900..964, exits at the epilogue entry
PriceK+968 (status 1 on the overflow arm, status 0 after the byte copy).
`q0..q5` are the post-division sum limbs (in place), `o0..o3` the four output
dwords at `outPtr`, `a*`/`p*` the untouched acc/prod cells. `v18`/`v19`/`v20`
stay symbolic (outer-loop parity). -/
theorem tail_core (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 : Word)
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsNBranchWithin 296 (PriceK + 900) priceCode
      (      ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
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
       FR))
      [(PriceK + 968, ((.x10 ↦ᵣ (1 : Word)) ** (((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) ≠ (0 : Word)⌝) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) **
       (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ v18) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
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
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR)))),
       (PriceK + 968, ((.x10 ↦ᵣ (0 : Word)) **       ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
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
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte o2 0 (((extractByte q1 (7)).zeroExtend 64).truncate 8)) 1 (((extractByte q1 (6)).zeroExtend 64).truncate 8)) 2 (((extractByte q1 (5)).zeroExtend 64).truncate 8)) 3 (((extractByte q1 (4)).zeroExtend 64).truncate 8)) 4 (((extractByte q1 (3)).zeroExtend 64).truncate 8)) 5 (((extractByte q1 (2)).zeroExtend 64).truncate 8)) 6 (((extractByte q1 (1)).zeroExtend 64).truncate 8)) 7 (((extractByte q1 (0)).zeroExtend 64).truncate 8))) ** FR)))] := by
  -- check phase: ld q4 ; ld q5 ; or
  have hld5 := ld_spec_gen_within .x5 .x22 (newSp + signExtend12 (160 : BitVec 12)) v5 q4
    (32 : BitVec 12) (PriceK + 900) (by decide)
  have hld5F : cpsTripleWithin 1 (PriceK + 900) (PriceK + 904) priceCode
      (((.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ v5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4)) **
              ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) **
       (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) **
       (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ v18) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       (.x21 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
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
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR)) ((((.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4)) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) **
       (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) **
       (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ v18) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       (.x21 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
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
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld5)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[225]'(by decide) = .LD .x5 .x22 (32 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 900) amsterdamBlobGasPriceU256_prog
      225 (.LD .x5 .x22 (32 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi
  have hld6 := ld_spec_gen_within .x6 .x22 (newSp + signExtend12 (160 : BitVec 12)) v6 q5
    (40 : BitVec 12) (PriceK + 904) (by decide)
  have hld6F : cpsTripleWithin 1 (PriceK + 904) (PriceK + 908) priceCode
      (((.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ v6) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5)) **
              ((.x5 ↦ᵣ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
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
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR)) ((((.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ q5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5)) **
            ((.x5 ↦ᵣ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
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
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld6)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[226]'(by decide) = .LD .x6 .x22 (40 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 904) amsterdamBlobGasPriceU256_prog
      226 (.LD .x6 .x22 (40 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi
  have hld6F' : cpsTripleWithin 1 (PriceK + 904) (PriceK + 908) priceCode
      ((((.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4)) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) **
       (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) **
       (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ v18) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       (.x21 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
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
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR))) ((((.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ q5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5)) **
            ((.x5 ↦ᵣ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
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
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld6F
  have hld5F' : cpsTripleWithin 1 (PriceK + 900) (PriceK + 904) priceCode
      (      ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
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
       FR)) (((.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4)) **
              ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) **
       (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) **
       (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ v18) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       (.x21 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
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
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld5F
  have hsA := cpsTripleWithin_seq_same_cr hld5F' hld6F'
  have hor := or_spec_gen_rd_eq_rs1_within .x5 .x6 q4 q5 (PriceK + 908) (by decide)
  have horF : cpsTripleWithin 1 (PriceK + 908) (PriceK + 912) priceCode
      (((.x5 ↦ᵣ q4) ** (.x6 ↦ᵣ q5)) **
              ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
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
       FR)) ((((.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5)) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
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
       FR))) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[227]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 908) amsterdamBlobGasPriceU256_prog
      227 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi
  have horF' : cpsTripleWithin 1 (PriceK + 908) (PriceK + 912) priceCode
      ((((.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ q5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5)) **
            ((.x5 ↦ᵣ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
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
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR))) ((((.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5)) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
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
       FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) horF
  have hCHK := cpsTripleWithin_seq_same_cr hsA horF'
  -- overflow dispatch: bnez (q4 ||| q5)
  have hb := bne_spec_gen_within .x5 .x0 (52 : BitVec 13) (q4 ||| q5) (0 : Word)
    (PriceK + 912)
  rw [show (PriceK + 912 : Word) + signExtend13 (52 : BitVec 13) = PriceK + 964 from by
      rw [show signExtend13 (52 : BitVec 13) = (52 : Word) from by decide]
      decide,
    show (PriceK + 912 : Word) + 4 = PriceK + 916 from by decide] at hb
  have hbF := cpsBranchWithin_frameR (      ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
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
       FR)) (by pcFree; exact hFR) hb
  have hbE : cpsBranchWithin 1 (PriceK + 912) priceCode
      (((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word))) **
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
       FR))
      (PriceK + 964)
      ((((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) ≠ (0 : Word)⌝) **
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
       FR)))
      (PriceK + 916)
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
       FR))) := by
    refine cpsBranchWithin_extend_code ?_ hbF
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[228]'(by decide) = .BNE .x5 .x0 (52 : BitVec 13) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 912) amsterdamBlobGasPriceU256_prog
      228 (.BNE .x5 .x0 (52 : BitVec 13)) (by decide) (by decide) hins (by decide) a i hi
  have hbE' : cpsBranchWithin 1 (PriceK + 912) priceCode
      ((((.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5)) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
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
       FR)))
      (PriceK + 964)
      ((((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) ≠ (0 : Word)⌝) **
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
       FR)))
      (PriceK + 916)
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
       FR))) :=
    cpsBranchWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx)
      (fun _ hx => hx) hbE
  have hB := cpsTripleWithin_seq_cpsBranchWithin_same_cr hCHK hbE'
  -- overflow arm: li a0, 1
  have hOVFl := li_spec_gen_within .x10 excess (1 : Word) (PriceK + 964) (by decide)
  have hOVFlF : cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      ((.x10 ↦ᵣ excess) **
        (((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) ≠ (0 : Word)⌝) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) **
       (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ v18) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
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
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR))) ((.x10 ↦ᵣ (1 : Word)) **
        (((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) ≠ (0 : Word)⌝) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) **
       (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ v18) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
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
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hOVFl)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[241]'(by decide) = .LI .x10 (1 : Word) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 964) amsterdamBlobGasPriceU256_prog
      241 (.LI .x10 (1 : Word)) (by decide) (by decide) hins (by decide) a i hi
  have hOVFlF' : cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      ((((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) ≠ (0 : Word)⌝) **
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
       FR))) ((.x10 ↦ᵣ (1 : Word)) **
        (((.x5 ↦ᵣ (q4 ||| q5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(q4 ||| q5) ≠ (0 : Word)⌝) **
            ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) **
       (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ v18) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
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
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hOVFlF
  have hOVF := branch_seqTaken_same_cr hB hOVFlF'
  have hCOPY := tail_copyarm newSp excess outPtr vals q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v6 v7 v18 v19 v20 v28 v29 v30 v31 hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid FR hFR
  exact cpsBranchWithin_as_cpsNBranchWithin
    (cpsBranchWithin_seq_cpsTripleWithin_same_cr hOVF hCOPY (fun _ hx => hx))

#print axioms tail_core
