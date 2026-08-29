/- Outer-loop assembly adapters for K70 (#12851).

   The first adapter below is deliberately small: it closes the terminal-index
   round before the recurrence fold is attempted.  The seven loop-scratch
   registers are owned by the parity invariant, while the linked terminal
   theorem consumes concrete values.  The existential exit posts retain those
   values for the subsequent exit-divide and outer-loop adapters.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundComposition
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceTaylorTie

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody5Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14TerminalSpec
open EvmAsm.Codegen.AmsterdamBlobGasPrice
open EvmAsm.Codegen.AmsterdamBlobGasPriceTaylorTie

set_option maxRecDepth 8000

/- The status-0 tail writes the four output words in big-endian byte order.
   Keep this bridge at the assertion level: the tail starts from four existing
   dwords, replaces all 32 bytes, and therefore produces one contiguous
   `bytesRegion` rather than four unrelated cells. -/
def tailOutputFullReplaceBE (o q : Word) : Word :=
  replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte
    (replaceByte (replaceByte o 0 (((extractByte q 7).zeroExtend 64).truncate 8))
      1 (((extractByte q 6).zeroExtend 64).truncate 8))
      2 (((extractByte q 5).zeroExtend 64).truncate 8))
      3 (((extractByte q 4).zeroExtend 64).truncate 8))
      4 (((extractByte q 3).zeroExtend 64).truncate 8))
      5 (((extractByte q 2).zeroExtend 64).truncate 8))
      6 (((extractByte q 1).zeroExtend 64).truncate 8))
      7 (((extractByte q 0).zeroExtend 64).truncate 8)

def tailOutputWordBytes (q : Word) : List (BitVec 8) :=
  (List.range 8).map (fun j => extractByte q (7 - j))

def tailOutputBytes (q0 q1 q2 q3 : Word) : List (BitVec 8) :=
  tailOutputWordBytes q3 ++ tailOutputWordBytes q2 ++
    tailOutputWordBytes q1 ++ tailOutputWordBytes q0

theorem tailOutputFullReplaceBE_eq_pack (o q : Word) :
    tailOutputFullReplaceBE o q = packBytes (tailOutputWordBytes q) := by
  simp only [tailOutputFullReplaceBE, truncate_zeroExtend_byte]
  rw [← packBytes_limbBytes o]
  rw [packBytes_set _ 0 _ (by decide) (by simp [limbBytes_length])]
  rw [packBytes_set _ 1 _ (by decide) (by simp [limbBytes_length])]
  rw [packBytes_set _ 2 _ (by decide) (by simp [limbBytes_length])]
  rw [packBytes_set _ 3 _ (by decide) (by simp [limbBytes_length])]
  rw [packBytes_set _ 4 _ (by decide) (by simp [limbBytes_length])]
  rw [packBytes_set _ 5 _ (by decide) (by simp [limbBytes_length])]
  rw [packBytes_set _ 6 _ (by decide) (by simp [limbBytes_length])]
  rw [packBytes_set _ 7 _ (by decide) (by simp [limbBytes_length])]
  congr 1

theorem tailOutputBytes_take0 (q0 q1 q2 q3 : Word) :
    (tailOutputBytes q0 q1 q2 q3).take 8 = tailOutputWordBytes q3 := by
  simp [tailOutputBytes, tailOutputWordBytes]

theorem tailOutputBytes_drop8_take1 (q0 q1 q2 q3 : Word) :
    ((tailOutputBytes q0 q1 q2 q3).drop 8).take 8 = tailOutputWordBytes q2 := by
  simp [tailOutputBytes, tailOutputWordBytes]

theorem tailOutputBytes_drop16_take2 (q0 q1 q2 q3 : Word) :
    ((tailOutputBytes q0 q1 q2 q3).drop 16).take 8 = tailOutputWordBytes q1 := by
  simp [tailOutputBytes, tailOutputWordBytes, List.drop_append,
    List.drop_eq_nil_of_le]

theorem tailOutputBytes_drop24_take3 (q0 q1 q2 q3 : Word) :
    ((tailOutputBytes q0 q1 q2 q3).drop 24).take 8 = tailOutputWordBytes q0 := by
  simp [tailOutputBytes, tailOutputWordBytes, List.drop_append,
    List.drop_eq_nil_of_le]

theorem tailOutputBytes_length (q0 q1 q2 q3 : Word) :
    (tailOutputBytes q0 q1 q2 q3).length = 32 := by
  simp [tailOutputBytes, tailOutputWordBytes]

theorem tailOutputCells_eq_bytesRegion
    (base q0 q1 q2 q3 o0 o1 o2 o3 : Word) :
    (((base + BitVec.ofNat 64 0) ↦ₘ tailOutputFullReplaceBE o3 q3) **
      ((base + BitVec.ofNat 64 8) ↦ₘ tailOutputFullReplaceBE o2 q2) **
      ((base + BitVec.ofNat 64 16) ↦ₘ tailOutputFullReplaceBE o1 q1) **
      ((base + BitVec.ofNat 64 24) ↦ₘ tailOutputFullReplaceBE o0 q0))
      = bytesRegion base (tailOutputBytes q0 q1 q2 q3) := by
  rw [tailOutputFullReplaceBE_eq_pack, tailOutputFullReplaceBE_eq_pack,
    tailOutputFullReplaceBE_eq_pack, tailOutputFullReplaceBE_eq_pack]
  unfold bytesRegion
  have hlen : (tailOutputBytes q0 q1 q2 q3).length = 32 :=
    tailOutputBytes_length _ _ _ _
  rw [hlen]
  have hchunks : (32 + 7) / 8 = 4 := by decide
  rw [hchunks]
  simp only [bytesRegionAux]
  rw [tailOutputBytes_take0, tailOutputBytes_drop8_take1]
  simp only [List.drop_drop]
  rw [tailOutputBytes_drop16_take2, tailOutputBytes_drop24_take3]
  simp only [sepConj_emp_right']
  rw [show base + BitVec.ofNat 64 0 = base from by bv_omega,
    show base + 8 + 8 = base + BitVec.ofNat 64 16 from by bv_omega,
    show (base + BitVec.ofNat 64 16) + 8 =
      base + BitVec.ofNat 64 24 from by bv_omega]
  rfl

/- The model uses division by powers of 256 while the machine-facing tie uses
   shifts.  The two encodings are definitionally different, so make the
   equality explicit before connecting the tail's byte list to `priceOutcome`.
   The proof is independent of the 256-bit envelope; truncation is supplied by
   `BitVec.ofNat 8`. -/
theorem natToBeBytes_eq_beBytes32OfNat (r : Nat) :
    natToBeBytes 32 r = beBytes32OfNat r := by
  apply List.ext_getElem
  · simp [natToBeBytes, beBytes32OfNat]
  · intro i h1 h2
    have hi : i < 32 := by simpa [natToBeBytes] using h1
    simp only [natToBeBytes, beBytes32OfNat, List.getElem_map,
      List.getElem_range]
    rw [Nat.shiftRight_eq_div_pow]
    have hpow : (2 : Nat) ^ (8 * (31 - i)) =
        256 ^ (31 - i) := by
      rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
    rw [hpow]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega

theorem tailOutputCells_to_bytesRegion
    (P : Assertion) (base q0 q1 q2 q3 o0 o1 o2 o3 : Word) :
    ∀ h,
      (P **
        (((base + BitVec.ofNat 64 0) ↦ₘ tailOutputFullReplaceBE o3 q3) **
          ((base + BitVec.ofNat 64 8) ↦ₘ tailOutputFullReplaceBE o2 q2) **
          ((base + BitVec.ofNat 64 16) ↦ₘ tailOutputFullReplaceBE o1 q1) **
          ((base + BitVec.ofNat 64 24) ↦ₘ tailOutputFullReplaceBE o0 q0))) h →
        (P ** bytesRegion base (tailOutputBytes q0 q1 q2 q3)) h := by
  intro h hp
  rw [← tailOutputCells_eq_bytesRegion base q0 q1 q2 q3 o0 o1 o2 o3]
  xperm_hyp hp

/- A non-symmetric kernel test anchors the machine byte ordering to the
   representation-free Nat decoder.  The four words are deliberately chosen
   so neither word order nor byte order can be hidden by a palindrome. -/
theorem tailOutputBytes_decode_kat :
    EvmAsm.Stateless.SpecRef.bytesBEtoNat
      (tailOutputBytes
        (0x8899aabbccddeeff : Word)
        (0x0011223344556677 : Word)
        (0x8899aabbccddeeff : Word)
        (0x0011223344556677 : Word)) =
      0x00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff := by
  decide

/- The status-0 tail post has one semantic boundary: every assertion except the
   four output dwords is unchanged, while those dwords contain the 32-byte
   result.  Name the retained part so the output conversion does not have to
   duplicate the whole branch post. -/
@[reducible] private def tailStatus0Rest
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 : Word)
    (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) **
    (.x21 ↦ᵣ outPtr) **
    (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
    (.x0 ↦ᵣ (0 : Word)) **
    (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
    (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) **
    (.x29 ↦ᵣ (32 : Word)) **
    (.x30 ↦ᵣ BitVec.ofNat 64 32) **
    (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
    (.x2 ↦ᵣ newSp) **
    (.x1 ↦ᵣ (vals .x1)) **
    (.x11 ↦ᵣ outPtr) **
    (.x8 ↦ᵣ excess) **
    (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ v18) **
    (.x19 ↦ᵣ v19) **
    (.x20 ↦ᵣ v20) **
    (.x31 ↦ᵣ v31) **
    (.x5 ↦ᵣ (q4 ||| q5)) **
    (.x6 ↦ᵣ q5) **
    frameSlotsSaved priceFrame newSp vals **
    (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
    (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
    (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
    (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
    (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
    (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
    (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
    (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
    (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
    (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
    (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
    (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
    (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
    (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) **
    (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
    (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) **
    (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) ** FR

/- The linked status-1 tail post also owns x0, but the outer exit-divide
   adapter needs that cell factored uniformly out of both tail exits.  Keep
   the rest as the exact emitted post, with only the x0 atom removed. -/
@[reducible] private def tailStatus1NoX0
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 v7 v18 v19 v20 v28 v29 v30 v31 : Word)
    (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) **
    (((.x5 ↦ᵣ (q4 ||| q5)) ** ⌜(q4 ||| q5) ≠ (0 : Word)⌝) **
      ((((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) **
       (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ v18) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** (.x6 ↦ᵣ q5) **
       frameSlotsSaved priceFrame newSp vals **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
       (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
       (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) **
       (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
       ((outPtr + BitVec.ofNat 64 0) ↦ₘ o0) **
       ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) **
       ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) **
       ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR))

@[reducible] private def tailStatus0RestNoX0
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 : Word)
    (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) **
    (.x21 ↦ᵣ outPtr) **
    (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
    (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
    (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) **
    (.x29 ↦ᵣ (32 : Word)) **
    (.x30 ↦ᵣ BitVec.ofNat 64 32) **
    (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
    (.x2 ↦ᵣ newSp) **
    (.x1 ↦ᵣ (vals .x1)) **
    (.x11 ↦ᵣ outPtr) **
    (.x8 ↦ᵣ excess) **
    (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ v18) **
    (.x19 ↦ᵣ v19) **
    (.x20 ↦ᵣ v20) **
    (.x31 ↦ᵣ v31) **
    (.x5 ↦ᵣ (q4 ||| q5)) **
    (.x6 ↦ᵣ q5) **
    frameSlotsSaved priceFrame newSp vals **
    (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
    (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
    (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
    (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
    (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
    (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
    (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
    (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
    (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
    (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
    (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
    (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
    (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
    (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) **
    (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
    (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) **
    (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) ** FR

@[reducible] private def tailStatus0Cells
    (outPtr q0 q1 q2 q3 o0 o1 o2 o3 : Word) : Assertion :=
  ((outPtr + BitVec.ofNat 64 0) ↦ₘ tailOutputFullReplaceBE o0 q3) **
    ((outPtr + BitVec.ofNat 64 8) ↦ₘ tailOutputFullReplaceBE o1 q2) **
    ((outPtr + BitVec.ofNat 64 16) ↦ₘ tailOutputFullReplaceBE o2 q1) **
    ((outPtr + BitVec.ofNat 64 24) ↦ₘ tailOutputFullReplaceBE o3 q0)

@[reducible] private def tailStatus0Source
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 : Word)
    (FR : Assertion) : Assertion :=
  ((.x10 ↦ᵣ (0 : Word)) **
    ((.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ ((extractByte q0 0).zeroExtend 64)) **
      (.x28 ↦ᵣ (outPtr + BitVec.ofNat 64 31)) ** (.x29 ↦ᵣ (32 : Word)) **
      (.x30 ↦ᵣ BitVec.ofNat 64 32) **
      (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 0) ↦ₘ q0) **
      ((outPtr + BitVec.ofNat 64 24) ↦ₘ tailOutputFullReplaceBE o3 q0) **
      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x31 ↦ᵣ v31) **
      (.x5 ↦ᵣ (q4 ||| q5)) ** (.x6 ↦ᵣ q5) **
      frameSlotsSaved priceFrame newSp vals **
      (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
      (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
      (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
      (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
      (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
      (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
      (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
      (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
      (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
      (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
      (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
      (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
      (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 8) ↦ₘ q1) **
      (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 16) ↦ₘ q2) **
      (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 24) ↦ₘ q3) **
      (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 32) ↦ₘ q4) **
      (((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 40) ↦ₘ q5) **
      ((outPtr + BitVec.ofNat 64 0) ↦ₘ tailOutputFullReplaceBE o0 q3) **
      ((outPtr + BitVec.ofNat 64 8) ↦ₘ tailOutputFullReplaceBE o1 q2) **
      ((outPtr + BitVec.ofNat 64 16) ↦ₘ tailOutputFullReplaceBE o2 q1) ** FR))

@[reducible] private def tailStatus0Bytes
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 : Word)
    (FR : Assertion) : Assertion :=
  tailStatus0Rest newSp excess outPtr vals q0 q1 q2 q3 q4 q5
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR **
    bytesRegion outPtr (tailOutputBytes q0 q1 q2 q3)

@[reducible] private def tailStatus0BytesNoX0
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 : Word)
    (FR : Assertion) : Assertion :=
  tailStatus0RestNoX0 newSp excess outPtr vals q0 q1 q2 q3 q4 q5
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR **
    bytesRegion outPtr (tailOutputBytes q0 q1 q2 q3)

theorem tailStatus0Cells_to_bytes
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 : Word)
    (FR : Assertion) : ∀ h,
    (tailStatus0Rest newSp excess outPtr vals q0 q1 q2 q3 q4 q5
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR **
      tailStatus0Cells outPtr q0 q1 q2 q3 o0 o1 o2 o3) h →
    tailStatus0Bytes newSp excess outPtr vals q0 q1 q2 q3 q4 q5
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR h := by
  intro h hp
  unfold tailStatus0Bytes
  apply tailOutputCells_to_bytesRegion
  exact hp

theorem tailStatus0Source_to_bytes
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 : Word)
    (FR : Assertion) : ∀ h,
    tailStatus0Source newSp excess outPtr vals q0 q1 q2 q3 q4 q5
      o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
      v18 v19 v20 v31 FR h →
    tailStatus0Bytes newSp excess outPtr vals q0 q1 q2 q3 q4 q5
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR h := by
  intro h hp
  unfold tailStatus0Bytes
  apply tailOutputCells_to_bytesRegion
  simp only [tailStatus0Source, tailStatus0Rest,
    tailOutputFullReplaceBE] at hp ⊢
  xperm_hyp hp

/- The two tail exits share their program counter.  Keep the status-1 post
   abstract while changing only the second (status-0) post; this lets the
   concrete `tail_core` theorem supply the first post without copying it into
   this adapter. -/
private theorem cpsNBranchWithin_weaken_second_same_pc
    {n : Nat} {entry pc : Word} {cr : CodeReq} {P Q1 Q0 Q0' : Assertion}
    (h : cpsNBranchWithin n entry cr P [(pc, Q1), (pc, Q0)])
    (hQ0 : ∀ h, Q0 h → Q0' h) :
    cpsNBranchWithin n entry cr P [(pc, Q1), (pc, Q0')] := by
  apply cpsNBranchWithin_weaken_posts h
  intro ex hex
  simp only [List.mem_cons] at hex
  rcases hex with h1 | h2
  · subst ex
    exact ⟨(pc, Q1), by simp, rfl, fun _ hs => hs⟩
  · rcases h2 with h2 | hnil
    · subst ex
      exact ⟨(pc, Q0'), by simp, rfl, hQ0⟩
    · simp at hnil

private theorem cpsNBranchWithin_weaken_two_same_pc
    {n : Nat} {entry pc : Word} {cr : CodeReq} {P Q1 Q0 Q1' Q0' : Assertion}
    (h : cpsNBranchWithin n entry cr P [(pc, Q1), (pc, Q0)])
    (hQ1 : ∀ h, Q1 h → Q1' h)
    (hQ0 : ∀ h, Q0 h → Q0' h) :
    cpsNBranchWithin n entry cr P [(pc, Q1'), (pc, Q0')] := by
  apply cpsNBranchWithin_weaken_posts h
  intro ex hex
  simp only [List.mem_cons] at hex
  rcases hex with h1 | h2
  · subst ex
    exact ⟨(pc, Q1'), by simp, rfl, hQ1⟩
  · rcases h2 with h2 | hnil
    · subst ex
      exact ⟨(pc, Q0'), by simp, rfl, hQ0⟩
    · simp at hnil

/- A reusable outer-fold seam: callers provide the already-derived tail
   theorem and the status-0 output conversion, while the status-1 post stays
   exactly the one emitted by the linked tail proof. -/
theorem tail_core_status0_bytes
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 : Word)
    (v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 : Word)
    (FR : Assertion)
    {Q1 Q0 : Assertion}
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (tailCorePre newSp excess outPtr vals q0 q1 q2 q3 q4 q5
        o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
        v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 FR)
      [(PriceK + 968, Q1), (PriceK + 968, Q0)])
    (hStatus0 : ∀ h, Q0 h →
      tailStatus0Bytes newSp excess outPtr vals q0 q1 q2 q3 q4 q5
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR h) :
    cpsNBranchWithin 296 (PriceK + 900) priceCode
      (tailCorePre newSp excess outPtr vals q0 q1 q2 q3 q4 q5
        o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
        v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 FR)
      [(PriceK + 968, Q1),
       (PriceK + 968, tailStatus0Bytes newSp excess outPtr vals
         q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
         v18 v19 v20 v31 FR)] := by
  exact cpsNBranchWithin_weaken_second_same_pc hTail hStatus0

theorem tail_core_status0_source_to_bytes
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 : Word)
    (v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 : Word)
    (FR : Assertion) {Q1 : Assertion}
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (tailCorePre newSp excess outPtr vals q0 q1 q2 q3 q4 q5
        o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
        v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 FR)
      [(PriceK + 968, Q1),
       (PriceK + 968,
        tailStatus0Source newSp excess outPtr vals q0 q1 q2 q3 q4 q5
          o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
          v18 v19 v20 v31 FR)]) :
    cpsNBranchWithin 296 (PriceK + 900) priceCode
      (tailCorePre newSp excess outPtr vals q0 q1 q2 q3 q4 q5
        o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
        v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 FR)
      [(PriceK + 968, Q1),
       (PriceK + 968,
        tailStatus0Bytes newSp excess outPtr vals q0 q1 q2 q3 q4 q5
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR)] := by
  apply tail_core_status0_bytes (hTail := hTail)
  exact tailStatus0Source_to_bytes newSp excess outPtr vals
    q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
    p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR

/- Type-check the adapter against the actual linked tail theorem.  The first
   exit is intentionally existential here: the adapter preserves it without
   copying its large status-1 assertion, while the second exit is the concrete
   bytes-producing result used by the outer fold. -/
theorem tail_core_status0_source_of_tail_core
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 : Word)
    (v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 : Word)
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (FR : Assertion) (hFR : FR.pcFree) :
    ∃ Q1 : Assertion,
      cpsNBranchWithin 296 (PriceK + 900) priceCode
        (tailCorePre newSp excess outPtr vals q0 q1 q2 q3 q4 q5
          o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
          v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 FR)
        [(PriceK + 968, Q1),
         (PriceK + 968,
          tailStatus0Bytes newSp excess outPtr vals q0 q1 q2 q3 q4 q5
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR)] := by
  have hTail := EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec.tail_core
    newSp excess outPtr vals
    q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
    p0 p1 p2 p3 p4 p5 v5 v6 v7 v18 v19 v20 v28 v29 v30 v31
    hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid FR hFR
  have hAdapt := tail_core_status0_source_to_bytes
    newSp excess outPtr vals
    q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
    p0 p1 p2 p3 p4 p5 v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 FR
    (hTail := hTail)
  exact ⟨_, hAdapt⟩

/- The outer exit-divide continuation appends x0 to every chosen exit.  The
   linked tail already owns x0 in both posts, so expose the same resource once
   and only once by changing the two posts to their no-x0 forms. -/
theorem tail_core_status0_source_of_tail_core_x0_split
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 : Word)
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
      (tailCorePre newSp excess outPtr vals q0 q1 q2 q3 q4 q5
        o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
        v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 FR)
      [(PriceK + 968,
        tailStatus1NoX0 newSp excess outPtr vals
          q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
          p0 p1 p2 p3 p4 p5 v7 v18 v19 v20 v28 v29 v30 v31 FR **
          (.x0 ↦ᵣ (0 : Word))),
       (PriceK + 968,
        tailStatus0BytesNoX0 newSp excess outPtr vals
          q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5
          p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR **
          (.x0 ↦ᵣ (0 : Word)))] := by
  have hTail := EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec.tail_core
    newSp excess outPtr vals
    q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
    p0 p1 p2 p3 p4 p5 v5 v6 v7 v18 v19 v20 v28 v29 v30 v31
    hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid FR hFR
  apply cpsNBranchWithin_weaken_two_same_pc hTail
  · intro h hp
    simp only [tailStatus1NoX0]
    xperm_hyp hp
  · intro h hp
    unfold tailStatus0BytesNoX0
    rw [← tailOutputCells_eq_bytesRegion outPtr q0 q1 q2 q3 o3 o2 o1 o0]
    simp only [tailStatus0RestNoX0, tailOutputFullReplaceBE]
    xperm_hyp hp

/- The library currently provides the N-branch bulk adapter for nine
   registers.  K70's round owns exactly these seven registers, so keep the
   smaller adapter local rather than manufacturing two unrelated resources. -/
private theorem nbranch_regOwn7
    {n : Nat} {entry : Word} {r1 r2 r3 r4 r5 r6 r7 : Reg}
    {P : Assertion} {exits : List (Word × Assertion)} {cr : CodeReq}
    (h : ∀ v1 v2 v3 v4 v5 v6 v7, cpsNBranchWithin n entry cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) **
       (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) **
       (r7 ↦ᵣ v7)) exits) :
    cpsNBranchWithin n entry cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 **
       regOwn r4 ** regOwn r5 ** regOwn r6 ** regOwn r7) exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v6, hv6⟩, ⟨v7, hv7⟩⟩ := hO6
  exact h v1 v2 v3 v4 v5 v6 v7 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1,
       g4, g5, d3, u3, hv2, g6, g7, d4, u4, hv3,
       g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5,
       g12, g13, d7, u7, hv6, hv7⟩, hRb⟩ hpc

@[reducible] def terminalCore
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ vals .x1) **
  (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
  (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
  (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ AB) ** (.x20 ↦ᵣ PB) **
  (.x21 ↦ᵣ outPtr) **
  (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
  frameSlotsSaved priceFrame newSp vals **
  cellsOf AB [a0, a1, a2, a3, a4, a5] **
  cellsOf PB [p0, p1, p2, p3, p4, p5] **
  cellsOf (newSp + signExtend12 (160 : BitVec 12))
    [s0, s1, s2, s3, s4, s5] ** FR

@[reducible] def terminalZeroAny
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  fun h => ∃ v7 v28 v29 v30 v31 : Word,
    roundZeroNoX0 newSp excess outPtr iVal AB PB vals w
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
      s2 s3 s4 s5 v7 v28 v29 v30 v31 FR h

@[reducible] def terminalStatus1Any
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  fun h => ∃ v7 v28 v29 v30 v31 : Word,
    roundTerminalStatus1NoX0 newSp excess outPtr iVal AB PB vals w
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
      s2 s3 s4 s5 v7 v28 v29 v30 v31 FR h

/- The linked terminal round consumes concrete values for the seven owned
   scratch registers.  Package the five values which its posts retain; the
   subsequent exit-divide adapter destructures them before it continues. -/
theorem taylor_round_terminal_496_from_footprint
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) (hFR : FR.pcFree)
    (h_i : iVal = (496 : Word)) :
    cpsNBranchWithin 17 (PriceK + 144) priceCode
      (taylorRoundFootprint newSp excess outPtr iVal AB PB vals
        [a0, a1, a2, a3, a4, a5] [p0, p1, p2, p3, p4, p5]
        [s0, s1, s2, s3, s4, s5] FR)
      [ (PriceK + 804,
          terminalZeroAny newSp excess outPtr iVal AB PB vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR),
        (PriceK + 968,
          terminalStatus1Any newSp excess outPtr iVal AB PB vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR) ] := by
  let core := terminalCore newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR
  let exits : List (Word × Assertion) := [
    (PriceK + 804,
      terminalZeroAny newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR),
    (PriceK + 968,
      terminalStatus1Any newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR)]
  have hConcrete : ∀ v5 v6 v7 v28 v29 v30 v31 : Word,
      cpsNBranchWithin 17 (PriceK + 144) priceCode
        (core ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
          (.x31 ↦ᵣ v31)) exits := by
    intro v5 v6 v7 v28 v29 v30 v31
    have hBranch := taylor_round_terminal_496_status1_drop_x0
      newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v5 v6 v7 v28 v29 v30 v31 FR hFR h_i
    have hN := cpsBranchWithin_as_cpsNBranchWithin hBranch
    have hN' := cpsNBranchWithin_weaken_pre (P' :=
        core ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
          (.x31 ↦ᵣ v31)) (fun h hp => by
      simp only [core, terminalCore, roundEntryNoX0, roundFrame,
        EvmAsm.Rv64.AddrNorm.se12_0,
        EvmAsm.Rv64.AddrNorm.se12_8, EvmAsm.Rv64.AddrNorm.se12_16,
        EvmAsm.Rv64.AddrNorm.se12_24, EvmAsm.Rv64.AddrNorm.se12_32,
        EvmAsm.Rv64.AddrNorm.se12_40,
        EvmAsm.Rv64.AddrNorm.word_add_zero] at hp ⊢
      rw [cellsOf_six, cellsOf_six, cellsOf_six] at hp
      xperm_hyp hp) hN
    refine cpsNBranchWithin_weaken_posts hN' ?_
    intro ex hex
    have hex' : ex =
        (PriceK + 804,
          roundZeroNoX0 newSp excess outPtr iVal AB PB vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
            s2 s3 s4 s5 v7 v28 v29 v30 v31 FR) ∨
      ex =
        (PriceK + 968,
          roundTerminalStatus1NoX0 newSp excess outPtr iVal AB PB vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
            s2 s3 s4 s5 v7 v28 v29 v30 v31 FR) := by
      simpa [hBranch] using hex
    rcases hex' with rfl | rfl
    · refine ⟨_, List.Mem.head _, rfl, ?_⟩
      intro h hh
      exact ⟨v7, v28, v29, v30, v31, hh⟩
    · refine ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, ?_⟩
      intro h hh
      exact ⟨v7, v28, v29, v30, v31, hh⟩
  have hOwned := nbranch_regOwn7 (P := core)
    (r1 := .x5) (r2 := .x6) (r3 := .x7) (r4 := .x28)
    (r5 := .x29) (r6 := .x30) (r7 := .x31) hConcrete
  have hFinal := cpsNBranchWithin_weaken_pre
    (P' := taylorRoundFootprint newSp excess outPtr iVal AB PB vals
      [a0, a1, a2, a3, a4, a5] [p0, p1, p2, p3, p4, p5]
      [s0, s1, s2, s3, s4, s5] FR)
    (fun h hp => by
      simp only [taylorRoundFootprint, regOwns, sepConj_emp_right', core,
        terminalCore] at hp ⊢
      xperm_hyp hp) hOwned
  simpa [exits] using hFinal

/- The terminal-index arm is reached from the actual parity invariant at the
   last loop index.  Keep this adapter separate from the value-packaging
   theorem above: its post is still the explicit terminal relation consumed
   by `round_zero_exitdiv_tail`, so the five scratch witnesses are available
   to that continuation rather than being treated as dead state. -/
theorem taylor_round_terminal_496_from_parity
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsNBranchWithin 17 (PriceK + 144) priceCode
      (taylorLoopInvParityAt newSp excess outPtr vals 495 (496 : Word)
        evenBase oddBase [a0, a1, a2, a3, a4, a5]
        [p0, p1, p2, p3, p4, p5] [s0, s1, s2, s3, s4, s5] FR)
      [ (PriceK + 804,
          terminalZeroAny newSp excess outPtr (496 : Word)
            (parityBuffer 495 evenBase oddBase)
            (parityBuffer 495 oddBase evenBase) vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR),
        (PriceK + 968,
          terminalStatus1Any newSp excess outPtr (496 : Word)
            (parityBuffer 495 evenBase oddBase)
            (parityBuffer 495 oddBase evenBase) vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR) ] := by
  let AB := parityBuffer 495 evenBase oddBase
  let PB := parityBuffer 495 oddBase evenBase
  have hRound := taylor_round_terminal_496_from_footprint
    newSp excess outPtr (496 : Word) AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR hFR
    (by decide)
  have hPre : ∀ h,
      taylorLoopInvParityAt newSp excess outPtr vals 495 (496 : Word)
        evenBase oddBase [a0, a1, a2, a3, a4, a5]
        [p0, p1, p2, p3, p4, p5] [s0, s1, s2, s3, s4, s5] FR h →
      taylorRoundFootprint newSp excess outPtr (496 : Word) AB PB vals
        [a0, a1, a2, a3, a4, a5] [p0, p1, p2, p3, p4, p5]
        [s0, s1, s2, s3, s4, s5] FR h := by
    intro h hh
    simpa [AB, PB] using
      (taylorLoopInvParityAt_to_taylorRoundFootprint
        newSp excess outPtr vals 495 (496 : Word) evenBase oddBase
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR h hh)
  have hFinal := cpsNBranchWithin_weaken_pre hPre hRound
  simpa [AB, PB] using hFinal

/- The zero arm is consumed immediately by `round_zero_exitdiv_tail`.  That
   continuation needs the five scratch values, so this adapter destructures
   `terminalZeroAny` and threads each value through the exit-divide proof. -/
private theorem outer_x0Free_sepConj {P Q : Assertion}
    (hP : x0FreeAssertion P) (hQ : x0FreeAssertion Q) :
    x0FreeAssertion (P ** Q) := by
  intro h hh
  obtain ⟨h1, h2, hd, hu, hp, hq⟩ := hh
  have h1x := hP h1 hp
  have h2x := hQ h2 hq
  rw [← hu]
  simp [PartialState.union, h1x, h2x]

private theorem outer_x0Free_regIs {r : Reg} {v : Word} (hr : r ≠ .x0) :
    x0FreeAssertion (regIs r v) := by
  intro h hh
  rw [hh]
  simp [PartialState.singletonReg, Ne.symm hr]

private theorem outer_x0Free_memIs {a v : Word} :
    x0FreeAssertion (memIs a v) := by
  intro h hh
  rw [hh.1]
  rfl

private theorem outer_x0Free_frameSlotsSaved
    (frame : FrameDesc) (newSp : Word) (vals : Reg → Word) :
    x0FreeAssertion (frameSlotsSaved frame newSp vals) := by
  induction frame with
  | nil =>
      intro h hh
      rw [hh]
      rfl
  | cons p rest ih =>
      simpa only [frameSlotsSaved_cons] using
        outer_x0Free_sepConj outer_x0Free_memIs ih

private theorem outer_x0Free_roundFrame :
    ∀ (newSp excess outPtr AB PB : Word) (vals : Reg → Word)
      (v6 v7 v28 v29 v30 v31 : Word)
      (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
      (FR : Assertion) (_hFR : x0FreeAssertion FR),
      x0FreeAssertion
      (roundFrame newSp excess outPtr AB PB vals v6 v7 v28 v29 v30 v31
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR) := by
  intro newSp excess outPtr AB PB vals v6 v7 v28 v29 v30 v31
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR _hFR
  unfold roundFrame
  repeat' first
    | apply outer_x0Free_sepConj
    | exact outer_x0Free_regIs (by decide)
    | exact outer_x0Free_memIs
    | exact outer_x0Free_frameSlotsSaved _ _ _
    | assumption

private theorem outer_x0Free_pure {P : Prop} : x0FreeAssertion (⌜P⌝) := by
  intro h hh
  rw [hh.1]
  rfl

private theorem outer_x0Free_roundZeroNoX0
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion)
    (hFR : x0FreeAssertion FR) :
    x0FreeAssertion (roundZeroNoX0 newSp excess outPtr iVal AB PB vals w
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
      s2 s3 s4 s5 v7 v28 v29 v30 v31 FR) := by
  unfold roundZeroNoX0
  repeat' first
    | apply outer_x0Free_sepConj
    | exact outer_x0Free_regIs (by decide)
    | exact outer_x0Free_memIs
    | exact outer_x0Free_frameSlotsSaved _ _ _
    | exact outer_x0Free_pure
    | exact outer_x0Free_roundFrame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    | assumption

private theorem outer_x0Free_exitdivOutputCells
    (outPtr o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : x0FreeAssertion FR) :
    x0FreeAssertion (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) := by
  unfold exitdivOutputCells
  repeat' first
    | apply outer_x0Free_sepConj
    | exact outer_x0Free_memIs
    | assumption

theorem terminal_zero_any_to_exitdiv
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree) (hFRx0 : x0FreeAssertion FR)
    (hAB : AB = newSp + signExtend12 (64 : BitVec 12))
    (hPB : PB = newSp + signExtend12 (112 : BitVec 12))
    {exits : List (Word × Assertion)}
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr iVal vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 o0 o1 o2 o3 AB PB FR)
      (exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word))))) :
    cpsNBranchWithin 4183 (PriceK + 804) priceCode
      (terminalZeroAny newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
      exits := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0Free : x0FreeAssertion FR0 := by
    unfold FR0
    exact outer_x0Free_exitdivOutputCells outPtr o0 o1 o2 o3 FR hFRx0
  have hZero : ∀ v7 v28 v29 v30 v31 : Word,
      cpsNBranchWithin 4183 (PriceK + 804) priceCode
        (roundZeroNoX0 newSp excess outPtr iVal AB PB vals
          (roundAccum a0 a1 a2 a3 a4 a5)
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
          s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0) exits := by
    intro v7 v28 v29 v30 v31
    have hZeroX := round_zero_exitdiv_tail
      newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
      s2 s3 s4 s5 v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR hAB hPB
      (exits := exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word))))
      hTail
    have hZeroX' :
        cpsNBranchWithin 4183 (PriceK + 804) priceCode
          ((roundZeroNoX0 newSp excess outPtr iVal AB PB vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
            s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0) **
            regIs .x0 (0 : Word))
          (exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word)))) := by
      refine cpsNBranchWithin_weaken_pre ?_ hZeroX
      intro h hp
      simp only [roundZeroNoX0, roundZero] at hp ⊢
      xperm_hyp hp
    have hZeroFree := outer_x0Free_roundZeroNoX0
      newSp excess outPtr iVal AB PB vals
      (roundAccum a0 a1 a2 a3 a4 a5)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
      s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0 hFR0Free
    have hDrop := cpsNBranchWithin_drop_x0
      (P := roundZeroNoX0 newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0)
      (exits := exits) hZeroFree hZeroX'
    simpa [FR0] using hDrop
  intro R hR s hcr hP hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hP
  obtain ⟨v7, v28, v29, v30, v31, hv⟩ := hPP
  exact hZero v7 v28 v29 v30 v31 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu, hv, hRb⟩ hpc

/- The actual terminal BGEU arm carries the exit-divide output cells in the
   caller frame.  Frame those cells before invoking the parity adapter, then
   consume only the zero arm; the nonzero status arm stays as the second
   branch.  This is the first list-level composition that checks the five
   retained scratch values at their real consumer boundary. -/
theorem taylor_round_terminal_496_from_parity_exitdiv
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree) (hFRx0 : x0FreeAssertion FR)
    (hAB : parityBuffer 495 evenBase oddBase =
      newSp + signExtend12 (64 : BitVec 12))
    (hPB : parityBuffer 495 oddBase evenBase =
      newSp + signExtend12 (112 : BitVec 12))
    {exits : List (Word × Assertion)}
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr (496 : Word) vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 o0 o1 o2 o3
        (parityBuffer 495 evenBase oddBase)
        (parityBuffer 495 oddBase evenBase) FR)
      (exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word))))) :
    cpsNBranchWithin (17 + 4183) (PriceK + 144) priceCode
      (taylorLoopInvParityAt newSp excess outPtr vals 495 (496 : Word)
        evenBase oddBase [a0, a1, a2, a3, a4, a5]
        [p0, p1, p2, p3, p4, p5] [s0, s1, s2, s3, s4, s5]
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
      (exits ++
        [(PriceK + 968,
          terminalStatus1Any newSp excess outPtr (496 : Word)
            (parityBuffer 495 evenBase oddBase)
            (parityBuffer 495 oddBase evenBase) vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
            s2 s3 s4 s5 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))]) := by
  let AB := parityBuffer 495 evenBase oddBase
  let PB := parityBuffer 495 oddBase evenBase
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0 : FR0.pcFree := by
    unfold FR0
    pcFree
    exact hFR
  have hRound := taylor_round_terminal_496_from_parity
    newSp excess outPtr vals evenBase oddBase
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    FR0 hFR0
  have hZero := terminal_zero_any_to_exitdiv
    newSp excess outPtr (496 : Word) AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    o0 o1 o2 o3 FR hFR hFRx0 (by simpa [AB] using hAB)
    (by simpa [PB] using hPB) hTail
  have hAll := nb_extend_head_same_cr hRound hZero
  simpa [AB, PB, FR0] using hAll

/- The concrete tail inputs produced by `exitdiv` are exactly a `tailCorePre`
   instance.  Keep this bridge separate from the round composition: it is the
   point where the synthetic tail theorem is replaced by the linked
   `tail_core` result, while preserving the explicit x0 factor needed by the
   exit-divide continuation. -/
theorem exitdiv_tail_core_x0_split
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 v19 v20 : Word) (FR : Assertion)
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (hFR : FR.pcFree) :
    cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr iVal vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 o0 o1 o2 o3 v19 v20 FR)
      [(PriceK + 968,
        tailStatus1NoX0 newSp excess outPtr vals
          (exitdivQ0 s0 s1 s2 s3 s4 s5)
          (exitdivQ1 s0 s1 s2 s3 s4 s5)
          (exitdivQ2 s0 s1 s2 s3 s4 s5)
          (exitdivQ3 s0 s1 s2 s3 s4 s5)
          (exitdivQ4 s0 s1 s2 s3 s4 s5)
          (exitdivQ5 s0 s1 s2 s3 s4 s5)
          o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
          (exitdivZ0 s0 s1 s2 s3 s4 s5).2.1 iVal v19 v20
          (exitdivQ0 s0 s1 s2 s3 s4 s5) (0 : Word)
          (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) +
            signExtend12 (-8 : BitVec 12)) (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR **
          (.x0 ↦ᵣ (0 : Word))),
       (PriceK + 968,
        tailStatus0BytesNoX0 newSp excess outPtr vals
          (exitdivQ0 s0 s1 s2 s3 s4 s5)
          (exitdivQ1 s0 s1 s2 s3 s4 s5)
          (exitdivQ2 s0 s1 s2 s3 s4 s5)
          (exitdivQ3 s0 s1 s2 s3 s4 s5)
          (exitdivQ4 s0 s1 s2 s3 s4 s5)
          (exitdivQ5 s0 s1 s2 s3 s4 s5)
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 iVal v19 v20
          (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR **
          (.x0 ↦ᵣ (0 : Word)))] := by
  have hCore := tail_core_status0_source_of_tail_core_x0_split
    newSp excess outPtr vals
    (exitdivQ0 s0 s1 s2 s3 s4 s5)
    (exitdivQ1 s0 s1 s2 s3 s4 s5)
    (exitdivQ2 s0 s1 s2 s3 s4 s5)
    (exitdivQ3 s0 s1 s2 s3 s4 s5)
    (exitdivQ4 s0 s1 s2 s3 s4 s5)
    (exitdivQ5 s0 s1 s2 s3 s4 s5)
    o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
    taylorDW (exitdivZ0 s0 s1 s2 s3 s4 s5).1
    (exitdivZ0 s0 s1 s2 s3 s4 s5).2.1 iVal v19 v20
    (exitdivQ0 s0 s1 s2 s3 s4 s5) (0 : Word)
    (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) +
      signExtend12 (-8 : BitVec 12)) (lcnt 5 + signExtend12 (-1 : BitVec 12))
    hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid FR hFR
  simpa only [exitdivTailPre] using hCore

/- At odd outer-loop parity the logical `AB` buffer is the physical `+112`
   buffer and `PB` is the physical `+64` buffer.  `exitdiv_seq_tail` names
   those physical cells as its `a` and `p` arguments, so the continuation must
   swap the argument values rather than assert the even-parity equalities. -/
theorem round_zero_exitdiv_tail_swapped
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion) (hFR : FR.pcFree)
    (hAB : AB = newSp + signExtend12 (112 : BitVec 12))
    (hPB : PB = newSp + signExtend12 (64 : BitVec 12))
    {exits : List (Word × Assertion)}
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr iVal vals
        p0 p1 p2 p3 p4 p5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
        o0 o1 o2 o3 AB PB FR) exits) :
    cpsNBranchWithin 4183 (PriceK + 804) priceCode
      (roundZero newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) exits := by
  have hSeq := exitdiv_seq_tail newSp excess outPtr iVal vals
    p0 p1 p2 p3 p4 p5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
    o0 o1 o2 o3 (roundAccum a0 a1 a2 a3 a4 a5) a5 v7 AB PB v28 v29 v30 v31
    FR hFR hTail
  refine cpsNBranchWithin_weaken_pre ?_ hSeq
  intro h hp
  simp only [roundZero] at hp
  have hp' := EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec.pure_drop_mid
    (L1 := (.x18 ↦ᵣ iVal))
    (L2 := ((.x5 ↦ᵣ (roundAccum a0 a1 a2 a3 a4 a5)) ** (.x0 ↦ᵣ (0 : Word))))
    (P := roundAccum a0 a1 a2 a3 a4 a5 = (0 : Word))
    (R := roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
    h (by
      simpa only [sepConj_assoc'] using hp)
  simp only [roundFrame, exitdivPre, exitdivOutputCells, hAB, hPB,
    EvmAsm.Rv64.AddrNorm.se12_0, EvmAsm.Rv64.AddrNorm.se12_8,
    EvmAsm.Rv64.AddrNorm.se12_16, EvmAsm.Rv64.AddrNorm.se12_24,
    EvmAsm.Rv64.AddrNorm.se12_32, EvmAsm.Rv64.AddrNorm.se12_40,
    EvmAsm.Rv64.AddrNorm.word_add_zero] at hp' ⊢
  xperm_hyp hp'

/- Consume the linked tail at the terminal-index round.  The existential is
   only the list-level packaging needed by the preceding parity adapter; its
   two members are fixed below to the status-1 and status-0 posts produced by
   the actual `tail_core` theorem, not an arbitrary continuation premise. -/
theorem taylor_round_terminal_496_from_parity_exitdiv_tail_core
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree) (hFRx0 : x0FreeAssertion FR)
    (hAB : parityBuffer 495 evenBase oddBase =
      newSp + signExtend12 (64 : BitVec 12))
    (hPB : parityBuffer 495 oddBase evenBase =
      newSp + signExtend12 (112 : BitVec 12))
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true) :
    ∃ exits : List (Word × Assertion),
      cpsNBranchWithin (17 + 4183) (PriceK + 144) priceCode
        (taylorLoopInvParityAt newSp excess outPtr vals 495 (496 : Word)
          evenBase oddBase [a0, a1, a2, a3, a4, a5]
          [p0, p1, p2, p3, p4, p5] [s0, s1, s2, s3, s4, s5]
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
        (exits ++
          [(PriceK + 968,
            terminalStatus1Any newSp excess outPtr (496 : Word)
              (parityBuffer 495 evenBase oddBase)
              (parityBuffer 495 oddBase evenBase) vals
              (roundAccum a0 a1 a2 a3 a4 a5)
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
              s2 s3 s4 s5 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))]) := by
  let AB := parityBuffer 495 evenBase oddBase
  let PB := parityBuffer 495 oddBase evenBase
  let Q1 : Assertion :=
    tailStatus1NoX0 newSp excess outPtr vals
      (exitdivQ0 s0 s1 s2 s3 s4 s5)
      (exitdivQ1 s0 s1 s2 s3 s4 s5)
      (exitdivQ2 s0 s1 s2 s3 s4 s5)
      (exitdivQ3 s0 s1 s2 s3 s4 s5)
      (exitdivQ4 s0 s1 s2 s3 s4 s5)
      (exitdivQ5 s0 s1 s2 s3 s4 s5)
      o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
      (exitdivZ0 s0 s1 s2 s3 s4 s5).2.1 (496 : Word) AB PB
      (exitdivQ0 s0 s1 s2 s3 s4 s5) (0 : Word)
      (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) +
        signExtend12 (-8 : BitVec 12)) (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR
  let Q0 : Assertion :=
    tailStatus0BytesNoX0 newSp excess outPtr vals
      (exitdivQ0 s0 s1 s2 s3 s4 s5)
      (exitdivQ1 s0 s1 s2 s3 s4 s5)
      (exitdivQ2 s0 s1 s2 s3 s4 s5)
      (exitdivQ3 s0 s1 s2 s3 s4 s5)
      (exitdivQ4 s0 s1 s2 s3 s4 s5)
      (exitdivQ5 s0 s1 s2 s3 s4 s5)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
      (496 : Word) AB PB
      (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR
  let exits : List (Word × Assertion) :=
    [(PriceK + 968, Q1), (PriceK + 968, Q0)]
  have hTail0 := exitdiv_tail_core_x0_split
    newSp excess outPtr (496 : Word) vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    o0 o1 o2 o3 AB PB FR
    hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR
  have hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr (496 : Word) vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 o0 o1 o2 o3 AB PB FR)
      (exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word)))) := by
    simpa [AB, PB, Q1, Q0, exits] using hTail0
  have hOut := taylor_round_terminal_496_from_parity_exitdiv
    newSp excess outPtr vals evenBase oddBase
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
    s2 s3 s4 s5 o0 o1 o2 o3 FR hFR hFRx0 hAB hPB hTail
  exact ⟨exits, hOut⟩

/- The terminal adapter's entry is not accepted merely because its CPS type
   elaborates.  Exhibit one joint heap for the actual parity invariant, with
   all three six-word buffers and the saved frame cells nonempty.  In
   particular, the scratch `regOwn` atoms are supplied once each and `x0` is
   absent, matching the x0-free continuation interface above. -/
private inductive terminalWitnessResource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private inductive terminalWitnessAtom where
  | regVal (r : Reg) (v : Word)
  | regOwn (r : Reg)
  | memVal (a : Word) (v : Word) (valid : isValidDwordAccess a = true)
  deriving DecidableEq

private def terminalWitnessAtomResource : terminalWitnessAtom → terminalWitnessResource
  | .regVal r _ => .reg r
  | .regOwn r => .reg r
  | .memVal a _ _ => .mem a

private def terminalWitnessAtomAssertion : terminalWitnessAtom → Assertion
  | .regVal r v => r ↦ᵣ v
  | .regOwn r => regOwn r
  | .memVal a v _ => a ↦ₘ v

private def terminalWitnessAtomHeap : terminalWitnessAtom → PartialState
  | .regVal r v => PartialState.singletonReg r v
  | .regOwn r => PartialState.singletonReg r 0
  | .memVal a v _ => PartialState.singletonMem a v

private theorem terminalWitnessSingletonReg_disjoint
    {r1 r2 : Reg} {v1 v2 : Word} (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r
    right
    simp [PartialState.singletonReg, hne]
  · left
    simp [PartialState.singletonReg, h]

private theorem terminalWitnessSingletonMem_disjoint
    {a1 a2 : Word} {v1 v2 : Word} (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a
    right
    simp [PartialState.singletonMem, hne]
  · left
    simp [PartialState.singletonMem, h]

private theorem terminalWitnessReg_mem_disjoint
    {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem terminalWitnessMem_reg_disjoint
    {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  terminalWitnessReg_mem_disjoint.symm

private theorem terminalWitnessAtomHeap_disjoint_of_resource_ne
    {x y : terminalWitnessAtom}
    (h : terminalWitnessAtomResource x ≠ terminalWitnessAtomResource y) :
    (terminalWitnessAtomHeap x).Disjoint (terminalWitnessAtomHeap y) := by
  cases x <;> cases y
  · apply terminalWitnessSingletonReg_disjoint
    simpa [terminalWitnessAtomResource] using h
  · apply terminalWitnessSingletonReg_disjoint
    simpa [terminalWitnessAtomResource] using h
  · exact terminalWitnessReg_mem_disjoint
  · apply terminalWitnessSingletonReg_disjoint
    simpa [terminalWitnessAtomResource] using h
  · apply terminalWitnessSingletonReg_disjoint
    simpa [terminalWitnessAtomResource] using h
  · exact terminalWitnessReg_mem_disjoint
  · exact terminalWitnessMem_reg_disjoint
  · exact terminalWitnessMem_reg_disjoint
  · apply terminalWitnessSingletonMem_disjoint
    simpa [terminalWitnessAtomResource] using h

private def terminalWitnessAtoms : List terminalWitnessAtom :=
  [ .regVal .x2 roundWitnessSp
  , .regVal .x1 0
  , .regVal .x10 0
  , .regVal .x11 roundWitnessOut
  , .regVal .x8 0
  , .regVal .x9 taylorDW
  , .regVal .x18 496
  , .regVal .x19 roundWitnessAB
  , .regVal .x20 roundWitnessPB
  , .regVal .x21 roundWitnessOut
  , .regVal .x22 roundWitnessSum
  , .memVal (roundWitnessSp + signExtend12 (0 : BitVec 12)) 0 (by decide)
  , .memVal (roundWitnessSp + signExtend12 (8 : BitVec 12)) 0 (by decide)
  , .memVal (roundWitnessSp + signExtend12 (16 : BitVec 12)) 0 (by decide)
  , .memVal (roundWitnessSp + signExtend12 (24 : BitVec 12)) 0 (by decide)
  , .memVal (roundWitnessSp + signExtend12 (32 : BitVec 12)) 0 (by decide)
  , .memVal (roundWitnessSp + signExtend12 (40 : BitVec 12)) 0 (by decide)
  , .memVal (roundWitnessSp + signExtend12 (48 : BitVec 12)) 0 (by decide)
  , .memVal (roundWitnessSp + signExtend12 (56 : BitVec 12)) 0 (by decide)
  , .regOwn .x5, .regOwn .x6, .regOwn .x7
  , .regOwn .x28, .regOwn .x29, .regOwn .x30, .regOwn .x31
  , .memVal roundWitnessAB 0 (by decide)
  , .memVal (roundWitnessAB + (8 : Word)) 0 (by decide)
  , .memVal (roundWitnessAB + (16 : Word)) 0 (by decide)
  , .memVal (roundWitnessAB + (24 : Word)) 0 (by decide)
  , .memVal (roundWitnessAB + (32 : Word)) 0 (by decide)
  , .memVal (roundWitnessAB + (40 : Word)) 0 (by decide)
  , .memVal roundWitnessPB 0 (by decide)
  , .memVal (roundWitnessPB + (8 : Word)) 0 (by decide)
  , .memVal (roundWitnessPB + (16 : Word)) 0 (by decide)
  , .memVal (roundWitnessPB + (24 : Word)) 0 (by decide)
  , .memVal (roundWitnessPB + (32 : Word)) 0 (by decide)
  , .memVal (roundWitnessPB + (40 : Word)) 0 (by decide)
  , .memVal roundWitnessSum 0 (by decide)
  , .memVal (roundWitnessSum + (8 : Word)) 0 (by decide)
  , .memVal (roundWitnessSum + (16 : Word)) 0 (by decide)
  , .memVal (roundWitnessSum + (24 : Word)) 0 (by decide)
  , .memVal (roundWitnessSum + (32 : Word)) 0 (by decide)
  , .memVal (roundWitnessSum + (40 : Word)) 0 (by decide) ]

private def terminalWitnessAtomsAssert : Assertion :=
  terminalWitnessAtoms.foldr
    (fun x acc => terminalWitnessAtomAssertion x ** acc) empAssertion

private def terminalWitnessHeap : PartialState :=
  terminalWitnessAtoms.foldr
    (fun x acc => (terminalWitnessAtomHeap x).union acc) PartialState.empty

private theorem terminalWitnessAtoms_pairwise :
    terminalWitnessAtoms.Pairwise
      (fun x y => terminalWitnessAtomResource x ≠ terminalWitnessAtomResource y) := by
  unfold terminalWitnessAtoms terminalWitnessAtomResource
    roundWitnessSp roundWitnessAB roundWitnessPB roundWitnessSum roundWitnessOut
  decide

private theorem terminalWitnessAtoms_hsat :
    terminalWitnessAtomsAssert terminalWitnessHeap := by
  apply sepConj_foldr_satisfiable terminalWitnessAtomAssertion
    terminalWitnessAtomHeap terminalWitnessAtoms
  · intro x hx
    cases x with
    | regVal r v => exact rfl
    | regOwn r => exact ⟨0, rfl⟩
    | memVal a v hvalid => exact ⟨rfl, hvalid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => terminalWitnessAtomHeap_disjoint_of_resource_ne h)
      terminalWitnessAtoms_pairwise

theorem taylor_loop_inv_parity_at_496_inhabited :
    ∃ h : PartialState,
      taylorLoopInvParityAt roundWitnessSp 0 roundWitnessOut roundWitnessVals
        495 (496 : Word) roundWitnessPB roundWitnessAB
        [0, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 0]
        empAssertion h := by
  refine ⟨terminalWitnessHeap, ?_⟩
  simpa [taylorLoopInvParityAt, terminalWitnessAtomsAssert,
    terminalWitnessAtoms, terminalWitnessAtomAssertion,
    terminalWitnessHeap, terminalWitnessAtomHeap,
    frameSlotsSaved, priceFrame, roundWitnessVals,
    roundWitnessSp, roundWitnessAB, roundWitnessPB, roundWitnessSum,
        roundWitnessOut, cellsOf_six, sepConj_emp_right', sepConj_assoc',
    EvmAsm.Rv64.SAsm.regOwns, parityBuffer,
    EvmAsm.Rv64.AddrNorm.se12_0, EvmAsm.Rv64.AddrNorm.se12_8,
    EvmAsm.Rv64.AddrNorm.se12_16, EvmAsm.Rv64.AddrNorm.se12_24,
    EvmAsm.Rv64.AddrNorm.se12_32, EvmAsm.Rv64.AddrNorm.se12_40,
    EvmAsm.Rv64.AddrNorm.se12_48, EvmAsm.Rv64.AddrNorm.se12_56] using terminalWitnessAtoms_hsat

#print axioms taylor_round_terminal_496_from_footprint
#print axioms taylor_round_terminal_496_from_parity
#print axioms terminal_zero_any_to_exitdiv
#print axioms taylor_round_terminal_496_from_parity_exitdiv
#print axioms taylor_round_terminal_496_from_parity_exitdiv_tail_core
#print axioms taylor_loop_inv_parity_at_496_inhabited

end EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec
