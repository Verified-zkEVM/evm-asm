/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakPure

  Pure sponge correspondence for the inline `zkvm_keccak256` wrapper.
  Bridges the guest's zero / XOR-absorb / pad10*1 / squeeze steps to
  SpecRef `keccak256` without touching the emitted Program.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakSpec
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.MultiRw

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

/-- Zero sponge as 200 LE state bytes. -/
def keccakZeroStateBytes : List (BitVec 8) :=
  List.replicate 200 (0 : BitVec 8)

@[simp] theorem keccakZeroStateBytes_length : keccakZeroStateBytes.length = 200 := by
  simp only [keccakZeroStateBytes, List.length_replicate]

private theorem extractByte_zero (pos : Nat) :
    extractByte (0 : Word) pos = 0 := by
  simp [extractByte]

private theorem dwordBytes_zero :
    dwordBytes (0 : Word) = List.replicate 8 (0 : BitVec 8) := by
  simp only [dwordBytes, extractByte_zero]
  rfl

private theorem flatten_replicate_replicate (a : BitVec 8) (n m : Nat) :
    (List.replicate n (List.replicate m a)).flatten = List.replicate (n * m) a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul]
    rw [← List.replicate_add]
    congr 1
    omega

theorem keccakStateBytes_zero :
    keccakStateBytes (List.replicate 25 (0 : BitVec 64)) = keccakZeroStateBytes := by
  unfold keccakStateBytes keccakZeroStateBytes
  have hlane := dwordBytes_zero
  have hmap :
      (List.replicate 25 (0 : BitVec 64)).map dwordBytes =
        List.replicate 25 (List.replicate 8 (0 : BitVec 8)) := by
    rw [List.map_replicate, hlane]
  have hflat :
      (List.replicate 25 (0 : BitVec 64)).flatMap dwordBytes =
        (List.replicate 25 (List.replicate 8 (0 : BitVec 8))).flatten := by
    change ((List.replicate 25 (0 : BitVec 64)).map dwordBytes).flatten =
      (List.replicate 25 (List.replicate 8 (0 : BitVec 8))).flatten
    exact congrArg List.flatten hmap
  rw [hflat, flatten_replicate_replicate]

theorem chunkBytes_nil (n : Nat) : chunkBytes n ([] : Bytes) = [] := by
  simp [chunkBytes, chunkBytesAux]

theorem chunkBytes_take_zero (n : Nat) (bs : Bytes) :
    chunkBytes n (bs.take 0) = [] := by
  simp [List.take_zero, chunkBytes_nil]

theorem keccakAbsorbedState_zero (input : Bytes) :
    keccakAbsorbedState input 0 = keccakZeroStateBytes := by
  unfold keccakAbsorbedState keccakAbsorbBlocks
  rw [show keccakRateBytes * 0 = 0 from Nat.mul_zero _, List.take_zero,
    chunkBytes_nil, keccakAbsorb, keccakStateBytes_zero]

/-- First four LE lanes of a 25-lane state, as 32 bytes (the squeeze). -/
def keccakSqueeze32 (st : List (BitVec 64)) : Bytes :=
  (st.take 4).flatMap (fun lane => natToBytesLE 8 lane.toNat)

theorem keccak256_eq_squeeze_absorb (msg : Bytes) :
    keccak256 msg =
      keccakSqueeze32
        (keccakAbsorb (List.replicate 25 (0 : BitVec 64))
          (chunkBytes keccakRateBytes (keccakPad msg))) := by
  rfl

/-- Guest pad on residual state after `rem` remainder bytes XOR-absorbed at
    a zero-origin cursor: XOR `0x01` at offset `rem` and XOR `0x80` at 135.
    When `rem = 135` the two collide to `0x81`. -/
def keccakGuestPad (st : List (BitVec 8)) (rem : Nat) : List (BitVec 8) :=
  let st1 := setBytes st rem [((st.getD rem 0) ^^^ (1 : BitVec 8))]
  setBytes st1 135 [((st1.getD 135 0) ^^^ (0x80 : BitVec 8))]

/-- Splice one LE dword XOR at lane `q` (byte offset `8*q`). -/
def xorDwordAt (st : List (BitVec 8)) (q : Nat) (v : Word) : List (BitVec 8) :=
  let old := packBytes ((st.drop (8 * q)).take 8)
  setBytes st (8 * q) (dwordBytes (old ^^^ v))

end EvmAsm.Codegen.Proofs
