/-
  EvmAsm.EL.Secp256r1VerifyInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_secp256r1_verify` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge

@[expose] public section

namespace EvmAsm.EL

namespace Secp256r1VerifyInputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- A secp256r1 message hash as represented by `zkvm_secp256r1_hash`. -/
abbrev MessageHashBytes := Fin 32 → Byte

/-- A secp256r1 signature as represented by `zkvm_secp256r1_signature`. -/
abbrev SignatureBytes := Fin 64 → Byte

/-- A secp256r1 public key as represented by `zkvm_secp256r1_pubkey`. -/
abbrev PublicKeyBytes := Fin 64 → Byte

/-- Input payload passed to `zkvm_secp256r1_verify(msg, sig, pubkey, verified)`. -/
structure AcceleratorInput where
  msg : MessageHashBytes
  sig : SignatureBytes
  pubkey : PublicKeyBytes

/-- Read one fixed-width secp256r1 message hash from executable memory. -/
def messageHashFromMemory (memory : MemoryReader) (start : Nat) : MessageHashBytes :=
  fun i => memory (start + i.toNat)

/-- Read one fixed-width secp256r1 signature from executable memory. -/
def signatureFromMemory (memory : MemoryReader) (start : Nat) : SignatureBytes :=
  fun i => memory (start + i.toNat)

/-- Read one fixed-width secp256r1 public key from executable memory. -/
def publicKeyFromMemory (memory : MemoryReader) (start : Nat) : PublicKeyBytes :=
  fun i => memory (start + i.toNat)

/--
Distinctive token: Secp256r1VerifyInputBridge.secp256r1VerifyInputFromMemory.
-/
def secp256r1VerifyInputFromMemory
    (memory : MemoryReader) (msgStart sigStart pubkeyStart : Nat) :
    AcceleratorInput :=
  { msg := messageHashFromMemory memory msgStart
    sig := signatureFromMemory memory sigStart
    pubkey := publicKeyFromMemory memory pubkeyStart }

theorem messageHashFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 32) :
    messageHashFromMemory memory start i = memory (start + i.toNat) := rfl

theorem signatureFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    signatureFromMemory memory start i = memory (start + i.toNat) := rfl

theorem publicKeyFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    publicKeyFromMemory memory start i = memory (start + i.toNat) := rfl

theorem secp256r1VerifyInputFromMemory_msg
    (memory : MemoryReader) (msgStart sigStart pubkeyStart : Nat) :
    (secp256r1VerifyInputFromMemory memory msgStart sigStart pubkeyStart).msg =
      messageHashFromMemory memory msgStart := rfl

theorem secp256r1VerifyInputFromMemory_sig
    (memory : MemoryReader) (msgStart sigStart pubkeyStart : Nat) :
    (secp256r1VerifyInputFromMemory memory msgStart sigStart pubkeyStart).sig =
      signatureFromMemory memory sigStart := rfl

theorem secp256r1VerifyInputFromMemory_pubkey
    (memory : MemoryReader) (msgStart sigStart pubkeyStart : Nat) :
    (secp256r1VerifyInputFromMemory memory msgStart sigStart pubkeyStart).pubkey =
      publicKeyFromMemory memory pubkeyStart := rfl

end Secp256r1VerifyInputBridge

end EvmAsm.EL
