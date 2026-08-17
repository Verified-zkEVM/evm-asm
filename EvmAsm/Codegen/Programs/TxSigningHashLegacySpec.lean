/-
  EvmAsm.Codegen.Programs.TxSigningHashLegacySpec

  K146 `tx_signing_hash_legacy_eip155` whole-routine contract.
-/

import EvmAsm.Codegen.Programs.TxSigningHashResidual
import EvmAsm.Codegen.Programs.TxSigningHashLegacySpecCore
import EvmAsm.Stateless.SpecRef.Transactions
import EvmAsm.EL.RLP.Properties

namespace EvmAsm.Codegen.TxSigningHashLegacySpec

open EvmAsm.Codegen
open EvmAsm.Codegen.TxSigningHashResidual
open EvmAsm.EL.RLP
open EvmAsm.Stateless.SpecRef

/-! The source-level message used by the machine and the SpecRef message are
    deliberately kept separate.  The bridge below is the only place where an
    encoded legacy transaction is related to `signing_hash_155`. -/

private def specScalar (n : Nat) : RLPItem :=
  .bytes (EvmAsm.EL.RLP.Nat.toBytesBE n)

private def specToItem : Option Address → RLPItem
  | none => .bytes []
  | some a => .bytes a

def legacySpecMessage (tx : LegacyTransaction) (chainId : U64) : Bytes :=
  EvmAsm.EL.RLP.encode (.list
    [specScalar tx.nonce, specScalar tx.gasPrice, specScalar tx.gas,
      specToItem tx.to, specScalar tx.value, .bytes tx.data,
      specScalar chainId, specScalar 0, specScalar 0])

theorem legacySpecMessage_eq_signing_hash_preimage
    (tx : LegacyTransaction) (chainId : U64) :
    EvmAsm.Stateless.SpecRef.keccak256 (legacySpecMessage tx chainId) =
      EvmAsm.Stateless.SpecRef.signing_hash_155 tx chainId := by
  rfl

theorem legacyEip155SigningMessage_of_encode_transaction
    (tx : LegacyTransaction) (chainId : U64)
    (hchain : chainId < 2 ^ 64)
    (hbound : (EvmAsm.EL.RLP.encode (EvmAsm.Stateless.SpecRef.txToRlpItem
      (.legacy tx))).length < 256 ^ 8) :
    legacyEip155SigningMessage
        (EvmAsm.Stateless.SpecRef.encode_transaction (.legacy tx))
        (BitVec.ofNat 64 chainId) =
      some (legacySpecMessage tx chainId) := by
  have hdecode :
      decodeFully (EvmAsm.EL.RLP.encode
        (EvmAsm.Stateless.SpecRef.txToRlpItem (.legacy tx))) =
        some (EvmAsm.Stateless.SpecRef.txToRlpItem (.legacy tx)) :=
    EvmAsm.EL.RLP.decodeFully_encode _ hbound
  simp only [EvmAsm.Stateless.SpecRef.encode_transaction]
  unfold legacyEip155SigningMessage
  rw [hdecode]
  simp only [EvmAsm.Stateless.SpecRef.txToRlpItem]
  dsimp
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hchain]
  change some (EvmAsm.EL.RLP.encode (.list
      [.bytes (Nat.toBytesBE tx.nonce), .bytes (Nat.toBytesBE tx.gasPrice),
       .bytes (Nat.toBytesBE tx.gas), specToItem tx.to,
       .bytes (Nat.toBytesBE tx.value), .bytes tx.data,
       .bytes (Nat.toBytesBE chainId), .bytes [], .bytes []])) = _
  simp [legacySpecMessage, specScalar, specToItem, Nat.toBytesBE_zero]

end EvmAsm.Codegen.TxSigningHashLegacySpec
