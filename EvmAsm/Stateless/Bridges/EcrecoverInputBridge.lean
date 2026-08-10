/-
  EvmAsm.Stateless.Bridges.EcrecoverInputBridge

  Lay out the input buffer the ECRECOVER ECALL bridge expects.
  Mirrors `EvmAsm/EL/Keccak{Stack,Input}Bridge.lean`'s split:
  input layout is its own file so the proof structure can talk
  about it independently of the ECALL semantics.

  ## Buffer layout (matches zkvm-standards types)

      offset  size  field
       0..32   32   msg digest (zkvm_secp256k1_hash)
      32..96   64   signature  (zkvm_secp256k1_signature, r||s)
      96..97    1   recid       (uint8_t)
      97..104   7   padding to 8-byte alignment

  Total: 104 bytes (rounded to 104 = 13 * 8 doublewords).

  Buffer placement is caller-chosen (scaffold). The former
  `ECRECOVER_SCRATCH` MemoryLayout VA was reclaimed under GH #11186
  (collided with the raised block-read pack); do not revive it as a
  scheme-A region.

  ## PR-K12 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Bridges.EcrecoverInputBridge

-- TODO(stateless-bridges): expose helpers to write msg / sig /
-- recid into the scratch buffer.

end EvmAsm.Stateless.Bridges.EcrecoverInputBridge
