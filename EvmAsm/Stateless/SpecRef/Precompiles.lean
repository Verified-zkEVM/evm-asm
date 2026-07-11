/-
  EvmAsm.Stateless.SpecRef.Precompiles

  Port of `execution-specs/src/ethereum/forks/amsterdam/vm/
  precompiled_contracts/` (`@tests-zkevm@v0.5.0`, `bd8c673`) — bead
  `evm-asm-s1d19.5`:

  * the 18 addresses of `__init__.py` and the dispatch table of
    `mapping.py` (`PRE_COMPILED_CONTRACTS`)
  * `ecrecover.py` — function `ecrecover`
  * `sha256.py` — function `sha256`
  * `identity.py` — function `identity`
  * `modexp.py` — functions `modexp`, `complexity`, `iterations`,
    `gas_cost`

  ## Status: SUPERSEDED by `PrecompilesTable.lean`

  The staging table below (4 implementations + reject-on-contact
  placeholders) and the hybrid fallback `elExecuteHybrid` are retained
  only as the historical staging mechanism (scope doc §3) and for
  divergence triage; the DEFAULT seam is the complete-table
  `elExecute` (`PrecompilesTable.lean`) with no fallback.
-/

import EvmAsm.Stateless.SpecRef.ElExecute

namespace EvmAsm.Stateless.SpecRef

private def addr (n : Nat) : Address := natToBytesBE 20 n

def ECRECOVER_ADDRESS : Address := addr 0x01
def SHA256_ADDRESS : Address := addr 0x02
def RIPEMD160_ADDRESS : Address := addr 0x03
def IDENTITY_ADDRESS : Address := addr 0x04
def MODEXP_ADDRESS : Address := addr 0x05
def ALT_BN128_ADD_ADDRESS : Address := addr 0x06
def ALT_BN128_MUL_ADDRESS : Address := addr 0x07
def ALT_BN128_PAIRING_CHECK_ADDRESS : Address := addr 0x08
def BLAKE2F_ADDRESS : Address := addr 0x09
def POINT_EVALUATION_ADDRESS : Address := addr 0x0a
def BLS12_G1_ADD_ADDRESS : Address := addr 0x0b
def BLS12_G1_MSM_ADDRESS : Address := addr 0x0c
def BLS12_G2_ADD_ADDRESS : Address := addr 0x0d
def BLS12_G2_MSM_ADDRESS : Address := addr 0x0e
def BLS12_PAIRING_ADDRESS : Address := addr 0x0f
def BLS12_MAP_FP_TO_G1_ADDRESS : Address := addr 0x10
def BLS12_MAP_FP2_TO_G2_ADDRESS : Address := addr 0x11
def P256VERIFY_ADDRESS : Address := addr 0x100

namespace GasCosts
def PRECOMPILE_SHA256_BASE : Uint := 60
def PRECOMPILE_SHA256_PER_WORD : Uint := 12
def PRECOMPILE_IDENTITY_BASE : Uint := 15
def PRECOMPILE_IDENTITY_PER_WORD : Uint := 3
end GasCosts

/-! ## `ecrecover.py` (function `ecrecover`) -/

def pEcrecover : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  charge_gas GasCosts.PRECOMPILE_ECRECOVER
  let message_hash := buffer_read data 0 32
  let v := bytesBEtoNat (buffer_read data 32 32)
  let r := bytesBEtoNat (buffer_read data 64 32)
  let s := bytesBEtoNat (buffer_read data 96 32)
  if v ≠ 27 && v ≠ 28 then return
  if r == 0 || r ≥ SECP256K1N then return
  if s == 0 || s ≥ SECP256K1N then return
  match Secp256k1.recover (bytesBEtoNat message_hash) r s (v - 27) with
  | .error _ => return
  | .ok (x, y) =>
      let address := (keccak256 (natToBytesBE 32 x ++ natToBytesBE 32 y)).drop 12
      EvmM.modifyEvm (fun e => { e with output := List.replicate 12 0x00 ++ address })

/-! ## `sha256.py` (function `sha256`) -/

def pSha256 : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  let word_count := ceil32 data.length / 32
  charge_gas (GasCosts.PRECOMPILE_SHA256_BASE
    + GasCosts.PRECOMPILE_SHA256_PER_WORD * word_count)
  EvmM.modifyEvm (fun e => { e with output := sha256 data })

/-! ## `identity.py` (function `identity`) -/

def pIdentity : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  let word_count := ceil32 data.length / 32
  charge_gas (GasCosts.PRECOMPILE_IDENTITY_BASE
    + GasCosts.PRECOMPILE_IDENTITY_PER_WORD * word_count)
  EvmM.modifyEvm (fun e => { e with output := data })

/-! ## `modexp.py` (functions `modexp`, `complexity`, `iterations`,
`gas_cost`) -/

def modexpComplexity (base_length modulus_length : U256) : Uint :=
  let max_length := max base_length modulus_length
  let words := (max_length + 7) / 8
  if max_length > 32 then 2 * words^2 else 16

def modexpIterations (exponent_length exponent_head : U256) : Uint :=
  let bitlen := fun (n : Nat) => if n == 0 then 0 else Nat.log2 n + 1
  let count :=
    if exponent_length ≤ 32 && exponent_head == 0 then 0
    else if exponent_length ≤ 32 then bitlen exponent_head - 1
    else 16 * (exponent_length - 32) +
      (let b := bitlen exponent_head; b - 1)
  max count 1

def modexpGasCost (base_length modulus_length exponent_length
    exponent_head : U256) : Uint :=
  max 500 (modexpComplexity base_length modulus_length
    * modexpIterations exponent_length exponent_head)

def pModexp : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  let base_length := bytesBEtoNat (buffer_read data 0 32)
  if base_length > 1024 then throw .outOfGas
  let exp_length := bytesBEtoNat (buffer_read data 32 32)
  if exp_length > 1024 then throw .outOfGas
  let modulus_length := bytesBEtoNat (buffer_read data 64 32)
  if modulus_length > 1024 then throw .outOfGas
  let exp_start := 96 + base_length
  let exp_head := bytesBEtoNat (buffer_read data exp_start (min 32 exp_length))
  charge_gas (modexpGasCost base_length modulus_length exp_length exp_head)
  if base_length == 0 && modulus_length == 0 then
    EvmM.modifyEvm (fun e => { e with output := [] })
    return
  let base := bytesBEtoNat (buffer_read data 96 base_length)
  let exp := bytesBEtoNat (buffer_read data exp_start exp_length)
  let modulus := bytesBEtoNat (buffer_read data (exp_start + exp_length) modulus_length)
  if modulus == 0 then
    EvmM.modifyEvm (fun e => { e with output := List.replicate modulus_length 0x00 })
  else
    -- exponent ≤ 1024 bytes = 8192 bits; fuel accordingly.
    let r := EvmAsm.Rv64.Accel.powModAux modulus (8 * 1024 + 8) (base % modulus) exp
    EvmM.modifyEvm (fun e => { e with output := natToBytesBE modulus_length r })

/-! ## The dispatch table (`mapping.py` `PRE_COMPILED_CONTRACTS`) -/

/-- Placeholder for a not-yet-ported implementation: rejects on contact
    (never a wrong value; see the header — the seam is not wired until
    none of these remain). -/
private def unimplemented (name : String) : EvmM Unit :=
  EvmM.liftSpec (throw (.unimplementedPrecompile name))

/-- `PRE_COMPILED_CONTRACTS`.  Address set complete; see the header for
    the implementation status. -/
def specRefPrecompiles : PrecompileMap :=
  [(ECRECOVER_ADDRESS, pEcrecover),
   (SHA256_ADDRESS, pSha256),
   (RIPEMD160_ADDRESS, unimplemented "ripemd160"),
   (IDENTITY_ADDRESS, pIdentity),
   (MODEXP_ADDRESS, pModexp),
   (ALT_BN128_ADD_ADDRESS, unimplemented "alt_bn128_add"),
   (ALT_BN128_MUL_ADDRESS, unimplemented "alt_bn128_mul"),
   (ALT_BN128_PAIRING_CHECK_ADDRESS, unimplemented "alt_bn128_pairing_check"),
   (BLAKE2F_ADDRESS, unimplemented "blake2f"),
   (POINT_EVALUATION_ADDRESS, unimplemented "point_evaluation"),
   (BLS12_G1_ADD_ADDRESS, unimplemented "bls12_g1_add"),
   (BLS12_G1_MSM_ADDRESS, unimplemented "bls12_g1_msm"),
   (BLS12_G2_ADD_ADDRESS, unimplemented "bls12_g2_add"),
   (BLS12_G2_MSM_ADDRESS, unimplemented "bls12_g2_msm"),
   (BLS12_PAIRING_ADDRESS, unimplemented "bls12_pairing"),
   (BLS12_MAP_FP_TO_G1_ADDRESS, unimplemented "bls12_map_fp_to_g1"),
   (BLS12_MAP_FP2_TO_G2_ADDRESS, unimplemented "bls12_map_fp2_to_g2"),
   (P256VERIFY_ADDRESS, unimplemented "p256verify")]

/-! ## The hybrid seam

Full `elExecute` with the table above; contact with a not-yet-ported
precompile falls back to the sound-for-accepts static shell
(`executeSeamShell`) for THAT input — the fall-back only ever accepts
more, so the hybrid stays monotone (scope doc §3): no false rejects,
and every fixture not touching a missing precompile gets the real
verdict. -/

def elExecuteHybrid : ExecutionSeam := fun input =>
  match elExecuteWith specRefPrecompiles input with
  | .error (.unimplementedPrecompile _) => executeSeamShell input
  | r => r

end EvmAsm.Stateless.SpecRef
