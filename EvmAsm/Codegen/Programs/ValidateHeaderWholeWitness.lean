/-
  EvmAsm.Codegen.Programs.ValidateHeaderWholeWitness

  Concrete non-vacuity witnesses for `validateHeaderCorePre` (#12346).

  These theorems only show that the caller-side atom conjunction is
  satisfiable.  They do not discharge `validate_header_cps_compose`: the
  machine route contract remains an explicit, undischarged premise and the
  routine has no semantic callers yet.  In particular, the non-empty frame
  below is intentional; an `empAssertion` witness alone would not demonstrate
  that a real framed resource can coexist with the caller-owned atoms.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderWhole
import EvmAsm.Rv64.MemSat
import Batteries.Tactic.OpenPrivate

set_option maxRecDepth 8000

namespace EvmAsm.Stateless.SpecRef
open private numericFieldsOk bytesFieldsOk getNChecked getBChecked from
  EvmAsm.Stateless.SpecRef.Stateless
def validateHeaderWitness_numericFieldsOk (bs : List Bytes) : Bool := numericFieldsOk bs
def validateHeaderWitness_bytesFieldsOk (isCurrent : Bool) (bs : List Bytes) : Bool :=
  bytesFieldsOk isCurrent bs
end EvmAsm.Stateless.SpecRef

namespace EvmAsm.Codegen.ValidateHeaderWhole

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCompose
open EvmAsm.Codegen.ValidateHeaderInlineArms
open private numericFieldsOk bytesFieldsOk checkNumericFields decodeHeaderArm rlpBytes?
  getNChecked getBChecked from
  EvmAsm.Stateless.SpecRef.Stateless
open private scalarItem from EvmAsm.Stateless.SpecRef.BlocksRlp

abbrev hcoreWitnessSpC : Word := 0x10000
abbrev hcoreWitnessSp0 : Word := 0x10038
abbrev hcoreWitnessHeader : Word := 0x20000
abbrev hcoreWitnessParent : Word := 0x30000
abbrev hcoreWitnessParent2 : Word := 0x31000
abbrev hcoreWitnessParentRlp : Word := 0x32000
abbrev hcoreWitnessGAddr : Word := 0x40000

private def hcoreZero8 : List (BitVec 8) := List.replicate 8 0
private def hcoreZero32 : List (BitVec 8) := List.replicate 32 0
private def hcoreZero256 : List (BitVec 8) := List.replicate 256 0

/- The concrete row-00045 pair used by the linked probe.  Keeping these as
   `Header` values (rather than an opaque byte blob) lets the strengthened
   precondition tie both raw RLP regions to the exact values represented by
   the decoder records.  The pair is canonical and each encoding is 645
   bytes, as measured by the probe's RLP decode. -/
def hcoreWitnessHeaderSpec : EvmAsm.Stateless.SpecRef.Header :=
  { isCurrentFork := true,
    parentHash := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x335e8238c6e0bdad99a808afaf4c36a768e07a2acb3e940595f392aeb0bd57a0,
    ommersHash := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347,
    coinbase := EvmAsm.Stateless.SpecRef.natToBytesBE 20
      0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba,
    stateRoot := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x6d5bcf6e34aca2c571d7a31286ab1d51c5b5056fea0abd3f1d88019ef771d8ab,
    transactionsRoot := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0xade9583168af2e073a47ac6b9cf022c0acee600b6180bd459653f9fdab3304cd,
    receiptRoot := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0xb7b075e3ad31ca1eac7ae23f52c828df249370d1ad1046ed06d550d4fb185f83,
    bloom := hcoreZero256,
    difficulty := 0, number := 2, gasLimit := 120000000, gasUsed := 97920,
    timestamp := 24, extraData := [],
    prevRandao := hcoreZero32, nonce := hcoreZero8,
    baseFeePerGas := 7,
    withdrawalsRoot := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421,
    blobGasUsed := 131072, excessBlobGas := 262144,
    parentBeaconBlockRoot := hcoreZero32,
    requestsHash := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855,
    blockAccessListHash := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x1edb1944c095f9f65003b99d1597fb3739f41aec6ef032253684e17d29f45661,
    slotNumber := 0 }

def hcoreWitnessParentSpec : EvmAsm.Stateless.SpecRef.Header :=
  { isCurrentFork := true,
    parentHash := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0xf4bdc1d30cbe6682cbbd2e4de0a12458739bcc2000127a3069216020b40c6863,
    ommersHash := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347,
    coinbase := EvmAsm.Stateless.SpecRef.natToBytesBE 20
      0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba,
    stateRoot := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x0eb69123ca4508e96d10d93b69d37302adad8f2c577bdffecb060c82b7ca7fb1,
    transactionsRoot := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x8235286e676f686c956095b4d350824b745abf81f14bcd022503b8193665bbfa,
    receiptRoot := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0xf25bea4db3d79fa348bc78be6d622b241124fde0bc85f3e7b8349a11a9d0990a,
    bloom := hcoreZero256,
    difficulty := 0, number := 1, gasLimit := 120000000, gasUsed := 183600,
    timestamp := 12, extraData := [],
    prevRandao := hcoreZero32, nonce := hcoreZero8,
    baseFeePerGas := 7,
    withdrawalsRoot := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421,
    blobGasUsed := 786432, excessBlobGas := 1310720,
    parentBeaconBlockRoot := hcoreZero32,
    requestsHash := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855,
    blockAccessListHash := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x8c092354d3b4411df0c64a0fadb1a4924396b54b240d96ea7d946a28db9d0467,
    slotNumber := 0 }

/- A successful status-0 instance reuses the measured parent and all of the
   child fields, changing only the parent-hash field to the hash that the
   validator actually checks.  This keeps the non-vacuity witness on the same
   concrete header shape as the existing rejection witness. -/
def hcoreStatus0HeaderSpec : EvmAsm.Stateless.SpecRef.Header :=
  { hcoreWitnessHeaderSpec with
    parentHash := EvmAsm.Stateless.SpecRef.headerHash hcoreWitnessParentSpec }

def hcoreStatus0HeaderStruct : List (BitVec 8) :=
  headerCoreStructBytes hcoreStatus0HeaderSpec

def hcoreStatus0HeaderRlp : List (BitVec 8) :=
  EvmAsm.EL.RLP.encode
    (EvmAsm.Stateless.SpecRef.headerToRlpItem hcoreStatus0HeaderSpec)

theorem hcoreStatus0_validate_header :
    EvmAsm.Stateless.SpecRef.validate_header hcoreWitnessParentSpec
      hcoreStatus0HeaderSpec = .ok () := by
  have hcalc : EvmAsm.Stateless.SpecRef.calculate_excess_blob_gas
      hcoreWitnessParentSpec = .ok 262144 := by decide
  have hbase : EvmAsm.Stateless.SpecRef.calculate_base_fee_per_gas
      120000000 120000000 183600 7 = .ok 7 := by decide
  have hbase' : EvmAsm.Stateless.SpecRef.calculate_base_fee_per_gas
      120000000 hcoreWitnessParentSpec.gasLimit hcoreWitnessParentSpec.gasUsed
      hcoreWitnessParentSpec.baseFeePerGas = .ok 7 := by
    simpa [hcoreWitnessParentSpec] using hbase
  have hpnonce : hcoreWitnessParentSpec.nonce = List.replicate 8 (0 : BitVec 8) := by rfl
  have hpommers : hcoreWitnessParentSpec.ommersHash =
      EvmAsm.Stateless.SpecRef.EMPTY_OMMER_HASH := by decide
  have hpnum : hcoreWitnessParentSpec.number = 1 := by rfl
  have hplimit : hcoreWitnessParentSpec.gasLimit = 120000000 := by rfl
  have hpused : hcoreWitnessParentSpec.gasUsed = 183600 := by rfl
  have hpbasefee : hcoreWitnessParentSpec.baseFeePerGas = 7 := by rfl
  have hptime : hcoreWitnessParentSpec.timestamp = 12 := by rfl
  have hommersLit :
      EvmAsm.Stateless.SpecRef.natToBytesBE 32
          0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347 =
        EvmAsm.Stateless.SpecRef.EMPTY_OMMER_HASH := by decide
  unfold EvmAsm.Stateless.SpecRef.validate_header
  rw [hcalc]
  simp [hcoreStatus0HeaderSpec, hcoreWitnessHeaderSpec, hcoreZero8,
    hpnum, hplimit, hpused, hpbasefee, hptime, hommersLit,
    EvmAsm.Stateless.SpecRef.calculate_base_fee_per_gas,
    EvmAsm.Stateless.SpecRef.check_gas_limit,
    EvmAsm.Stateless.SpecRef.GasCosts.LIMIT_ADJUSTMENT_FACTOR,
    EvmAsm.Stateless.SpecRef.GasCosts.LIMIT_MINIMUM]
  rfl

def hcoreWitnessHeaderStruct : List (BitVec 8) :=
  headerCoreStructBytes hcoreWitnessHeaderSpec

def hcoreWitnessParentStruct : List (BitVec 8) :=
  headerCoreStructBytes hcoreWitnessParentSpec

/- The repaired precondition owns the two RLP byte regions as well as the
   decoded 144-byte records.  These are the exact canonical encodings of the
   concrete synthetic headers above (the row-00045 pair is added below as a
   separate, production-shaped witness).  Defining them through the encoder
   makes the raw-to-spec relation close by construction rather than by an
   untrusted decoder premise. -/
def hcoreWitnessHeaderRlp : List (BitVec 8) :=
  EvmAsm.EL.RLP.encode
    (EvmAsm.Stateless.SpecRef.headerToRlpItem hcoreWitnessHeaderSpec)

def hcoreWitnessParentRlpBytes : List (BitVec 8) :=
  EvmAsm.EL.RLP.encode
    (EvmAsm.Stateless.SpecRef.headerToRlpItem hcoreWitnessParentSpec)

theorem hcoreEncodeNatBE32 (n : Nat) :
    (EvmAsm.EL.RLP.encode
      (.bytes (EvmAsm.Stateless.SpecRef.natToBytesBE 32 n))).length = 33 := by
  change (EvmAsm.EL.RLP.encodeBytes
    (EvmAsm.Stateless.SpecRef.natToBytesBE 32 n)).length = 33
  have hlen := EvmAsm.Stateless.SpecRef.natToBytesBE_length 32 n
  have hne : (EvmAsm.Stateless.SpecRef.natToBytesBE 32 n).length ≠ 1 := by omega
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by omega) hne]
  simp [hlen]

private theorem hcoreEncodeNatLE8 (n : Nat) :
    (EvmAsm.EL.RLP.encode
      (.bytes (EvmAsm.Stateless.SpecRef.natToBytesLE 8 n))).length = 9 := by
  change (EvmAsm.EL.RLP.encodeBytes
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 n)).length = 9
  have hlen := EvmAsm.Stateless.SpecRef.natToBytesLE_length 8 n
  have hne : (EvmAsm.Stateless.SpecRef.natToBytesLE 8 n).length ≠ 1 := by omega
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by omega) hne]
  simp [hlen]

private theorem hcoreEncodeNatBE20 (n : Nat) :
    (EvmAsm.EL.RLP.encode
      (.bytes (EvmAsm.Stateless.SpecRef.natToBytesBE 20 n))).length = 21 := by
  change (EvmAsm.EL.RLP.encodeBytes
    (EvmAsm.Stateless.SpecRef.natToBytesBE 20 n)).length = 21
  have hlen := EvmAsm.Stateless.SpecRef.natToBytesBE_length 20 n
  have hne : (EvmAsm.Stateless.SpecRef.natToBytesBE 20 n).length ≠ 1 := by omega
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by omega) hne]
  simp [hlen]

private theorem hcoreEncodeBytesNatBE32_len (n : Nat) :
    (EvmAsm.EL.RLP.encodeBytes
      (EvmAsm.Stateless.SpecRef.natToBytesBE 32 n)).length = 33 := by
  have hlen := EvmAsm.Stateless.SpecRef.natToBytesBE_length 32 n
  have hne : (EvmAsm.Stateless.SpecRef.natToBytesBE 32 n).length ≠ 1 := by
    omega
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by omega) hne]
  simp [hlen]

private theorem hcoreEncodeBytesNatBE20_len (n : Nat) :
    (EvmAsm.EL.RLP.encodeBytes
      (EvmAsm.Stateless.SpecRef.natToBytesBE 20 n)).length = 21 := by
  have hlen := EvmAsm.Stateless.SpecRef.natToBytesBE_length 20 n
  have hne : (EvmAsm.Stateless.SpecRef.natToBytesBE 20 n).length ≠ 1 := by
    omega
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by omega) hne]
  simp [hlen]

private theorem hcoreEncodeBytesNatLE8_len (n : Nat) :
    (EvmAsm.EL.RLP.encodeBytes
      (EvmAsm.Stateless.SpecRef.natToBytesLE 8 n)).length = 9 := by
  have hlen := EvmAsm.Stateless.SpecRef.natToBytesLE_length 8 n
  have hne : (EvmAsm.Stateless.SpecRef.natToBytesLE 8 n).length ≠ 1 := by
    omega
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by omega) hne]
  simp [hlen]

private theorem hcoreEncodeBloom :
    (EvmAsm.EL.RLP.encode
      (.bytes (List.replicate 256 (0 : BitVec 8)))).length = 259 := by
  change (EvmAsm.EL.RLP.encodeBytes (List.replicate 256 (0 : BitVec 8))).length = 259
  rw [EvmAsm.EL.RLP.encodeBytes_long_of_length _ (by simp)]
  norm_num [List.length_append, List.length_replicate,
    EvmAsm.EL.RLP.Nat.toBytesBE]

theorem hcoreEncodeScalar0 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 0))).length = 1 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

theorem hcoreEncodeScalar1 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 1))).length = 1 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeScalar2 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 2))).length = 1 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeScalar7 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 7))).length = 1 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeScalar12 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 12))).length = 1 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeScalar24 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 24))).length = 1 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeScalar120000000 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 120000000))).length = 5 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeScalar97920 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 97920))).length = 4 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeScalar183600 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 183600))).length = 4 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeScalar131072 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 131072))).length = 4 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeScalar262144 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 262144))).length = 4 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeScalar786432 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 786432))).length = 4 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeScalar1310720 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 1310720))).length = 4 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

theorem hcoreEncodeBytesRep32 (b : BitVec 8) :
    (EvmAsm.EL.RLP.encode (.bytes (List.replicate 32 b))).length = 33 := by
  change (EvmAsm.EL.RLP.encodeBytes (List.replicate 32 b)).length = 33
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by simp) (by simp)]
  simp

private theorem hcoreEncodeBytesRep32_len (b : BitVec 8) :
    (EvmAsm.EL.RLP.encodeBytes (List.replicate 32 b)).length = 33 := by
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by simp) (by simp)]
  simp

private theorem hcoreEncodeBytesRep20 (b : BitVec 8) :
    (EvmAsm.EL.RLP.encode (.bytes (List.replicate 20 b))).length = 21 := by
  change (EvmAsm.EL.RLP.encodeBytes (List.replicate 20 b)).length = 21
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by simp) (by simp)]
  simp

private theorem hcoreEncodeBytesRep20_len (b : BitVec 8) :
    (EvmAsm.EL.RLP.encodeBytes (List.replicate 20 b)).length = 21 := by
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by simp) (by simp)]
  simp

theorem hcoreEncodeBytesRep8 (b : BitVec 8) :
    (EvmAsm.EL.RLP.encode (.bytes (List.replicate 8 b))).length = 9 := by
  change (EvmAsm.EL.RLP.encodeBytes (List.replicate 8 b)).length = 9
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by simp) (by simp)]
  simp

private theorem hcoreEncodeBytesRep8_len (b : BitVec 8) :
    (EvmAsm.EL.RLP.encodeBytes (List.replicate 8 b)).length = 9 := by
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by simp) (by simp)]
  simp

private theorem hcoreEncodeBytesRep256 (b : BitVec 8) :
    (EvmAsm.EL.RLP.encode (.bytes (List.replicate 256 b))).length = 259 := by
  change (EvmAsm.EL.RLP.encodeBytes (List.replicate 256 b)).length = 259
  rw [EvmAsm.EL.RLP.encodeBytes_long_of_length _ (by simp)]
  simp [EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeBytesRep256_len (b : BitVec 8) :
    (EvmAsm.EL.RLP.encodeBytes (List.replicate 256 b)).length = 259 := by
  rw [EvmAsm.EL.RLP.encodeBytes_long_of_length _ (by simp)]
  simp [EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeBytesEmpty :
    (EvmAsm.EL.RLP.encode (.bytes ([] : List (BitVec 8)))).length = 1 := by
  rfl

private theorem hcoreEncodeBytesEmpty_len :
    (EvmAsm.EL.RLP.encodeBytes ([] : List (BitVec 8))).length = 1 := by
  rfl

private theorem hcoreEncodeZero8 :
    (EvmAsm.EL.RLP.encode (.bytes hcoreZero8)).length = 9 := by
  simpa [hcoreZero8] using hcoreEncodeBytesRep8 (0 : BitVec 8)

private theorem hcoreEncodeZero32 :
    (EvmAsm.EL.RLP.encode (.bytes hcoreZero32)).length = 33 := by
  simpa [hcoreZero32] using hcoreEncodeBytesRep32 (0 : BitVec 8)

private theorem hcoreEncodeZero256 :
    (EvmAsm.EL.RLP.encode (.bytes hcoreZero256)).length = 259 := by
  simpa [hcoreZero256] using hcoreEncodeBytesRep256 (0 : BitVec 8)

theorem hcoreEncode_len_of_bytes_length
    (bs : List (BitVec 8)) (n : Nat) (hlen : bs.length = n) (hne : n ≠ 1)
    (hshort : n ≤ 55) :
    (EvmAsm.EL.RLP.encode (.bytes bs)).length = n + 1 := by
  change (EvmAsm.EL.RLP.encodeBytes bs).length = n + 1
  have hshort' : bs.length ≤ 55 := by simpa [hlen] using hshort
  have hne' : bs.length ≠ 1 := by simpa [hlen] using hne
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one bs hshort' hne']
  simp [hlen]

private theorem hcoreEncode_len_of_bytes_long
    (bs : List (BitVec 8)) (n : Nat) (hlen : bs.length = n) (hlong : 55 < n) :
    (EvmAsm.EL.RLP.encode (.bytes bs)).length =
      1 + (EvmAsm.EL.RLP.Nat.toBytesBE n).length + n := by
  change (EvmAsm.EL.RLP.encodeBytes bs).length =
    1 + (EvmAsm.EL.RLP.Nat.toBytesBE n).length + n
  have hlong' : 55 < bs.length := by simpa [hlen] using hlong
  rw [EvmAsm.EL.RLP.encodeBytes_long_of_length bs hlong']
  simp [hlen]
  omega

private theorem hcoreEncode_len_of_bytes_short_direct
    (bs : List (BitVec 8)) (hshort : bs.length ≤ 55) (hne : bs.length ≠ 1) :
    (EvmAsm.EL.RLP.encode (.bytes bs)).length = bs.length + 1 := by
  change (EvmAsm.EL.RLP.encodeBytes bs).length = bs.length + 1
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one bs hshort hne]
  simp

private theorem hcoreEncode_len_of_bytes_long_direct
    (bs : List (BitVec 8)) (hlong : 55 < bs.length) :
    (EvmAsm.EL.RLP.encode (.bytes bs)).length =
      1 + (EvmAsm.EL.RLP.Nat.toBytesBE bs.length).length + bs.length := by
  change (EvmAsm.EL.RLP.encodeBytes bs).length =
    1 + (EvmAsm.EL.RLP.Nat.toBytesBE bs.length).length + bs.length
  rw [EvmAsm.EL.RLP.encodeBytes_long_of_length bs hlong]
  simp
  omega

private theorem hcoreEncodeItems_length_nil :
    (EvmAsm.EL.RLP.encode.encodeItems ([] : List EvmAsm.EL.RLP.RLPItem)).length = 0 := by
  rfl

private theorem hcoreEncodeItems_length_cons
    (item : EvmAsm.EL.RLP.RLPItem) (rest : List EvmAsm.EL.RLP.RLPItem) :
    (EvmAsm.EL.RLP.encode.encodeItems (item :: rest)).length =
      (EvmAsm.EL.RLP.encode item).length +
        (EvmAsm.EL.RLP.encode.encodeItems rest).length := by
  simp [EvmAsm.EL.RLP.encode.encodeItems, List.length_append]

theorem hcoreHeaderItems_length :
    (match EvmAsm.Stateless.SpecRef.headerToRlpItem hcoreWitnessHeaderSpec with
     | .list items => (EvmAsm.EL.RLP.encode.encodeItems items).length
     | .bytes _ => 0) = 642 := by
  simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.headerToRlpItem,
    scalarItem]
  rw [hcoreEncodeItems_length_cons]
  simp only [hcoreEncodeItems_length_cons, hcoreEncodeItems_length_nil,
    hcoreEncodeNatBE32, hcoreEncodeNatBE20,
    hcoreEncodeScalar0,
    hcoreEncodeScalar2, hcoreEncodeScalar7, hcoreEncodeScalar24,
    hcoreEncodeScalar120000000, hcoreEncodeScalar97920,
    hcoreEncodeScalar131072, hcoreEncodeScalar262144,
    hcoreEncodeBytesEmpty,
    hcoreEncodeZero8, hcoreEncodeZero32, hcoreEncodeZero256]

theorem hcoreParentItems_length :
    (match EvmAsm.Stateless.SpecRef.headerToRlpItem hcoreWitnessParentSpec with
     | .list items => (EvmAsm.EL.RLP.encode.encodeItems items).length
     | .bytes _ => 0) = 642 := by
  simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.headerToRlpItem,
    scalarItem]
  rw [hcoreEncodeItems_length_cons]
  simp only [hcoreEncodeItems_length_cons, hcoreEncodeItems_length_nil,
    hcoreEncodeNatBE32, hcoreEncodeNatBE20,
    hcoreEncodeScalar0, hcoreEncodeScalar1,
    hcoreEncodeScalar7, hcoreEncodeScalar12,
    hcoreEncodeScalar120000000,
    hcoreEncodeScalar183600, hcoreEncodeScalar786432,
    hcoreEncodeScalar1310720,
    hcoreEncodeBytesEmpty,
    hcoreEncodeZero8, hcoreEncodeZero32, hcoreEncodeZero256]

theorem hcoreEncodeList_length_642
    (items : List EvmAsm.EL.RLP.RLPItem)
    (hitems : (EvmAsm.EL.RLP.encode.encodeItems items).length = 642) :
    (EvmAsm.EL.RLP.encode (.list items)).length = 645 := by
  simp [EvmAsm.EL.RLP.encode, hitems, EvmAsm.EL.RLP.Nat.toBytesBE]

theorem hcoreHeaderRlp_length : hcoreWitnessHeaderRlp.length = 645 := by
  unfold hcoreWitnessHeaderRlp
  generalize hitem : EvmAsm.Stateless.SpecRef.headerToRlpItem hcoreWitnessHeaderSpec = item
  cases item with
  | bytes bs =>
      simp [EvmAsm.Stateless.SpecRef.headerToRlpItem] at hitem
  | list items =>
      have hitems : (EvmAsm.EL.RLP.encode.encodeItems items).length = 642 := by
        simpa [hitem] using hcoreHeaderItems_length
      exact hcoreEncodeList_length_642 items hitems

private theorem hcoreStatus0EncodeHash32 :
    (EvmAsm.EL.RLP.encode
      (.bytes (EvmAsm.Stateless.SpecRef.headerHash hcoreWitnessParentSpec))).length = 33 := by
  have hlen : (EvmAsm.Stateless.SpecRef.headerHash hcoreWitnessParentSpec).length = 32 :=
    EvmAsm.Stateless.SpecRef.keccak256_length _
  have h := hcoreEncode_len_of_bytes_short_direct
    (EvmAsm.Stateless.SpecRef.headerHash hcoreWitnessParentSpec)
    (by rw [hlen]; omega) (by rw [hlen]; omega)
  simpa [hlen] using h

private theorem hcoreStatus0HeaderItems_length :
    (match EvmAsm.Stateless.SpecRef.headerToRlpItem hcoreStatus0HeaderSpec with
     | .list items => (EvmAsm.EL.RLP.encode.encodeItems items).length
     | .bytes _ => 0) = 642 := by
  simp [hcoreStatus0HeaderSpec, hcoreWitnessHeaderSpec,
    EvmAsm.Stateless.SpecRef.headerToRlpItem,
    scalarItem]
  rw [hcoreEncodeItems_length_cons]
  simp only [hcoreEncodeItems_length_cons, hcoreEncodeItems_length_nil,
    hcoreStatus0EncodeHash32, hcoreEncodeNatBE32,
    hcoreEncodeNatBE20, hcoreEncodeScalar0, hcoreEncodeScalar2,
    hcoreEncodeScalar7, hcoreEncodeScalar24, hcoreEncodeScalar120000000,
    hcoreEncodeScalar97920, hcoreEncodeScalar131072, hcoreEncodeScalar262144,
    hcoreEncodeBytesEmpty, hcoreEncodeZero8, hcoreEncodeZero32,
    hcoreEncodeZero256]

theorem hcoreStatus0HeaderRlp_length : hcoreStatus0HeaderRlp.length = 645 := by
  unfold hcoreStatus0HeaderRlp
  generalize hitem : EvmAsm.Stateless.SpecRef.headerToRlpItem hcoreStatus0HeaderSpec = item
  cases item with
  | bytes bs =>
      simp [EvmAsm.Stateless.SpecRef.headerToRlpItem] at hitem
  | list items =>
      have hitems : (EvmAsm.EL.RLP.encode.encodeItems items).length = 642 := by
        simpa [hitem] using hcoreStatus0HeaderItems_length
      exact hcoreEncodeList_length_642 items hitems

theorem hcore_decodeHeaderArm_ok
    (isCurrent : Bool) (bs : List EvmAsm.Stateless.SpecRef.Bytes)
    (hnum : EvmAsm.Stateless.SpecRef.validateHeaderWitness_numericFieldsOk bs = true)
    (hbytes : EvmAsm.Stateless.SpecRef.validateHeaderWitness_bytesFieldsOk isCurrent bs = true) :
    decodeHeaderArm isCurrent bs =
      .ok (EvmAsm.Stateless.SpecRef.mkHeaderFields isCurrent bs) := by
  change numericFieldsOk bs = true at hnum
  change bytesFieldsOk isCurrent bs = true at hbytes
  unfold decodeHeaderArm checkNumericFields
  rw [hnum, hbytes]
  rfl

theorem hcoreStatus0_decodeHeader :
    EvmAsm.Stateless.SpecRef._decode_header hcoreStatus0HeaderRlp =
      .ok hcoreStatus0HeaderSpec := by
  let h := hcoreStatus0HeaderSpec
  let bs : List EvmAsm.Stateless.SpecRef.Bytes :=
    [h.parentHash, h.ommersHash, h.coinbase, h.stateRoot,
     h.transactionsRoot, h.receiptRoot, h.bloom,
     EvmAsm.EL.RLP.Nat.toBytesBE h.difficulty,
     EvmAsm.EL.RLP.Nat.toBytesBE h.number,
     EvmAsm.EL.RLP.Nat.toBytesBE h.gasLimit,
     EvmAsm.EL.RLP.Nat.toBytesBE h.gasUsed,
     EvmAsm.EL.RLP.Nat.toBytesBE h.timestamp,
     h.extraData, h.prevRandao, h.nonce,
     EvmAsm.EL.RLP.Nat.toBytesBE h.baseFeePerGas,
     h.withdrawalsRoot,
     EvmAsm.EL.RLP.Nat.toBytesBE h.blobGasUsed,
     EvmAsm.EL.RLP.Nat.toBytesBE h.excessBlobGas,
     h.parentBeaconBlockRoot, h.requestsHash, h.blockAccessListHash,
     EvmAsm.EL.RLP.Nat.toBytesBE h.slotNumber]
  have hitem : EvmAsm.Stateless.SpecRef.headerToRlpItem h =
      .list (bs.map EvmAsm.EL.RLP.RLPItem.bytes) := by
    simp [bs, h, hcoreStatus0HeaderSpec, hcoreWitnessHeaderSpec,
      EvmAsm.Stateless.SpecRef.headerToRlpItem, scalarItem]
  have hmap : (bs.map EvmAsm.EL.RLP.RLPItem.bytes).mapM rlpBytes? = some bs := by
    induction bs with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, List.mapM_cons, rlpBytes?]
        rw [ih]
        simp
  have hnum : EvmAsm.Stateless.SpecRef.validateHeaderWitness_numericFieldsOk bs = true := by
    change numericFieldsOk bs = true
    simp [numericFieldsOk, EvmAsm.Stateless.SpecRef.numericFieldWidths, getNChecked,
      EvmAsm.Stateless.SpecRef.decodeItemScalar, bs, h, hcoreStatus0HeaderSpec,
      hcoreWitnessHeaderSpec, EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD]
    decide
  have hbytes : EvmAsm.Stateless.SpecRef.validateHeaderWitness_bytesFieldsOk true bs = true := by
    change bytesFieldsOk true bs = true
    simp [bytesFieldsOk, EvmAsm.Stateless.SpecRef.fixedBytesFieldWidths,
      EvmAsm.Stateless.SpecRef.currentForkBytesFieldWidths, getBChecked,
      EvmAsm.Stateless.SpecRef.decodeItemFixedBytes, bs, h, hcoreStatus0HeaderSpec,
      hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length,
      EvmAsm.Stateless.SpecRef.headerHash,
      EvmAsm.Stateless.SpecRef.keccak256_length, List.all, List.getD]
    decide
  have hmk : EvmAsm.Stateless.SpecRef.mkHeaderFields true bs = h := by
    simp [EvmAsm.Stateless.SpecRef.mkHeaderFields, bs, h, hcoreStatus0HeaderSpec,
      hcoreWitnessHeaderSpec, EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]
  unfold hcoreStatus0HeaderRlp
  rw [hitem]
  have hlen : hcoreStatus0HeaderRlp.length = 645 := hcoreStatus0HeaderRlp_length
  have hfull := EvmAsm.EL.RLP.decodeFully_encode
    (.list (bs.map EvmAsm.EL.RLP.RLPItem.bytes))
    (by change hcoreStatus0HeaderRlp.length < 256 ^ 8; rw [hlen]; decide)
  simp only [EvmAsm.Stateless.SpecRef._decode_header, hfull, hmap]
  simp [bs, h, hcore_decodeHeaderArm_ok, hnum, hbytes, hmk]

theorem hcoreParentRlp_length : hcoreWitnessParentRlpBytes.length = 645 := by
  unfold hcoreWitnessParentRlpBytes
  generalize hitem : EvmAsm.Stateless.SpecRef.headerToRlpItem hcoreWitnessParentSpec = item
  cases item with
  | bytes bs =>
      simp [EvmAsm.Stateless.SpecRef.headerToRlpItem] at hitem
  | list items =>
      have hitems : (EvmAsm.EL.RLP.encode.encodeItems items).length = 642 := by
        simpa [hitem] using hcoreParentItems_length
      exact hcoreEncodeList_length_642 items hitems

theorem hcoreParent_decodeHeader :
    EvmAsm.Stateless.SpecRef._decode_header hcoreWitnessParentRlpBytes =
      .ok hcoreWitnessParentSpec := by
  let h := hcoreWitnessParentSpec
  let bs : List EvmAsm.Stateless.SpecRef.Bytes :=
    [h.parentHash, h.ommersHash, h.coinbase, h.stateRoot,
     h.transactionsRoot, h.receiptRoot, h.bloom,
     EvmAsm.EL.RLP.Nat.toBytesBE h.difficulty,
     EvmAsm.EL.RLP.Nat.toBytesBE h.number,
     EvmAsm.EL.RLP.Nat.toBytesBE h.gasLimit,
     EvmAsm.EL.RLP.Nat.toBytesBE h.gasUsed,
     EvmAsm.EL.RLP.Nat.toBytesBE h.timestamp,
     h.extraData, h.prevRandao, h.nonce,
     EvmAsm.EL.RLP.Nat.toBytesBE h.baseFeePerGas,
     h.withdrawalsRoot,
     EvmAsm.EL.RLP.Nat.toBytesBE h.blobGasUsed,
     EvmAsm.EL.RLP.Nat.toBytesBE h.excessBlobGas,
     h.parentBeaconBlockRoot, h.requestsHash, h.blockAccessListHash,
     EvmAsm.EL.RLP.Nat.toBytesBE h.slotNumber]
  have hitem : EvmAsm.Stateless.SpecRef.headerToRlpItem h =
      .list (bs.map EvmAsm.EL.RLP.RLPItem.bytes) := by
    simp [bs, h, hcoreWitnessParentSpec,
      EvmAsm.Stateless.SpecRef.headerToRlpItem, scalarItem]
  have hmap : (bs.map EvmAsm.EL.RLP.RLPItem.bytes).mapM rlpBytes? = some bs := by
    induction bs with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, List.mapM_cons, rlpBytes?]
        rw [ih]
        simp
  have hnum : EvmAsm.Stateless.SpecRef.validateHeaderWitness_numericFieldsOk bs = true := by
    change numericFieldsOk bs = true
    simp [numericFieldsOk, EvmAsm.Stateless.SpecRef.numericFieldWidths, getNChecked,
      EvmAsm.Stateless.SpecRef.decodeItemScalar, bs, h,
      hcoreWitnessParentSpec, EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD]
    decide
  have hbytes : EvmAsm.Stateless.SpecRef.validateHeaderWitness_bytesFieldsOk true bs = true := by
    change bytesFieldsOk true bs = true
    simp [bytesFieldsOk, EvmAsm.Stateless.SpecRef.fixedBytesFieldWidths,
      EvmAsm.Stateless.SpecRef.currentForkBytesFieldWidths, getBChecked,
      EvmAsm.Stateless.SpecRef.decodeItemFixedBytes, bs, h, hcoreWitnessParentSpec,
      EvmAsm.Stateless.SpecRef.natToBytesBE_length,
      List.all, List.getD]
    decide
  have hmk : EvmAsm.Stateless.SpecRef.mkHeaderFields true bs = h := by
    simp [EvmAsm.Stateless.SpecRef.mkHeaderFields, bs, h, hcoreWitnessParentSpec,
      EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]
  unfold hcoreWitnessParentRlpBytes
  rw [hitem]
  have hlen : hcoreWitnessParentRlpBytes.length = 645 := hcoreParentRlp_length
  have hfull := EvmAsm.EL.RLP.decodeFully_encode
    (.list (bs.map EvmAsm.EL.RLP.RLPItem.bytes))
    (by change hcoreWitnessParentRlpBytes.length < 256 ^ 8; rw [hlen]; decide)
  simp only [EvmAsm.Stateless.SpecRef._decode_header, hfull, hmap]
  simp [bs, h, hcore_decodeHeaderArm_ok, hnum, hbytes, hmk]

private def hcoreWitnessRlpMems (base : Word) (bs : List (BitVec 8)) : List (Word × Word) :=
  (List.range ((bs.length + 7) / 8)).map (fun i =>
    (base + BitVec.ofNat 64 (8 * i), packBytes ((bs.drop (8 * i)).take 8)))

def hcoreWitnessGBytes : List (BitVec 8) :=
  [1, 2, 3, 4, 5, 6, 7, 8]

def hcoreWitnessRegs : List (Reg × Word) :=
  [(.x1, 0), (.x2, hcoreWitnessSpC), (.x8, hcoreWitnessHeader),
   (.x9, BitVec.ofNat 64 hcoreWitnessHeaderRlp.length),
   (.x18, hcoreWitnessParent), (.x19, hcoreWitnessParent2),
   (.x20, hcoreWitnessParentRlp), (.x21, BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length),
   (.x10, hcoreWitnessHeader), (.x11, BitVec.ofNat 64 hcoreWitnessHeaderRlp.length),
   (.x12, hcoreWitnessParent), (.x13, hcoreWitnessParent2),
   (.x14, hcoreWitnessParentRlp),
   (.x15, BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)]

def hcoreWitnessStructMems (base : Word) (bs : List (BitVec 8)) : List (Word × Word) :=
  [(base, packBytes (bs.take 8)),
   (base + 8, packBytes ((bs.drop 8).take 8)),
   (base + 16, packBytes ((bs.drop 16).take 8)),
   (base + 24, packBytes ((bs.drop 24).take 8)),
   (base + 32, packBytes ((bs.drop 32).take 8)),
   (base + 40, packBytes ((bs.drop 40).take 8)),
   (base + 48, packBytes ((bs.drop 48).take 8)),
   (base + 56, packBytes ((bs.drop 56).take 8)),
   (base + 64, packBytes ((bs.drop 64).take 8)),
   (base + 72, packBytes ((bs.drop 72).take 8)),
   (base + 80, packBytes ((bs.drop 80).take 8)),
   (base + 88, packBytes ((bs.drop 88).take 8)),
   (base + 96, packBytes ((bs.drop 96).take 8)),
   (base + 104, packBytes ((bs.drop 104).take 8)),
   (base + 112, packBytes ((bs.drop 112).take 8)),
   (base + 120, packBytes ((bs.drop 120).take 8)),
   (base + 128, packBytes ((bs.drop 128).take 8)),
   (base + 136, packBytes ((bs.drop 136).take 8))]

def hcoreWitnessMems : List (Word × Word) :=
  [(hcoreWitnessSpC, 0), (hcoreWitnessSpC + 8, hcoreWitnessHeader),
   (hcoreWitnessSpC + 16, BitVec.ofNat 64 hcoreWitnessHeaderRlp.length),
   (hcoreWitnessSpC + 24, hcoreWitnessParent),
   (hcoreWitnessSpC + 32, hcoreWitnessParent2),
   (hcoreWitnessSpC + 40, hcoreWitnessParentRlp),
   (hcoreWitnessSpC + 48, BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)] ++
  hcoreWitnessStructMems hcoreWitnessParent hcoreWitnessHeaderStruct ++
  hcoreWitnessStructMems hcoreWitnessParent2 hcoreWitnessParentStruct ++
  [(hcoreWitnessGAddr, packBytes hcoreWitnessGBytes)]

private def hcoreWitnessMemsNoG : List (Word × Word) :=
  [(hcoreWitnessSpC, 0), (hcoreWitnessSpC + 8, hcoreWitnessHeader),
   (hcoreWitnessSpC + 16, BitVec.ofNat 64 hcoreWitnessHeaderRlp.length),
   (hcoreWitnessSpC + 24, hcoreWitnessParent),
   (hcoreWitnessSpC + 32, hcoreWitnessParent2),
   (hcoreWitnessSpC + 40, hcoreWitnessParentRlp),
   (hcoreWitnessSpC + 48, BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)] ++
  hcoreWitnessStructMems hcoreWitnessParent hcoreWitnessHeaderStruct ++
  hcoreWitnessStructMems hcoreWitnessParent2 hcoreWitnessParentStruct

def hcoreStatus0Mems : List (Word × Word) :=
  [(hcoreWitnessSpC, 0), (hcoreWitnessSpC + 8, hcoreWitnessHeader),
   (hcoreWitnessSpC + 16, BitVec.ofNat 64 hcoreStatus0HeaderRlp.length),
   (hcoreWitnessSpC + 24, hcoreWitnessParent),
   (hcoreWitnessSpC + 32, hcoreWitnessParent2),
   (hcoreWitnessSpC + 40, hcoreWitnessParentRlp),
   (hcoreWitnessSpC + 48, BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)] ++
  hcoreWitnessStructMems hcoreWitnessParent hcoreStatus0HeaderStruct ++
  hcoreWitnessStructMems hcoreWitnessParent2 hcoreWitnessParentStruct ++
  [(hcoreWitnessGAddr, packBytes hcoreWitnessGBytes)]

theorem hcoreStatus0HeaderStruct_length :
    hcoreStatus0HeaderStruct.length = 144 := by
  have hp : (EvmAsm.Stateless.SpecRef.headerHash hcoreWitnessParentSpec).length = 32 :=
    EvmAsm.Stateless.SpecRef.keccak256_length _
  have hs : hcoreStatus0HeaderSpec.stateRoot.length = 32 := by
    simp [hcoreStatus0HeaderSpec, hcoreWitnessHeaderSpec,
      EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  simp [hcoreStatus0HeaderStruct, hcoreStatus0HeaderSpec,
    hcoreWitnessHeaderSpec, headerCoreStructBytes, hp,
    EvmAsm.Stateless.SpecRef.natToBytesBE_length,
    EvmAsm.Stateless.SpecRef.natToBytesLE_length]

def hcoreStatus0MemHeap : (Word × Word) → PartialState :=
  fun p => PartialState.singletonMem p.1 p.2

def hcoreStatus0MemAtom : (Word × Word) → Assertion :=
  fun p => p.1 ↦ₘ p.2

def hcoreStatus0MemFold : Assertion :=
  hcoreStatus0Mems.foldr (fun p acc => hcoreStatus0MemAtom p ** acc) empAssertion

def hcoreStatus0MemHeapFold : PartialState :=
  hcoreStatus0Mems.foldr
    (fun p acc => (hcoreStatus0MemHeap p).union acc) PartialState.empty

theorem hcoreStatus0MemFold_sat :
    hcoreStatus0MemFold hcoreStatus0MemHeapFold := by
  apply sepConj_foldr_satisfiable hcoreStatus0MemAtom
    hcoreStatus0MemHeap hcoreStatus0Mems
  · intro p hp
    simp_all [hcoreStatus0Mems, hcoreWitnessStructMems,
      hcoreStatus0HeaderRlp_length]
    repeat' first | rcases hp with hp | hp
    all_goals
      simp only [hcoreStatus0MemAtom, hcoreStatus0MemHeap, memIs,
        PartialState.singletonMem]
      exact ⟨by trivial, by decide⟩
  · have hd : hcoreStatus0Mems.Pairwise (fun p q => p.1 ≠ q.1) := by
      have hdold : hcoreWitnessMems.Pairwise (fun p q => p.1 ≠ q.1) := by
        decide
      have hdoldAddr :
          (hcoreWitnessMems.map Prod.fst).Pairwise (fun a b => a ≠ b) := by
        exact hdold.map Prod.fst (by intro a b h; exact h)
      have haddr : hcoreStatus0Mems.map Prod.fst =
          hcoreWitnessMems.map Prod.fst := by
        simp [hcoreStatus0Mems, hcoreWitnessMems, hcoreWitnessStructMems,
          hcoreStatus0HeaderRlp_length, hcoreHeaderRlp_length]
      rw [← haddr] at hdoldAddr
      exact List.pairwise_map.mp hdoldAddr
    exact List.Pairwise.imp
      (fun {_ _} h =>
        EvmAsm.Codegen.ValidateHeaderCompose.routeInhabitantMemSingletonDisjoint h)
      hd

private theorem hcoreWitnessStructFold_eq_bytesRegion
    (base : Word) (bs : List (BitVec 8)) (tail : Assertion)
    (hlen : bs.length = 144) :
    (hcoreWitnessStructMems base bs).foldr
        (fun p acc => (p.1 ↦ₘ p.2) ** acc) tail =
      (bytesRegion base bs ** tail) := by
  simp [hcoreWitnessStructMems, bytesRegion, bytesRegionAux, hlen,
    BitVec.add_assoc, sepConj_assoc', sepConj_emp_right']

private theorem hcoreStatus0HeaderStructFold_eq_acc (tail : Assertion) :
    (hcoreWitnessStructMems hcoreWitnessParent hcoreStatus0HeaderStruct).foldr
        (fun p acc => (p.1 ↦ₘ p.2) ** acc) tail =
      (bytesRegion hcoreWitnessParent hcoreStatus0HeaderStruct ** tail) := by
  exact hcoreWitnessStructFold_eq_bytesRegion hcoreWitnessParent
    hcoreStatus0HeaderStruct tail hcoreStatus0HeaderStruct_length

def hcoreStatus0StackMems : List (Word × Word) :=
  [(hcoreWitnessSpC, 0), (hcoreWitnessSpC + 8, hcoreWitnessHeader),
   (hcoreWitnessSpC + 16, BitVec.ofNat 64 hcoreStatus0HeaderRlp.length),
   (hcoreWitnessSpC + 24, hcoreWitnessParent),
   (hcoreWitnessSpC + 32, hcoreWitnessParent2),
   (hcoreWitnessSpC + 40, hcoreWitnessParentRlp),
   (hcoreWitnessSpC + 48, BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)]

def hcoreStatus0StackFold : Assertion :=
  hcoreStatus0StackMems.foldr
    (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion

private theorem hcoreStatus0StackSat :
    hcoreStatus0StackFold.SatWithin 65536 65592 := by
  have h0 := satWithin_memIs (a := hcoreWitnessSpC) (v := (0 : Word)) (by decide)
  have h1 := satWithin_memIs (a := hcoreWitnessSpC + 8)
    (v := hcoreWitnessHeader) (by decide)
  have h2 := satWithin_memIs (a := hcoreWitnessSpC + 16)
    (v := BitVec.ofNat 64 hcoreStatus0HeaderRlp.length) (by
      change isValidDwordAccess (65552 : Word) = true
      decide)
  have h3 := satWithin_memIs (a := hcoreWitnessSpC + 24)
    (v := hcoreWitnessParent) (by decide)
  have h4 := satWithin_memIs (a := hcoreWitnessSpC + 32)
    (v := hcoreWitnessParent2) (by decide)
  have h5 := satWithin_memIs (a := hcoreWitnessSpC + 40)
    (v := hcoreWitnessParentRlp) (by decide)
  have h6 := satWithin_memIs (a := hcoreWitnessSpC + 48)
    (v := BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length) (by decide)
  have h01 := h0.sepConj h1 (by decide) (by decide)
  have h012 := h01.sepConj h2 (by decide) (by decide)
  have h0123 := h012.sepConj h3 (by decide) (by decide)
  have h01234 := h0123.sepConj h4 (by decide) (by decide)
  have h012345 := h01234.sepConj h5 (by decide) (by decide)
  have h0123456 := h012345.sepConj h6 (by decide) (by decide)
  simpa [hcoreStatus0StackFold, hcoreStatus0StackMems,
    hcoreWitnessSpC, hcoreStatus0HeaderRlp_length, hcoreHeaderRlp_length,
    hcoreParentRlp_length, sepConj_assoc', sepConj_emp_right'] using h0123456

private def hcoreWitnessRegHeap : (Reg × Word) → PartialState :=
  fun p => PartialState.singletonReg p.1 p.2

private def hcoreWitnessMemHeap : (Word × Word) → PartialState :=
  fun p => PartialState.singletonMem p.1 p.2

def hcoreWitnessRegAtom : (Reg × Word) → Assertion :=
  fun p => p.1 ↦ᵣ p.2

private def hcoreWitnessMemAtom : (Word × Word) → Assertion :=
  fun p => p.1 ↦ₘ p.2

def hcoreWitnessRegFold : Assertion :=
  hcoreWitnessRegs.foldr (fun p acc => hcoreWitnessRegAtom p ** acc) empAssertion

private def hcoreWitnessMemFold : Assertion :=
  hcoreWitnessMems.foldr (fun p acc => hcoreWitnessMemAtom p ** acc) empAssertion

private def hcoreWitnessRegHeapFold : PartialState :=
  hcoreWitnessRegs.foldr
    (fun p acc => (hcoreWitnessRegHeap p).union acc) PartialState.empty

private def hcoreWitnessMemHeapFold : PartialState :=
  hcoreWitnessMems.foldr
    (fun p acc => (hcoreWitnessMemHeap p).union acc) PartialState.empty

private def hcoreWitnessMemFoldNoG : Assertion :=
  hcoreWitnessMemsNoG.foldr
    (fun p acc => hcoreWitnessMemAtom p ** acc) empAssertion

private def hcoreWitnessMemHeapFoldNoG : PartialState :=
  hcoreWitnessMemsNoG.foldr
    (fun p acc => (hcoreWitnessMemHeap p).union acc) PartialState.empty

private theorem hcoreWitnessRegFold_sat :
    hcoreWitnessRegFold hcoreWitnessRegHeapFold := by
  apply sepConj_foldr_satisfiable hcoreWitnessRegAtom
    hcoreWitnessRegHeap hcoreWitnessRegs
  · intro p hp
    rfl
  · have hd : hcoreWitnessRegs.Pairwise (fun p q => p.1 ≠ q.1) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h =>
        EvmAsm.Codegen.ValidateHeaderCompose.routeInhabitantRegSingletonDisjoint h)
      hd

private theorem hcoreWitnessMemFold_sat :
    hcoreWitnessMemFold hcoreWitnessMemHeapFold := by
  apply sepConj_foldr_satisfiable hcoreWitnessMemAtom
    hcoreWitnessMemHeap hcoreWitnessMems
  · intro p hp
    rcases p with ⟨a, v⟩
    simp [hcoreWitnessMems, hcoreWitnessStructMems] at hp
    rcases hp with
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩
    all_goals
      simp only [hcoreWitnessMemAtom, hcoreWitnessMemHeap, memIs,
        PartialState.singletonMem]
      exact ⟨by trivial, by decide⟩
  · have hd : hcoreWitnessMems.Pairwise (fun p q => p.1 ≠ q.1) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h =>
        EvmAsm.Codegen.ValidateHeaderCompose.routeInhabitantMemSingletonDisjoint h)
      hd

private theorem hcoreWitnessMemFoldNoG_sat :
    hcoreWitnessMemFoldNoG hcoreWitnessMemHeapFoldNoG := by
  apply sepConj_foldr_satisfiable hcoreWitnessMemAtom
    hcoreWitnessMemHeap hcoreWitnessMemsNoG
  · intro p hp
    rcases p with ⟨a, v⟩
    simp [hcoreWitnessMemsNoG, hcoreWitnessStructMems] at hp
    rcases hp with
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩
    all_goals
      simp only [hcoreWitnessMemAtom, hcoreWitnessMemHeap, memIs,
        PartialState.singletonMem]
      exact ⟨by trivial, by decide⟩
  · have hd : hcoreWitnessMemsNoG.Pairwise (fun p q => p.1 ≠ q.1) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h =>
        EvmAsm.Codegen.ValidateHeaderCompose.routeInhabitantMemSingletonDisjoint h)
      hd

private theorem hcoreWitnessFold_cross :
    ∀ p ∈ hcoreWitnessRegs, ∀ q ∈ hcoreWitnessMems,
      (hcoreWitnessRegHeap p).Disjoint (hcoreWitnessMemHeap q) := by
  intro p hp q hq
  unfold hcoreWitnessRegHeap hcoreWitnessMemHeap
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem hcoreWitnessFoldNoG_cross :
    ∀ p ∈ hcoreWitnessRegs, ∀ q ∈ hcoreWitnessMemsNoG,
      (hcoreWitnessRegHeap p).Disjoint (hcoreWitnessMemHeap q) := by
  intro p hp q hq
  unfold hcoreWitnessRegHeap hcoreWitnessMemHeap
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

def hcoreWitnessAssertion : Assertion :=
  hcoreWitnessRegFold ** hcoreWitnessMemFold

def hcoreWitnessStackMems : List (Word × Word) :=
  [(hcoreWitnessSpC, 0), (hcoreWitnessSpC + 8, hcoreWitnessHeader),
   (hcoreWitnessSpC + 16, BitVec.ofNat 64 hcoreWitnessHeaderRlp.length),
   (hcoreWitnessSpC + 24, hcoreWitnessParent),
   (hcoreWitnessSpC + 32, hcoreWitnessParent2),
   (hcoreWitnessSpC + 40, hcoreWitnessParentRlp),
   (hcoreWitnessSpC + 48, BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)]

def hcoreWitnessStackFold : Assertion :=
  hcoreWitnessStackMems.foldr
    (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion

private theorem hcoreWitnessHeaderStructFold_eq :
    (hcoreWitnessStructMems hcoreWitnessParent hcoreWitnessHeaderStruct).foldr
        (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion =
      bytesRegion hcoreWitnessParent hcoreWitnessHeaderStruct := by
  have hp : hcoreWitnessHeaderSpec.parentHash.length = 32 := by
    simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hs : hcoreWitnessHeaderSpec.stateRoot.length = 32 := by
    simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hlen : hcoreWitnessHeaderStruct.length = 144 := by
    simp [hcoreWitnessHeaderStruct, headerCoreStructBytes, hp, hs,
    EvmAsm.Stateless.SpecRef.natToBytesBE_length,
    EvmAsm.Stateless.SpecRef.natToBytesLE_length]
  have h := hcoreWitnessStructFold_eq_bytesRegion
    hcoreWitnessParent hcoreWitnessHeaderStruct empAssertion hlen
  simpa [sepConj_emp_right'] using h

private theorem hcoreWitnessParentStructFold_eq :
    (hcoreWitnessStructMems hcoreWitnessParent2 hcoreWitnessParentStruct).foldr
        (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion =
      bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct := by
  have hp : hcoreWitnessParentSpec.parentHash.length = 32 := by
    simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hs : hcoreWitnessParentSpec.stateRoot.length = 32 := by
    simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hlen : hcoreWitnessParentStruct.length = 144 := by
    simp [hcoreWitnessParentStruct, headerCoreStructBytes, hp, hs,
    EvmAsm.Stateless.SpecRef.natToBytesBE_length,
    EvmAsm.Stateless.SpecRef.natToBytesLE_length]
  have h := hcoreWitnessStructFold_eq_bytesRegion
    hcoreWitnessParent2 hcoreWitnessParentStruct empAssertion hlen
  simpa [sepConj_emp_right'] using h

private theorem hcoreWitnessHeaderStructFold_eq_acc (tail : Assertion) :
    (hcoreWitnessStructMems hcoreWitnessParent hcoreWitnessHeaderStruct).foldr
        (fun p acc => (p.1 ↦ₘ p.2) ** acc) tail =
      (bytesRegion hcoreWitnessParent hcoreWitnessHeaderStruct ** tail) := by
  have hp : hcoreWitnessHeaderSpec.parentHash.length = 32 := by
    simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hs : hcoreWitnessHeaderSpec.stateRoot.length = 32 := by
    simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hlen : hcoreWitnessHeaderStruct.length = 144 := by
    simp [hcoreWitnessHeaderStruct, headerCoreStructBytes,
    hp, hs,
    EvmAsm.Stateless.SpecRef.natToBytesBE_length,
    EvmAsm.Stateless.SpecRef.natToBytesLE_length]
  exact hcoreWitnessStructFold_eq_bytesRegion
    hcoreWitnessParent hcoreWitnessHeaderStruct tail hlen

private theorem hcoreWitnessParentStructFold_eq_acc (tail : Assertion) :
    (hcoreWitnessStructMems hcoreWitnessParent2 hcoreWitnessParentStruct).foldr
        (fun p acc => (p.1 ↦ₘ p.2) ** acc) tail =
      (bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct ** tail) := by
  have hp : hcoreWitnessParentSpec.parentHash.length = 32 := by
    simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hs : hcoreWitnessParentSpec.stateRoot.length = 32 := by
    simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hlen : hcoreWitnessParentStruct.length = 144 := by
    simp [hcoreWitnessParentStruct, headerCoreStructBytes,
    hp, hs,
    EvmAsm.Stateless.SpecRef.natToBytesBE_length,
    EvmAsm.Stateless.SpecRef.natToBytesLE_length]
  exact hcoreWitnessStructFold_eq_bytesRegion
    hcoreWitnessParent2 hcoreWitnessParentStruct tail hlen

theorem hcoreWitnessGRegion :
    bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes =
      (hcoreWitnessGAddr ↦ₘ packBytes hcoreWitnessGBytes) := by
  simp [bytesRegion, bytesRegionAux, hcoreWitnessGBytes, sepConj_emp_right']

private theorem hcoreWitnessMemFold_eq :
    hcoreWitnessMemFold =
      (hcoreWitnessStackFold **
            (bytesRegion hcoreWitnessParent hcoreWitnessHeaderStruct **
              (bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct **
            (hcoreWitnessGAddr ↦ₘ packBytes hcoreWitnessGBytes)))) := by
  unfold hcoreWitnessMemFold hcoreWitnessMems hcoreWitnessMemAtom
  simp only [List.foldr_append]
  rw [hcoreWitnessHeaderStructFold_eq_acc,
    hcoreWitnessParentStructFold_eq_acc]
  simp [hcoreWitnessStackFold, hcoreWitnessStackMems,
    sepConj_assoc', sepConj_emp_right']

theorem hcoreStatus0MemFold_eq :
    hcoreStatus0MemFold =
      (hcoreStatus0StackFold **
        (bytesRegion hcoreWitnessParent hcoreStatus0HeaderStruct **
          (bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct **
            (hcoreWitnessGAddr ↦ₘ packBytes hcoreWitnessGBytes)))) := by
  unfold hcoreStatus0MemFold hcoreStatus0Mems hcoreStatus0MemAtom
  simp only [List.foldr_append]
  rw [hcoreStatus0HeaderStructFold_eq_acc]
  have hp : hcoreWitnessParentSpec.parentHash.length = 32 := by
    simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hs : hcoreWitnessParentSpec.stateRoot.length = 32 := by
    simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hlen : hcoreWitnessParentStruct.length = 144 := by
    simp [hcoreWitnessParentStruct, headerCoreStructBytes, hp, hs,
      EvmAsm.Stateless.SpecRef.natToBytesBE_length,
      EvmAsm.Stateless.SpecRef.natToBytesLE_length]
  rw [hcoreWitnessStructFold_eq_bytesRegion hcoreWitnessParent2
    hcoreWitnessParentStruct _ hlen]
  simp [hcoreStatus0StackFold, hcoreStatus0StackMems,
    sepConj_assoc', sepConj_emp_right']

def hcoreStatus0Assertion : Assertion :=
  hcoreWitnessRegFold ** hcoreStatus0MemFold

def hcoreStatus0Heap : PartialState :=
  hcoreWitnessRegHeapFold.union hcoreStatus0MemHeapFold

private theorem hcoreStatus0Fold_cross :
    ∀ p ∈ hcoreWitnessRegs, ∀ q ∈ hcoreStatus0Mems,
      (hcoreWitnessRegHeap p).Disjoint (hcoreStatus0MemHeap q) := by
  intro p hp q hq
  unfold hcoreWitnessRegHeap hcoreStatus0MemHeap
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

theorem hcoreStatus0Sat :
    hcoreStatus0Assertion hcoreStatus0Heap := by
  exact sepConj_foldr_cross_satisfiable hcoreWitnessRegAtom
    hcoreWitnessRegHeap hcoreWitnessRegs hcoreStatus0MemAtom
    hcoreStatus0MemHeap hcoreStatus0Mems hcoreWitnessRegFold_sat
    hcoreStatus0MemFold_sat hcoreStatus0Fold_cross

private theorem hcoreStatus0Assertion_eq :
    hcoreStatus0Assertion =
      (hcoreWitnessRegFold **
        (hcoreStatus0StackFold **
          (bytesRegion hcoreWitnessParent hcoreStatus0HeaderStruct **
            (bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct **
              (hcoreWitnessGAddr ↦ₘ packBytes hcoreWitnessGBytes))))) := by
  simp only [hcoreStatus0Assertion, hcoreStatus0MemFold_eq]

theorem hcoreStatus0Assertion_eq_bytes :
    hcoreStatus0Assertion =
      (hcoreWitnessRegFold **
        (hcoreStatus0StackFold **
          (bytesRegion hcoreWitnessParent hcoreStatus0HeaderStruct **
            (bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct **
              bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes)))) := by
  rw [hcoreStatus0Assertion_eq]
  have hg : bytesRegion (262144 : Word) hcoreWitnessGBytes =
      ((262144 : Word) ↦ₘ packBytes hcoreWitnessGBytes) := by
    simpa [hcoreWitnessGAddr] using hcoreWitnessGRegion
  rw [← hg]

theorem hcoreStatus0MemFold_mem_of_ne_none :
    ∀ (xs : List (Word × Word)) (a : Word),
      (xs.foldr (fun p acc => (hcoreStatus0MemHeap p).union acc)
        PartialState.empty).mem a ≠ none →
      ∃ p, p ∈ xs ∧ p.1 = a := by
  intro xs
  induction xs with
  | nil =>
      intro a ha
      simp [PartialState.empty] at ha
  | cons p xs ih =>
      intro a ha
      by_cases hpa : a = p.1
      · exact ⟨p, by simp, hpa.symm⟩
      · have htail :
            (xs.foldr (fun q acc => (hcoreStatus0MemHeap q).union acc)
              PartialState.empty).mem a ≠ none := by
          intro hnone
          apply ha
          rw [List.foldr]
          have hcell : (hcoreStatus0MemHeap p).mem a = none := by
            simp [hcoreStatus0MemHeap, PartialState.singletonMem, hpa]
          simp only [PartialState.union, hcell]
          exact hnone
        obtain ⟨q, hq, hqa⟩ := ih a htail
        exact ⟨q, by simp [hq], hqa⟩

theorem hcoreStatus0Heap_mem_outside
    (a : Word) (ha : hcoreStatus0Heap.mem a ≠ none) :
    a.toNat < 131072 ∨
      (131720 ≤ a.toNat ∧ a.toNat < 204800) ∨
      205448 ≤ a.toNat := by
  have hmem : hcoreStatus0MemHeapFold.mem a ≠ none := by
    intro hm
    apply ha
    have hreg : hcoreWitnessRegHeapFold.mem a = none := by
      simp [hcoreWitnessRegHeapFold, hcoreWitnessRegHeap, hcoreWitnessRegs,
        PartialState.union, PartialState.singletonReg, PartialState.empty]
    simp [hcoreStatus0Heap, PartialState.union, hreg, hm]
  obtain ⟨p, hp, hpa⟩ :=
    hcoreStatus0MemFold_mem_of_ne_none hcoreStatus0Mems a hmem
  rcases p with ⟨paddr, pval⟩
  subst a
  have hp' : (paddr, pval) ∈ hcoreStatus0Mems := hp
  simp [hcoreStatus0Mems, hcoreWitnessStructMems,
    hcoreStatus0HeaderRlp_length] at hp'
  repeat' first | rcases hp' with hp' | hp'
  all_goals norm_num

theorem hcoreStatus0HeaderStruct_relation :
    headerCoreStructRelation hcoreStatus0HeaderStruct hcoreStatus0HeaderSpec := by
  exact ⟨hcoreStatus0HeaderStruct_length, rfl⟩

theorem hcoreWitnessParentStruct_relation :
    headerCoreStructRelation hcoreWitnessParentStruct hcoreWitnessParentSpec := by
  have hp : hcoreWitnessParentSpec.parentHash.length = 32 := by
    simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hs : hcoreWitnessParentSpec.stateRoot.length = 32 := by
    simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  refine ⟨?_, rfl⟩
  simp [hcoreWitnessParentStruct, headerCoreStructBytes, hp, hs,
    EvmAsm.Stateless.SpecRef.natToBytesBE_length,
    EvmAsm.Stateless.SpecRef.natToBytesLE_length]

theorem hcoreWitnessAssertion_eq :
    hcoreWitnessAssertion =
      (hcoreWitnessRegFold **
        (hcoreWitnessStackFold **
          (bytesRegion hcoreWitnessParent hcoreWitnessHeaderStruct **
            (bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct **
              bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes)))) := by
  simp only [hcoreWitnessAssertion, hcoreWitnessMemFold_eq]
  have hg : bytesRegion (262144 : Word) hcoreWitnessGBytes =
      ((262144 : Word) ↦ₘ packBytes hcoreWitnessGBytes) := by
    simpa [hcoreWitnessGAddr] using hcoreWitnessGRegion
  rw [hg]

def hcoreWitnessHeap : PartialState :=
  hcoreWitnessRegHeapFold.union hcoreWitnessMemHeapFold

theorem hcoreWitnessSat :
    hcoreWitnessAssertion hcoreWitnessHeap := by
  exact sepConj_foldr_cross_satisfiable hcoreWitnessRegAtom
    hcoreWitnessRegHeap hcoreWitnessRegs hcoreWitnessMemAtom
    hcoreWitnessMemHeap hcoreWitnessMems hcoreWitnessRegFold_sat
    hcoreWitnessMemFold_sat hcoreWitnessFold_cross

private def hcoreWitnessAssertionNoG : Assertion :=
  hcoreWitnessRegFold ** hcoreWitnessMemFoldNoG

private def hcoreWitnessHeapNoG : PartialState :=
  hcoreWitnessRegHeapFold.union hcoreWitnessMemHeapFoldNoG

private theorem hcoreWitnessSatNoG :
    hcoreWitnessAssertionNoG hcoreWitnessHeapNoG := by
  exact sepConj_foldr_cross_satisfiable hcoreWitnessRegAtom
    hcoreWitnessRegHeap hcoreWitnessRegs hcoreWitnessMemAtom
    hcoreWitnessMemHeap hcoreWitnessMemsNoG hcoreWitnessRegFold_sat
    hcoreWitnessMemFoldNoG_sat hcoreWitnessFoldNoG_cross

private theorem hcoreWitnessMemFold_mem_of_ne_none :
    ∀ (xs : List (Word × Word)) (a : Word),
      (xs.foldr (fun p acc => (hcoreWitnessMemHeap p).union acc)
        PartialState.empty).mem a ≠ none →
      ∃ p, p ∈ xs ∧ p.1 = a := by
  intro xs
  induction xs with
  | nil =>
      intro a ha
      simp [PartialState.empty] at ha
  | cons p xs ih =>
      intro a ha
      by_cases hpa : a = p.1
      · exact ⟨p, by simp, hpa.symm⟩
      · have htail :
            (xs.foldr (fun q acc => (hcoreWitnessMemHeap q).union acc)
              PartialState.empty).mem a ≠ none := by
          intro hnone
          apply ha
          rw [List.foldr]
          have hcell : (hcoreWitnessMemHeap p).mem a = none := by
            simp [hcoreWitnessMemHeap, PartialState.singletonMem, hpa]
          simp only [PartialState.union, hcell]
          exact hnone
        obtain ⟨q, hq, hqa⟩ := ih a htail
        exact ⟨q, by simp [hq], hqa⟩

theorem hcoreWitnessHeap_mem_outside
    (a : Word) (ha : hcoreWitnessHeap.mem a ≠ none) :
    a.toNat < 131072 ∨
      (131720 ≤ a.toNat ∧ a.toNat < 204800) ∨
      205448 ≤ a.toNat := by
  have hmem : hcoreWitnessMemHeapFold.mem a ≠ none := by
    intro hm
    apply ha
    have hreg : hcoreWitnessRegHeapFold.mem a = none := by
      simp [hcoreWitnessRegHeapFold, hcoreWitnessRegHeap, hcoreWitnessRegs,
        PartialState.union, PartialState.singletonReg, PartialState.empty]
    simp [hcoreWitnessHeap, PartialState.union, hreg, hm]
  obtain ⟨p, hp, hpa⟩ :=
    hcoreWitnessMemFold_mem_of_ne_none hcoreWitnessMems a hmem
  rcases p with ⟨paddr, pval⟩
  subst a
  have hp' : (paddr, pval) ∈ hcoreWitnessMems := hp
  simp [hcoreWitnessMems, hcoreWitnessStructMems] at hp'
  rcases hp' with
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩
  all_goals norm_num

theorem hcoreWitnessRlpSat :
    (bytesRegion hcoreWitnessHeader hcoreWitnessHeaderRlp).SatWithin
        131072 131720 ∧
      (bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes).SatWithin
        204800 205448 := by
  have hlen : hcoreWitnessHeaderRlp.length = 645 := hcoreHeaderRlp_length
  have hlenP : hcoreWitnessParentRlpBytes.length = 645 := hcoreParentRlp_length
  have hvalidHeader (k : Nat) (hk : k < 81) :
      isValidDwordAccess (hcoreWitnessHeader + BitVec.ofNat 64 (8 * k)) = true := by
    have hbase : hcoreWitnessHeader.toNat = 131072 := by rfl
    have hto :
        (hcoreWitnessHeader + BitVec.ofNat 64 (8 * k)).toNat =
          hcoreWitnessHeader.toNat + 8 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hk64 : 8 * k < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hk64]
      have hsum : hcoreWitnessHeader.toNat + 8 * k < 2 ^ 64 := by
        rw [hbase]
        omega
      rw [Nat.mod_eq_of_lt hsum]
    apply isValidDwordAccess_of_toNat
    · rw [hto]
      rw [hbase]
      omega
    · left
      constructor <;> rw [hto, hbase] <;> omega
  have hvalidParent (k : Nat) (hk : k < 81) :
      isValidDwordAccess (hcoreWitnessParentRlp + BitVec.ofNat 64 (8 * k)) = true := by
    have hbase : hcoreWitnessParentRlp.toNat = 204800 := by rfl
    have hto :
        (hcoreWitnessParentRlp + BitVec.ofNat 64 (8 * k)).toNat =
          hcoreWitnessParentRlp.toNat + 8 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hk64 : 8 * k < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hk64]
      have hsum : hcoreWitnessParentRlp.toNat + 8 * k < 2 ^ 64 := by
        rw [hbase]
        omega
      rw [Nat.mod_eq_of_lt hsum]
    apply isValidDwordAccess_of_toNat
    · rw [hto]
      rw [hbase]
      omega
    · left
      constructor <;> rw [hto, hbase] <;> omega
  have h1 := satWithin_bytesRegion hcoreWitnessHeader hcoreWitnessHeaderRlp
    (fun k hk => by
      rw [hlen] at hk
      have hk81 : k < 81 := by omega
      exact hvalidHeader k hk81)
  have h2 := satWithin_bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes
    (fun k hk => by
      rw [hlenP] at hk
      have hk81 : k < 81 := by omega
      exact hvalidParent k hk81)
  have h1' :
      (bytesRegion hcoreWitnessHeader hcoreWitnessHeaderRlp).SatWithin 131072 131720 := by
    simpa [hcoreWitnessHeader, hlen] using h1
  have h2' :
      (bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes).SatWithin 204800 205448 := by
    simpa [hcoreWitnessParentRlp, hlenP] using h2
  exact ⟨h1', h2'⟩
