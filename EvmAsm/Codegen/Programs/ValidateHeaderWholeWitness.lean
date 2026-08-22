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
    bloom := List.replicate 256 0,
    difficulty := 0, number := 2, gasLimit := 120000000, gasUsed := 97920,
    timestamp := 24, extraData := [],
    prevRandao := List.replicate 32 0, nonce := List.replicate 8 0,
    baseFeePerGas := 7,
    withdrawalsRoot := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421,
    blobGasUsed := 131072, excessBlobGas := 262144,
    parentBeaconBlockRoot := List.replicate 32 0,
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
    bloom := List.replicate 256 0,
    difficulty := 0, number := 1, gasLimit := 120000000, gasUsed := 183600,
    timestamp := 12, extraData := [],
    prevRandao := List.replicate 32 0, nonce := List.replicate 8 0,
    baseFeePerGas := 7,
    withdrawalsRoot := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421,
    blobGasUsed := 786432, excessBlobGas := 1310720,
    parentBeaconBlockRoot := List.replicate 32 0,
    requestsHash := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855,
    blockAccessListHash := EvmAsm.Stateless.SpecRef.natToBytesBE 32
      0x8c092354d3b4411df0c64a0fadb1a4924396b54b240d96ea7d946a28db9d0467,
    slotNumber := 0 }

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

private theorem hcoreEncodeNatBE32 (n : Nat) :
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

private theorem hcoreEncodeScalar0 :
    (EvmAsm.EL.RLP.encode (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 0))).length = 1 := by
  norm_num [EvmAsm.EL.RLP.encode, EvmAsm.EL.RLP.encodeBytes,
    EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreEncodeScalar1 :
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

private theorem hcoreEncodeBytesRep32 (b : BitVec 8) :
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

private theorem hcoreEncodeBytesRep8 (b : BitVec 8) :
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

private theorem hcoreEncode_len_of_bytes_length
    (bs : List (BitVec 8)) (n : Nat) (hlen : bs.length = n) (hne : n ≠ 1)
    (hshort : n ≤ 55) :
    (EvmAsm.EL.RLP.encode (.bytes bs)).length = n + 1 := by
  change (EvmAsm.EL.RLP.encodeBytes bs).length = n + 1
  rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one bs hshort]
  simp [hlen]

private theorem hcoreEncode_len_of_bytes_long
    (bs : List (BitVec 8)) (n : Nat) (hlen : bs.length = n) (hlong : 55 < n) :
    (EvmAsm.EL.RLP.encode (.bytes bs)).length =
      1 + (EvmAsm.EL.RLP.Nat.toBytesBE n).length + n := by
  change (EvmAsm.EL.RLP.encodeBytes bs).length =
    1 + (EvmAsm.EL.RLP.Nat.toBytesBE n).length + n
  rw [EvmAsm.EL.RLP.encodeBytes_long_of_length bs hlong]
  simp [hlen]

private theorem hcoreEncodeItems_length_nil :
    (EvmAsm.EL.RLP.encode.encodeItems ([] : List EvmAsm.EL.RLP.RLPItem)).length = 0 := by
  rfl

private theorem hcoreEncodeItems_length_cons
    (item : EvmAsm.EL.RLP.RLPItem) (rest : List EvmAsm.EL.RLP.RLPItem) :
    (EvmAsm.EL.RLP.encode.encodeItems (item :: rest)).length =
      (EvmAsm.EL.RLP.encode item).length +
        (EvmAsm.EL.RLP.encode.encodeItems rest).length := by
  simp [EvmAsm.EL.RLP.encode.encodeItems, List.length_append]

private theorem hcoreHeaderItems_length :
    (match EvmAsm.Stateless.SpecRef.headerToRlpItem hcoreWitnessHeaderSpec with
     | .list items => (EvmAsm.EL.RLP.encode.encodeItems items).length
     | .bytes _ => 0) = 642 := by
  simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.headerToRlpItem,
    scalarItem, if_true, List.append]
  rw [hcoreEncodeItems_length_cons]
  simp only [hcoreEncodeItems_length_cons, hcoreEncodeItems_length_nil,
    hcoreEncodeNatBE32, hcoreEncodeNatBE20, hcoreEncodeNatLE8,
    hcoreEncodeBloom, hcoreEncodeScalar0, hcoreEncodeScalar1,
    hcoreEncodeScalar2, hcoreEncodeScalar7, hcoreEncodeScalar24,
    hcoreEncodeScalar120000000, hcoreEncodeScalar97920,
    hcoreEncodeScalar131072, hcoreEncodeScalar262144,
    hcoreEncodeBytesRep32, hcoreEncodeBytesRep20, hcoreEncodeBytesRep8,
    hcoreEncodeBytesRep256, hcoreEncodeBytesEmpty,
    hcoreEncode_len_of_bytes_length, hcoreEncode_len_of_bytes_long]
  norm_num

private theorem hcoreParentItems_length :
    (match EvmAsm.Stateless.SpecRef.headerToRlpItem hcoreWitnessParentSpec with
     | .list items => (EvmAsm.EL.RLP.encode.encodeItems items).length
     | .bytes _ => 0) = 642 := by
  simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.headerToRlpItem,
    scalarItem, if_true, List.append]
  rw [hcoreEncodeItems_length_cons]
  simp only [hcoreEncodeItems_length_cons, hcoreEncodeItems_length_nil,
    hcoreEncodeNatBE32, hcoreEncodeNatBE20, hcoreEncodeNatLE8,
    hcoreEncodeBloom, hcoreEncodeScalar0, hcoreEncodeScalar1,
    hcoreEncodeScalar2, hcoreEncodeScalar7, hcoreEncodeScalar12,
    hcoreEncodeScalar24, hcoreEncodeScalar120000000,
    hcoreEncodeScalar183600, hcoreEncodeScalar786432,
    hcoreEncodeScalar1310720, hcoreEncodeScalar262144,
    hcoreEncodeBytesRep32, hcoreEncodeBytesRep20, hcoreEncodeBytesRep8,
    hcoreEncodeBytesRep256, hcoreEncodeBytesEmpty,
    hcoreEncode_len_of_bytes_length, hcoreEncode_len_of_bytes_long]
  try rw [hcoreEncodeBloom]
  try rw [hcoreEncodeBytesRep32]
  try rw [hcoreEncodeBytesRep8]
  norm_num

private theorem hcoreHeaderRlp_length : hcoreWitnessHeaderRlp.length = 645 := by
  unfold hcoreWitnessHeaderRlp
  simp only [EvmAsm.EL.RLP.encode]
  rw [hcoreHeaderItems_length]
  simp [EvmAsm.EL.RLP.Nat.toBytesBE]

private theorem hcoreParentRlp_length : hcoreWitnessParentRlpBytes.length = 645 := by
  unfold hcoreWitnessParentRlpBytes
  simp only [EvmAsm.EL.RLP.encode]
  rw [hcoreParentItems_length]
  simp [EvmAsm.EL.RLP.Nat.toBytesBE]

/-! The decoder's arm and check are private to `Stateless`.  Keep this small
bridge here (rather than duplicating their definitions in the witness): the
two public wrapper booleans above are exactly the facts needed to discharge
the arm's checks. -/
private theorem hcore_decodeHeaderArm_ok
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

def hcoreWitnessRlpMems (base : Word) (bs : List (BitVec 8)) : List (Word × Word) :=
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

def hcoreWitnessMemsNoG : List (Word × Word) :=
  [(hcoreWitnessSpC, 0), (hcoreWitnessSpC + 8, hcoreWitnessHeader),
   (hcoreWitnessSpC + 16, BitVec.ofNat 64 hcoreWitnessHeaderRlp.length),
   (hcoreWitnessSpC + 24, hcoreWitnessParent),
   (hcoreWitnessSpC + 32, hcoreWitnessParent2),
   (hcoreWitnessSpC + 40, hcoreWitnessParentRlp),
   (hcoreWitnessSpC + 48, BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)] ++
  hcoreWitnessStructMems hcoreWitnessParent hcoreWitnessHeaderStruct ++
  hcoreWitnessStructMems hcoreWitnessParent2 hcoreWitnessParentStruct

private theorem hcoreWitnessStructFold_eq_bytesRegion
    (base : Word) (bs : List (BitVec 8)) (tail : Assertion)
    (hlen : bs.length = 144) :
    (hcoreWitnessStructMems base bs).foldr
        (fun p acc => (p.1 ↦ₘ p.2) ** acc) tail =
      (bytesRegion base bs ** tail) := by
  simp [hcoreWitnessStructMems, bytesRegion, bytesRegionAux, hlen,
    List.length_drop, BitVec.add_assoc, sepConj_assoc', sepConj_emp_right']

private def hcoreWitnessRegHeap : (Reg × Word) → PartialState :=
  fun p => PartialState.singletonReg p.1 p.2

private def hcoreWitnessMemHeap : (Word × Word) → PartialState :=
  fun p => PartialState.singletonMem p.1 p.2

private def hcoreWitnessRegAtom : (Reg × Word) → Assertion :=
  fun p => p.1 ↦ᵣ p.2

private def hcoreWitnessMemAtom : (Word × Word) → Assertion :=
  fun p => p.1 ↦ₘ p.2

private def hcoreWitnessRegFold : Assertion :=
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

private def hcoreWitnessAssertion : Assertion :=
  hcoreWitnessRegFold ** hcoreWitnessMemFold

private def hcoreWitnessStackMems : List (Word × Word) :=
  [(hcoreWitnessSpC, 0), (hcoreWitnessSpC + 8, hcoreWitnessHeader),
   (hcoreWitnessSpC + 16, BitVec.ofNat 64 hcoreWitnessHeaderRlp.length),
   (hcoreWitnessSpC + 24, hcoreWitnessParent),
   (hcoreWitnessSpC + 32, hcoreWitnessParent2),
   (hcoreWitnessSpC + 40, hcoreWitnessParentRlp),
   (hcoreWitnessSpC + 48, BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)]

private def hcoreWitnessStackFold : Assertion :=
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

private theorem hcoreWitnessGRegion :
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
  simp [hcoreWitnessMemAtom, hcoreWitnessStackFold, hcoreWitnessStackMems,
    sepConj_assoc', sepConj_emp_right']

private theorem hcoreWitnessAssertion_eq :
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

private def hcoreWitnessHeap : PartialState :=
  hcoreWitnessRegHeapFold.union hcoreWitnessMemHeapFold

private theorem hcoreWitnessSat :
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

private theorem hcoreWitnessHeap_mem_outside
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

private theorem hcoreWitnessRlpSat :
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

private theorem hcoreWitnessHeaderStruct_slice16 :
    (List.take 8 (List.drop 16 hcoreWitnessHeaderStruct)) =
      List.take 8 (List.drop 16 (headerCoreStructBytes hcoreWitnessHeaderSpec)) := by
  rfl

private theorem hcoreWitnessHeaderStruct_slice80 :
    (List.take 8 (List.drop 80 hcoreWitnessHeaderStruct)) =
      List.take 8 (List.drop 80 (headerCoreStructBytes hcoreWitnessHeaderSpec)) := by
  rfl

private theorem hcoreWitnessHeaderStruct_slice136 :
    (List.take 8 (List.drop 136 hcoreWitnessHeaderStruct)) =
      List.take 8 (List.drop 136 (headerCoreStructBytes hcoreWitnessHeaderSpec)) := by
  rfl

private theorem hcoreWitnessParentStruct_slice16 :
    (List.take 8 (List.drop 16 hcoreWitnessParentStruct)) =
      List.take 8 (List.drop 16 (headerCoreStructBytes hcoreWitnessParentSpec)) := by
  rfl

private theorem hcoreWitnessParentStruct_slice80 :
    (List.take 8 (List.drop 80 hcoreWitnessParentStruct)) =
      List.take 8 (List.drop 80 (headerCoreStructBytes hcoreWitnessParentSpec)) := by
  rfl

private theorem hcoreWitnessParentStruct_slice136 :
    (List.take 8 (List.drop 136 hcoreWitnessParentStruct)) =
      List.take 8 (List.drop 136 (headerCoreStructBytes hcoreWitnessParentSpec)) := by
  rfl

/- The concrete witness stores all 18 dwords of each 144-byte record.  Keep
the chunk equation parametric so simplification can normalize whichever
offset a framed `bytesRegion` exposes (not just the five offsets read by the
core body). -/
private theorem hcoreWitnessHeaderStruct_chunk (i : Nat) :
    List.take 8 (List.drop (8 * i) hcoreWitnessHeaderStruct) =
      List.take 8 (List.drop (8 * i)
        (headerCoreStructBytes hcoreWitnessHeaderSpec)) := by
  rfl

private theorem hcoreWitnessParentStruct_chunk (i : Nat) :
    List.take 8 (List.drop (8 * i) hcoreWitnessParentStruct) =
      List.take 8 (List.drop (8 * i)
        (headerCoreStructBytes hcoreWitnessParentSpec)) := by
  rfl

private theorem hcore_drop40_take8_append_of_len32
    {α : Type} (a b rest : List α)
    (ha : a.length = 32) (hb : b.length = 32) :
    List.take 8 (List.drop 40 (a ++ b ++ rest)) =
      List.take 8 (List.drop 8 (b ++ rest)) := by
  simp [List.drop_append, List.drop_eq_nil_of_le, ha, hb]

private theorem hcoreWitnessHeaderStruct_chunk40_rev :
    List.take 8 (List.drop 8
        (hcoreWitnessHeaderSpec.stateRoot ++
          EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.number ++
          EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.timestamp ++
          EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.gasLimit ++
          EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.gasUsed ++
          EvmAsm.Stateless.SpecRef.natToBytesBE 32 hcoreWitnessHeaderSpec.baseFeePerGas ++
          EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.blobGasUsed ++
          EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.excessBlobGas)) =
      List.take 8 (List.drop 40
        (headerCoreStructBytes hcoreWitnessHeaderSpec)) := by
  have hp : hcoreWitnessHeaderSpec.parentHash.length = 32 := by
    simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hs : hcoreWitnessHeaderSpec.stateRoot.length = 32 := by
    simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  symm
  simpa [headerCoreStructBytes] using
    (hcore_drop40_take8_append_of_len32
      hcoreWitnessHeaderSpec.parentHash hcoreWitnessHeaderSpec.stateRoot
      (EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.number ++
        EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.timestamp ++
        EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.gasLimit ++
        EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.gasUsed ++
        EvmAsm.Stateless.SpecRef.natToBytesBE 32 hcoreWitnessHeaderSpec.baseFeePerGas ++
        EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.blobGasUsed ++
        EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.excessBlobGas)
      hp hs)

/-- The full core precondition is inhabited with a real, non-empty frame.

The frame is eight concrete bytes at `0x40000`, separated from all fourteen
register atoms and seven stack cells.  This is the primary non-vacuity witness;
it demonstrates that the abstract frame can carry content rather than merely
being instantiated with `empAssertion`. -/
theorem validateHeaderCorePre_nonempty_G :
    ∃ h : PartialState,
      validateHeaderCorePre hcoreWitnessParentSpec hcoreWitnessHeaderSpec
        hcoreWitnessSpC 0 hcoreWitnessHeader hcoreWitnessHeaderRlp.length
        hcoreWitnessHeaderRlp hcoreWitnessParentRlpBytes
        hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
        hcoreWitnessParentRlpBytes.length
        hcoreWitnessHeaderStruct hcoreWitnessParentStruct
        hcoreWitnessHeader hcoreWitnessHeaderRlp.length hcoreWitnessParent hcoreWitnessParent2
        hcoreWitnessParentRlp hcoreWitnessParentRlpBytes.length
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) h := by
  -- v4.33: a single `simpa` leaves the hypothesis' `List.take 8 (List.drop k ...)`
  -- windows unreduced while the goal's are fully reduced, so the closing `exact`
  -- (at reducible transparency) fails.  Simp the hypothesis on its own until it
  -- reaches the same normal form, then close at default transparency.
  obtain ⟨h1sat, h2sat⟩ := hcoreWitnessRlpSat
  obtain ⟨h1, h1sat, h1within⟩ := h1sat
  obtain ⟨h2, h2sat, h2within⟩ := h2sat
  have h12disj : h1.Disjoint h2 := by
    refine ⟨fun _ => Or.inl (h1within.regs _), ?_,
      fun _ => Or.inl (h1within.code _), Or.inl h1within.pc,
      Or.inl h1within.publicValues, Or.inl h1within.privateInput,
      Or.inl h1within.inputBufBase⟩
    intro a
    by_cases h1none : h1.mem a = none
    · exact Or.inl h1none
    by_cases h2none : h2.mem a = none
    · exact Or.inr h2none
    have hin1 := h1within.mem a h1none
    have hin2 := h2within.mem a h2none
    omega
  have hrawsat :
      (bytesRegion hcoreWitnessHeader hcoreWitnessHeaderRlp **
        bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes)
        (h1.union h2) :=
    ⟨h1, h2, h12disj, rfl, h1sat, h2sat⟩
  have hdisj : hcoreWitnessHeap.Disjoint (h1.union h2) := by
    refine ⟨fun _ => Or.inr (by simp [PartialState.union,
          h1within.regs, h2within.regs]), ?_,
      fun _ => Or.inr (by simp [PartialState.union,
          h1within.code, h2within.code]),
      Or.inr (by simp [PartialState.union, h1within.pc, h2within.pc]),
      Or.inr (by simp [PartialState.union,
          h1within.publicValues, h2within.publicValues]),
      Or.inr (by simp [PartialState.union,
          h1within.privateInput, h2within.privateInput]),
      Or.inr (by simp [PartialState.union,
          h1within.inputBufBase, h2within.inputBufBase])⟩
    intro a
    by_cases hold : hcoreWitnessHeap.mem a = none
    · exact Or.inl hold
    by_cases h1none : h1.mem a = none
    · by_cases h2none : h2.mem a = none
      · exact Or.inr (by simp [PartialState.union, h1none, h2none])
      · have hout := hcoreWitnessHeap_mem_outside a hold
        have hin2 := h2within.mem a h2none
        omega
    · have hout := hcoreWitnessHeap_mem_outside a hold
      have hin1 := h1within.mem a h1none
      omega
  have hbase := show
      (hcoreWitnessAssertion **
        (bytesRegion hcoreWitnessHeader hcoreWitnessHeaderRlp **
          bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes))
        (hcoreWitnessHeap.union (h1.union h2)) from
    ⟨hcoreWitnessHeap, h1.union h2, hdisj, rfl, hcoreWitnessSat, hrawsat⟩
  have hmap1 :
      List.map (fun i => BitVec.ofNat 8 (1 >>> (8 * i))) (List.range 8) =
        [1, 0, 0, 0, 0, 0, 0, 0] := by
    norm_num [List.map, List.range, List.range.loop]
    decide
  have hmap30000000 :
      List.map (fun i => BitVec.ofNat 8 (30000000 >>> (8 * i))) (List.range 8) =
        [128, 195, 201, 1, 0, 0, 0, 0] := by
    norm_num [List.map, List.range, List.range.loop]
    decide
  have hrel1 :
      headerRlpRelation hcoreWitnessHeaderRlp hcoreWitnessHeaderSpec := by
    let h := hcoreWitnessHeaderSpec
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
      simp [bs, h, hcoreWitnessHeaderSpec,
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
        hcoreWitnessHeaderSpec,
        EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE,
        EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD] <;> norm_num <;> decide
    have hbytes : EvmAsm.Stateless.SpecRef.validateHeaderWitness_bytesFieldsOk true bs = true := by
      change bytesFieldsOk true bs = true
      simp [bytesFieldsOk,
        EvmAsm.Stateless.SpecRef.fixedBytesFieldWidths,
        EvmAsm.Stateless.SpecRef.currentForkBytesFieldWidths, getBChecked,
        EvmAsm.Stateless.SpecRef.decodeItemFixedBytes, bs, h, hcoreWitnessHeaderSpec,
        EvmAsm.Stateless.SpecRef.natToBytesBE_length,
        List.all, List.getD] <;> norm_num <;> decide
    have hmk : EvmAsm.Stateless.SpecRef.mkHeaderFields true bs = h := by
      simpa [EvmAsm.Stateless.SpecRef.mkHeaderFields, bs, h, hcoreWitnessHeaderSpec,
        EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]
    unfold headerRlpRelation hcoreWitnessHeaderRlp
    rw [hitem]
    have hlen : hcoreWitnessHeaderRlp.length = 645 := hcoreHeaderRlp_length
    have hfull := EvmAsm.EL.RLP.decodeFully_encode
      (.list (bs.map EvmAsm.EL.RLP.RLPItem.bytes))
      (by change hcoreWitnessHeaderRlp.length < 256 ^ 8; rw [hlen]; decide)
    simp only [EvmAsm.Stateless.SpecRef._decode_header, hfull, hmap]
    simp [bs, h, hcore_decodeHeaderArm_ok, hnum, hbytes, hmk]
  have hrel2 :
      headerRlpRelation hcoreWitnessParentRlpBytes hcoreWitnessParentSpec := by
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
        hcoreWitnessParentSpec,
        EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE,
        EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD] <;> norm_num <;> decide
    have hbytes : EvmAsm.Stateless.SpecRef.validateHeaderWitness_bytesFieldsOk true bs = true := by
      change bytesFieldsOk true bs = true
      simp [bytesFieldsOk,
        EvmAsm.Stateless.SpecRef.fixedBytesFieldWidths,
        EvmAsm.Stateless.SpecRef.currentForkBytesFieldWidths, getBChecked,
        EvmAsm.Stateless.SpecRef.decodeItemFixedBytes, bs, h, hcoreWitnessParentSpec,
        EvmAsm.Stateless.SpecRef.natToBytesBE_length,
        List.all, List.getD] <;> norm_num <;> decide
    have hmk : EvmAsm.Stateless.SpecRef.mkHeaderFields true bs = h := by
      simpa [EvmAsm.Stateless.SpecRef.mkHeaderFields, bs, h, hcoreWitnessParentSpec,
        EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]
    unfold headerRlpRelation hcoreWitnessParentRlpBytes
    rw [hitem]
    have hlen : hcoreWitnessParentRlpBytes.length = 645 := hcoreParentRlp_length
    have hfull := EvmAsm.EL.RLP.decodeFully_encode
      (.list (bs.map EvmAsm.EL.RLP.RLPItem.bytes))
      (by change hcoreWitnessParentRlpBytes.length < 256 ^ 8; rw [hlen]; decide)
    simp only [EvmAsm.Stateless.SpecRef._decode_header, hfull, hmap]
    simp [bs, h, hcore_decodeHeaderArm_ok, hnum, hbytes, hmk]
  have h_with_rel1 :
      ((hcoreWitnessAssertion **
        (bytesRegion hcoreWitnessHeader hcoreWitnessHeaderRlp **
          bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes)) **
        ⌜headerRlpRelation hcoreWitnessHeaderRlp hcoreWitnessHeaderSpec⌝)
        (hcoreWitnessHeap.union (h1.union h2)) := by
    exact (sepConj_pure_right _).2 ⟨hbase, hrel1⟩
  have h_with_rel2 :
      (((hcoreWitnessAssertion **
        (bytesRegion hcoreWitnessHeader hcoreWitnessHeaderRlp **
          bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes)) **
        ⌜headerRlpRelation hcoreWitnessHeaderRlp hcoreWitnessHeaderSpec⌝) **
        ⌜headerRlpRelation hcoreWitnessParentRlpBytes hcoreWitnessParentSpec⌝)
        (hcoreWitnessHeap.union (h1.union h2)) := by
    exact (sepConj_pure_right _).2 ⟨h_with_rel1, hrel2⟩
  have hstruct1 :
      headerCoreStructRelation hcoreWitnessHeaderStruct hcoreWitnessHeaderSpec := by
    have hp : hcoreWitnessHeaderSpec.parentHash.length = 32 := by
      simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
    have hs : hcoreWitnessHeaderSpec.stateRoot.length = 32 := by
      simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
    refine ⟨?_, rfl⟩
    simp [hcoreWitnessHeaderStruct, headerCoreStructBytes,
      hp, hs,
      EvmAsm.Stateless.SpecRef.natToBytesBE_length,
      EvmAsm.Stateless.SpecRef.natToBytesLE_length]
  have hstruct2 :
      headerCoreStructRelation hcoreWitnessParentStruct hcoreWitnessParentSpec := by
    have hp : hcoreWitnessParentSpec.parentHash.length = 32 := by
      simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
    have hs : hcoreWitnessParentSpec.stateRoot.length = 32 := by
      simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
    refine ⟨?_, rfl⟩
    simp [hcoreWitnessParentStruct, headerCoreStructBytes,
      hp, hs,
      EvmAsm.Stateless.SpecRef.natToBytesBE_length,
      EvmAsm.Stateless.SpecRef.natToBytesLE_length]
  have hall :
      hcoreWitnessHeaderRlp.length = hcoreWitnessHeaderRlp.length ∧
      hcoreWitnessParentRlpBytes.length = hcoreWitnessParentRlpBytes.length ∧
      headerRlpRelation hcoreWitnessHeaderRlp hcoreWitnessHeaderSpec ∧
      headerRlpRelation hcoreWitnessParentRlpBytes hcoreWitnessParentSpec ∧
      headerCoreStructRelation hcoreWitnessHeaderStruct hcoreWitnessHeaderSpec ∧
      headerCoreStructRelation hcoreWitnessParentStruct hcoreWitnessParentSpec :=
    ⟨rfl, rfl, hrel1, hrel2, hstruct1, hstruct2⟩
  have h := (sepConj_pure_right _).2 ⟨hbase, hall⟩
  rw [hcoreWitnessAssertion_eq] at h
  refine ⟨hcoreWitnessHeap.union (h1.union h2), ?_⟩
  simp [hcoreWitnessRegFold, hcoreWitnessRegAtom, hcoreWitnessRegs,
    hcoreWitnessStackFold, hcoreWitnessStackMems,
    validateHeaderCorePre, validateHeaderCoreFrame,
    hcoreWitnessSpC, hcoreWitnessHeader, hcoreWitnessParent,
    sepConj_emp_right', sepConj_assoc'] at h
  simp [validateHeaderCorePre, validateHeaderCoreFrame,
    hcoreWitnessSpC, hcoreWitnessHeader, hcoreWitnessParent,
    hcoreWitnessGRegion, sepConj_emp_right', sepConj_assoc'] at h ⊢
  xperm_hyp h

/-- The complete caller-side premise conjunction is inhabited with the
non-empty frame, including the stack-pointer relation, return-address
alignment, frame `pcFree`, and `validateHeaderCorePre` itself.  This is a
non-vacuity result only: the abstract `hcore` route premise is still
undischarged and has no semantic callers. -/
theorem validateHeaderCorePremises_nonempty_G :
    ∃ h : PartialState,
      hcoreWitnessSpC = hcoreWitnessSp0 + signExtend12 (-56 : BitVec 12) ∧
      ((0 : Word) &&& ~~~(1 : Word) = 0) ∧
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes).pcFree ∧
      validateHeaderCorePre hcoreWitnessParentSpec hcoreWitnessHeaderSpec
        hcoreWitnessSpC 0 hcoreWitnessHeader hcoreWitnessHeaderRlp.length
        hcoreWitnessHeaderRlp hcoreWitnessParentRlpBytes
        hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
        hcoreWitnessParentRlpBytes.length
        hcoreWitnessHeaderStruct hcoreWitnessParentStruct
        hcoreWitnessHeader hcoreWitnessHeaderRlp.length hcoreWitnessParent hcoreWitnessParent2
        hcoreWitnessParentRlp hcoreWitnessParentRlpBytes.length
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) h := by
  obtain ⟨h, hpre⟩ := validateHeaderCorePre_nonempty_G
  refine ⟨h, ?_, ?_, ?_, hpre⟩
  · decide
  · decide
  · exact bytesRegion_pcFree _ _

/-! ## Repaired-pre execution probe (#12715)

The concrete frame above uses the repaired `headerCoreStructRelation` rather
than an unconstrained cell at `thisStruct + 64`.  Four machine steps from the
core entry therefore execute the number/nonzero guard and the first three
loads; the post-state is at `H + 72` with the excess-blob status still zero.
This is an executable witness for the repaired pre, not a claim that the
abstract `hcore` route contract has already been proved.
-/

private def hcoreProbeRegHeap : (Reg × Word) → PartialState :=
  fun p => PartialState.singletonReg p.1 p.2

private def hcoreProbeMemHeap : (Word × Word) → PartialState :=
  fun p => PartialState.singletonMem p.1 p.2

private def hcoreProbeRegHeapFold : PartialState :=
  hcoreWitnessRegs.foldr
    (fun p acc => (hcoreProbeRegHeap p).union acc) PartialState.empty

private def hcoreProbeMemHeapFold : PartialState :=
  hcoreWitnessMems.foldr
    (fun p acc => (hcoreProbeMemHeap p).union acc) PartialState.empty

private def hcoreProbeHeap : PartialState :=
  hcoreProbeRegHeapFold.union hcoreProbeMemHeapFold

private def hcoreProbeState : MachineState where
  regs := fun r => (hcoreProbeHeap.regs r).getD 0
  mem := fun a => (hcoreProbeHeap.mem a).getD 0
  code := callerCode
  pc := H + 56

theorem validateHeaderCore_repairedPre_step4_pc :
    (stepN 4 hcoreProbeState).map MachineState.pc = some (H + 72) := by
  simp only [stepN, hcoreProbeState, Option.bind]
  simp [step, hcoreProbeHeap, hcoreProbeRegHeapFold, hcoreProbeMemHeapFold,
    hcoreProbeRegHeap, hcoreProbeMemHeap, hcoreWitnessRegs, hcoreWitnessMems,
    hcoreWitnessStructMems, hcoreWitnessHeaderStruct,
    hcoreWitnessParentStruct, headerCoreStructBytes,
    hcoreWitnessHeaderSpec, PartialState.union,
    PartialState.singletonReg, PartialState.singletonMem, PartialState.empty]
  decide

theorem validateHeaderCore_repairedPre_step4_status :
    (stepN 4 hcoreProbeState).map (fun s => s.getReg .x10) =
      some (262144 : Word) := by
  simp only [stepN, hcoreProbeState, Option.bind]
  simp [step, hcoreProbeHeap, hcoreProbeRegHeapFold, hcoreProbeMemHeapFold,
    hcoreProbeRegHeap, hcoreProbeMemHeap, hcoreWitnessRegs, hcoreWitnessMems,
    hcoreWitnessStructMems, hcoreWitnessHeaderStruct,
    hcoreWitnessParentStruct, headerCoreStructBytes,
    hcoreWitnessHeaderSpec, PartialState.union,
    PartialState.singletonReg, PartialState.singletonMem, PartialState.empty]
  decide

/-! The relation is sufficient to project the five scalar cells read by the
core body.  Its 144-byte length forces the two leading byte regions together
to occupy 64 bytes; the remaining chunks have fixed lengths, so no decoder
fact is needed for this projection itself. -/
theorem headerCoreStructRelation_five_reads
    (bs : List (BitVec 8)) (h : EvmAsm.Stateless.SpecRef.Header)
    (hrel : headerCoreStructRelation bs h) :
    (bs.drop 64).take 8 = EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number ∧
    (bs.drop 72).take 8 = EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp ∧
    (bs.drop 80).take 8 = EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit ∧
    (bs.drop 88).take 8 = EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ∧
    (bs.drop 136).take 8 = EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas := by
  rcases hrel with ⟨hlen, rfl⟩
  have hsum : h.parentHash.length + h.stateRoot.length = 64 := by
    simp [headerCoreStructBytes] at hlen
    omega
  have hslice (pre rest : List (BitVec 8)) :
      ((h.parentHash ++ h.stateRoot ++ pre ++ rest).drop
        (h.parentHash.length + h.stateRoot.length + pre.length)).take 8 =
        rest.take 8 := by
    have hd := List.drop_append_length
      (l₁ := h.parentHash ++ h.stateRoot ++ pre) (l₂ := rest)
    simpa only [List.length_append, Nat.add_assoc, List.append_assoc] using
      congrArg (List.take 8) hd
  have hn := hslice []
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesBE 32 h.baseFeePerGas ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.blobGasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas)
  have ht := hslice (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number)
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesBE 32 h.baseFeePerGas ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.blobGasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas)
  have hgL := hslice
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp)
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesBE 32 h.baseFeePerGas ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.blobGasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas)
  have hgU := hslice
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit)
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesBE 32 h.baseFeePerGas ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.blobGasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas)
  have he := hslice
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesBE 32 h.baseFeePerGas ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.blobGasUsed)
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas)
  constructor
  · simpa [headerCoreStructBytes, hsum] using hn
  constructor
  · simpa [headerCoreStructBytes, hsum] using ht
  constructor
  · simpa [headerCoreStructBytes, hsum] using hgL
  constructor
  · simpa [headerCoreStructBytes, hsum] using hgU
  · -- `exact`, not `simpa using`: the two sides differ only by the reducible
    -- `SpecRef.Byte` synonym in the `List _` index, which v4.33's `simpa` will
    -- not unfold at reducible transparency.
    simp [headerCoreStructBytes, hsum] at he ⊢
    exact he

end EvmAsm.Codegen.ValidateHeaderWhole
