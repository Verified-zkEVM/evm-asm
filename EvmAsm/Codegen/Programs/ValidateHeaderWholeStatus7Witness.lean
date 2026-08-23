import EvmAsm.Codegen.Programs.ValidateHeaderWholeWitness
import EvmAsm.Rv64.MemSat
import Batteries.Tactic.OpenPrivate

set_option maxRecDepth 8000

/-!
  A constructive status-7 witness for `validate_header` (#12715).

  The current header is encoded from a `Header` whose `extraData` is genuinely
  33 bytes.  Thus the raw RLP view, the decoded 144-byte record and the
  strengthened core precondition all agree.  The linked routine reaches the
  extra-data-length arm (status 7), while `SpecRef.validate_header` returns
  the corresponding invalid-block error.
-/

namespace EvmAsm.Codegen.ValidateHeaderWhole

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef
open private scalarItem from EvmAsm.Stateless.SpecRef.BlocksRlp
open private numericFieldsOk bytesFieldsOk checkNumericFields decodeHeaderArm
  rlpBytes? getNChecked getBChecked from EvmAsm.Stateless.SpecRef.Stateless

def status7WitnessHeader : Header :=
  { hcoreWitnessHeaderSpec with extraData := List.replicate 33 0 }

def status7WitnessParent : Header := hcoreWitnessParentSpec

def status7WitnessRlp : Bytes :=
  EvmAsm.EL.RLP.encode (headerToRlpItem status7WitnessHeader)

def status7WitnessParentRlp : Bytes := hcoreWitnessParentRlpBytes

def status7WitnessHeaderPtr : Word := 0xa4200000
def status7WitnessSp : Word := hcoreWitnessSpC

def status7WitnessRegs : List (Reg × Word) :=
  [(.x1, 0), (.x2, status7WitnessSp), (.x8, status7WitnessHeaderPtr),
   (.x9, BitVec.ofNat 64 status7WitnessRlp.length),
   (.x18, hcoreWitnessParent), (.x19, hcoreWitnessParent2),
   (.x20, hcoreWitnessParentRlp),
   (.x21, BitVec.ofNat 64 status7WitnessParentRlp.length),
   (.x10, status7WitnessHeaderPtr),
   (.x11, BitVec.ofNat 64 status7WitnessRlp.length),
   (.x12, hcoreWitnessParent), (.x13, hcoreWitnessParent2),
   (.x14, hcoreWitnessParentRlp),
   (.x15, BitVec.ofNat 64 status7WitnessParentRlp.length)]

def status7WitnessRegAtom (p : Reg × Word) : Assertion := p.1 ↦ᵣ p.2
def status7WitnessRegHeap (p : Reg × Word) : PartialState :=
  PartialState.singletonReg p.1 p.2
def status7WitnessRegFold : Assertion :=
  status7WitnessRegs.foldr (fun p acc => status7WitnessRegAtom p ** acc) empAssertion
def status7WitnessRegHeapFold : PartialState :=
  status7WitnessRegs.foldr
    (fun p acc => (status7WitnessRegHeap p).union acc) PartialState.empty

def status7WitnessStack : Assertion :=
  ((((((status7WitnessSp ↦ₘ 0) **
      ((status7WitnessSp + 8) ↦ₘ hcoreWitnessParent)) **
      ((status7WitnessSp + 16) ↦ₘ
        (BitVec.ofNat 64 status7WitnessRlp.length))) **
      ((status7WitnessSp + 24) ↦ₘ hcoreWitnessParent)) **
      ((status7WitnessSp + 32) ↦ₘ hcoreWitnessParent2)) **
      ((status7WitnessSp + 40) ↦ₘ hcoreWitnessParentRlp)) **
      ((status7WitnessSp + 48) ↦ₘ
        (BitVec.ofNat 64 status7WitnessParentRlp.length))

def status7WitnessMem : Assertion :=
  (((((status7WitnessStack **
      bytesRegion hcoreWitnessParent hcoreWitnessHeaderStruct) **
      bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct) **
      bytesRegion hcoreWitnessParentRlp status7WitnessParentRlp) **
      bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) **
      bytesRegion status7WitnessHeaderPtr status7WitnessRlp)

theorem status7WitnessRlp_length : status7WitnessRlp.length = 678 := by
  let oldItems : List EvmAsm.EL.RLP.RLPItem :=
    match headerToRlpItem hcoreWitnessHeaderSpec with
    | .list items => items
    | .bytes _ => []
  let newItems : List EvmAsm.EL.RLP.RLPItem :=
    match headerToRlpItem status7WitnessHeader with
    | .list items => items
    | .bytes _ => []
  let pref : List EvmAsm.EL.RLP.RLPItem :=
    [.bytes hcoreWitnessHeaderSpec.parentHash,
     .bytes hcoreWitnessHeaderSpec.ommersHash,
     .bytes hcoreWitnessHeaderSpec.coinbase,
     .bytes hcoreWitnessHeaderSpec.stateRoot,
     .bytes hcoreWitnessHeaderSpec.transactionsRoot,
     .bytes hcoreWitnessHeaderSpec.receiptRoot,
     .bytes hcoreWitnessHeaderSpec.bloom,
     scalarItem hcoreWitnessHeaderSpec.difficulty,
     scalarItem hcoreWitnessHeaderSpec.number,
     scalarItem hcoreWitnessHeaderSpec.gasLimit,
     scalarItem hcoreWitnessHeaderSpec.gasUsed,
     scalarItem hcoreWitnessHeaderSpec.timestamp]
  let suf : List EvmAsm.EL.RLP.RLPItem :=
    [.bytes hcoreWitnessHeaderSpec.prevRandao,
     .bytes hcoreWitnessHeaderSpec.nonce,
     scalarItem hcoreWitnessHeaderSpec.baseFeePerGas,
     .bytes hcoreWitnessHeaderSpec.withdrawalsRoot,
     scalarItem hcoreWitnessHeaderSpec.blobGasUsed,
     scalarItem hcoreWitnessHeaderSpec.excessBlobGas,
     .bytes hcoreWitnessHeaderSpec.parentBeaconBlockRoot,
     .bytes hcoreWitnessHeaderSpec.requestsHash,
     .bytes hcoreWitnessHeaderSpec.blockAccessListHash,
     scalarItem hcoreWitnessHeaderSpec.slotNumber]
  have holdDecomp : oldItems = pref ++ [.bytes hcoreWitnessHeaderSpec.extraData] ++ suf := by
    simp [oldItems, pref, suf, hcoreWitnessHeaderSpec, headerToRlpItem, scalarItem]
  have hnewDecomp : newItems = pref ++ [.bytes (List.replicate 33 0)] ++ suf := by
    simp [newItems, pref, suf, status7WitnessHeader,
      hcoreWitnessHeaderSpec, headerToRlpItem, scalarItem]
  have encodeItems_appendP (xs ys : List EvmAsm.EL.RLP.RLPItem) :
      EvmAsm.EL.RLP.encode.encodeItems (xs ++ ys) =
        EvmAsm.EL.RLP.encode.encodeItems xs ++
          EvmAsm.EL.RLP.encode.encodeItems ys := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.cons_append, EvmAsm.EL.RLP.encode.encodeItems,
          ih, List.append_assoc]
  have hitem0 : (EvmAsm.EL.RLP.encode
      (.bytes hcoreWitnessHeaderSpec.extraData)).length = 1 := by
    simp [hcoreWitnessHeaderSpec, EvmAsm.EL.RLP.encode,
      EvmAsm.EL.RLP.encodeBytes]
  have hitem33 : (EvmAsm.EL.RLP.encode
      (.bytes (List.replicate 33 0))).length = 34 := by
    change (EvmAsm.EL.RLP.encodeBytes
      (List.replicate 33 (0 : BitVec 8))).length = 34
    rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one]
    · simp
    · simp
    · simp
  have holdLen :
      (EvmAsm.EL.RLP.encode.encodeItems oldItems).length = 642 := by
    simpa [oldItems, hcoreWitnessHeaderSpec, headerToRlpItem]
      using hcoreHeaderItems_length
  have hitemsNew :
      (EvmAsm.EL.RLP.encode.encodeItems newItems).length = 675 := by
    rw [hnewDecomp, encodeItems_appendP, encodeItems_appendP]
    simp only [EvmAsm.EL.RLP.encode.encodeItems, List.length_append,
      List.length_nil, hitem33]
    rw [holdDecomp, encodeItems_appendP, encodeItems_appendP] at holdLen
    simp only [EvmAsm.EL.RLP.encode.encodeItems, List.length_append,
      List.length_nil, hitem0] at holdLen
    omega
  have hitemEq : headerToRlpItem status7WitnessHeader = .list newItems := by
    unfold newItems
    cases h : headerToRlpItem status7WitnessHeader with
    | bytes bs => simp [headerToRlpItem, status7WitnessHeader,
        hcoreWitnessHeaderSpec] at h
    | list items => simp
  unfold status7WitnessRlp
  rw [hitemEq]
  simp [EvmAsm.EL.RLP.encode, hitemsNew, EvmAsm.EL.RLP.Nat.toBytesBE]

theorem status7WitnessParentRlp_length : status7WitnessParentRlp.length = 645 := by
  simpa [status7WitnessParentRlp] using hcoreParentRlp_length

theorem status7WitnessHeader_decode :
    _decode_header status7WitnessRlp = .ok status7WitnessHeader := by
  let h := status7WitnessHeader
  let bs : List Bytes :=
    [h.parentHash, h.ommersHash, h.coinbase, h.stateRoot,
     h.transactionsRoot, h.receiptRoot, h.bloom,
     EvmAsm.EL.RLP.Nat.toBytesBE h.difficulty,
     EvmAsm.EL.RLP.Nat.toBytesBE h.number,
     EvmAsm.EL.RLP.Nat.toBytesBE h.gasLimit,
     EvmAsm.EL.RLP.Nat.toBytesBE h.gasUsed,
     EvmAsm.EL.RLP.Nat.toBytesBE h.timestamp,
     h.extraData, h.prevRandao, h.nonce,
     EvmAsm.EL.RLP.Nat.toBytesBE h.baseFeePerGas,
     h.withdrawalsRoot, EvmAsm.EL.RLP.Nat.toBytesBE h.blobGasUsed,
     EvmAsm.EL.RLP.Nat.toBytesBE h.excessBlobGas,
     h.parentBeaconBlockRoot, h.requestsHash, h.blockAccessListHash,
     EvmAsm.EL.RLP.Nat.toBytesBE h.slotNumber]
  have hitem : headerToRlpItem h = .list (bs.map EvmAsm.EL.RLP.RLPItem.bytes) := by
    simp [bs, h, status7WitnessHeader, hcoreWitnessHeaderSpec,
      headerToRlpItem, scalarItem]
  have hmap : (bs.map EvmAsm.EL.RLP.RLPItem.bytes).mapM rlpBytes? = some bs := by
    induction bs with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, List.mapM_cons, rlpBytes?]
        rw [ih]
        simp
  have hnum : validateHeaderWitness_numericFieldsOk bs = true := by
    change numericFieldsOk bs = true
    simp [numericFieldsOk, numericFieldWidths, getNChecked, decodeItemScalar,
      bs, h, status7WitnessHeader, hcoreWitnessHeaderSpec,
      EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD]
    all_goals decide
  have hbytes : validateHeaderWitness_bytesFieldsOk true bs = true := by
    change bytesFieldsOk true bs = true
    simp [bytesFieldsOk, fixedBytesFieldWidths, currentForkBytesFieldWidths,
      getBChecked, decodeItemFixedBytes, bs, h, status7WitnessHeader,
      hcoreWitnessHeaderSpec, natToBytesBE_length, List.all, List.getD]
    all_goals decide
  have hmk : mkHeaderFields true bs = h := by
    simp [mkHeaderFields, bs, h, status7WitnessHeader,
      hcoreWitnessHeaderSpec, EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]
  unfold status7WitnessRlp
  rw [hitem]
  have hfull := EvmAsm.EL.RLP.decodeFully_encode
    (.list (bs.map EvmAsm.EL.RLP.RLPItem.bytes))
    (by change status7WitnessRlp.length < 256 ^ 8
        rw [status7WitnessRlp_length]
        decide)
  simp only [_decode_header, hfull, hmap]
  have harm := hcore_decodeHeaderArm_ok true bs hnum hbytes
  rw [hmk] at harm
  exact harm

theorem status7WitnessParent_decode :
    _decode_header status7WitnessParentRlp = .ok status7WitnessParent := by
  let h := status7WitnessParent
  let bs : List Bytes :=
    [h.parentHash, h.ommersHash, h.coinbase, h.stateRoot,
     h.transactionsRoot, h.receiptRoot, h.bloom,
     EvmAsm.EL.RLP.Nat.toBytesBE h.difficulty,
     EvmAsm.EL.RLP.Nat.toBytesBE h.number,
     EvmAsm.EL.RLP.Nat.toBytesBE h.gasLimit,
     EvmAsm.EL.RLP.Nat.toBytesBE h.gasUsed,
     EvmAsm.EL.RLP.Nat.toBytesBE h.timestamp,
     h.extraData, h.prevRandao, h.nonce,
     EvmAsm.EL.RLP.Nat.toBytesBE h.baseFeePerGas,
     h.withdrawalsRoot, EvmAsm.EL.RLP.Nat.toBytesBE h.blobGasUsed,
     EvmAsm.EL.RLP.Nat.toBytesBE h.excessBlobGas,
     h.parentBeaconBlockRoot, h.requestsHash, h.blockAccessListHash,
     EvmAsm.EL.RLP.Nat.toBytesBE h.slotNumber]
  have hitem : headerToRlpItem h = .list (bs.map EvmAsm.EL.RLP.RLPItem.bytes) := by
    simp [bs, h, status7WitnessParent, hcoreWitnessParentSpec,
      headerToRlpItem, scalarItem]
  have hmap : (bs.map EvmAsm.EL.RLP.RLPItem.bytes).mapM rlpBytes? = some bs := by
    induction bs with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, List.mapM_cons, rlpBytes?]
        rw [ih]
        simp
  have hnum : validateHeaderWitness_numericFieldsOk bs = true := by
    change numericFieldsOk bs = true
    simp [numericFieldsOk, numericFieldWidths, getNChecked, decodeItemScalar,
      bs, h, status7WitnessParent, hcoreWitnessParentSpec,
      EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD]
    all_goals decide
  have hbytes : validateHeaderWitness_bytesFieldsOk true bs = true := by
    change bytesFieldsOk true bs = true
    simp [bytesFieldsOk, fixedBytesFieldWidths, currentForkBytesFieldWidths,
      getBChecked, decodeItemFixedBytes, bs, h, status7WitnessParent,
      hcoreWitnessParentSpec, natToBytesBE_length, List.all, List.getD]
    all_goals decide
  have hmk : mkHeaderFields true bs = h := by
    simp [mkHeaderFields, bs, h, status7WitnessParent,
      hcoreWitnessParentSpec, EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]
  unfold status7WitnessParentRlp
  change _decode_header (EvmAsm.EL.RLP.encode (headerToRlpItem h)) = .ok h
  rw [hitem]
  have hfull := EvmAsm.EL.RLP.decodeFully_encode
    (.list (bs.map EvmAsm.EL.RLP.RLPItem.bytes))
    (by change status7WitnessParentRlp.length < 256 ^ 8
        rw [status7WitnessParentRlp_length]
        decide)
  simp only [_decode_header, hfull, hmap]
  have harm := hcore_decodeHeaderArm_ok true bs hnum hbytes
  rw [hmk] at harm
  exact harm

theorem status7Witness_spec_reject :
    validate_header status7WitnessParent status7WitnessHeader =
      .error (.invalidBlock "extra data too long") := by
  decide

theorem status7WitnessHeader_struct :
    headerCoreStructRelation (headerCoreStructBytes status7WitnessHeader)
      status7WitnessHeader := by
  refine ⟨?_, rfl⟩
  simp [headerCoreStructBytes, status7WitnessHeader, hcoreWitnessHeaderSpec,
    natToBytesBE_length, natToBytesLE_length]

theorem status7WitnessParent_struct :
    headerCoreStructRelation (headerCoreStructBytes status7WitnessParent)
      status7WitnessParent := by
  refine ⟨?_, rfl⟩
  simp [headerCoreStructBytes, status7WitnessParent, hcoreWitnessParentSpec,
    natToBytesBE_length, natToBytesLE_length]

def status7WitnessMemSatAssertion : Assertion :=
  (((((status7WitnessStack ** bytesRegion hcoreWitnessParent
      hcoreWitnessHeaderStruct) ** bytesRegion hcoreWitnessParent2
      hcoreWitnessParentStruct) ** bytesRegion hcoreWitnessParentRlp
      status7WitnessParentRlp) ** bytesRegion hcoreWitnessGAddr
      hcoreWitnessGBytes) ** bytesRegion status7WitnessHeaderPtr
      status7WitnessRlp)

theorem status7WitnessMemSat : ∃ h, status7WitnessMemSatAssertion h ∧
    (∀ r, h.regs r = none) ∧ (∀ a, h.code a = none) ∧ h.pc = none ∧
    h.publicValues = none ∧ h.privateInput = none ∧ h.inputBufBase = none := by
  have hlenP : status7WitnessParentRlp.length = 645 :=
    status7WitnessParentRlp_length
  have hlenH : status7WitnessRlp.length = 678 :=
    status7WitnessRlp_length
  have hlenStructH : hcoreWitnessHeaderStruct.length = 144 := by
    simp [hcoreWitnessHeaderStruct, headerCoreStructBytes,
      hcoreWitnessHeaderSpec, natToBytesBE_length, natToBytesLE_length]
  have hlenStructP : hcoreWitnessParentStruct.length = 144 := by
    simp [hcoreWitnessParentStruct, headerCoreStructBytes,
      hcoreWitnessParentSpec, natToBytesBE_length, natToBytesLE_length]
  have hvalidOf (base : Word) (b n : Nat) (hbase : base.toNat = b)
      (halign : b % 8 = 0)
      (hzone : (0x20 ≤ b ∧ b + 8 * n ≤ 0x78000000) ∨
        (0x40000000 ≤ b ∧ b + 8 * n ≤ 0x40002000) ∨
        (0xa0000000 ≤ b ∧ b + 8 * n ≤ 0xc0000000)) :
      ∀ k, k < n →
        isValidDwordAccess (base + BitVec.ofNat 64 (8 * k)) = true := by
    intro k hk
    have hto :
        (base + BitVec.ofNat 64 (8 * k)).toNat = base.toNat + 8 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hk64 : 8 * k < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hk64]
      have hsum : base.toNat + 8 * k < 2 ^ 64 := by
        rw [hbase]
        omega
      rw [Nat.mod_eq_of_lt hsum]
    have haddr : (base + BitVec.ofNat 64 (8 * k)).toNat = b + 8 * k := by
      rw [hto, hbase]
    apply isValidDwordAccess_of_toNat
    · rw [haddr]
      simp [Nat.add_mod, halign]
    · have hkle : k ≤ n := Nat.le_of_lt hk
      have hle : b + 8 * k ≤ b + 8 * n := by omega
      rcases hzone with hzone | hzone | hzone
      · exact Or.inl ⟨by rw [haddr]; omega,
          by rw [haddr]; exact le_trans hle hzone.2⟩
      · exact Or.inr (Or.inl ⟨by rw [haddr]; omega,
          by rw [haddr]; exact le_trans hle hzone.2⟩)
      · exact Or.inr (Or.inr ⟨by rw [haddr]; omega,
          by rw [haddr]; exact le_trans hle hzone.2⟩)
  have hvalidP : ∀ k, k < (status7WitnessParentRlp.length + 7) / 8 →
      isValidDwordAccess (hcoreWitnessParentRlp + BitVec.ofNat 64 (8 * k)) = true := by
    intro k hk
    apply hvalidOf hcoreWitnessParentRlp 0x32000
      ((status7WitnessParentRlp.length + 7) / 8) (by rfl)
      (by norm_num) (by norm_num [hlenP]) k hk
  have hvalidH : ∀ k, k < (status7WitnessRlp.length + 7) / 8 →
      isValidDwordAccess (status7WitnessHeaderPtr + BitVec.ofNat 64 (8 * k)) = true := by
    intro k hk
    apply hvalidOf status7WitnessHeaderPtr 0xa4200000
      ((status7WitnessRlp.length + 7) / 8) (by rfl)
      (by norm_num) (by norm_num [hlenH]) k hk
  have hvalidStructH : ∀ k, k < (hcoreWitnessHeaderStruct.length + 7) / 8 →
      isValidDwordAccess (hcoreWitnessParent + BitVec.ofNat 64 (8 * k)) = true := by
    intro k hk
    apply hvalidOf hcoreWitnessParent 0x30000 18 (by rfl)
      (by norm_num) (by norm_num [hlenStructH]) k
    simpa [hlenStructH] using hk
  have hvalidStructP : ∀ k, k < (hcoreWitnessParentStruct.length + 7) / 8 →
      isValidDwordAccess (hcoreWitnessParent2 + BitVec.ofNat 64 (8 * k)) = true := by
    intro k hk
    apply hvalidOf hcoreWitnessParent2 0x31000 18 (by rfl)
      (by norm_num) (by norm_num [hlenStructP]) k
    simpa [hlenStructP] using hk
  have hsp0 := satWithin_memIs (a := status7WitnessSp) (v := (0 : Word)) (by decide)
  have hsp8 := satWithin_memIs (a := status7WitnessSp + 8)
    (v := hcoreWitnessParent) (by decide)
  have hsp16 := satWithin_memIs (a := status7WitnessSp + 16)
    (v := BitVec.ofNat 64 status7WitnessRlp.length) (by decide)
  have hsp24 := satWithin_memIs (a := status7WitnessSp + 24)
    (v := hcoreWitnessParent) (by decide)
  have hsp32 := satWithin_memIs (a := status7WitnessSp + 32)
    (v := hcoreWitnessParent2) (by decide)
  have hsp40 := satWithin_memIs (a := status7WitnessSp + 40)
    (v := hcoreWitnessParentRlp) (by decide)
  have hsp48 := satWithin_memIs (a := status7WitnessSp + 48)
    (v := BitVec.ofNat 64 status7WitnessParentRlp.length) (by decide)
  have hsp0' : (status7WitnessSp ↦ₘ (0 : Word)).SatWithin
      0x10000 0x10008 := by simpa [status7WitnessSp] using hsp0
  have hsp8' : ((status7WitnessSp + 8) ↦ₘ hcoreWitnessParent).SatWithin
      0x10008 0x10010 := by simpa [status7WitnessSp] using hsp8
  have hsp16' : ((status7WitnessSp + 16) ↦ₘ
      (BitVec.ofNat 64 status7WitnessRlp.length)).SatWithin
      0x10010 0x10018 := by simpa [status7WitnessSp] using hsp16
  have hsp24' : ((status7WitnessSp + 24) ↦ₘ hcoreWitnessParent).SatWithin
      0x10018 0x10020 := by simpa [status7WitnessSp] using hsp24
  have hsp32' : ((status7WitnessSp + 32) ↦ₘ hcoreWitnessParent2).SatWithin
      0x10020 0x10028 := by simpa [status7WitnessSp] using hsp32
  have hsp40' : ((status7WitnessSp + 40) ↦ₘ hcoreWitnessParentRlp).SatWithin
      0x10028 0x10030 := by simpa [status7WitnessSp] using hsp40
  have hsp48' : ((status7WitnessSp + 48) ↦ₘ
      (BitVec.ofNat 64 status7WitnessParentRlp.length)).SatWithin
      0x10030 0x10038 := by simpa [status7WitnessSp] using hsp48
  have hstack1 := hsp0'.sepConj hsp8' (by norm_num) (by norm_num)
  have hstack2 := hstack1.sepConj hsp16' (by norm_num) (by norm_num)
  have hstack3 := hstack2.sepConj hsp24' (by norm_num) (by norm_num)
  have hstack4 := hstack3.sepConj hsp32' (by norm_num) (by norm_num)
  have hstack5 := hstack4.sepConj hsp40' (by norm_num) (by norm_num)
  have hstack := hstack5.sepConj hsp48' (by norm_num) (by norm_num)
  have hpRaw := satWithin_bytesRegion hcoreWitnessParentRlp
    status7WitnessParentRlp hvalidP
  have hhRaw := satWithin_bytesRegion status7WitnessHeaderPtr
    status7WitnessRlp hvalidH
  have hhs := satWithin_bytesRegion hcoreWitnessParent
    hcoreWitnessHeaderStruct hvalidStructH
  have hps := satWithin_bytesRegion hcoreWitnessParent2
    hcoreWitnessParentStruct hvalidStructP
  have hpRaw' : (bytesRegion hcoreWitnessParentRlp status7WitnessParentRlp).SatWithin
      0x32000 0x32288 := by simpa [hcoreWitnessParentRlp, hlenP] using hpRaw
  have hhRaw' : (bytesRegion status7WitnessHeaderPtr status7WitnessRlp).SatWithin
      0xa4200000 0xa42002a8 := by simpa [status7WitnessHeaderPtr, hlenH] using hhRaw
  have hhs' : (bytesRegion hcoreWitnessParent hcoreWitnessHeaderStruct).SatWithin
      0x30000 0x30090 := by simpa [hcoreWitnessParent, hlenStructH] using hhs
  have hps' : (bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct).SatWithin
      0x31000 0x31090 := by simpa [hcoreWitnessParent2, hlenStructP] using hps
  have hg : (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes).SatWithin
      0x40000 0x40008 := by
    have hg0 := satWithin_memIs (a := hcoreWitnessGAddr)
      (v := packBytes hcoreWitnessGBytes) (by decide)
    rw [hcoreWitnessGRegion]
    simpa [hcoreWitnessGAddr, hcoreWitnessGBytes] using hg0
  have hhs'' : (bytesRegion hcoreWitnessParent hcoreWitnessHeaderStruct).SatWithin
      65592 0x30090 := hhs'.mono (by norm_num) (by rfl)
  have hps'' : (bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct).SatWithin
      0x30090 0x31090 := hps'.mono (by norm_num) (by rfl)
  have hpRaw'' : (bytesRegion hcoreWitnessParentRlp status7WitnessParentRlp).SatWithin
      0x31090 0x32288 := hpRaw'.mono (by norm_num) (by rfl)
  have hg'' : (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes).SatWithin
      0x32288 0x40008 := hg.mono (by norm_num) (by rfl)
  have hhRaw'' : (bytesRegion status7WitnessHeaderPtr status7WitnessRlp).SatWithin
      0x40008 0xa42002a8 := hhRaw'.mono (by norm_num) (by rfl)
  have hm1 := hstack.sepConj hhs'' (by norm_num) (by norm_num)
  have hm2 := hm1.sepConj hps'' (by norm_num) (by norm_num)
  have hm3 := hm2.sepConj hpRaw'' (by norm_num) (by norm_num)
  have hm4 := hm3.sepConj hg'' (by norm_num) (by norm_num)
  have hm5 := hm4.sepConj hhRaw'' (by norm_num) (by norm_num)
  obtain ⟨hm, hmsat, hmwithin⟩ := hm5
  refine ⟨hm, ?_, hmwithin.regs, hmwithin.code, hmwithin.pc,
    hmwithin.publicValues, hmwithin.privateInput, hmwithin.inputBufBase⟩
  change status7WitnessMemSatAssertion hm at hmsat
  exact hmsat

theorem status7WitnessRegSat :
    status7WitnessRegFold status7WitnessRegHeapFold := by
  apply sepConj_foldr_satisfiable status7WitnessRegAtom
    status7WitnessRegHeap status7WitnessRegs
  · intro p hp
    rfl
  · have hd : status7WitnessRegs.Pairwise (fun p q => p.1 ≠ q.1) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h =>
        EvmAsm.Codegen.ValidateHeaderCompose.routeInhabitantRegSingletonDisjoint h)
      hd

theorem status7WitnessRegNoFields :
    (∀ a, status7WitnessRegHeapFold.mem a = none) ∧
    (∀ a, status7WitnessRegHeapFold.code a = none) ∧
    status7WitnessRegHeapFold.pc = none ∧
    status7WitnessRegHeapFold.publicValues = none ∧
    status7WitnessRegHeapFold.privateInput = none ∧
    status7WitnessRegHeapFold.inputBufBase = none := by
  have foldReg_no_fields :
      ∀ {α : Type} (xs : List α) (reg : α → Reg) (val : α → Word),
        (∀ a, (xs.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).mem a = none) ∧
        (∀ a, (xs.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).code a = none) ∧
        (xs.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).pc = none ∧
        (xs.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).publicValues = none ∧
        (xs.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).privateInput = none ∧
        (xs.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).inputBufBase = none := by
    intro α xs reg val
    induction xs with
    | nil => simp [PartialState.empty]
    | cons p ps ih =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro a
        change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).mem a = none
        exact ih.1 a
      · intro a
        change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).code a = none
        exact ih.2.1 a
      · change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).pc = none
        exact ih.2.2.1
      · change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).publicValues = none
        exact ih.2.2.2.1
      · change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).privateInput = none
        exact ih.2.2.2.2.1
      · change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).inputBufBase = none
        exact ih.2.2.2.2.2
  simpa [status7WitnessRegHeapFold, status7WitnessRegHeap] using
    foldReg_no_fields status7WitnessRegs (fun p => p.1) (fun p => p.2)

noncomputable def status7WitnessMemHeap : PartialState :=
  Classical.choose status7WitnessMemSat

theorem status7WitnessMemHeap_sat :
    status7WitnessMemSatAssertion status7WitnessMemHeap :=
  (Classical.choose_spec status7WitnessMemSat).1

theorem status7WitnessMemHeap_noFields :
    (∀ r, status7WitnessMemHeap.regs r = none) ∧
    (∀ a, status7WitnessMemHeap.code a = none) ∧
    status7WitnessMemHeap.pc = none ∧
    status7WitnessMemHeap.publicValues = none ∧
    status7WitnessMemHeap.privateInput = none ∧
    status7WitnessMemHeap.inputBufBase = none :=
  (Classical.choose_spec status7WitnessMemSat).2

theorem status7WitnessHeap_sat :
    (status7WitnessRegFold ** status7WitnessMemSatAssertion)
      (status7WitnessRegHeapFold.union status7WitnessMemHeap) := by
  have hn := status7WitnessMemHeap_noFields
  have hrn := status7WitnessRegNoFields
  have hd : status7WitnessRegHeapFold.Disjoint status7WitnessMemHeap := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r; exact Or.inr (hn.1 r)
    · intro a; exact Or.inl (hrn.1 a)
    · intro a; exact Or.inl (hrn.2.1 a)
    · exact Or.inl hrn.2.2.1
    · exact Or.inl hrn.2.2.2.1
    · exact Or.inl hrn.2.2.2.2.1
    · exact Or.inl hrn.2.2.2.2.2
  exact ⟨status7WitnessRegHeapFold, status7WitnessMemHeap, hd, rfl,
    status7WitnessRegSat, status7WitnessMemHeap_sat⟩

theorem validateHeaderCorePre_status7_nonempty :
    validateHeaderCorePre status7WitnessParent status7WitnessHeader
      status7WitnessSp 0 status7WitnessHeaderPtr
      (BitVec.ofNat 64 status7WitnessRlp.length) status7WitnessRlp
      status7WitnessParentRlp hcoreWitnessParent hcoreWitnessParent2
      hcoreWitnessParentRlp (BitVec.ofNat 64 status7WitnessParentRlp.length)
      hcoreWitnessHeaderStruct hcoreWitnessParentStruct
      hcoreWitnessParent (BitVec.ofNat 64 status7WitnessRlp.length)
      hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 status7WitnessParentRlp.length)
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes)
      (status7WitnessRegHeapFold.union status7WitnessMemHeap) := by
  have hbitH : status7WitnessRlp.length =
      (BitVec.ofNat 64 status7WitnessRlp.length).toNat := by
    rw [status7WitnessRlp_length]
    decide
  have hbitP : status7WitnessParentRlp.length =
      (BitVec.ofNat 64 status7WitnessParentRlp.length).toNat := by
    rw [status7WitnessParentRlp_length]
    decide
  have hrel :
      status7WitnessRlp.length =
          (BitVec.ofNat 64 status7WitnessRlp.length).toNat ∧
      status7WitnessParentRlp.length =
          (BitVec.ofNat 64 status7WitnessParentRlp.length).toNat ∧
      _decode_header status7WitnessRlp = .ok status7WitnessHeader ∧
      _decode_header status7WitnessParentRlp = .ok status7WitnessParent ∧
      headerCoreStructRelation hcoreWitnessHeaderStruct status7WitnessHeader ∧
      headerCoreStructRelation hcoreWitnessParentStruct status7WitnessParent := by
    have hsH : headerCoreStructRelation hcoreWitnessHeaderStruct
        status7WitnessHeader := by
      rw [show hcoreWitnessHeaderStruct = headerCoreStructBytes hcoreWitnessHeaderSpec
        from rfl]
      simpa [status7WitnessHeader, hcoreWitnessHeaderSpec,
        headerCoreStructBytes] using
        status7WitnessHeader_struct
    have hsP : headerCoreStructRelation hcoreWitnessParentStruct
        status7WitnessParent := by
      simpa [hcoreWitnessParentStruct, status7WitnessParent, hcoreWitnessParentSpec,
        headerCoreStructBytes] using
        status7WitnessParent_struct
    exact ⟨hbitH, hbitP, status7WitnessHeader_decode,
      status7WitnessParent_decode, hsH, hsP⟩
  have h := (sepConj_pure_right _).2
    ⟨status7WitnessHeap_sat, hrel⟩
  simp [status7WitnessRegFold, status7WitnessRegAtom, status7WitnessRegs,
    status7WitnessMemSatAssertion, status7WitnessStack,
    validateHeaderCorePre, validateHeaderCoreFrame,
    status7WitnessSp, status7WitnessHeaderPtr,
    sepConj_emp_right', sepConj_assoc', status7WitnessRlp_length,
    status7WitnessParentRlp_length] at h ⊢
  xperm_hyp h

end EvmAsm.Codegen.ValidateHeaderWhole
