import EvmAsm.Codegen.Programs.ValidateHeaderWholeStatus7Witness
import EvmAsm.Rv64.MemSat
import Batteries.Tactic.OpenPrivate

set_option maxRecDepth 8000

/-!
  Constructive witnesses for the four remaining `validate_header` error arms
  (#12715): statuses 8 (difficulty), 9 (nonce), 10 (ommers hash), and 11
  (parent hash).  Every raw RLP view is encoded from the corresponding Header;
  the parent mutation in status 11 is therefore reflected in both its RLP and
  decoded 144-byte record.
-/

namespace EvmAsm.Codegen.ValidateHeaderWhole

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef
open EvmAsm.Stateless.SpecRef (decodeHeaderArm rlpBytes? getNChecked)
open EvmAsm.Stateless.SpecRef (checkNumericFields)
open EvmAsm.Stateless.SpecRef (bytesFieldsOk)
open EvmAsm.Stateless.SpecRef (numericFieldsOk)
open EvmAsm.Stateless.SpecRef (getBChecked)
-- `scalarItem` is no longer `private`: the exposed public body of
-- `headerToRlpItem` references it, and a public body may not mention a
-- private declaration. Plain `open` reaches it now.
open EvmAsm.Stateless.SpecRef (scalarItem)
open private hcore_decodeHeaderArm_ok from
  EvmAsm.Codegen.Programs.ValidateHeaderWholeWitness
open private hcoreHeaderItems_length hcoreParentItems_length
  hcoreHeaderRlp_length hcoreParentRlp_length hcoreEncodeList_length_642
  hcoreEncodeScalar0 hcoreEncodeScalar1 hcoreEncodeZero8
  hcoreEncodeBytesRep8 hcoreEncodeBytesRep32 hcoreEncode_len_of_bytes_length
  hcoreEncodeNatBE32 hcoreWitnessGRegion from
  EvmAsm.Codegen.Programs.ValidateHeaderWholeWitness

def errorArm8Header : Header :=
  {hcoreWitnessHeaderSpec with difficulty := 1}

def errorArm9Header : Header :=
  {hcoreWitnessHeaderSpec with nonce := [1, 0, 0, 0, 0, 0, 0, 0]}

def errorArm10Header : Header :=
  {hcoreWitnessHeaderSpec with ommersHash := List.replicate 32 1}

def errorArm11Parent : Header :=
  {hcoreWitnessParentSpec with
    parentHash := List.replicate 32 0}

def errorArm8Rlp : Bytes :=
  EvmAsm.EL.RLP.encode (headerToRlpItem errorArm8Header)

def errorArm9Rlp : Bytes :=
  EvmAsm.EL.RLP.encode (headerToRlpItem errorArm9Header)

def errorArm10Rlp : Bytes :=
  EvmAsm.EL.RLP.encode (headerToRlpItem errorArm10Header)

def errorArm11ParentRlp : Bytes :=
  EvmAsm.EL.RLP.encode (headerToRlpItem errorArm11Parent)

private theorem encodeItems_appendP (xs ys : List EvmAsm.EL.RLP.RLPItem) :
    EvmAsm.EL.RLP.encode.encodeItems (xs ++ ys) =
      EvmAsm.EL.RLP.encode.encodeItems xs ++
        EvmAsm.EL.RLP.encode.encodeItems ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, EvmAsm.EL.RLP.encode.encodeItems,
        ih, List.append_assoc]

theorem errorArm8Rlp_length : errorArm8Rlp.length = 645 := by
  let items : List EvmAsm.EL.RLP.RLPItem :=
    match headerToRlpItem errorArm8Header with
    | .list xs => xs
    | .bytes _ => []
  let pref : List EvmAsm.EL.RLP.RLPItem :=
    [.bytes errorArm8Header.parentHash, .bytes errorArm8Header.ommersHash,
     .bytes errorArm8Header.coinbase, .bytes errorArm8Header.stateRoot,
     .bytes errorArm8Header.transactionsRoot, .bytes errorArm8Header.receiptRoot,
     .bytes errorArm8Header.bloom]
  let suf : List EvmAsm.EL.RLP.RLPItem :=
    [scalarItem errorArm8Header.number, scalarItem errorArm8Header.gasLimit,
     scalarItem errorArm8Header.gasUsed, scalarItem errorArm8Header.timestamp,
     .bytes errorArm8Header.extraData, .bytes errorArm8Header.prevRandao,
     .bytes errorArm8Header.nonce, scalarItem errorArm8Header.baseFeePerGas,
     .bytes errorArm8Header.withdrawalsRoot, scalarItem errorArm8Header.blobGasUsed,
     scalarItem errorArm8Header.excessBlobGas, .bytes errorArm8Header.parentBeaconBlockRoot,
     .bytes errorArm8Header.requestsHash, .bytes errorArm8Header.blockAccessListHash,
     scalarItem errorArm8Header.slotNumber]
  have hitems : (EvmAsm.EL.RLP.encode.encodeItems items).length = 642 := by
    have hdecomp : items = pref ++
        [.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 1)] ++ suf := by
      simp [items, pref, suf, errorArm8Header, hcoreWitnessHeaderSpec,
        headerToRlpItem, scalarItem, EvmAsm.EL.RLP.Nat.toBytesBE]
    rw [hdecomp]
    rw [encodeItems_appendP, encodeItems_appendP]
    simp only [EvmAsm.EL.RLP.encode.encodeItems, List.length_append]
    let oldItems : List EvmAsm.EL.RLP.RLPItem :=
      match headerToRlpItem hcoreWitnessHeaderSpec with
      | .list xs => xs
      | .bytes _ => []
    have holdDecomp : oldItems = pref ++
        [.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 0)] ++ suf := by
      simp [oldItems, pref, suf, errorArm8Header, hcoreWitnessHeaderSpec,
        headerToRlpItem, scalarItem, EvmAsm.EL.RLP.Nat.toBytesBE]
    have holdLen : (EvmAsm.EL.RLP.encode.encodeItems oldItems).length = 642 := by
      simpa [oldItems, headerToRlpItem] using hcoreHeaderItems_length
    have holdLen' := holdLen
    rw [holdDecomp, encodeItems_appendP, encodeItems_appendP] at holdLen'
    simp only [EvmAsm.EL.RLP.encode.encodeItems, List.length_append] at holdLen'
    rw [hcoreEncodeScalar0] at holdLen'
    rw [hcoreEncodeScalar1]
    omega
  have hitem : headerToRlpItem errorArm8Header = .list items := by
    simp [items, headerToRlpItem, errorArm8Header, hcoreWitnessHeaderSpec,
      scalarItem]
  unfold errorArm8Rlp
  rw [hitem]
  exact hcoreEncodeList_length_642 items hitems

theorem errorArm9Rlp_length : errorArm9Rlp.length = 645 := by
  let items : List EvmAsm.EL.RLP.RLPItem :=
    match headerToRlpItem errorArm9Header with
    | .list xs => xs
    | .bytes _ => []
  let pref : List EvmAsm.EL.RLP.RLPItem :=
    [.bytes errorArm9Header.parentHash, .bytes errorArm9Header.ommersHash,
     .bytes errorArm9Header.coinbase, .bytes errorArm9Header.stateRoot,
     .bytes errorArm9Header.transactionsRoot, .bytes errorArm9Header.receiptRoot,
     .bytes errorArm9Header.bloom, scalarItem errorArm9Header.difficulty,
     scalarItem errorArm9Header.number, scalarItem errorArm9Header.gasLimit,
     scalarItem errorArm9Header.gasUsed, scalarItem errorArm9Header.timestamp,
     .bytes errorArm9Header.extraData, .bytes errorArm9Header.prevRandao]
  let suf : List EvmAsm.EL.RLP.RLPItem :=
    [scalarItem errorArm9Header.baseFeePerGas,
     .bytes errorArm9Header.withdrawalsRoot, scalarItem errorArm9Header.blobGasUsed,
     scalarItem errorArm9Header.excessBlobGas, .bytes errorArm9Header.parentBeaconBlockRoot,
     .bytes errorArm9Header.requestsHash, .bytes errorArm9Header.blockAccessListHash,
     scalarItem errorArm9Header.slotNumber]
  have hitems : (EvmAsm.EL.RLP.encode.encodeItems items).length = 642 := by
    have hdecomp : items = pref ++ [.bytes [1, 0, 0, 0, 0, 0, 0, 0]] ++ suf := by
      simp [items, pref, suf, errorArm9Header, hcoreWitnessHeaderSpec,
        headerToRlpItem, scalarItem, EvmAsm.EL.RLP.Nat.toBytesBE]
    rw [hdecomp]
    rw [encodeItems_appendP, encodeItems_appendP]
    simp only [EvmAsm.EL.RLP.encode.encodeItems, List.length_append]
    let oldItems : List EvmAsm.EL.RLP.RLPItem :=
      match headerToRlpItem hcoreWitnessHeaderSpec with
      | .list xs => xs
      | .bytes _ => []
    have holdDecomp : oldItems = pref ++
        [.bytes hcoreWitnessHeaderSpec.nonce] ++ suf := by
      simp [oldItems, pref, suf, errorArm9Header, hcoreWitnessHeaderSpec,
        headerToRlpItem, scalarItem]
    have holdLen : (EvmAsm.EL.RLP.encode.encodeItems oldItems).length = 642 := by
      simpa [oldItems, headerToRlpItem] using hcoreHeaderItems_length
    have holdLen' := holdLen
    rw [holdDecomp, encodeItems_appendP, encodeItems_appendP] at holdLen'
    simp only [EvmAsm.EL.RLP.encode.encodeItems, List.length_append] at holdLen'
    have hnew : (EvmAsm.EL.RLP.encode
        (.bytes [1, 0, 0, 0, 0, 0, 0, 0])).length = 9 := by
      change (EvmAsm.EL.RLP.encodeBytes
        [1, 0, 0, 0, 0, 0, 0, 0]).length = 9
      rw [EvmAsm.EL.RLP.encodeBytes_short_of_length_ne_one _ (by decide) (by decide)]
      simp
    have hold : (EvmAsm.EL.RLP.encode
        (.bytes hcoreWitnessHeaderSpec.nonce)).length = 9 := by
      have hnonce : hcoreWitnessHeaderSpec.nonce =
          List.replicate 8 (0 : BitVec 8) := by rfl
      rw [hnonce]
      exact hcoreEncodeBytesRep8 (0 : BitVec 8)
    rw [hold] at holdLen'
    rw [hnew]
    omega
  have hitem : headerToRlpItem errorArm9Header = .list items := by
    simp [items, headerToRlpItem, errorArm9Header, hcoreWitnessHeaderSpec,
      scalarItem]
  unfold errorArm9Rlp
  rw [hitem]
  exact hcoreEncodeList_length_642 items hitems

theorem errorArm10Rlp_length : errorArm10Rlp.length = 645 := by
  let items : List EvmAsm.EL.RLP.RLPItem :=
    match headerToRlpItem errorArm10Header with
    | .list xs => xs
    | .bytes _ => []
  let pref : List EvmAsm.EL.RLP.RLPItem :=
    [.bytes errorArm10Header.parentHash]
  let suf : List EvmAsm.EL.RLP.RLPItem :=
    [.bytes errorArm10Header.coinbase, .bytes errorArm10Header.stateRoot,
     .bytes errorArm10Header.transactionsRoot, .bytes errorArm10Header.receiptRoot,
     .bytes errorArm10Header.bloom, scalarItem errorArm10Header.difficulty,
     scalarItem errorArm10Header.number, scalarItem errorArm10Header.gasLimit,
     scalarItem errorArm10Header.gasUsed, scalarItem errorArm10Header.timestamp,
     .bytes errorArm10Header.extraData, .bytes errorArm10Header.prevRandao,
     .bytes errorArm10Header.nonce, scalarItem errorArm10Header.baseFeePerGas,
     .bytes errorArm10Header.withdrawalsRoot, scalarItem errorArm10Header.blobGasUsed,
     scalarItem errorArm10Header.excessBlobGas, .bytes errorArm10Header.parentBeaconBlockRoot,
     .bytes errorArm10Header.requestsHash, .bytes errorArm10Header.blockAccessListHash,
     scalarItem errorArm10Header.slotNumber]
  have hitems : (EvmAsm.EL.RLP.encode.encodeItems items).length = 642 := by
    have hdecomp : items = pref ++ [.bytes (List.replicate 32 1)] ++ suf := by
      simp [items, pref, suf, errorArm10Header, hcoreWitnessHeaderSpec,
        headerToRlpItem, scalarItem, EvmAsm.EL.RLP.Nat.toBytesBE]
    rw [hdecomp]
    rw [encodeItems_appendP, encodeItems_appendP]
    simp only [EvmAsm.EL.RLP.encode.encodeItems, List.length_append]
    let oldItems : List EvmAsm.EL.RLP.RLPItem :=
      match headerToRlpItem hcoreWitnessHeaderSpec with
      | .list xs => xs
      | .bytes _ => []
    have holdDecomp : oldItems = pref ++
        [.bytes hcoreWitnessHeaderSpec.ommersHash] ++ suf := by
      simp [oldItems, pref, suf, errorArm10Header, hcoreWitnessHeaderSpec,
        headerToRlpItem, scalarItem]
    have holdLen : (EvmAsm.EL.RLP.encode.encodeItems oldItems).length = 642 := by
      simpa [oldItems, headerToRlpItem] using hcoreHeaderItems_length
    have holdLen' := holdLen
    rw [holdDecomp, encodeItems_appendP, encodeItems_appendP] at holdLen'
    simp only [EvmAsm.EL.RLP.encode.encodeItems, List.length_append] at holdLen'
    have hnew : (EvmAsm.EL.RLP.encode
        (.bytes (List.replicate 32 (1 : BitVec 8)))).length = 33 := by
      exact hcoreEncodeBytesRep32 (1 : BitVec 8)
    have hold : (EvmAsm.EL.RLP.encode
        (.bytes hcoreWitnessHeaderSpec.ommersHash)).length = 33 := by
      apply hcoreEncode_len_of_bytes_length _ 32
      · simp [hcoreWitnessHeaderSpec]
      · decide
      · decide
    rw [hold] at holdLen'
    rw [hnew]
    omega
  have hitem : headerToRlpItem errorArm10Header = .list items := by
    simp [items, headerToRlpItem, errorArm10Header, hcoreWitnessHeaderSpec,
      scalarItem]
  unfold errorArm10Rlp
  rw [hitem]
  exact hcoreEncodeList_length_642 items hitems

theorem errorArm11ParentRlp_length : errorArm11ParentRlp.length = 645 := by
  let items : List EvmAsm.EL.RLP.RLPItem :=
    match headerToRlpItem errorArm11Parent with
    | .list xs => xs
    | .bytes _ => []
  let pref : List EvmAsm.EL.RLP.RLPItem :=
    [.bytes errorArm11Parent.ommersHash, .bytes errorArm11Parent.coinbase,
     .bytes errorArm11Parent.stateRoot, .bytes errorArm11Parent.transactionsRoot,
     .bytes errorArm11Parent.receiptRoot, .bytes errorArm11Parent.bloom,
     scalarItem errorArm11Parent.difficulty,
     scalarItem errorArm11Parent.number, scalarItem errorArm11Parent.gasLimit,
     scalarItem errorArm11Parent.gasUsed, scalarItem errorArm11Parent.timestamp,
     .bytes errorArm11Parent.extraData, .bytes errorArm11Parent.prevRandao,
     .bytes errorArm11Parent.nonce, scalarItem errorArm11Parent.baseFeePerGas,
     .bytes errorArm11Parent.withdrawalsRoot, scalarItem errorArm11Parent.blobGasUsed,
     scalarItem errorArm11Parent.excessBlobGas, .bytes errorArm11Parent.parentBeaconBlockRoot,
     .bytes errorArm11Parent.requestsHash, .bytes errorArm11Parent.blockAccessListHash,
     scalarItem errorArm11Parent.slotNumber]
  have hitems : (EvmAsm.EL.RLP.encode.encodeItems items).length = 642 := by
    have hdecomp : items = [.bytes errorArm11Parent.parentHash] ++ pref := by
      simp [items, pref, errorArm11Parent, hcoreWitnessParentSpec,
        headerToRlpItem, scalarItem, EvmAsm.EL.RLP.Nat.toBytesBE]
    let oldItems : List EvmAsm.EL.RLP.RLPItem :=
      match headerToRlpItem hcoreWitnessParentSpec with
      | .list xs => xs
      | .bytes _ => []
    have holdDecomp : oldItems =
        [.bytes hcoreWitnessParentSpec.parentHash] ++ pref := by
      simp [oldItems, pref, errorArm11Parent, hcoreWitnessParentSpec,
        headerToRlpItem, scalarItem]
    have holdLen : (EvmAsm.EL.RLP.encode.encodeItems oldItems).length = 642 := by
      simpa [oldItems, headerToRlpItem] using hcoreParentItems_length
    have holdLen' := holdLen
    rw [holdDecomp, encodeItems_appendP] at holdLen'
    simp only [EvmAsm.EL.RLP.encode.encodeItems, List.length_append] at holdLen'
    rw [hdecomp]
    rw [encodeItems_appendP]
    simp only [EvmAsm.EL.RLP.encode.encodeItems, List.length_append]
    have hnew : (EvmAsm.EL.RLP.encode
        (.bytes errorArm11Parent.parentHash)).length = 33 := by
      simpa [errorArm11Parent] using hcoreEncodeBytesRep32 (0 : BitVec 8)
    have hold : (EvmAsm.EL.RLP.encode
        (.bytes hcoreWitnessParentSpec.parentHash)).length = 33 := by
      simpa [hcoreWitnessParentSpec] using hcoreEncodeNatBE32 _
    rw [hold] at holdLen'
    rw [hnew]
    omega
  have hitem : headerToRlpItem errorArm11Parent = .list items := by
    simp [items, headerToRlpItem, errorArm11Parent, hcoreWitnessParentSpec,
      scalarItem]
  unfold errorArm11ParentRlp
  rw [hitem]
  exact hcoreEncodeList_length_642 items hitems

def errorArmFields (h : Header) : List Bytes :=
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

def errorArmSp : Word := hcoreWitnessSpC
def errorArmHeaderPtr : Word := 0xa4200000

def errorArmRegs (raw rawP : Bytes) : List (Reg × Word) :=
  [(.x1, 0), (.x2, errorArmSp), (.x8, errorArmHeaderPtr),
   (.x9, BitVec.ofNat 64 raw.length), (.x18, hcoreWitnessParent),
   (.x19, hcoreWitnessParent2), (.x20, hcoreWitnessParentRlp),
   (.x21, BitVec.ofNat 64 rawP.length), (.x10, errorArmHeaderPtr),
   (.x11, BitVec.ofNat 64 raw.length), (.x12, hcoreWitnessParent),
   (.x13, hcoreWitnessParent2), (.x14, hcoreWitnessParentRlp),
   (.x15, BitVec.ofNat 64 rawP.length)]

def errorArmRegAtom (p : Reg × Word) : Assertion := p.1 ↦ᵣ p.2
def errorArmRegHeap (p : Reg × Word) : PartialState :=
  PartialState.singletonReg p.1 p.2
def errorArmRegFold (raw rawP : Bytes) : Assertion :=
  (errorArmRegs raw rawP).foldr (fun p acc => errorArmRegAtom p ** acc)
    empAssertion
def errorArmRegHeapFold (raw rawP : Bytes) : PartialState :=
  (errorArmRegs raw rawP).foldr
    (fun p acc => (errorArmRegHeap p).union acc) PartialState.empty

def errorArmStack (raw rawP : Bytes) : Assertion :=
  ((((((errorArmSp ↦ₘ 0) **
      ((errorArmSp + 8) ↦ₘ hcoreWitnessParent)) **
      ((errorArmSp + 16) ↦ₘ (BitVec.ofNat 64 raw.length))) **
      ((errorArmSp + 24) ↦ₘ hcoreWitnessParent)) **
      ((errorArmSp + 32) ↦ₘ hcoreWitnessParent2)) **
      ((errorArmSp + 40) ↦ₘ hcoreWitnessParentRlp)) **
      ((errorArmSp + 48) ↦ₘ (BitVec.ofNat 64 rawP.length))

def errorArmMem (raw rawP curStruct parStruct : Bytes) : Assertion :=
  (((((errorArmStack raw rawP ** bytesRegion hcoreWitnessParent curStruct) **
      bytesRegion hcoreWitnessParent2 parStruct) **
      bytesRegion hcoreWitnessParentRlp rawP) **
      bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) **
      bytesRegion errorArmHeaderPtr raw)

def errorArmMemSatAssertion (raw rawP curStruct parStruct : Bytes) : Assertion :=
  errorArmMem raw rawP curStruct parStruct

theorem errorArmRegSat (raw rawP : Bytes) :
    errorArmRegFold raw rawP (errorArmRegHeapFold raw rawP) := by
  apply sepConj_foldr_satisfiable errorArmRegAtom errorArmRegHeap
    (errorArmRegs raw rawP)
  · intro p hp
    rfl
  · have hd : (errorArmRegs raw rawP).Pairwise (fun p q => p.1 ≠ q.1) := by
      simp [errorArmRegs]
    exact List.Pairwise.imp
      (fun {_ _} h =>
        EvmAsm.Codegen.ValidateHeaderCompose.routeInhabitantRegSingletonDisjoint h)
      hd

theorem errorArmRegNoFields (raw rawP : Bytes) :
    (∀ a, (errorArmRegHeapFold raw rawP).mem a = none) ∧
    (∀ a, (errorArmRegHeapFold raw rawP).code a = none) ∧
    (errorArmRegHeapFold raw rawP).pc = none ∧
    (errorArmRegHeapFold raw rawP).publicValues = none ∧
    (errorArmRegHeapFold raw rawP).privateInput = none ∧
    (errorArmRegHeapFold raw rawP).inputBufBase = none := by
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
      · intro a; change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).mem a = none; exact ih.1 a
      · intro a; change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).code a = none; exact ih.2.1 a
      · change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).pc = none; exact ih.2.2.1
      · change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).publicValues = none; exact ih.2.2.2.1
      · change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).privateInput = none; exact ih.2.2.2.2.1
      · change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).inputBufBase = none; exact ih.2.2.2.2.2
  simpa [errorArmRegHeapFold, errorArmRegHeap] using
    foldReg_no_fields (errorArmRegs raw rawP) (fun p => p.1) (fun p => p.2)

theorem errorArmMemSat (raw rawP curStruct parStruct : Bytes)
    (hlen : raw.length = 645) (hlenP : rawP.length = 645)
    (hlenCur : curStruct.length = 144) (hlenPar : parStruct.length = 144) :
    ∃ h, errorArmMemSatAssertion raw rawP curStruct parStruct h ∧
      (∀ r, h.regs r = none) ∧ (∀ a, h.code a = none) ∧ h.pc = none ∧
      h.publicValues = none ∧ h.privateInput = none ∧ h.inputBufBase = none := by
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
  have hvalidP : ∀ k, k < (rawP.length + 7) / 8 →
      isValidDwordAccess (hcoreWitnessParentRlp + BitVec.ofNat 64 (8 * k)) = true := by
    intro k hk
    apply hvalidOf hcoreWitnessParentRlp 0x32000
      ((rawP.length + 7) / 8) (by rfl) (by norm_num)
      (by norm_num [hlenP]) k hk
  have hvalidH : ∀ k, k < (raw.length + 7) / 8 →
      isValidDwordAccess (errorArmHeaderPtr + BitVec.ofNat 64 (8 * k)) = true := by
    intro k hk
    apply hvalidOf errorArmHeaderPtr 0xa4200000
      ((raw.length + 7) / 8) (by rfl) (by norm_num)
      (by norm_num [hlen]) k hk
  have hvalidStructH : ∀ k, k < (curStruct.length + 7) / 8 →
      isValidDwordAccess (hcoreWitnessParent + BitVec.ofNat 64 (8 * k)) = true := by
    intro k hk
    apply hvalidOf hcoreWitnessParent 0x30000 18 (by rfl)
      (by norm_num) (by norm_num [hlenCur]) k
    simpa [hlenCur] using hk
  have hvalidStructP : ∀ k, k < (parStruct.length + 7) / 8 →
      isValidDwordAccess (hcoreWitnessParent2 + BitVec.ofNat 64 (8 * k)) = true := by
    intro k hk
    apply hvalidOf hcoreWitnessParent2 0x31000 18 (by rfl)
      (by norm_num) (by norm_num [hlenPar]) k
    simpa [hlenPar] using hk
  have hsp0 := satWithin_memIs (a := errorArmSp) (v := (0 : Word)) (by decide)
  have hsp8 := satWithin_memIs (a := errorArmSp + 8)
    (v := hcoreWitnessParent) (by decide)
  have hsp16 := satWithin_memIs (a := errorArmSp + 16)
    (v := BitVec.ofNat 64 raw.length) (by decide)
  have hsp24 := satWithin_memIs (a := errorArmSp + 24)
    (v := hcoreWitnessParent) (by decide)
  have hsp32 := satWithin_memIs (a := errorArmSp + 32)
    (v := hcoreWitnessParent2) (by decide)
  have hsp40 := satWithin_memIs (a := errorArmSp + 40)
    (v := hcoreWitnessParentRlp) (by decide)
  have hsp48 := satWithin_memIs (a := errorArmSp + 48)
    (v := BitVec.ofNat 64 rawP.length) (by decide)
  have hsp0' : (errorArmSp ↦ₘ (0 : Word)).SatWithin
      0x10000 0x10008 := by simpa [errorArmSp] using hsp0
  have hsp8' : ((errorArmSp + 8) ↦ₘ hcoreWitnessParent).SatWithin
      0x10008 0x10010 := by simpa [errorArmSp] using hsp8
  have hsp16' : ((errorArmSp + 16) ↦ₘ
      (BitVec.ofNat 64 raw.length)).SatWithin
      0x10010 0x10018 := by simpa [errorArmSp] using hsp16
  have hsp24' : ((errorArmSp + 24) ↦ₘ hcoreWitnessParent).SatWithin
      0x10018 0x10020 := by simpa [errorArmSp] using hsp24
  have hsp32' : ((errorArmSp + 32) ↦ₘ hcoreWitnessParent2).SatWithin
      0x10020 0x10028 := by simpa [errorArmSp] using hsp32
  have hsp40' : ((errorArmSp + 40) ↦ₘ hcoreWitnessParentRlp).SatWithin
      0x10028 0x10030 := by simpa [errorArmSp] using hsp40
  have hsp48' : ((errorArmSp + 48) ↦ₘ
      (BitVec.ofNat 64 rawP.length)).SatWithin
      0x10030 0x10038 := by simpa [errorArmSp] using hsp48
  have hstack1 := hsp0'.sepConj hsp8' (by norm_num) (by norm_num)
  have hstack2 := hstack1.sepConj hsp16' (by norm_num) (by norm_num)
  have hstack3 := hstack2.sepConj hsp24' (by norm_num) (by norm_num)
  have hstack4 := hstack3.sepConj hsp32' (by norm_num) (by norm_num)
  have hstack5 := hstack4.sepConj hsp40' (by norm_num) (by norm_num)
  have hstack := hstack5.sepConj hsp48' (by norm_num) (by norm_num)
  have hpRaw := satWithin_bytesRegion hcoreWitnessParentRlp rawP hvalidP
  have hhRaw := satWithin_bytesRegion errorArmHeaderPtr raw hvalidH
  have hhs := satWithin_bytesRegion hcoreWitnessParent curStruct hvalidStructH
  have hps := satWithin_bytesRegion hcoreWitnessParent2 parStruct hvalidStructP
  have hpRaw' : (bytesRegion hcoreWitnessParentRlp rawP).SatWithin
      0x32000 0x32288 := by simpa [hcoreWitnessParentRlp, hlenP] using hpRaw
  have hhRaw' : (bytesRegion errorArmHeaderPtr raw).SatWithin
      0xa4200000 0xa4200288 := by simpa [errorArmHeaderPtr, hlen] using hhRaw
  have hhs' : (bytesRegion hcoreWitnessParent curStruct).SatWithin
      0x30000 0x30090 := by simpa [hcoreWitnessParent, hlenCur] using hhs
  have hps' : (bytesRegion hcoreWitnessParent2 parStruct).SatWithin
      0x31000 0x31090 := by simpa [hcoreWitnessParent2, hlenPar] using hps
  have hhs'' : (bytesRegion hcoreWitnessParent curStruct).SatWithin
      65592 0x30090 := hhs'.mono (by norm_num) (by rfl)
  have hps'' : (bytesRegion hcoreWitnessParent2 parStruct).SatWithin
      0x30090 0x31090 := hps'.mono (by norm_num) (by rfl)
  have hpRaw'' : (bytesRegion hcoreWitnessParentRlp rawP).SatWithin
      0x31090 0x32288 := hpRaw'.mono (by norm_num) (by rfl)
  have hg0 := satWithin_memIs (a := hcoreWitnessGAddr)
      (v := packBytes hcoreWitnessGBytes) (by decide)
  have hg : (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes).SatWithin
      0x40000 0x40008 := by
    rw [hcoreWitnessGRegion]
    simpa [hcoreWitnessGAddr, hcoreWitnessGBytes] using hg0
  have hg'' : (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes).SatWithin
      0x32288 0x40008 := hg.mono (by norm_num) (by rfl)
  have hhRaw'' : (bytesRegion errorArmHeaderPtr raw).SatWithin
      0x40008 0xa4200288 := hhRaw'.mono (by norm_num) (by rfl)
  have hm1 := hstack.sepConj hhs'' (by norm_num) (by norm_num)
  have hm2 := hm1.sepConj hps'' (by norm_num) (by norm_num)
  have hm3 := hm2.sepConj hpRaw'' (by norm_num) (by norm_num)
  have hm4 := hm3.sepConj hg'' (by norm_num) (by norm_num)
  have hm5 := hm4.sepConj hhRaw'' (by norm_num) (by norm_num)
  obtain ⟨hm, hmsat, hmwithin⟩ := hm5
  refine ⟨hm, ?_, hmwithin.regs, hmwithin.code, hmwithin.pc,
    hmwithin.publicValues, hmwithin.privateInput, hmwithin.inputBufBase⟩
  change errorArmMemSatAssertion raw rawP curStruct parStruct hm at hmsat
  exact hmsat

theorem errorArm8_struct :
    headerCoreStructRelation (headerCoreStructBytes errorArm8Header)
      errorArm8Header := by
  refine ⟨?_, rfl⟩
  simp [headerCoreStructBytes, errorArm8Header, hcoreWitnessHeaderSpec,
    natToBytesBE_length, natToBytesLE_length]

theorem errorArm9_struct :
    headerCoreStructRelation (headerCoreStructBytes errorArm9Header)
      errorArm9Header := by
  refine ⟨?_, rfl⟩
  simp [headerCoreStructBytes, errorArm9Header, hcoreWitnessHeaderSpec,
    natToBytesBE_length, natToBytesLE_length]

theorem errorArm10_struct :
    headerCoreStructRelation (headerCoreStructBytes errorArm10Header)
      errorArm10Header := by
  refine ⟨?_, rfl⟩
  simp [headerCoreStructBytes, errorArm10Header, hcoreWitnessHeaderSpec,
    natToBytesBE_length, natToBytesLE_length]

theorem errorArm11_current_struct :
    headerCoreStructRelation hcoreWitnessHeaderStruct
      hcoreWitnessHeaderSpec := by
  rw [show hcoreWitnessHeaderStruct = headerCoreStructBytes hcoreWitnessHeaderSpec
    from rfl]
  simp [headerCoreStructRelation, headerCoreStructBytes, hcoreWitnessHeaderSpec,
    natToBytesBE_length, natToBytesLE_length]

theorem errorArm11_parent_struct :
    headerCoreStructRelation (headerCoreStructBytes errorArm11Parent)
      errorArm11Parent := by
  refine ⟨?_, rfl⟩
  simp [headerCoreStructBytes, errorArm11Parent, hcoreWitnessParentSpec,
    natToBytesBE_length, natToBytesLE_length]

theorem errorArmHeapSat (raw rawP curStruct parStruct : Bytes)
    (memHeap : PartialState)
    (hmem : errorArmMemSatAssertion raw rawP curStruct parStruct memHeap)
    (hmRegs : ∀ r, memHeap.regs r = none)
    (hmMem : ∀ a, (errorArmRegHeapFold raw rawP).mem a = none)
    (hmCode : ∀ a, (errorArmRegHeapFold raw rawP).code a = none)
    (hmPc : (errorArmRegHeapFold raw rawP).pc = none)
    (hmPublic : (errorArmRegHeapFold raw rawP).publicValues = none)
    (hmPrivate : (errorArmRegHeapFold raw rawP).privateInput = none)
    (hmInput : (errorArmRegHeapFold raw rawP).inputBufBase = none) :
    (errorArmRegFold raw rawP ** errorArmMemSatAssertion raw rawP curStruct parStruct)
      ((errorArmRegHeapFold raw rawP).union memHeap) := by
  have hd : (errorArmRegHeapFold raw rawP).Disjoint memHeap := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r; exact Or.inr (hmRegs r)
    · intro a; exact Or.inl (hmMem a)
    · intro a; exact Or.inl (hmCode a)
    · exact Or.inl hmPc
    · exact Or.inl hmPublic
    · exact Or.inl hmPrivate
    · exact Or.inl hmInput
  exact ⟨errorArmRegHeapFold raw rawP, memHeap, hd, rfl,
    errorArmRegSat raw rawP, hmem⟩

theorem decodeEncodedHeader (h : Header) (raw : Bytes)
    (hraw : raw = EvmAsm.EL.RLP.encode (headerToRlpItem h))
    (hlen : raw.length < 256 ^ 8)
    (hcurrent : h.isCurrentFork = true)
    (hnum : validateHeaderWitness_numericFieldsOk (errorArmFields h) = true)
    (hbytes : validateHeaderWitness_bytesFieldsOk true (errorArmFields h) = true)
    (hmk : mkHeaderFields true (errorArmFields h) = h) :
    _decode_header raw = .ok h := by
  let bs : List Bytes := errorArmFields h
  have hitem : headerToRlpItem h =
      .list (bs.map EvmAsm.EL.RLP.RLPItem.bytes) := by
    simp [bs, errorArmFields, headerToRlpItem, scalarItem, hcurrent]
  have hmap : (bs.map EvmAsm.EL.RLP.RLPItem.bytes).mapM rlpBytes? = some bs := by
    induction bs with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, List.mapM_cons, rlpBytes?]
        rw [ih]
        simp
  have henc : (EvmAsm.EL.RLP.encode
      (.list (bs.map EvmAsm.EL.RLP.RLPItem.bytes))).length < 256 ^ 8 := by
    rw [← hitem, ← hraw]
    exact hlen
  unfold _decode_header
  rw [hraw, hitem]
  have hfull := EvmAsm.EL.RLP.decodeFully_encode
    (.list (bs.map EvmAsm.EL.RLP.RLPItem.bytes)) henc
  simp only [hfull, hmap]
  have harm := hcore_decodeHeaderArm_ok true bs hnum hbytes
  rw [hmk] at harm
  exact harm

theorem errorArm8_decode : _decode_header errorArm8Rlp = .ok errorArm8Header := by
  apply decodeEncodedHeader errorArm8Header errorArm8Rlp rfl
  · rw [errorArm8Rlp_length]
    decide
  · rfl
  · change numericFieldsOk (errorArmFields errorArm8Header) = true
    simp [numericFieldsOk, numericFieldWidths, getNChecked, decodeItemScalar,
      errorArmFields, errorArm8Header, hcoreWitnessHeaderSpec,
      EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD]
    all_goals decide
  · change bytesFieldsOk true (errorArmFields errorArm8Header) = true
    simp [bytesFieldsOk, fixedBytesFieldWidths, currentForkBytesFieldWidths,
      getBChecked, decodeItemFixedBytes, errorArmFields, errorArm8Header,
      hcoreWitnessHeaderSpec, natToBytesBE_length, List.all, List.getD]
    all_goals decide
  · simp [mkHeaderFields, errorArmFields, errorArm8Header,
      hcoreWitnessHeaderSpec, EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]

theorem errorArm9_decode : _decode_header errorArm9Rlp = .ok errorArm9Header := by
  apply decodeEncodedHeader errorArm9Header errorArm9Rlp rfl
  · rw [errorArm9Rlp_length]
    decide
  · rfl
  · change numericFieldsOk (errorArmFields errorArm9Header) = true
    simp [numericFieldsOk, numericFieldWidths, getNChecked, decodeItemScalar,
      errorArmFields, errorArm9Header, hcoreWitnessHeaderSpec,
      EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD]
    all_goals decide
  · change bytesFieldsOk true (errorArmFields errorArm9Header) = true
    simp [bytesFieldsOk, fixedBytesFieldWidths, currentForkBytesFieldWidths,
      getBChecked, decodeItemFixedBytes, errorArmFields, errorArm9Header,
      hcoreWitnessHeaderSpec, natToBytesBE_length, List.all, List.getD]
    all_goals decide
  · simp [mkHeaderFields, errorArmFields, errorArm9Header,
      hcoreWitnessHeaderSpec, EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]

theorem errorArm10_decode : _decode_header errorArm10Rlp = .ok errorArm10Header := by
  apply decodeEncodedHeader errorArm10Header errorArm10Rlp rfl
  · rw [errorArm10Rlp_length]
    decide
  · rfl
  · change numericFieldsOk (errorArmFields errorArm10Header) = true
    simp [numericFieldsOk, numericFieldWidths, getNChecked, decodeItemScalar,
      errorArmFields, errorArm10Header, hcoreWitnessHeaderSpec,
      EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD]
    all_goals decide
  · change bytesFieldsOk true (errorArmFields errorArm10Header) = true
    simp [bytesFieldsOk, fixedBytesFieldWidths, currentForkBytesFieldWidths,
      getBChecked, decodeItemFixedBytes, errorArmFields, errorArm10Header,
      hcoreWitnessHeaderSpec, natToBytesBE_length, List.all, List.getD]
    all_goals decide
  · simp [mkHeaderFields, errorArmFields, errorArm10Header,
      hcoreWitnessHeaderSpec, EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]

theorem errorArm11_parent_decode :
    _decode_header errorArm11ParentRlp = .ok errorArm11Parent := by
  apply decodeEncodedHeader errorArm11Parent errorArm11ParentRlp rfl
  · rw [errorArm11ParentRlp_length]
    decide
  · rfl
  · change numericFieldsOk (errorArmFields errorArm11Parent) = true
    simp [numericFieldsOk, numericFieldWidths, getNChecked, decodeItemScalar,
      errorArmFields, errorArm11Parent, hcoreWitnessParentSpec,
      EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD]
    all_goals decide
  · change bytesFieldsOk true (errorArmFields errorArm11Parent) = true
    simp [bytesFieldsOk, fixedBytesFieldWidths, currentForkBytesFieldWidths,
      getBChecked, decodeItemFixedBytes, errorArmFields, errorArm11Parent,
      hcoreWitnessParentSpec, natToBytesBE_length, List.all, List.getD]
    all_goals decide
  · simp [mkHeaderFields, errorArmFields, errorArm11Parent,
      hcoreWitnessParentSpec, EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]

theorem errorArm11_current_decode :
    _decode_header hcoreWitnessHeaderRlp = .ok hcoreWitnessHeaderSpec := by
  apply decodeEncodedHeader hcoreWitnessHeaderSpec hcoreWitnessHeaderRlp rfl
  · rw [hcoreHeaderRlp_length]
    decide
  · rfl
  · change numericFieldsOk (errorArmFields hcoreWitnessHeaderSpec) = true
    simp [numericFieldsOk, numericFieldWidths, getNChecked, decodeItemScalar,
      errorArmFields, hcoreWitnessHeaderSpec,
      EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD]
    all_goals decide
  · change bytesFieldsOk true (errorArmFields hcoreWitnessHeaderSpec) = true
    simp [bytesFieldsOk, fixedBytesFieldWidths, currentForkBytesFieldWidths,
      getBChecked, decodeItemFixedBytes, errorArmFields,
      hcoreWitnessHeaderSpec, natToBytesBE_length, List.all, List.getD]
    all_goals decide
  · simp [mkHeaderFields, errorArmFields, hcoreWitnessHeaderSpec,
      EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]

theorem errorArm8_spec_reject :
    validate_header hcoreWitnessParentSpec errorArm8Header =
      .error (.invalidBlock "difficulty nonzero") := by
  decide

theorem errorArm9_spec_reject :
    validate_header hcoreWitnessParentSpec errorArm9Header =
      .error (.invalidBlock "nonce nonzero") := by
  decide

theorem errorArm10_spec_reject :
    validate_header hcoreWitnessParentSpec errorArm10Header =
      .error (.invalidBlock "ommers hash not empty") := by
  decide

theorem validateHeaderCorePre_errorArm
    (parentSpec headerSpec : Header)
    (raw rawP curStruct parStruct : EvmAsm.Stateless.SpecRef.Bytes)
    (memHeap : PartialState)
    (_hrawLen : raw.length = 645) (_hrawPLen : rawP.length = 645)
    (hrawDecode : _decode_header raw = .ok headerSpec)
    (hrawPDecode : _decode_header rawP = .ok parentSpec)
    (hcurRel : headerCoreStructRelation curStruct headerSpec)
    (hparRel : headerCoreStructRelation parStruct parentSpec)
    (hheap : (errorArmRegFold raw rawP **
      errorArmMemSatAssertion raw rawP curStruct parStruct)
      ((errorArmRegHeapFold raw rawP).union memHeap)) :
    validateHeaderCorePre parentSpec headerSpec
      errorArmSp 0 errorArmHeaderPtr (BitVec.ofNat 64 raw.length)
      raw rawP hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 rawP.length) curStruct parStruct
      hcoreWitnessParent (BitVec.ofNat 64 raw.length)
      hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 rawP.length)
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes)
      ((errorArmRegHeapFold raw rawP).union memHeap) := by
  have hrel :
      (raw.length : Word) = BitVec.ofNat 64 raw.length ∧
      (rawP.length : Word) = BitVec.ofNat 64 rawP.length ∧
      _decode_header raw = .ok headerSpec ∧
      _decode_header rawP = .ok parentSpec ∧
      headerCoreStructRelation curStruct headerSpec ∧
      headerCoreStructRelation parStruct parentSpec := by
    exact ⟨rfl, rfl, hrawDecode, hrawPDecode, hcurRel, hparRel⟩
  have h := (sepConj_pure_right _).2 ⟨hheap, hrel⟩
  unfold validateHeaderCorePre at h ⊢
  unfold validateHeaderCoreFrame at ⊢
  unfold errorArmRegFold errorArmRegAtom errorArmRegs at h
  unfold errorArmMemSatAssertion errorArmMem errorArmStack at h
  simp only [errorArmSp, errorArmHeaderPtr] at h ⊢
  simp only [List.foldr] at h ⊢
  simp only [sepConj_emp_right'] at h ⊢
  xperm_hyp h

theorem validateHeaderCorePre_errorArm8_nonempty :
    ∃ heap, validateHeaderCorePre hcoreWitnessParentSpec errorArm8Header
      errorArmSp 0 errorArmHeaderPtr (BitVec.ofNat 64 errorArm8Rlp.length)
      errorArm8Rlp hcoreWitnessParentRlpBytes hcoreWitnessParent
      hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      hcoreWitnessHeaderStruct hcoreWitnessParentStruct hcoreWitnessParent
      (BitVec.ofNat 64 errorArm8Rlp.length) hcoreWitnessParent
      hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) heap := by
  let memSat := errorArmMemSat errorArm8Rlp hcoreWitnessParentRlpBytes
      (headerCoreStructBytes errorArm8Header) hcoreWitnessParentStruct
      errorArm8Rlp_length hcoreParentRlp_length (by decide) (by decide)
  let mh := Classical.choose memSat
  have hms := (Classical.choose_spec memSat).1
  have hnreg := (Classical.choose_spec memSat).2.1
  have hnm := (Classical.choose_spec memSat).2.2.1
  have hnc := (Classical.choose_spec memSat).2.2.2.1
  have hnp := (Classical.choose_spec memSat).2.2.2.2.1
  have hnv := (Classical.choose_spec memSat).2.2.2.2.2.1
  have hni := (Classical.choose_spec memSat).2.2.2.2.2.2
  have hrn := errorArmRegNoFields errorArm8Rlp hcoreWitnessParentRlpBytes
  have hh := errorArmHeapSat errorArm8Rlp hcoreWitnessParentRlpBytes
    (headerCoreStructBytes errorArm8Header) hcoreWitnessParentStruct mh hms
    hnreg hrn.1 hrn.2.1 hrn.2.2.1 hrn.2.2.2.1 hrn.2.2.2.2.1 hrn.2.2.2.2.2
  refine ⟨(errorArmRegHeapFold errorArm8Rlp hcoreWitnessParentRlpBytes).union mh, ?_⟩
  apply validateHeaderCorePre_errorArm
    hcoreWitnessParentSpec errorArm8Header errorArm8Rlp
    hcoreWitnessParentRlpBytes (headerCoreStructBytes errorArm8Header)
    hcoreWitnessParentStruct mh
  · exact errorArm8Rlp_length
  · exact hcoreParentRlp_length
  · exact errorArm8_decode
  · exact status7WitnessParent_decode
  · exact errorArm8_struct
  · exact status7WitnessParent_struct
  · exact hh

theorem validateHeaderCorePre_errorArm9_nonempty :
    ∃ heap, validateHeaderCorePre hcoreWitnessParentSpec errorArm9Header
      errorArmSp 0 errorArmHeaderPtr (BitVec.ofNat 64 errorArm9Rlp.length)
      errorArm9Rlp hcoreWitnessParentRlpBytes hcoreWitnessParent
      hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      hcoreWitnessHeaderStruct hcoreWitnessParentStruct hcoreWitnessParent
      (BitVec.ofNat 64 errorArm9Rlp.length) hcoreWitnessParent
      hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) heap := by
  let memSat := errorArmMemSat errorArm9Rlp hcoreWitnessParentRlpBytes
      (headerCoreStructBytes errorArm9Header) hcoreWitnessParentStruct
      errorArm9Rlp_length hcoreParentRlp_length (by decide) (by decide)
  let mh := Classical.choose memSat
  have hms := (Classical.choose_spec memSat).1
  have hnreg := (Classical.choose_spec memSat).2.1
  have hnm := (Classical.choose_spec memSat).2.2.1
  have hnc := (Classical.choose_spec memSat).2.2.2.1
  have hnp := (Classical.choose_spec memSat).2.2.2.2.1
  have hnv := (Classical.choose_spec memSat).2.2.2.2.2.1
  have hni := (Classical.choose_spec memSat).2.2.2.2.2.2
  have hrn := errorArmRegNoFields errorArm9Rlp hcoreWitnessParentRlpBytes
  have hh := errorArmHeapSat errorArm9Rlp hcoreWitnessParentRlpBytes
    (headerCoreStructBytes errorArm9Header) hcoreWitnessParentStruct mh hms
    hnreg hrn.1 hrn.2.1 hrn.2.2.1 hrn.2.2.2.1 hrn.2.2.2.2.1 hrn.2.2.2.2.2
  refine ⟨(errorArmRegHeapFold errorArm9Rlp hcoreWitnessParentRlpBytes).union mh, ?_⟩
  apply validateHeaderCorePre_errorArm
    hcoreWitnessParentSpec errorArm9Header errorArm9Rlp
    hcoreWitnessParentRlpBytes (headerCoreStructBytes errorArm9Header)
    hcoreWitnessParentStruct mh
  · exact errorArm9Rlp_length
  · exact hcoreParentRlp_length
  · exact errorArm9_decode
  · exact status7WitnessParent_decode
  · exact errorArm9_struct
  · exact status7WitnessParent_struct
  · exact hh

theorem validateHeaderCorePre_errorArm10_nonempty :
    ∃ heap, validateHeaderCorePre hcoreWitnessParentSpec errorArm10Header
      errorArmSp 0 errorArmHeaderPtr (BitVec.ofNat 64 errorArm10Rlp.length)
      errorArm10Rlp hcoreWitnessParentRlpBytes hcoreWitnessParent
      hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      hcoreWitnessHeaderStruct hcoreWitnessParentStruct hcoreWitnessParent
      (BitVec.ofNat 64 errorArm10Rlp.length) hcoreWitnessParent
      hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) heap := by
  let memSat := errorArmMemSat errorArm10Rlp hcoreWitnessParentRlpBytes
      (headerCoreStructBytes errorArm10Header) hcoreWitnessParentStruct
      errorArm10Rlp_length hcoreParentRlp_length (by decide) (by decide)
  let mh := Classical.choose memSat
  have hms := (Classical.choose_spec memSat).1
  have hnreg := (Classical.choose_spec memSat).2.1
  have hnm := (Classical.choose_spec memSat).2.2.1
  have hnc := (Classical.choose_spec memSat).2.2.2.1
  have hnp := (Classical.choose_spec memSat).2.2.2.2.1
  have hnv := (Classical.choose_spec memSat).2.2.2.2.2.1
  have hni := (Classical.choose_spec memSat).2.2.2.2.2.2
  have hrn := errorArmRegNoFields errorArm10Rlp hcoreWitnessParentRlpBytes
  have hh := errorArmHeapSat errorArm10Rlp hcoreWitnessParentRlpBytes
    (headerCoreStructBytes errorArm10Header) hcoreWitnessParentStruct mh hms
    hnreg hrn.1 hrn.2.1 hrn.2.2.1 hrn.2.2.2.1 hrn.2.2.2.2.1 hrn.2.2.2.2.2
  refine ⟨(errorArmRegHeapFold errorArm10Rlp hcoreWitnessParentRlpBytes).union mh, ?_⟩
  apply validateHeaderCorePre_errorArm
    hcoreWitnessParentSpec errorArm10Header errorArm10Rlp
    hcoreWitnessParentRlpBytes (headerCoreStructBytes errorArm10Header)
    hcoreWitnessParentStruct mh
  · exact errorArm10Rlp_length
  · exact hcoreParentRlp_length
  · exact errorArm10_decode
  · exact status7WitnessParent_decode
  · exact errorArm10_struct
  · exact status7WitnessParent_struct
  · exact hh

theorem validateHeaderCorePre_errorArm11_nonempty :
    ∃ heap, validateHeaderCorePre errorArm11Parent hcoreWitnessHeaderSpec
      errorArmSp 0 errorArmHeaderPtr (BitVec.ofNat 64 hcoreWitnessHeaderRlp.length)
      hcoreWitnessHeaderRlp errorArm11ParentRlp hcoreWitnessParent
      hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 errorArm11ParentRlp.length)
      hcoreWitnessHeaderStruct (headerCoreStructBytes errorArm11Parent)
      hcoreWitnessParent (BitVec.ofNat 64 hcoreWitnessHeaderRlp.length)
      hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 errorArm11ParentRlp.length)
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) heap := by
  let memSat := errorArmMemSat hcoreWitnessHeaderRlp errorArm11ParentRlp
      hcoreWitnessHeaderStruct (headerCoreStructBytes errorArm11Parent)
      hcoreHeaderRlp_length errorArm11ParentRlp_length (by decide) (by decide)
  let mh := Classical.choose memSat
  have hms := (Classical.choose_spec memSat).1
  have hnreg := (Classical.choose_spec memSat).2.1
  have hnm := (Classical.choose_spec memSat).2.2.1
  have hnc := (Classical.choose_spec memSat).2.2.2.1
  have hnp := (Classical.choose_spec memSat).2.2.2.2.1
  have hnv := (Classical.choose_spec memSat).2.2.2.2.2.1
  have hni := (Classical.choose_spec memSat).2.2.2.2.2.2
  have hrn := errorArmRegNoFields hcoreWitnessHeaderRlp errorArm11ParentRlp
  have hh := errorArmHeapSat hcoreWitnessHeaderRlp errorArm11ParentRlp
    hcoreWitnessHeaderStruct (headerCoreStructBytes errorArm11Parent) mh hms
    hnreg hrn.1 hrn.2.1 hrn.2.2.1 hrn.2.2.2.1 hrn.2.2.2.2.1 hrn.2.2.2.2.2
  refine ⟨(errorArmRegHeapFold hcoreWitnessHeaderRlp errorArm11ParentRlp).union mh, ?_⟩
  apply validateHeaderCorePre_errorArm
    errorArm11Parent hcoreWitnessHeaderSpec hcoreWitnessHeaderRlp
    errorArm11ParentRlp hcoreWitnessHeaderStruct
    (headerCoreStructBytes errorArm11Parent) mh
  · exact hcoreHeaderRlp_length
  · exact errorArm11ParentRlp_length
  · exact errorArm11_current_decode
  · exact errorArm11_parent_decode
  · exact errorArm11_current_struct
  · exact errorArm11_parent_struct
  · exact hh

/- The status-11 SpecRef result is recorded by the linked probe (the hash
   reduction is intentionally kept out of this constructive witness):
   `validate_header errorArm11Parent hcoreWitnessHeaderSpec` evaluates to
   `Except.error (.invalidBlock "parent hash mismatch")`. -/

end EvmAsm.Codegen.ValidateHeaderWhole
