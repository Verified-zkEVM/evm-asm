import EvmAsm.Codegen.Programs.ValidateHeaderCompose
import EvmAsm.Codegen.Programs.ValidateHeaderInlineArms
import EvmAsm.Codegen.Programs.ValidateHeaderWholeErrorArmWitness
import EvmAsm.Codegen.Programs.ValidateHeaderWholeStatus0Witness
import EvmAsm.Rv64.MemSat
import Batteries.Tactic.OpenPrivate

set_option maxRecDepth 8000

/-!
  Constructive satisfiability witness for `validateHeaderCoreContract`
  (#12346): the status-1 (block number < 1) exit of the thirteen-exit hcore
  contract.  The concrete header is `hcoreWitnessHeaderSpec` with `number := 0`,
  whose RLP is a genuine canonical encoding (length 645) and whose SpecRef
  `validate_header` rejects with `.error (.invalidBlock "block number < 1")`.

  The machine route is callee-free: `LD x5,x18+64` (H+56), `BEQ x5,x0` (H+60)
  to the status-1 tail (H+260), `LI x10,1` (H+260), `JAL x0` (H+264) to the
  epilogue seam at H+352.  This instantiates `validateHeaderCoreContract` with
  `nCore := 4` and witness `validateHeaderCoreContract_hcoreStatus1_inhabited`,
  matching the K74 `_inhabited` precedent (the machine triple is axiom-clean).
-/

namespace EvmAsm.Codegen.ValidateHeaderWhole

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef
open EvmAsm.Codegen.ValidateHeaderCorrespondence
open EvmAsm.Codegen.ValidateHeaderInlineArms
open EvmAsm.Stateless.SpecRef (decodeHeaderArm rlpBytes? getNChecked)
open EvmAsm.Stateless.SpecRef (checkNumericFields)
open EvmAsm.Stateless.SpecRef (bytesFieldsOk)
open EvmAsm.Stateless.SpecRef (numericFieldsOk)
open EvmAsm.Stateless.SpecRef (getBChecked)
open EvmAsm.Stateless.SpecRef (scalarItem)
open private hcore_decodeHeaderArm_ok from
  EvmAsm.Codegen.Programs.ValidateHeaderWholeWitness
open private hcoreHeaderItems_length hcoreParentItems_length
  hcoreHeaderRlp_length hcoreParentRlp_length hcoreEncodeList_length_642
  hcoreEncodeScalar0 hcoreEncodeScalar1 hcoreEncodeScalar2 hcoreEncodeZero8
  hcoreEncodeBytesRep8 hcoreEncodeBytesRep32 hcoreEncode_len_of_bytes_length
  hcoreEncodeNatBE32 hcoreWitnessGRegion from
  EvmAsm.Codegen.Programs.ValidateHeaderWholeWitness

def hcoreStatus1HeaderSpec : Header :=
  {hcoreWitnessHeaderSpec with number := 0}

def hcoreStatus1HeaderRlp : Bytes :=
  EvmAsm.EL.RLP.encode (headerToRlpItem hcoreStatus1HeaderSpec)

def hcoreStatus1HeaderStruct : Bytes :=
  headerCoreStructBytes hcoreStatus1HeaderSpec

private theorem encodeItems_appendP (xs ys : List EvmAsm.EL.RLP.RLPItem) :
    EvmAsm.EL.RLP.encode.encodeItems (xs ++ ys) =
      EvmAsm.EL.RLP.encode.encodeItems xs ++
        EvmAsm.EL.RLP.encode.encodeItems ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, EvmAsm.EL.RLP.encode.encodeItems,
        ih, List.append_assoc]

theorem hcoreStatus1Rlp_length : hcoreStatus1HeaderRlp.length = 645 := by
  let items : List EvmAsm.EL.RLP.RLPItem :=
    match headerToRlpItem hcoreStatus1HeaderSpec with
    | .list xs => xs
    | .bytes _ => []
  let pref : List EvmAsm.EL.RLP.RLPItem :=
    [.bytes hcoreStatus1HeaderSpec.parentHash,
     .bytes hcoreStatus1HeaderSpec.ommersHash,
     .bytes hcoreStatus1HeaderSpec.coinbase,
     .bytes hcoreStatus1HeaderSpec.stateRoot,
     .bytes hcoreStatus1HeaderSpec.transactionsRoot,
     .bytes hcoreStatus1HeaderSpec.receiptRoot,
     .bytes hcoreStatus1HeaderSpec.bloom,
     scalarItem hcoreStatus1HeaderSpec.difficulty]
  let suf : List EvmAsm.EL.RLP.RLPItem :=
    [scalarItem hcoreStatus1HeaderSpec.gasLimit,
     scalarItem hcoreStatus1HeaderSpec.gasUsed,
     scalarItem hcoreStatus1HeaderSpec.timestamp,
     .bytes hcoreStatus1HeaderSpec.extraData,
     .bytes hcoreStatus1HeaderSpec.prevRandao,
     .bytes hcoreStatus1HeaderSpec.nonce,
     scalarItem hcoreStatus1HeaderSpec.baseFeePerGas,
     .bytes hcoreStatus1HeaderSpec.withdrawalsRoot,
     scalarItem hcoreStatus1HeaderSpec.blobGasUsed,
     scalarItem hcoreStatus1HeaderSpec.excessBlobGas,
     .bytes hcoreStatus1HeaderSpec.parentBeaconBlockRoot,
     .bytes hcoreStatus1HeaderSpec.requestsHash,
     .bytes hcoreStatus1HeaderSpec.blockAccessListHash,
     scalarItem hcoreStatus1HeaderSpec.slotNumber]
  have hitems : (EvmAsm.EL.RLP.encode.encodeItems items).length = 642 := by
    have hdecomp : items = pref ++
        [.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 0)] ++ suf := by
      simp [items, pref, suf, hcoreStatus1HeaderSpec, hcoreWitnessHeaderSpec,
        headerToRlpItem, scalarItem, EvmAsm.EL.RLP.Nat.toBytesBE]
    rw [hdecomp]
    rw [encodeItems_appendP, encodeItems_appendP]
    simp only [EvmAsm.EL.RLP.encode.encodeItems, List.length_append]
    let oldItems : List EvmAsm.EL.RLP.RLPItem :=
      match headerToRlpItem hcoreWitnessHeaderSpec with
      | .list xs => xs
      | .bytes _ => []
    have holdDecomp : oldItems = pref ++
        [.bytes (EvmAsm.EL.RLP.Nat.toBytesBE 2)] ++ suf := by
      simp [oldItems, pref, suf, hcoreStatus1HeaderSpec, hcoreWitnessHeaderSpec,
        headerToRlpItem, scalarItem, EvmAsm.EL.RLP.Nat.toBytesBE]
    have holdLen : (EvmAsm.EL.RLP.encode.encodeItems oldItems).length = 642 := by
      simpa [oldItems, headerToRlpItem] using hcoreHeaderItems_length
    have holdLen' := holdLen
    rw [holdDecomp, encodeItems_appendP, encodeItems_appendP] at holdLen'
    simp only [EvmAsm.EL.RLP.encode.encodeItems, List.length_append] at holdLen'
    rw [hcoreEncodeScalar2] at holdLen'
    rw [hcoreEncodeScalar0]
    omega
  have hitem : headerToRlpItem hcoreStatus1HeaderSpec = .list items := by
    simp [items, headerToRlpItem, hcoreStatus1HeaderSpec, hcoreWitnessHeaderSpec,
      scalarItem]
  unfold hcoreStatus1HeaderRlp
  rw [hitem]
  exact hcoreEncodeList_length_642 items hitems

theorem hcoreStatus1_struct :
    headerCoreStructRelation hcoreStatus1HeaderStruct
      hcoreStatus1HeaderSpec := by
  refine ⟨?_, rfl⟩
  simp [hcoreStatus1HeaderStruct, hcoreStatus1HeaderSpec, headerCoreStructBytes,
    hcoreWitnessHeaderSpec, natToBytesBE_length, natToBytesLE_length]

theorem hcoreStatus1_decode :
    _decode_header hcoreStatus1HeaderRlp = .ok hcoreStatus1HeaderSpec := by
  apply decodeEncodedHeader hcoreStatus1HeaderSpec hcoreStatus1HeaderRlp rfl
  · rw [hcoreStatus1Rlp_length]
    decide
  · rfl
  · change numericFieldsOk (errorArmFields hcoreStatus1HeaderSpec) = true
    simp [numericFieldsOk, numericFieldWidths, getNChecked, decodeItemScalar,
      errorArmFields, hcoreStatus1HeaderSpec, hcoreWitnessHeaderSpec,
      EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD]
    all_goals decide
  · change bytesFieldsOk true (errorArmFields hcoreStatus1HeaderSpec) = true
    simp [bytesFieldsOk, fixedBytesFieldWidths, currentForkBytesFieldWidths,
      getBChecked, decodeItemFixedBytes, errorArmFields, hcoreStatus1HeaderSpec,
      hcoreWitnessHeaderSpec, natToBytesBE_length, List.all, List.getD]
    all_goals decide
  · simp [mkHeaderFields, errorArmFields, hcoreStatus1HeaderSpec,
      hcoreWitnessHeaderSpec, EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]

theorem hcoreStatus1_spec_reject :
    validate_header hcoreWitnessParentSpec hcoreStatus1HeaderSpec =
      .error (.invalidBlock "block number < 1") := by
  decide

/-- The status-1 exit post, with the route's register values baked in.  The
    core route leaves every register and stack cell at its entry value, so
    `o1 := raIn`, `o8 := header`, `o9 := headerLen`, `o18 := thisStruct`,
    `o19 := parentStructPtr`, `o20 := parentRlpPtr`, `o21 := parentRlpLen`. -/
def validateHeaderCoreStatus1Post
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (G : Assertion) : Assertion :=
  validateHeaderCorePost parentSpec headerSpec 1 spC raIn header headerLen thisStruct
    parentStructPtr parentRlpPtr parentRlpLen rawBytes parentRawBytes headerStruct parentStruct
    raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen G **
    (.x11 ↦ᵣ headerLen) ** (.x12 ↦ᵣ thisStruct) ** (.x13 ↦ᵣ parentStructPtr) **
    (.x14 ↦ᵣ parentRlpPtr) ** (.x15 ↦ᵣ parentRlpLen)

/-- Status-1 tail: `LI x10,1` @ `H+260`; `JAL x0` @ `H+264` to the epilogue
    seam `H+352`.  This is the `status1Exit` two-step block without the
    `vhEpi` epilogue (the hcore contract exits at `H+352`, not `raIn`). -/
theorem status1TailToSeam (oldStatus : Word) :
    cpsTripleWithin 2 (H + 260) (H + 352) callerCode
      ((.x10 ↦ᵣ oldStatus)) ((.x10 ↦ᵣ (1 : Word))) := by
  have s0 := li_spec_gen_within .x10 oldStatus (1 : Word) (H + 260) (by decide)
  have s1 := jal_x0_spec_gen_within
    (jalOff (GuestAddrs.validate_header + 352) (GuestAddrs.validate_header + 264)) (H + 264)
  rw [show (H + 264) + signExtend21
      (jalOff (GuestAddrs.validate_header + 352) (GuestAddrs.validate_header + 264)) = H + 352 from by
    change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 264 + _ =
      BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 352
    have hL : BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 264 =
        BitVec.ofNat 64 (GuestAddrs.validate_header + 264) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (by decide : GuestAddrs.validate_header + 264 < 2 ^ 64); omega
    have hR : BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 352 =
        BitVec.ofNat 64 (GuestAddrs.validate_header + 352) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (by decide : GuestAddrs.validate_header + 352 < 2 ^ 64); omega
    rw [hL, hR]
    exact jalOff_correct (GuestAddrs.validate_header + 352)
      (GuestAddrs.validate_header + 264) (by decide)] at s1
  have s0C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 260) prog 65 (.LI .x10 (1 : Word))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)) s0
  have s1C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 264) prog 66
      (.JAL .x0 (jalOff (GuestAddrs.validate_header + 352) (GuestAddrs.validate_header + 264)))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)) s1
  runBlock s0C s1C

/-- `BEQ x5,x0` @ `H+60` taken (number = 0) without naming `x0` in the
    assertion.  `x0` is hardwired zero (`RegFile.get_x0`), so the branch
    semantics do not depend on `R` owning `x0`; the contract pre
    `(validateHeaderCorePre ** (x5 ↦ o5))` does not own `x0`, so the route
    must not demand it either. -/
private theorem numberZeroBeq_taken_branch (number : Word) (hnum : number = 0) :
    cpsBranchWithin 1 (H + 60) (CodeReq.singleton (H + 60) (.BEQ .x5 .x0 numberZeroBrOff))
      (.x5 ↦ᵣ number)
      (H + 60 + signExtend13 numberZeroBrOff) (.x5 ↦ᵣ number)
      (H + 64) ((.x5 ↦ᵣ number) ** ⌜number ≠ 0⌝) := by
  intro R hR s hcr hPR hpc
  have hfetch : s.code s.pc = some (.BEQ .x5 .x0 numberZeroBrOff) := by
    rw [hpc]
    exact CodeReq.singleton_satisfiedBy.mp hcr
  have hr5 : s.getReg .x5 = number :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR)
  have hr0 : s.getReg .x0 = (0 : Word) := rfl
  have hstep' : step s = some (execInstrBr s (.BEQ .x5 .x0 numberZeroBrOff)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BEQ .x5 .x0 numberZeroBrOff) =
      s.setPC (s.pc + signExtend13 numberZeroBrOff) := by
    simp only [execInstrBr, hr5, hr0, hnum, beq_self_eq_true, ite_true]
  refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 numberZeroBrOff), ?_, Or.inl ⟨?_, ?_⟩⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']
    rfl
  · rw [hpc]
    rfl
  · have hpc_free : ((.x5 ↦ᵣ number) ** R).pcFree :=
      pcFree_sepConj (by pcFree) hR
    have hPR' := holdsFor_pcFree_setPC hpc_free
      (v := s.pc + signExtend13 numberZeroBrOff) hPR
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
    exact ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩

/-- `cpsTripleWithin` version of `numberZeroBeq_taken` over `callerCode`
    (`BEQ x5,x0` @ `H+60` taken, no `x0` atom). -/
private theorem numberZeroBeq_taken_noX0 (number : Word) (hnum : number = 0) :
    cpsTripleWithin 1 (H + 60) (H + 260) callerCode
      (.x5 ↦ᵣ number) (.x5 ↦ᵣ number) := by
  have hbr := numberZeroBeq_taken_branch number hnum
  rw [numberZeroBeq_taken_pc] at hbr
  have hbr' := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 60) prog 15 (.BEQ .x5 .x0 numberZeroBrOff)
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)) hbr
  exact cpsBranchWithin_takenPath hbr' (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hpure⟩ := hQf
    exact hpure.2 hnum)

/-- Status-1 route from the core entry (`H+56`) to the epilogue seam (`H+352`):
    `LD x5,x18+64`; `BEQ x5,x0` (taken); `LI x10,1`; `JAL x0`.  The post is
    the status-1 exit with entry register/stack values. -/
theorem validateHeaderCoreStatus1Route
    (spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o5 : Word) (G : Assertion) (hG : G.pcFree)
    (hrel : headerCoreStructRelation headerStruct headerSpec)
    (hlen : headerStruct.length = 144)
    (hnum0 : headerSpec.number = 0)
    (hrej : EvmAsm.Stateless.SpecRef.validate_header parentSpec headerSpec =
      .error (.invalidBlock "block number < 1")) :
    cpsTripleWithin 4 (H + 56) (H + 352) callerCode
      (validateHeaderCorePre parentSpec headerSpec spC raIn header headerLen
        rawBytes parentRawBytes thisStruct parentStructPtr parentRlpPtr parentRlpLen
        headerStruct parentStruct header headerLen thisStruct parentStructPtr parentRlpPtr
        parentRlpLen G **
        (.x5 ↦ᵣ o5))
      (validateHeaderCoreStatus1Post parentSpec headerSpec spC raIn header headerLen thisStruct
        parentStructPtr parentRlpPtr parentRlpLen rawBytes parentRawBytes headerStruct parentStruct
        G ** (.x5 ↦ᵣ (0 : Word))) := by
  have hresult : validateHeaderStatusResult parentSpec headerSpec (1 : Word) header rawBytes := by
    right; left; exact ⟨rfl, hrej⟩
  have hq : 8 * 8 < headerStruct.length := by rw [hlen]; norm_num
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegion_dword_at thisStruct headerStruct 8 hq
  have hfive := (headerCoreStructRelation_five_reads headerStruct headerSpec hrel).1
  have hval : Rv64.packBytes ((headerStruct.drop 64).take 8) = (0 : Word) := by
    rw [hfive, hnum0]
    decide
  have hof : BitVec.ofNat 64 (8 * 8) = (64 : Word) := by decide
  rw [hof, hval] at heq
  let framePures := ⌜rawBytes.length = headerLen ∧ parentRawBytes.length = parentRlpLen ∧
      _decode_header rawBytes = .ok headerSpec ∧ _decode_header parentRawBytes = .ok parentSpec ∧
      headerCoreStructRelation headerStruct headerSpec ∧
      headerCoreStructRelation parentStruct parentSpec⌝
  let stackCells : Assertion :=
    (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ header) ** ((spC + 16) ↦ₘ headerLen) **
      ((spC + 24) ↦ₘ thisStruct) ** ((spC + 32) ↦ₘ parentStructPtr) **
      ((spC + 40) ↦ₘ parentRlpPtr) ** ((spC + 48) ↦ₘ parentRlpLen)
  let memRegions : Assertion :=
    bytesRegion header rawBytes ** bytesRegion parentRlpPtr parentRawBytes **
      front ** rest ** bytesRegion parentStructPtr parentStruct
  let savedRegs : Assertion :=
    (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) **
      (.x19 ↦ᵣ parentStructPtr) ** (.x20 ↦ᵣ parentRlpPtr) ** (.x21 ↦ᵣ parentRlpLen) **
      (.x11 ↦ᵣ headerLen) ** (.x12 ↦ᵣ thisStruct) ** (.x13 ↦ᵣ parentStructPtr) **
      (.x14 ↦ᵣ parentRlpPtr) ** (.x15 ↦ᵣ parentRlpLen)
  let ambient1 : Assertion :=
    ((.x10 ↦ᵣ header) ** savedRegs ** stackCells **
      memRegions ** framePures ** G)
  have hpf1 : ambient1.pcFree := by
    unfold ambient1 savedRegs stackCells memRegions framePures
    repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs |
      exact pcFree_pure | exact bytesRegion_pcFree _ _ | exact hG | exact hf | exact hr
  have hld := ldNumber thisStruct o5 (0 : Word)
  have hldF := cpsTripleWithin_frameR ambient1 hpf1 hld
  let ambient2 : Assertion :=
    ((.x18 ↦ᵣ thisStruct) ** ((thisStruct + 64) ↦ₘ (0 : Word)) **
      (.x10 ↦ᵣ header) ** savedRegs ** stackCells ** memRegions ** framePures ** G)
  have hpf2 : ambient2.pcFree := by
    unfold ambient2 savedRegs stackCells memRegions framePures
    repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs |
      exact pcFree_pure | exact bytesRegion_pcFree _ _ | exact hG | exact hf | exact hr
  have hb := numberZeroBeq_taken_noX0 (0 : Word) rfl
  have hbF := cpsTripleWithin_frameR ambient2 hpf2 hb
  let ambient3 : Assertion :=
    ((.x18 ↦ᵣ thisStruct) ** ((thisStruct + 64) ↦ₘ (0 : Word)) **
      (.x5 ↦ᵣ (0 : Word)) **
      savedRegs ** stackCells ** memRegions ** framePures ** G)
  have hpf3 : ambient3.pcFree := by
    unfold ambient3 savedRegs stackCells memRegions framePures
    repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs |
      exact pcFree_pure | exact bytesRegion_pcFree _ _ | exact hG | exact hf | exact hr
  have htail := status1TailToSeam header
  have htailF := cpsTripleWithin_frameR ambient3 hpf3 htail
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hldF hbF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 htailF
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      unfold validateHeaderCorePre at hp
      unfold validateHeaderCoreFrame at hp
      simp only [ambient1, savedRegs, stackCells, memRegions, framePures] at hp ⊢
      rw [heq] at hp
      xperm_hyp hp)
    (fun _ hq => by
      unfold validateHeaderCoreStatus1Post validateHeaderCorePost
      unfold validateHeaderCoreFrame
      simp only [ambient3, savedRegs, stackCells, memRegions, framePures] at hq ⊢
      rw [heq]
      have hq' := (sepConj_pure_right _).2 ⟨hq, hresult⟩
      xperm_hyp hq')
    s2

/-- Drop the middle conjunct of a three-way separating conjunction at the
    `holdsFor` level: `(P ** Q ** R).holdsFor s` → `(P ** R).holdsFor s`. -/
private theorem holdsFor_sepConj_elim_mid {P Q R : Assertion} {s : MachineState}
    (h : (P ** Q ** R).holdsFor s) : (P ** R).holdsFor s := by
  obtain ⟨hp, hcompat, hP⟩ := h
  obtain ⟨h1, hQR, hd1, hunion1, hp1, hQRp⟩ := hP
  obtain ⟨h2, h3, hd2, hunion2, hq2, hr3⟩ := hQRp
  have h1c : h1.CompatibleWith s := by
    rw [← hunion1] at hcompat
    exact (PartialState.CompatibleWith_union hd1).mp hcompat |>.1
  have hQRc : hQR.CompatibleWith s := by
    rw [← hunion1] at hcompat
    exact (PartialState.CompatibleWith_union hd1).mp hcompat |>.2
  have h3c : h3.CompatibleWith s := by
    rw [← hunion2] at hQRc
    exact (PartialState.CompatibleWith_union hd2).mp hQRc |>.2
  have hd13 : h1.Disjoint h3 := by
    have hQR_eq : hQR = h2.union h3 := hunion2.symm
    rw [hQR_eq] at hd1
    have hcomm : h2.union h3 = h3.union h2 := PartialState.union_comm_of_disjoint hd2
    rw [hcomm] at hd1
    exact RiscvZkvm.Rv64.disjoint_left_of_disjoint_union_right hd1
  refine ⟨h1.union h3, ?_, ?_⟩
  · exact (PartialState.CompatibleWith_union hd13).mpr ⟨h1c, h3c⟩
  · exact ⟨h1, h3, hd13, rfl, hp1, hr3⟩

/-- A concrete satisfiability witness for `validateHeaderCoreContract`: the
    status-1 (number < 1) header route runs the core from `H+56` to the epilogue
    seam at `H+352` with exit status 1.  This discharges the contract at a
    concrete instance, completing the status-1 arm. -/
theorem validateHeaderCoreContract_hcoreStatus1_inhabited :
    validateHeaderCoreContract 4 callerCode
      hcoreWitnessParentSpec hcoreStatus1HeaderSpec
      hcoreWitnessSpC 0 errorArmHeaderPtr (BitVec.ofNat 64 hcoreStatus1HeaderRlp.length)
      hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      hcoreStatus1HeaderRlp hcoreWitnessParentRlpBytes
      hcoreStatus1HeaderStruct hcoreWitnessParentStruct
      0 0 errorArmHeaderPtr (BitVec.ofNat 64 hcoreStatus1HeaderRlp.length)
      hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) := by
  unfold validateHeaderCoreContract
  intro R hRfree s hcr hpre hpc
  have hroute := validateHeaderCoreStatus1Route
      hcoreWitnessSpC 0 errorArmHeaderPtr (BitVec.ofNat 64 hcoreStatus1HeaderRlp.length)
      hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      hcoreWitnessParentSpec hcoreStatus1HeaderSpec
      hcoreStatus1HeaderRlp hcoreWitnessParentRlpBytes
      hcoreStatus1HeaderStruct hcoreWitnessParentStruct
      (0 : Word) (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes)
      (bytesRegion_pcFree hcoreWitnessGAddr hcoreWitnessGBytes)
      hcoreStatus1_struct hcoreStatus1_struct.1 rfl hcoreStatus1_spec_reject
  rcases hroute R hRfree s hcr hpre hpc with ⟨k, hk, s', hstep, hpc', hpost⟩
  let Post := validateHeaderCorePost hcoreWitnessParentSpec hcoreStatus1HeaderSpec 1 hcoreWitnessSpC 0
      errorArmHeaderPtr (BitVec.ofNat 64 hcoreStatus1HeaderRlp.length)
      hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      hcoreStatus1HeaderRlp hcoreWitnessParentRlpBytes
      hcoreStatus1HeaderStruct hcoreWitnessParentStruct
      0 errorArmHeaderPtr (BitVec.ofNat 64 hcoreStatus1HeaderRlp.length)
      hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes)
  let Q1 := (.x11 ↦ᵣ (BitVec.ofNat 64 hcoreStatus1HeaderRlp.length)) **
    (.x12 ↦ᵣ hcoreWitnessParent) ** (.x13 ↦ᵣ hcoreWitnessParent2) **
    (.x14 ↦ᵣ hcoreWitnessParentRlp) **
    (.x15 ↦ᵣ (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length))
  have hpost0 : (((Post ** Q1) ** (.x5 ↦ᵣ (0 : Word))) ** R).holdsFor s' := by
    simpa [Post, Q1, validateHeaderCoreStatus1Post] using hpost
  have hpost1 : ((Post ** Q1) ** ((.x5 ↦ᵣ (0 : Word)) ** R)).holdsFor s' :=
    (holdsFor_sepConj_assoc (P := Post ** Q1) (Q := (.x5 ↦ᵣ (0 : Word))) (R := R)).mp hpost0
  have hpost2 : (Post ** (Q1 ** ((.x5 ↦ᵣ (0 : Word)) ** R))).holdsFor s' :=
    (holdsFor_sepConj_assoc (P := Post) (Q := Q1) (R := (.x5 ↦ᵣ (0 : Word)) ** R)).mp hpost1
  have hpost3 : (Post ** ((.x5 ↦ᵣ (0 : Word)) ** R)).holdsFor s' :=
    holdsFor_sepConj_elim_mid (P := Post) (Q := Q1) (R := (.x5 ↦ᵣ (0 : Word)) ** R) hpost2
  have hpostCore : (Post ** R).holdsFor s' :=
    holdsFor_sepConj_elim_mid (P := Post) (Q := (.x5 ↦ᵣ (0 : Word))) (R := R) hpost3
  refine ⟨k, hk, s', hstep, ?_⟩
  refine ⟨(H + 352, validateHeaderCorePost hcoreWitnessParentSpec
      hcoreStatus1HeaderSpec 1 hcoreWitnessSpC 0 errorArmHeaderPtr
      (BitVec.ofNat 64 hcoreStatus1HeaderRlp.length) hcoreWitnessParent hcoreWitnessParent2
      hcoreWitnessParentRlp (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      hcoreStatus1HeaderRlp hcoreWitnessParentRlpBytes
      hcoreStatus1HeaderStruct hcoreWitnessParentStruct
      0 errorArmHeaderPtr (BitVec.ofNat 64 hcoreStatus1HeaderRlp.length)
      hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes)), ?_, hpc', (by simpa [Post] using hpostCore)⟩
  simp [validateHeaderCoreExits]

#print axioms validateHeaderCoreContract_hcoreStatus1_inhabited