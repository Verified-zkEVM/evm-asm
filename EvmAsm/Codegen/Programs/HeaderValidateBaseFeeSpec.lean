/-
  EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpec

  K74 `header_validate_base_fee` (25 instructions): whole-routine
  `cpsTripleWithin`.  The wrapper calls K73 `eip1559_calc_base_fee_per_gas`
  (supplied as the `hcallee` hypothesis — the K73 family is `.partly`, so its
  general contract is a named remaining premise, the `hcore` pattern of
  `validate_header_cps_compose`), then compares the computed expected fee
  against the header's claimed base fee with the proven `u256_eq` leaf.

  The return postcondition is a three-way disjunction: `a0 = 0` match (header
  fee = the SpecRef EIP-1559 recurrence encoding), `a0 = 1` mismatch —
  attributed to the reference's `.invalidBlock "base fee mismatch"` (the
  "gas limit out of bounds" raise comes from the reference's earlier
  gas-limit check and is a different guest routine's status) — and `a0 = 2`,
  a guest-internal K73 failure status the unbounded reference never produces.
  The comparison is bytewise (the guest's own); for expected fees below 2^256
  it coincides with the reference's `Uint` comparison.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeRoutes
import EvmAsm.Codegen.Programs.U256EqSAsm
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.RegionMap
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Stateless.SpecRef.WideFeeArithmetic

namespace EvmAsm.Codegen.HeaderValidateBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec
open EvmAsm.Codegen.U256EqSAsm
open EvmAsm.Stateless.SpecRef

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact pcFree_regOwns _
      | exact pcFree_regAtomsOf _ _
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_frameSlotsOwn _ _
      | apply hvbfBrFrame_pcFree
      | apply hvbfArmFrame_pcFree
      | assumption)

/-! ## §1  Linked code: the wrapper, the K73 union, and `u256_eq` -/

/-- Linked base of `header_validate_base_fee`. -/
abbrev K : Word := (GuestAddrs.header_validate_base_fee : Word)

/-- The wrapper program (25 instructions; byte-identical to the emitted
    guest text by the drift guards in HeaderBaseFee.lean). -/
abbrev hvbfProg : List Instr := headerValidateBaseFee_prog

/-- The wrapper's own code requirement. -/
abbrev hvbfCode : CodeReq := CodeReq.ofProg K hvbfProg

/-- Linked base of `u256_eq`. -/
abbrev u256EqEntry : Word := (GuestAddrs.u256_eq : Word)

/-- The `u256_eq` code requirement at its linked address. -/
abbrev hvbfU256EqCode : CodeReq := CodeReq.ofProg u256EqEntry u256Eq_prog

/-- The 32-byte `.bss` scratch receiving the expected base fee
    (`hvbf_expected`, 0xa438a6a0). -/
abbrev hvbfScratchAddr : Word := (GuestAddrs.hvbf_expected : Word)

/-- The full code requirement: wrapper ∪ K73-with-callees ∪ `u256_eq`. -/
abbrev hvbfWholeCode : CodeReq :=
  CodeReq.unionAll [hvbfCode, wholeCode, hvbfU256EqCode]

/-- JAL displacement from the wrapper's instruction 9 to K73. -/
abbrev hvbfJalOffK73 : BitVec 21 :=
  jalOff GuestAddrs.eip1559_calc_base_fee_per_gas
    (GuestAddrs.header_validate_base_fee + 36)

/-- JAL displacement from the wrapper's instruction 14 to `u256_eq`. -/
abbrev hvbfJalOffEq : BitVec 21 :=
  jalOff GuestAddrs.u256_eq (GuestAddrs.header_validate_base_fee + 56)

/-- The `u256_eq` call's step count at this call site. -/
abbrev hvbfEqSteps (hdrFeePtr : Word) (hdrFeeBytes : List (BitVec 8)) (expected : Nat) : Nat :=
  (u256EqBody hdrFeePtr hvbfScratchAddr hdrFeeBytes
        (natToBytesBE 32 expected)).steps

/-- Scratch registers owned across the K73 call (its argument registers are
    pinned separately).  A `def` (not `abbrev`) so `xperm` keeps the
    `regOwns` block folded as a single atom. -/
def hvbfK73ScratchRegs : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x14, .x15, .x16, .x17]

/-- The registers peeled for the `u256_eq` call adapter: `exposedRegs` minus
    the two pinned argument registers `a0`/`a1`. -/
def hvbfEqPeelRegs : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Scratch registers owned after the K73 call (a1–a3 are clobbered by the
    callee): `exposedRegs` minus `a0`, presented as `a1` cons the
    `u256_eq`-peel list so the `la a1` step can split the block. -/
def hvbfScratchRegs : List Reg := .x11 :: hvbfEqPeelRegs

theorem hvbf_length : hvbfProg.length = 25 := by decide

theorem hvbf_prog_bound : 4 * hvbfProg.length < 2 ^ 64 := by
  rw [hvbf_length]; norm_num

/-- Per-instruction membership of the wrapper program in its `ofProg`. -/
theorem hvbf_mem (k : Nat) (ins : Instr) (A : Word)
    (hA : A = K + BitVec.ofNat 64 (4 * k))
    (hk : k < hvbfProg.length)
    (hins : hvbfProg[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → hvbfCode a = some i := by
  intro a i hi
  exact CodeReq.ofProg_mem_at K A hvbfProg k ins hA hk hins hvbf_prog_bound a i hi

private theorem hvbf_disj_k73whole : hvbfCode.Disjoint wholeCode := by
  simp only [wholeCode, CodeReq.unionAll_cons, CodeReq.unionAll_nil]
  repeat' first
    | (apply CodeReq.Disjoint.ofProg_ranges <;> decide)
    | apply CodeReq.Disjoint.union_right
    | apply CodeReq.Disjoint.empty_right

private theorem k73whole_disj_eq : wholeCode.Disjoint hvbfU256EqCode := by
  simp only [wholeCode, CodeReq.unionAll_cons, CodeReq.unionAll_nil]
  repeat' first
    | (apply CodeReq.Disjoint.ofProg_ranges <;> decide)
    | apply CodeReq.Disjoint.union_left
    | apply CodeReq.Disjoint.empty_left

private theorem hvbf_disj_eq : hvbfCode.Disjoint hvbfU256EqCode := by
  apply CodeReq.Disjoint.ofProg_ranges <;> decide

private theorem hvbf_whole_components_disjoint :
    ∀ j (hj : j < [hvbfCode, wholeCode, hvbfU256EqCode].length),
      ∀ k (hk : k < j),
        ([hvbfCode, wholeCode, hvbfU256EqCode].get ⟨k, Nat.lt_trans hk hj⟩).Disjoint
          ([hvbfCode, wholeCode, hvbfU256EqCode].get ⟨j, hj⟩) := by
  intro j hj k hk
  have hj3 : j < 3 := by simpa using hj
  have hk3 : k < 3 := lt_trans hk hj3
  interval_cases j <;> interval_cases k <;> simp_all [List.get]
  · exact hvbf_disj_k73whole
  · exact hvbf_disj_eq
  · exact k73whole_disj_eq

/-- The wrapper's code is contained in the union. -/
theorem hvbf_mono : ∀ a i, hvbfCode a = some i → hvbfWholeCode a = some i := by
  intro a i h
  exact CodeReq.mono_unionAll _ 0 (by decide) (fun j hj => by omega) a i h

/-- The K73 union (K73 + its six callees) is contained in the union. -/
theorem k73whole_mono : ∀ a i, wholeCode a = some i → hvbfWholeCode a = some i := by
  intro a i h
  exact CodeReq.mono_unionAll _ 1 (by decide)
    (fun j hj => hvbf_whole_components_disjoint 1 (by decide) j hj) a i h

/-- The `u256_eq` code is contained in the union. -/
theorem u256eq_mono : ∀ a i, hvbfU256EqCode a = some i → hvbfWholeCode a = some i := by
  intro a i h
  exact CodeReq.mono_unionAll _ 2 (by decide)
    (fun j hj => hvbf_whole_components_disjoint 2 (by decide) j hj) a i h

/-! ## §2  The expected fee and the reference-check attribution -/

/-- The expected base fee: the reference EIP-1559 recurrence
    (`SpecRef.baseFeeRecurrenceWide`, the pure content of
    `calculate_base_fee_per_gas` after its gas-limit check) at the parent values. -/
abbrev hvbfExpected (gasLimit gasUsed : Word) (parentFeeBytes : List (BitVec 8)) : Nat :=
  baseFeeRecurrenceWide gasUsed.toNat (gasLimit.toNat / 2) (bytesBEtoNat parentFeeBytes)

/-- The `u256_eq` return value at this call site: 1 iff the header fee bytes
    match the expected encoding. -/
abbrev hvbfEqResult (hdrFeeBytes : List (BitVec 8)) (expected : Nat) : Word :=
  if firstDiff hdrFeeBytes (natToBytesBE 32 expected) 32 = 32
          then (1 : Word) else (0 : Word)

/-- The bridge: when the reference's gas-limit check passes,
    `calculate_base_fee_per_gas` returns exactly the recurrence value. -/
theorem hvbf_bridge (blockGasLimit : Nat) (parentGasLimit parentGasUsed : Word)
    (parentFeeBytes : List (BitVec 8))
    (hcheck : check_gas_limit blockGasLimit parentGasLimit.toNat = true) :
    calculate_base_fee_per_gas blockGasLimit parentGasLimit.toNat parentGasUsed.toNat
        (bytesBEtoNat parentFeeBytes) =
      .ok (hvbfExpected parentGasLimit parentGasUsed parentFeeBytes) := by
  unfold calculate_base_fee_per_gas hvbfExpected baseFeeRecurrenceWide
    baseFeeIncreaseDelta baseFeeDecreaseDelta
  rw [hcheck]
  simp
  split
  · rfl
  · split <;> rfl

/-- The reference `validate_header` base-fee check, isolated: compute via
    `calculate_base_fee_per_gas` (propagating its gas-limit-check throw) and
    compare the 32-byte big-endian encodings (the guest's own operation;
    below 2^256 it coincides with the reference's `Uint` comparison). -/
def hvbfSpecRefBaseFeeCheck (blockGasLimit : Nat) (parentGasLimit parentGasUsed : Word)
    (parentFeeBytes hdrFeeBytes : List (BitVec 8)) : Except SpecError Unit :=
  match calculate_base_fee_per_gas blockGasLimit parentGasLimit.toNat
      parentGasUsed.toNat (bytesBEtoNat parentFeeBytes) with
  | .error e => .error e
  | .ok expected =>
      if natToBytesBE 32 expected = hdrFeeBytes then .ok ()
      else .error (.invalidBlock "base fee mismatch")

/-- Match arm: check passes and the claimed fee IS the expected encoding. -/
theorem hvbfSpecRefBaseFeeCheck_ok (blockGasLimit : Nat)
    (parentGasLimit parentGasUsed : Word)
    (parentFeeBytes hdrFeeBytes : List (BitVec 8))
    (hcheck : check_gas_limit blockGasLimit parentGasLimit.toNat = true)
    (hmatch : hdrFeeBytes =
        natToBytesBE 32 (hvbfExpected parentGasLimit parentGasUsed parentFeeBytes)) :
    hvbfSpecRefBaseFeeCheck blockGasLimit parentGasLimit parentGasUsed
        parentFeeBytes hdrFeeBytes = .ok () := by
  unfold hvbfSpecRefBaseFeeCheck
  rw [hvbf_bridge blockGasLimit parentGasLimit parentGasUsed parentFeeBytes hcheck]
  show (if natToBytesBE 32 (hvbfExpected parentGasLimit parentGasUsed parentFeeBytes) =
      hdrFeeBytes then Except.ok () else Except.error (SpecError.invalidBlock "base fee mismatch")) =
    Except.ok ()
  rw [if_pos hmatch.symm]

/-- Mismatch arm: check passes and the claimed fee differs — the reference
    raises `.invalidBlock "base fee mismatch"`. -/
theorem hvbfSpecRefBaseFeeCheck_mismatch (blockGasLimit : Nat)
    (parentGasLimit parentGasUsed : Word)
    (parentFeeBytes hdrFeeBytes : List (BitVec 8))
    (hcheck : check_gas_limit blockGasLimit parentGasLimit.toNat = true)
    (hne : hdrFeeBytes ≠
        natToBytesBE 32 (hvbfExpected parentGasLimit parentGasUsed parentFeeBytes)) :
    hvbfSpecRefBaseFeeCheck blockGasLimit parentGasLimit parentGasUsed
        parentFeeBytes hdrFeeBytes = .error (.invalidBlock "base fee mismatch") := by
  unfold hvbfSpecRefBaseFeeCheck
  rw [hvbf_bridge blockGasLimit parentGasLimit parentGasUsed parentFeeBytes hcheck]
  show (if natToBytesBE 32 (hvbfExpected parentGasLimit parentGasUsed parentFeeBytes) =
      hdrFeeBytes then Except.ok () else Except.error (SpecError.invalidBlock "base fee mismatch")) =
    Except.error (SpecError.invalidBlock "base fee mismatch")
  rw [if_neg (fun h => hne h.symm)]

/-- Forward direction of the `u256_eq` scan result: a full `n`-byte match
    means per-position agreement. -/
theorem hvbf_firstDiff_prefix {bs1 bs2 : List (BitVec 8)} :
    ∀ n, firstDiff bs1 bs2 n = n → ∀ j, j < n → bs1.getD j 0 = bs2.getD j 0 := by
  intro n
  induction n with
  | zero => intro _ j hj; omega
  | succ n ih =>
    intro h j hj
    rw [firstDiff_succ] at h
    by_cases hlt : firstDiff bs1 bs2 n < n
    · rw [if_pos hlt] at h
      have := firstDiff_le bs1 bs2 n
      omega
    · rw [if_neg hlt] at h
      by_cases hne : bs1.getD n 0 ≠ bs2.getD n 0
      · rw [if_pos hne] at h; omega
      · rw [if_neg hne] at h
        have hn : firstDiff bs1 bs2 n = n := by
          have := firstDiff_le bs1 bs2 n; omega
        by_cases hjn : j < n
        · exact ih hn j hjn
        · have hjeq : j = n := by omega
          subst hjeq
          exact not_not.mp hne

/-- A full scan match on 32-byte lists is list equality. -/
theorem hvbf_eq_of_firstDiff_eq {bs1 bs2 : List (BitVec 8)}
    (h1 : bs1.length = 32) (h2 : bs2.length = 32)
    (hfd : firstDiff bs1 bs2 32 = 32) : bs1 = bs2 :=
  DualReadByteScan.bytes_eq_of_prefix_eq bs1 bs2 32 h1 h2
    (hvbf_firstDiff_prefix 32 hfd)

/-- A partial scan match means the lists differ. -/
theorem hvbf_ne_of_firstDiff_ne {bs1 bs2 : List (BitVec 8)}
    (hfd : firstDiff bs1 bs2 32 ≠ 32) : bs1 ≠ bs2 := by
  intro heq
  subst heq
  exact hfd (firstDiff_all_eq _ _ _ (fun j _ => rfl))

/-! ## §3  Assertions: entry, the K73 call boundary, and the return post -/

/-- The wrapper's entry assertion: argument registers, owned scratch
    registers, the two owned frame cells, the callee stack frames (K73's and
    the multiply's below it), the input/scratch/accumulator regions, and `G`. -/
def hvbfPre (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (hdrFeeBytes parentFeeBytes scratchBytes accBytes : List (BitVec 8))
    (G : Assertion) : Assertion :=
  (.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ sp0) **
  (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
  (.x10 ↦ᵣ hdrFeePtr) ** (.x11 ↦ᵣ gasLimit) ** (.x12 ↦ᵣ gasUsed) **
  (.x13 ↦ᵣ parentFeePtr) **
  regOwns hvbfK73ScratchRegs ** (.x0 ↦ᵣ (0 : Word)) **
  memOwn spC ** memOwn (spC + 8) **
  frameSlotsOwn k73Frame spH **
  U256MulU64Be.frameSlots spM f0 f1 f2 f3 f4 f5 **
  bytesRegion hdrFeePtr hdrFeeBytes ** bytesRegion parentFeePtr parentFeeBytes **
  bytesRegion hvbfScratchAddr scratchBytes **
  bytesRegion U256MulU64Be.accBase accBytes ** G

/-- The K73 call-site precondition (after the argument shuffle, minus the
    `ra` pin `callWithin_spec` supplies): `a0 = gasLimit`, `a1 = gasUsed`,
    `a2 = parentFeePtr`, `a3 = hvbf_expected`; the saved `ra`/`s0` cells and
    the header-fee region ride at the end (the callee's frame `F`). -/
def hvbfK73CalleePre (spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (hdrFeeBytes parentFeeBytes scratchBytes accBytes : List (BitVec 8))
    (G : Assertion) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ hdrFeePtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
  (.x20 ↦ᵣ v20) **
  (.x10 ↦ᵣ gasLimit) ** (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ parentFeePtr) **
  (.x13 ↦ᵣ hvbfScratchAddr) **
  regOwns hvbfK73ScratchRegs ** (.x0 ↦ᵣ (0 : Word)) **
  frameSlotsOwn k73Frame spH **
  U256MulU64Be.frameSlots spM f0 f1 f2 f3 f4 f5 **
  bytesRegion parentFeePtr parentFeeBytes **
  bytesRegion hvbfScratchAddr scratchBytes **
  bytesRegion U256MulU64Be.accBase accBytes **
  (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** bytesRegion hdrFeePtr hdrFeeBytes ** G

/-- The K73 call-site postcondition: callee-saved registers restored (`s0`
    still the header-fee pointer), the status in `a0`, and the scratch
    holding the expected encoding on the success status. -/
def hvbfK73CalleePost (spC spH spM Ret hdrFeePtr parentFeePtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (expected : Nat) (G : Assertion) : Assertion := fun h =>
  ∃ (status : Word) (outBytes : List (BitVec 8))
    (g0 g1 g2 g3 g4 g5 : Word),
    (((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ hdrFeePtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
      (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ status) ** regOwns hvbfScratchRegs ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
      U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 ** bytesRegion parentFeePtr parentFeeBytes **
      bytesRegion hvbfScratchAddr outBytes ** bytesRegion U256MulU64Be.accBase accBytes **
      (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** bytesRegion hdrFeePtr hdrFeeBytes ** G) **
      ⌜(status = (0 : Word) → outBytes = natToBytesBE 32 expected) ∧
        outBytes.length = 32⌝) h

theorem hvbfK73CalleePre_pcFree (spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (hdrFeeBytes parentFeeBytes scratchBytes accBytes : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree) :
    (hvbfK73CalleePre spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
      v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
      hdrFeeBytes parentFeeBytes scratchBytes accBytes G).pcFree := by
  unfold hvbfK73CalleePre U256MulU64Be.frameSlots
  pcf

/-- The shared return state: callee-saved registers and `sp` restored, all
    callee memory accounted for. -/
def hvbfRetCommon (sp0 spC spH spM Ret hdrFeePtr parentFeePtr : Word)
    (v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (G : Assertion) : Assertion :=
  (.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) **
  (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
  regOwns hvbfScratchRegs ** (.x0 ↦ᵣ (0 : Word)) **
  (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) **
  frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
  U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 **
  bytesRegion hdrFeePtr hdrFeeBytes ** bytesRegion parentFeePtr parentFeeBytes **
  bytesRegion U256MulU64Be.accBase accBytes ** G

/-- Return disjunct state, status 0 (match). -/
def hvbfRetMatchState (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (G : Assertion) : Assertion :=
  hvbfRetCommon sp0 spC spH spM Ret hdrFeePtr parentFeePtr
    v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes accBytes G **
  (.x10 ↦ᵣ (0 : Word)) **
  bytesRegion hvbfScratchAddr
    (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes))

/-- Return disjunct, status 0 (match): the header fee bytes ARE the
    expected encoding, and the reference's base-fee check accepts. -/
def hvbfRetMatchPost (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (G : Assertion) : Assertion := fun h =>
  ∃ (g0 g1 g2 g3 g4 g5 : Word),
    (hvbfRetMatchState sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes accBytes G **
      ⌜hdrFeeBytes = natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes) ∧
        ∀ blockGasLimit : Nat,
          check_gas_limit blockGasLimit gasLimit.toNat = true →
          hvbfSpecRefBaseFeeCheck blockGasLimit gasLimit gasUsed parentFeeBytes
            hdrFeeBytes = .ok ()⌝) h

/-- Return disjunct state, status 1 (mismatch). -/
def hvbfRetMismatchState (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (G : Assertion) : Assertion :=
  hvbfRetCommon sp0 spC spH spM Ret hdrFeePtr parentFeePtr
    v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes accBytes G **
  (.x10 ↦ᵣ (1 : Word)) **
  bytesRegion hvbfScratchAddr
    (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes))

/-- Return disjunct, status 1 (mismatch): the reference raises
    `.invalidBlock "base fee mismatch"` (never "gas limit out of bounds" —
    that check runs earlier in the reference and is another routine's status). -/
def hvbfRetMismatchPost (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (G : Assertion) : Assertion := fun h =>
  ∃ (g0 g1 g2 g3 g4 g5 : Word),
    (hvbfRetMismatchState sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes accBytes G **
      ⌜hdrFeeBytes ≠ natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes) ∧
        ∀ blockGasLimit : Nat,
          check_gas_limit blockGasLimit gasLimit.toNat = true →
          hvbfSpecRefBaseFeeCheck blockGasLimit gasLimit gasUsed parentFeeBytes
            hdrFeeBytes = .error (.invalidBlock "base fee mismatch")⌝) h

/-- Return disjunct state, status 2 (K73 failure). -/
def hvbfRetK73FailState (sp0 spC spH spM Ret hdrFeePtr parentFeePtr : Word)
    (v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (outBytes : List (BitVec 8)) (G : Assertion) : Assertion :=
  hvbfRetCommon sp0 spC spH spM Ret hdrFeePtr parentFeePtr
    v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes accBytes G **
  (.x10 ↦ᵣ (2 : Word)) **
  bytesRegion hvbfScratchAddr outBytes

/-- Return disjunct, status 2: the K73 compute step failed
    (guest-internal; the reference's unbounded arithmetic never fails here). -/
def hvbfRetK73FailPost (sp0 spC spH spM Ret hdrFeePtr parentFeePtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (G : Assertion) : Assertion := fun h =>
  ∃ (g0 g1 g2 g3 g4 g5 : Word) (outBytes : List (BitVec 8)) (k73status : Word),
    (hvbfRetK73FailState sp0 spC spH spM Ret hdrFeePtr parentFeePtr
        v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes accBytes
        outBytes G ** ⌜k73status ≠ (0 : Word) ∧ outBytes.length = 32⌝) h

/-- The whole-routine return postcondition: one disjunct per outcome. -/
def hvbfRetPost (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (G : Assertion) : Assertion := fun h =>
  (hvbfRetMatchPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
      v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) h ∨
  (hvbfRetMismatchPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
      v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) h ∨
  (hvbfRetK73FailPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr
      v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) h

/-- The two `u256_eq`-outcome disjuncts (the `beq` merge post). -/
def hvbfEqPost (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (G : Assertion) : Assertion := fun h =>
  (hvbfRetMatchPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
      v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) h ∨
  (hvbfRetMismatchPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
      v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) h

/-! ## §4  Small assertion-algebra helpers -/

/-- Pull one existential out of a right conjunct. -/
theorem hvbf_sepConj_exists_right {α : Sort _} (A : Assertion) (B : α → Assertion) :
    ∀ h, (A ** (fun h => ∃ x, B x h)) h → (fun h => ∃ x, (A ** B x) h) h := by
  intro h hp
  obtain ⟨g0, g1, d, u, hA, ⟨x, hB⟩⟩ := hp
  exact ⟨x, g0, g1, d, u, hA, hB⟩

/-- Move a trailing pure conjunct to the front past one conjunct. -/
theorem hvbf_pure_pull_last {A B : Assertion} {f : Prop} :
    ∀ h, (A ** (B ** ⌜f⌝)) h → (⌜f⌝ ** (A ** B)) h := by
  intro h hp
  obtain ⟨g0, g1, d, u, hA, hrest⟩ := hp
  obtain ⟨hB, hf⟩ := (sepConj_pure_right _).1 hrest
  exact (sepConj_pure_left _).2 ⟨hf, g0, g1, d, u, hA, hB⟩

/-- Move a pure conjunct sitting third in a framed branch post to the front
    (for `cpsTripleWithin_pure_pre`, which wants the pure first). -/
theorem hvbf_pure_pull_branch {A B F : Assertion} {f : Prop} :
    ∀ h, ((A ** (B ** ⌜f⌝)) ** F) h → (⌜f⌝ ** ((A ** B) ** F)) h := by
  intro h hp
  obtain ⟨g0, g1, d01, u01, hX, hF⟩ := hp
  obtain ⟨g2, g3, d23, u23, hA, hfF⟩ := hX
  obtain ⟨hB, hf⟩ := (sepConj_pure_right _).1 hfF
  have hd : (g2.union g3).Disjoint g1 := by rw [u23]; exact d01
  have hu : (g2.union g3).union g1 = h := by rw [u23]; exact u01
  exact (sepConj_pure_left _).2 ⟨hf, g2.union g3, g1, hd, hu,
    ⟨g2, g3, d23, rfl, hA, hB⟩, hF⟩

/-- `exposedRegs` with the two pinned argument registers split out (the
    `u256_eq` call adapter's valuation shape). -/
theorem hvbf_exposedRegs_split (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regAtomsOf vf hvbfEqPeelRegs) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [hvbfEqPeelRegs, regAtomsOf_cons, regAtomsOf_nil]
  xperm

/-- `exposedRegs` with only `a0` split out (the post-call shape). -/
theorem hvbf_exposedRegs_split_post (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf hvbfScratchRegs) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [hvbfScratchRegs, hvbfEqPeelRegs, regAtomsOf_cons, regAtomsOf_nil,
    sepConj_emp_right']
  xperm

theorem hvbf_x10_notin_peel : (.x10 : Reg) ∉ hvbfEqPeelRegs := by decide
theorem hvbf_x11_notin_peel : (.x11 : Reg) ∉ hvbfEqPeelRegs := by decide
end EvmAsm.Codegen.HeaderValidateBaseFeeSpec
