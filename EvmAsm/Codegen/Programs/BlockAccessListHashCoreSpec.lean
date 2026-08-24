/-
  EvmAsm.Codegen.Programs.BlockAccessListHashCoreSpec

  Whole-routine contract for `block_access_list_hash_core`: the six-instruction
  caller frame around `zkvm_keccak256`.

  ## Why this is a separate module from `BlockHashFromHeaderSpec`

  `blockAccessListHashCore_prog` and `blockHashFromHeader_prog` are the SAME six
  instructions modulo the `jalOff` displacement, which differs because the two
  routines sit at different linked addresses. The displacement is baked into the
  `Program` literal, so neither theorem can be instantiated at the other's base:
  the `CodeReq` is `CodeReq.ofProg` of a *different* instruction list. This is
  the guest-image claim, so the duplication is the point -- a single generic
  theorem would be a statement about a model, not about either linked routine.
-/

import EvmAsm.Codegen.Programs.BlockAccessListHash
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTop
import EvmAsm.Codegen.Proofs.HashBridgeKeccakBridge
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.TwoExitLoop

namespace EvmAsm.Codegen.BlockAccessListHashCoreSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs

abbrev B : Word := (GuestAddrs.block_access_list_hash_core : Word)
abbrev K : Word := (GuestAddrs.zkvm_keccak256 : Word)
abbrev wrapperCode : CodeReq := CodeReq.ofProg B blockAccessListHashCore_prog
abbrev keccakCode : CodeReq := CodeReq.ofProg K zkvmKeccak256_prog
abbrev fullCode : CodeReq := wrapperCode.union keccakCode

theorem wrapper_length : blockAccessListHashCore_prog.length = 6 := by decide

theorem wrapper_mem : ∀ a i,
    wrapperCode a = some i → fullCode a = some i := by
  intro a i h
  exact CodeReq.union_mono_left a i h

theorem keccak_mem : ∀ a i,
    keccakCode a = some i → fullCode a = some i := by
  intro a i h
  exact CodeReq.mono_union_right
    (CodeReq.Disjoint.ofProg_ranges B K blockAccessListHashCore_prog
      zkvmKeccak256_prog
      (by rw [wrapper_length]; decide)
      (by decide)
      (by rw [wrapper_length]; decide))
    (fun _ _ h => h) a i h

theorem call_mem : ∀ a i,
    CodeReq.singleton (B + 8) (.JAL .x1
      (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.block_access_list_hash_core + 8))) a = some i →
      fullCode a = some i := by
  intro a i h
  have hw : wrapperCode a = some i := by
    exact CodeReq.ofProg_mem_at B (B + 8) blockAccessListHashCore_prog 2
      (.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.block_access_list_hash_core + 8)))
      (by decide) (by rw [wrapper_length]; decide) rfl (by rw [wrapper_length]; decide) a i h
  exact wrapper_mem a i hw

theorem stackFree4_eq_keccakFrameSlotsOwn (sp : Word) :
    stackFree sp 4 =
      frameSlotsOwn keccakFrame (sp + signExtend12 (-32 : BitVec 12)) := by
  show (memOwn (sp - BitVec.ofNat 64 (8 * 4)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 3)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 2)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 1)) ** empAssertion) = _
  show _ = (memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (8 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (16 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (24 : BitVec 12)) ** empAssertion)
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show sp - BitVec.ofNat 64 (8 * 4) = sp + (-32 : Word) + (0 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 3) = sp + (-32 : Word) + (8 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 2) = sp + (-32 : Word) + (16 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 1) = sp + (-32 : Word) + (24 : Word) from by bv_omega]

set_option maxRecDepth 8000 in
theorem block_access_list_hash_core_spec_within
    (sp0 ret inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (v8 v9 v18 v20 v28 v29 : Word)
    (os : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : input.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor inputBase N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor inputBase N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor inputBase N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (6 + (5 + keccakBodyFuel N rem + 6)) B ret fullCode
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        memOwn (sp0 + signExtend12 (-16 : BitVec 12)) **
        stackFree (sp0 + signExtend12 (-16 : BitVec 12)) 4 **
        regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
        keccakCallerPre inputBase (BitVec.ofNat 64 input.length) outputBase
          v28 v29 os input (List.replicate 32 (0 : BitVec 8)) A)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        ((sp0 + signExtend12 (-16 : BitVec 12)) ↦ₘ ret) **
        frameSlotsSaved keccakFrame
          (sp0 + signExtend12 (-16 : BitVec 12) +
            signExtend12 (-32 : BitVec 12))
          (keccakEntryVals v8 v9 v18 v20) **
        regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
        keccakCallerPost inputBase outputBase input N rem A) := by
  let spC := sp0 + signExtend12 (-16 : BitVec 12)
  let out0 := List.replicate 32 (0 : BitVec 8)
  have hcallee := zkvm_keccak256_spec_within spC (B + 12)
    inputBase outputBase input N rem v8 v9 v18 v20 v28 v29 os A hA
    (by decide) hlen hrem_le hos halign_zk hover hNbound hrem64 hb8i hovers hoveri
    hvalids hvalidi hvalidRem hvalid135 hvalidMem
  have hcallee' :
      cpsTripleWithin (5 + keccakBodyFuel N rem + 6) K (B + 12) keccakCode
        ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (B + 12)) **
          regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
          frameSlotsOwn keccakFrame
            (spC + signExtend12 (-32 : BitVec 12)) **
          keccakCallerPre inputBase (BitVec.ofNat 64 input.length) outputBase
            v28 v29 os input out0 A)
        ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (B + 12)) **
          regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
          frameSlotsSaved keccakFrame
            (spC + signExtend12 (-32 : BitVec 12))
            (keccakEntryVals v8 v9 v18 v20) **
          keccakCallerPost inputBase outputBase input N rem A) := by
    rw [← hlen] at hcallee
    simpa [B, K, keccakCode, spC, out0] using hcallee
  rw [← stackFree4_eq_keccakFrameSlotsOwn spC] at hcallee'
  have hcalleeFull :
      cpsTripleWithin (5 + keccakBodyFuel N rem + 6) K (B + 12) fullCode
        ((.x1 ↦ᵣ (B + 12)) ** (.x2 ↦ᵣ spC) **
          (stackFree spC 4 **
            regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
            keccakCallerPre inputBase (BitVec.ofNat 64 input.length) outputBase
              v28 v29 os input out0 A))
        ((.x1 ↦ᵣ (B + 12)) ** (.x2 ↦ᵣ spC) **
          (frameSlotsSaved keccakFrame
              (spC + signExtend12 (-32 : BitVec 12))
              (keccakEntryVals v8 v9 v18 v20) **
            regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
            keccakCallerPost inputBase outputBase input N rem A)) := by
    have h := cpsTripleWithin_extend_code keccak_mem hcallee'
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h
  have hcallPc : B + 8 + (4 : Word) = B + 12 := by bv_omega
  have hcall := abiFrameCall_spec (cr := fullCode)
    (calleePre := stackFree spC 4 **
      regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPre inputBase (BitVec.ofNat 64 input.length) outputBase
        v28 v29 os input out0 A)
    (calleePost := frameSlotsSaved keccakFrame
        (spC + signExtend12 (-32 : BitVec 12))
        (keccakEntryVals v8 v9 v18 v20) **
      regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPost inputBase outputBase input N rem A)
    (F := frameSlotsSaved [(.x1, (0 : BitVec 12))] spC
      (fun r => if r = .x1 then ret else 0)) (B + 8) K ret spC
    (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.block_access_list_hash_core + 8))
    0 (5 + keccakBodyFuel N rem + 6)
    (by decide)
    call_mem
    (pcFree_sepConj (pcFree_stackFree _ _)
      (pcFree_sepConj
        (pcFree_regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20))
        (keccakCallerPre_pcFree inputBase
          (BitVec.ofNat 64 input.length) outputBase v28 v29 os input out0 A hA)))
    (pcFree_frameSlotsSaved _ _ _)
    (by
      simpa only [hcallPc, stackFree_zero, sepConj_emp_left', sepConj_emp_right']
        using hcalleeFull)
  simp only [stackFree_zero, sepConj_emp_left'] at hcall
  rw [hcallPc] at hcall
  have hpreF : (stackFree spC 4 **
      regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPre inputBase (BitVec.ofNat 64 input.length) outputBase
        v28 v29 os input out0 A).pcFree := by
    exact pcFree_sepConj (pcFree_stackFree _ _)
      (pcFree_sepConj
        (pcFree_regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20))
        (keccakCallerPre_pcFree inputBase
          (BitVec.ofNat 64 input.length) outputBase v28 v29 os input out0 A hA))
  have hpostF : (frameSlotsSaved keccakFrame
      (spC + signExtend12 (-32 : BitVec 12))
      (keccakEntryVals v8 v9 v18 v20) **
      regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPost inputBase outputBase input N rem A).pcFree := by
    exact pcFree_sepConj (pcFree_frameSlotsSaved _ _ _)
      (pcFree_sepConj
        (pcFree_regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20))
        (keccakCallerPost_pcFree inputBase outputBase input N rem A hA))
  have hprogBound :
      4 * (abiFrameProg (-16 : BitVec 12) (16 : BitVec 12)
        [(.x1, (0 : BitVec 12))]
        [.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256
          (GuestAddrs.block_access_list_hash_core + 8))]).length < 2 ^ 64 := by
    norm_num [abiFrameProg, framePrologue, frameEpilogue, storeProg, loadProg]
  have hframe := abiFrame_spec_own B sp0 ret
    (-16 : BitVec 12) (16 : BitVec 12) [(.x1, (0 : BitVec 12))] 0 []
    (fun r => if r = .x1 then ret else 0)
    [.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.block_access_list_hash_core + 8))]
    (1 + (5 + keccakBodyFuel N rem + 6))
    (stackFree spC 4 ** regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPre inputBase (BitVec.ofNat 64 input.length) outputBase
        v28 v29 os input out0 A)
    (frameSlotsSaved keccakFrame
        (spC + signExtend12 (-32 : BitVec 12))
        (keccakEntryVals v8 v9 v18 v20) **
          regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPost inputBase outputBase input N rem A)
    fullCode rfl (by decide) (by decide) hprogBound (by simp)
    halign_ret (by
      have hneg : signExtend12 (-16 : BitVec 12) = BitVec.ofInt 64 (-16) := by decide
      have hpos : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
      rw [hneg, hpos, BitVec.add_assoc]
      bv_omega) hpreF hpostF
    (by
      intro a i h
      exact wrapper_mem a i h)
    (by
      refine cpsTripleWithin_weaken (fun _ hp => by
        simp [spC, regsAt, frameSlotsSaved, List.foldr, sepConj_emp_right'] at hp ⊢
        xperm_hyp hp) ?_ hcall
      intro a hq
      have hq1 :
          ((.x1 ↦ᵣ (B + 12)) **
            ((.x2 ↦ᵣ spC) **
              (frameSlotsSaved [(.x1, (0 : BitVec 12))] spC
                (fun r => if r = .x1 then ret else 0) **
                frameSlotsSaved keccakFrame
                  (spC + signExtend12 (-32 : BitVec 12))
                  (keccakEntryVals v8 v9 v18 v20) **
                regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
                keccakCallerPost inputBase outputBase input N rem A))) a := by
        xperm_hyp hq
      have hq2 := sepConj_mono_left
        (regIs_to_regOwn .x1 (B + 12)) a hq1
      have hq3 :
          ((.x2 ↦ᵣ spC) ** regOwn .x1 **
        (frameSlotsSaved [(.x1, (0 : BitVec 12))] spC
          (fun r => if r = .x1 then ret else 0) **
          frameSlotsSaved keccakFrame
            (spC + signExtend12 (-32 : BitVec 12))
            (keccakEntryVals v8 v9 v18 v20) **
          regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
          keccakCallerPost inputBase outputBase input N rem A)) a := by
        xperm_hyp hq2
      simpa [spC, regsOwnAt, regsAt, frameSlotsSaved, List.foldr,
        sepConj_emp_right'] using hq3)
  have hframeOwn :
      frameSlotsOwn [(.x1, (0 : BitVec 12))] spC = memOwn spC := by
    simp only [frameSlotsOwn, List.foldr, sepConj_emp_right']
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    exact congrArg memOwn (BitVec.add_zero spC)
  have hframeSaved :
      frameSlotsSaved [(.x1, (0 : BitVec 12))] spC
        (fun r => if r = .x1 then ret else 0) = (spC ↦ₘ ret) := by
    simp only [frameSlotsSaved, List.foldr, sepConj_emp_right']
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    simp
  rw [hframeOwn, hframeSaved] at hframe
  have hsteps :
      1 + [(Reg.x1, (0 : BitVec 12))].length +
          (1 + (5 + keccakBodyFuel N rem + 6)) +
          [(Reg.x1, (0 : BitVec 12))].length + 1 + 1 =
        6 + (5 + keccakBodyFuel N rem + 6) := by
    simp
    omega
  rw [hsteps] at hframe
  simpa [spC, out0, blockAccessListHashCore_prog, abiFrameProg, framePrologue,
    frameEpilogue, regsAt, regsOwnAt, stackFree, keccakEntryVals,
    sepConj_emp_right'] using hframe


/-! ## Non-vacuity of the hypothesis bundle

    `block_access_list_hash_core_spec_within` carries the `zkvm_keccak256`
    resource bundle verbatim. Every one of those hypotheses is a
    resource/ABI fact, so the row is `.proven` — but "resource/ABI only" is a
    claim that has to be checked in both directions, and neither direction is
    readable from the tier constructor:

    * the bundle must be **satisfiable**, otherwise the triple says nothing;
    * the bundle must not be **trivially true**, otherwise "no input-domain
      gate" would be a statement about a vacuous restriction rather than about
      the routine's totality.

    The two theorems below are that pair. `…_reachable` exhibits a concrete
    witness for the input-dependent half; `…_negative_control` exhibits an
    instantiation at which the *same* conjunct is provably FALSE, so the
    reachability result is not an artefact of a hypothesis nothing can fail. -/

/-- A concrete 4-byte BAL payload in the writable RAM zone, at an 8-aligned
    base. Any nonempty byte list works; this one is short enough that the
    `rem`-indexed side conditions are `decide`-checkable. -/
private def balSampleInput : List (BitVec 8) := [0xc3, 0x82, 0x01, 0x02]

private def balSampleBase : Word := (0xa0000000 : Word)

/-- ⭐ **The input-dependent hypotheses of the wrapper triple are satisfiable.**
    `N = 0`, `rem = 4` at an aligned RAM base discharges the length partition,
    the absorb-cursor alignment, and every `rem`-indexed overflow/validity
    obligation — on a byte string that is genuinely nonempty. -/
theorem blockAccessListHashCore_precondition_reachable :
    ∃ (inputBase : Word) (input : List (BitVec 8)) (N rem : Nat),
      input ≠ [] ∧
      input.length = keccakAbsorbStep * N + rem ∧
      rem ≤ 135 ∧
      keccakAbsorbStep * N + rem < 2 ^ 63 ∧
      rem < 2 ^ 64 ∧
      (keccakAbsorbCursor inputBase N).toNat % 8 = 0 ∧
      (∀ n, n < rem →
        (keccakAbsorbCursor inputBase N).toNat + (rem - (n + 1)) < 2 ^ 64) ∧
      (∀ n, n < rem →
        isValidByteAccess
          (keccakAbsorbCursor inputBase N + BitVec.ofNat 64 (rem - (n + 1)))
          = true) := by
  refine ⟨balSampleBase, balSampleInput, 0, 4, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_, ?_⟩
  · intro n hn
    interval_cases n <;> decide
  · intro n hn
    interval_cases n <;> decide

/-- ⛔ **Negative control.** The absorb-cursor alignment conjunct used above is
    a real constraint, not a tautology: one byte past the sample base it is
    provably false. A bundle that could not fail here would make the
    reachability theorem meaningless. -/
theorem blockAccessListHashCore_precondition_negative_control :
    ¬ ((keccakAbsorbCursor (0xa0000001 : Word) 0).toNat % 8 = 0) := by decide

/-- ⛔ **Second negative control**, on the byte-validity conjunct: an address
    outside all three memory zones fails `isValidByteAccess`, so the
    `hvalidi` family is not vacuously true either. -/
theorem blockAccessListHashCore_validity_negative_control :
    isValidByteAccess (keccakAbsorbCursor (0x90000000 : Word) 0) = false := by
  decide

/-- The fixed-resource half of the bundle — the `zk3_state` scratch arena — is
    a closed decidable fact about the linked image, recorded here so the row's
    "resource/ABI only" claim is checked rather than asserted. -/
theorem blockAccessListHashCore_zk3_state_resources :
    (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0 ∧
    (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64 ∧
    isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true := by
  decide
