/-
Native-shaped multiply callee contract at the K73 callsite (#12346 residual 2b,
coord ruling option ii, 2026-08-27).

DEFECT BEING REPAIRED (class (b) of #12851 family: ownership conflated with
value).  The seam family around here (`k73_decrease_mul_call_spec_within`,
`k73_decrease_entry_mul_status_spec_within`, their increase twins) carries the
multiply callee obligation as ONE symmetric pair of list parameters, so its
premise pins the initial accumulator/output windows and its conclusion pins the
same lists again as final content.  Bound against the deployed
`mulWhole_spec`, that forces `initOut = copyState M initOut 32` - false for
symbolic callers because `bytesRegion` pins content.  The existing mechanism
only ever worked at concrete witnesses (see WholeRoutes :1085, discharging by
definitional reduction of literal lists, and WholeSpec :396, which merely
respells the symmetric statement without discharging it).

THE FIX: pre OWNS the initial windows (content = whatever caller-supplied
scratch lists say); post PINS the computed images (`mulState` accumulator,
`copyState` output).  This REMOVES the hidden initial-content-equals-final-image
precondition rather than adding any, satisfying the standing rule that callee
instantiation adds no new preconditions.
-/
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeSpec
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeEntry
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecCore

namespace EvmAsm.Codegen.HeaderValidateBaseFeeMulNativeContract

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec

/-- Generic native-shaped multiply call frame: the callee obligation arrives
with SEPARATE initial-window lists (`accWin` / `outWin`, owned by the caller
through the premise) and final-image lists (`accImg` / `outImg`, pinned by the
callee's honest conclusion).  Everything else mirrors
`k73_mul_call_spec_within` (WholeSpec :294) positionally; the post conversion
reuses `k73_mul_body_post_factor`, which is name-blind, at the image lists. -/
theorem k73_mul_call_native_spec_within
    {cr : CodeReq} {n : Nat}
    (callerPC calleeEntry oldRa spOld spNew v8 v9 v18 v19 v20 aPtr b outPtr v13 : Word)
    (offset : BitVec 21) (F : Assertion) (hF : F.pcFree)
    (f0 f1 f2 f3 f4 f5 : Word)
    (aBytes accWin outWin accImg outImg : List (BitVec 8))
    (hcallee : cpsTripleWithin n calleeEntry (callerPC + 4) mulCode
      (EvmAsm.Codegen.U256MulU64Be.mulWholePre F spOld (callerPC + 4)
        v8 v9 v18 v19 v20 aPtr b outPtr v13 f0 f1 f2 f3 f4 f5
        aBytes accWin outWin)
      (EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost spNew (callerPC + 4)
        v8 v9 v18 v19 v20 aPtr b outPtr aBytes accImg outImg ** F))
    (htarget : callerPC + signExtend21 offset = calleeEntry)
    (hmem : ∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
      cr a = some i)
    (hcalleeMem : ∀ a i, mulCode a = some i → cr a = some i) :
    cpsTripleWithin (1 + n) callerPC (callerPC + 4) cr
      (((.x1 ↦ᵣ oldRa) **
        k73MulPreNoRa spOld v8 v9 v18 v19 v20 aPtr b outPtr v13
          f0 f1 f2 f3 f4 f5 aBytes accWin outWin F))
      (((.x1 ↦ᵣ (callerPC + 4)) **
        (k73MulBodyPostNoRa spNew (callerPC + 4) v8 v9 v18 v19 v20
          aPtr b outPtr aBytes accImg outImg ** F))) := by
  have hcalleeC := cpsTripleWithin_extend_code hcalleeMem hcallee
  have hcallee' : cpsTripleWithin n calleeEntry (callerPC + 4) cr
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        k73MulPreNoRa spOld v8 v9 v18 v19 v20 aPtr b outPtr v13
          f0 f1 f2 f3 f4 f5 aBytes accWin outWin F)
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        (k73MulBodyPostNoRa spNew (callerPC + 4) v8 v9 v18 v19 v20
          aPtr b outPtr aBytes accImg outImg ** F)) := by
    refine cpsTripleWithin_weaken (nSteps := n) (entry := calleeEntry)
      (exit_ := callerPC + 4) (cr := cr)
      (P := EvmAsm.Codegen.U256MulU64Be.mulWholePre F spOld (callerPC + 4)
        v8 v9 v18 v19 v20 aPtr b outPtr v13 f0 f1 f2 f3 f4 f5
        aBytes accWin outWin)
      (P' := ((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        k73MulPreNoRa spOld v8 v9 v18 v19 v20 aPtr b outPtr v13
          f0 f1 f2 f3 f4 f5 aBytes accWin outWin F)
      (Q := EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost spNew (callerPC + 4)
        v8 v9 v18 v19 v20 aPtr b outPtr aBytes accImg outImg ** F)
      (Q' := ((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        (k73MulBodyPostNoRa spNew (callerPC + 4) v8 v9 v18 v19 v20
          aPtr b outPtr aBytes accImg outImg ** F))
      ?_ ?_ hcalleeC
    · intro h hp
      dsimp [EvmAsm.Codegen.U256MulU64Be.mulWholePre, k73MulPreNoRa] at hp ⊢
      xperm_hyp hp
    · intro s hq
      exact k73_mul_body_post_factor spNew (callerPC + 4) v8 v9 v18 v19 v20
        aPtr b outPtr aBytes accImg outImg F s hq
  have hP : (k73MulPreNoRa spOld v8 v9 v18 v19 v20
      aPtr b outPtr v13 f0 f1 f2 f3 f4 f5 aBytes accWin outWin F).pcFree := by
    dsimp [k73MulPreNoRa]
    pcf
    exact hF
  exact callWithin_spec callerPC calleeEntry oldRa offset n
    htarget hmem hP hcallee'

open EvmAsm.Codegen.U256MulU64Be in
/-- Decrease-route multiply call-and-status stage over the NATIVE callee
shape.  Positionally a clone of `k73_decrease_mul_status_branch_spec_within`
(WholeEntry :520); the single difference is the callee obligation, now split
into owned initial windows (`accWin` / `outWin`) and computed final images
(`mulState` accumulator, `copyState` output).  Both branch exits pin the
downstream state at the image lists, which is the machine-honest threading
the divider seams continue from. -/
theorem k73_mul_status_branch_native_spec_within
    (spH raIn target delta basePtr outPtr v8 v9 v18 v19Saved v20Saved : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accWin outWin : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (EvmAsm.Codegen.U256MulU64Be.mulWholePre
        (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** G)
        spH (K73 + 88) basePtr outPtr target delta (0 : Word)
        basePtr delta outPtr outPtr f0 f1 f2 f3 f4 f5
        baseBytes accWin outWin)
      (EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target delta (0 : Word)
        basePtr delta outPtr baseBytes
        (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
        (EvmAsm.Codegen.U256MulU64Be.copyState
          (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32) outWin 32) **
        (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** G))) :
    cpsBranchWithin 3852 (K73 + 84) wholeCode
      (((.x1 : Reg) ↦ᵣ raIn) **
        k73MulPreNoRa spH basePtr outPtr target delta (0 : Word)
          basePtr delta outPtr outPtr f0 f1 f2 f3 f4 f5
          baseBytes accWin outWin
          (frameSlotsSaved k73Frame spH
            (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** G))
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest spH raIn basePtr outPtr target delta
            v8 v9 v18 v19Saved v20Saved baseBytes
            (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
            (EvmAsm.Codegen.U256MulU64Be.copyState
              (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
              outWin 32) G **
          regOwn .x10)
      (K73 + 92)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest spH raIn basePtr outPtr target delta
            v8 v9 v18 v19Saved v20Saved baseBytes
            (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
            (EvmAsm.Codegen.U256MulU64Be.copyState
              (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
              outWin 32) G **
          regOwn .x10) := by
  let Fframe : Assertion :=
    frameSlotsSaved k73Frame spH
      (k73Saved raIn v8 v9 v18 v19Saved v20Saved)
  have hFframe : Fframe.pcFree := by
    dsimp [Fframe]
    exact pcFree_frameSlotsSaved _ _ _
  let Fcall : Assertion := Fframe ** G
  have hFcall : Fcall.pcFree := by
    dsimp [Fcall]
    exact pcFree_sepConj hFframe hG
  have htarget :
      (K73 + 84) + signExtend21
        (jalOff GuestAddrs.u256_mul_u64_be
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 84)) =
      (GuestAddrs.u256_mul_u64_be : Word) := by
    change BitVec.ofNat 64 GuestAddrs.eip1559_calc_base_fee_per_gas +
      BitVec.ofNat 64 84 + _ = BitVec.ofNat 64 GuestAddrs.u256_mul_u64_be
    exact jalOff_correct_add GuestAddrs.u256_mul_u64_be
      GuestAddrs.eip1559_calc_base_fee_per_gas 84
      (by decide) (by decide) (by decide) (by decide)
  have hmem : ∀ a i, CodeReq.singleton (K73 + 84)
      (.JAL .x1 (jalOff GuestAddrs.u256_mul_u64_be
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 84))) a = some i →
      wholeCode a = some i := by
    intro a i hi
    exact k73_whole_mono a i (k73_mem 21 _ (K73 + 84) (by decide)
      (by rw [k73_length]; decide) (by rfl) a i hi)
  have hcalleeMem : ∀ a i, mulCode a = some i → wholeCode a = some i :=
    mul_whole_mono
  have hcall := k73_mul_call_native_spec_within
    (cr := wholeCode) (n := 3850)
    (callerPC := K73 + 84) (calleeEntry := GuestAddrs.u256_mul_u64_be)
    (oldRa := raIn) (spOld := spH) (spNew := spH + signExtend12 (-48 : BitVec 12))
    (v8 := basePtr) (v9 := outPtr) (v18 := target) (v19 := delta) (v20 := 0)
    (aPtr := basePtr) (b := delta) (outPtr := outPtr) (v13 := outPtr)
    (offset := jalOff GuestAddrs.u256_mul_u64_be
      (GuestAddrs.eip1559_calc_base_fee_per_gas + 84))
    (F := Fcall) hFcall f0 f1 f2 f3 f4 f5
    (aBytes := baseBytes) (accWin := accWin) (outWin := outWin)
    (accImg := EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
    (outImg := EvmAsm.Codegen.U256MulU64Be.copyState
      (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32) outWin 32)
    (by
      have hEq : (K73 : Word) + 88 = K73 + 84 + 4 := by
        dsimp only [K73]
        bv_omega
      rw [← hEq]
      exact hcallee)
    htarget hmem hcalleeMem
  have hmul : cpsTripleWithin 3851 (K73 + 84) (K73 + 88) wholeCode
      (((.x1 : Reg) ↦ᵣ raIn) **
        k73MulPreNoRa spH basePtr outPtr target delta (0 : Word)
          basePtr delta outPtr outPtr f0 f1 f2 f3 f4 f5
          baseBytes accWin outWin Fcall)
      (k73DecreaseMulPost spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes
        (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
        (EvmAsm.Codegen.U256MulU64Be.copyState
          (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
          outWin 32) G) :=
    hcall
  have hRest :
      (k73DecreaseMulCarryRest spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes
        (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
        (EvmAsm.Codegen.U256MulU64Be.copyState
          (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
          outWin 32) G).pcFree := by
    have hExists : Assertion.pcFree (fun s => ∃ k, (k73MulEpilogueNoRa
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target delta (0 : Word) **
        bytesRegion outPtr
          (EvmAsm.Codegen.U256MulU64Be.copyState
            (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
            outWin 32) **
        k73MulOverflowCoreNoStatus
          (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32) k) s) := by
      apply pcFree_exists
      intro k
      pcf
    dsimp [k73DecreaseMulCarryRest]
    pcf
    exact hExists
    exact hG
  have hmul' : cpsTripleWithin 3851 (K73 + 84) (K73 + 88) wholeCode
      (((.x1 : Reg) ↦ᵣ raIn) **
        k73MulPreNoRa spH basePtr outPtr target delta (0 : Word)
          basePtr delta outPtr outPtr f0 f1 f2 f3 f4 f5
          baseBytes accWin outWin Fcall)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target delta
          v8 v9 v18 v19Saved v20Saved baseBytes
          (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
          (EvmAsm.Codegen.U256MulU64Be.copyState
            (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
            outWin 32) G **
        regOwn .x10) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp)
      (fun s hq => by
        have hq' := k73_decrease_mul_post_factor
          spH raIn basePtr outPtr target delta v8 v9 v18 v19Saved v20Saved
          baseBytes (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
          (EvmAsm.Codegen.U256MulU64Be.copyState
            (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
            outWin 32) G s hq
        sep_perm hq') hmul
  have hstatus := k73_mul_status_branch_spec_within
    (k73DecreaseMulCarryRest spH raIn basePtr outPtr target delta
      v8 v9 v18 v19Saved v20Saved baseBytes
      (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
      (EvmAsm.Codegen.U256MulU64Be.copyState
        (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
        outWin 32) G) hRest
  have hseq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by sep_perm hp) hmul' hstatus
  simpa only [show 3851 + 1 = 3852 by decide] using hseq

end EvmAsm.Codegen.HeaderValidateBaseFeeMulNativeContract
