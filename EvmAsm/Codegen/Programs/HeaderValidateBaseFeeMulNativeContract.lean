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
import EvmAsm.Rv64.BitAux

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

/-- Witness scratch lists for the constructed inhabitant below.  The initial
windows are deliberately plain zeros: under the native shape that is legal
(the caller only owns them pre-call), which is exactly the honesty payoff of
the repair - the old symmetric contract would have forced these to be spelled
as the computed final image instead. -/
private def k73MulNatWBase : List (BitVec 8) := List.replicate 31 0 ++ [7]
private def k73MulNatWAccWin : List (BitVec 8) := List.replicate 40 0
private def k73MulNatWOutWin : List (BitVec 8) := List.replicate 32 0

/-- CONSTRUCTED inhabitant of the native decrease-callsite stage (closed
proposition, concrete values, no hypotheses): the same Arm4-family numbers as
the increase witnesses (base value 7, target 5000, gasUsed 2500, delta 2500,
product 17500) but discharged against the deployed flat triple through the
native contract, not through any name-instantiation trick. -/
theorem k73_mul_status_branch_native_inhabited :
    cpsBranchWithin 3852 (K73 + 84) wholeCode
      (((.x1 : Reg) ↦ᵣ (0 : Word)) **
        k73MulPreNoRa (0xa0050000 : Word) (0xa0000000 : Word)
          (0xa0000100 : Word) (5000 : Word) (2500 : Word) (0 : Word)
          (0xa0000000 : Word) (2500 : Word) (0xa0000100 : Word)
          (0xa0000100 : Word)
          0 1 2 3 4 5
          k73MulNatWBase k73MulNatWAccWin k73MulNatWOutWin
          (frameSlotsSaved k73Frame (0xa0050000 : Word)
            (k73Saved 0 0 0 0 0 0) **
            regOwns [.x14, .x15, .x16, .x17] ** empAssertion))
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest (0xa0050000 : Word) 0
            (0xa0000000 : Word) (0xa0000100 : Word) (5000 : Word)
            (2500 : Word) 0 0 0 0 0
            k73MulNatWBase
            (EvmAsm.Codegen.U256MulU64Be.mulState k73MulNatWBase
              (2500 : Word) 32)
            (EvmAsm.Codegen.U256MulU64Be.copyState
              (EvmAsm.Codegen.U256MulU64Be.mulState k73MulNatWBase
                (2500 : Word) 32) k73MulNatWOutWin 32)
            (regOwns [.x14, .x15, .x16, .x17] ** empAssertion) **
          regOwn .x10)
      (K73 + 92)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest (0xa0050000 : Word) 0
            (0xa0000000 : Word) (0xa0000100 : Word) (5000 : Word)
            (2500 : Word) 0 0 0 0 0
            k73MulNatWBase
            (EvmAsm.Codegen.U256MulU64Be.mulState k73MulNatWBase
              (2500 : Word) 32)
            (EvmAsm.Codegen.U256MulU64Be.copyState
              (EvmAsm.Codegen.U256MulU64Be.mulState k73MulNatWBase
                (2500 : Word) 32) k73MulNatWOutWin 32)
            (regOwns [.x14, .x15, .x16, .x17] ** empAssertion) **
          regOwn .x10) := by
  exact k73_mul_status_branch_native_spec_within
    (spH := (0xa0050000 : Word)) (raIn := (0 : Word))
    (target := (5000 : Word)) (delta := (2500 : Word))
    (basePtr := (0xa0000000 : Word)) (outPtr := (0xa0000100 : Word))
    (v8 := 0) (v9 := 0) (v18 := 0) (v19Saved := 0) (v20Saved := 0)
    (f0 := 0) (f1 := 1) (f2 := 2) (f3 := 3) (f4 := 4) (f5 := 5)
    (baseBytes := k73MulNatWBase) (accWin := k73MulNatWAccWin)
    (outWin := k73MulNatWOutWin)
    (G := regOwns [.x14, .x15, .x16, .x17] ** empAssertion)
    (hG := by pcf)
    (hcallee := by
      have hretCall :
          ((K73 + 88 : Word) &&& ~~~(1 : Word)) = K73 + 88 :=
        EvmAsm.Rv64.BitAux.word_add_even_andn_one (by decide) (by decide)
      exact EvmAsm.Codegen.U256MulU64Be.mulWhole_spec
        (F := frameSlotsSaved k73Frame (0xa0050000 : Word)
            (k73Saved 0 0 0 0 0 0) **
          regOwns [.x14, .x15, .x16, .x17] ** empAssertion)
        (hF := by pcf)
        (aBytes := k73MulNatWBase) (accBytes := k73MulNatWAccWin)
        (outBytes := k73MulNatWOutWin)
        (hlenA := by simp [k73MulNatWBase])
        (hlenAcc := by simp [k73MulNatWAccWin])
        (hout := by simp [k73MulNatWOutWin])
        (spOld := (0xa0050000 : Word)) (vRa := (K73 + 88))
        (v8 := (0xa0000000 : Word)) (v9 := (0xa0000100 : Word))
        (v18 := (5000 : Word)) (v19 := (2500 : Word)) (v20 := (0 : Word))
        (aPtr := (0xa0000000 : Word)) (b := (2500 : Word))
        (outPtr := (0xa0000100 : Word)) (v13 := (0xa0000100 : Word))
        (f0 := 0) (f1 := 1) (f2 := 2) (f3 := 3) (f4 := 4) (f5 := 5)
        (halignA := by decide) (hoverA := by decide) (hvalidA := by decide)
        (halignOut := by decide) (hoverOut := by decide)
        (hvalidOut := by decide) (hret := hretCall))

end EvmAsm.Codegen.HeaderValidateBaseFeeMulNativeContract
