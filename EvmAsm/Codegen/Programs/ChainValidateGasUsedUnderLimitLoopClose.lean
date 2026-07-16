/-
  Two-call status dispatch, loop induction, and whole-program caller contract
  for `chain_validate_gas_used_under_limit`.

  `cvgulDispatch2` handles the tail from K34's second `flatPost` (`D+188`): the
  gas-limit `bne`, the value reload/compare, and the dynamic `bltu` splitting to
  violation or advance+loop.  `cvgulDispatch1` prepends the gas-used `bne` and
  the second K34 call.  `cvgulIter` shapes the loop invariant into one full
  iteration, `cvgulLoop` runs the induction, and
  `chain_validate_gas_used_under_limit_spec_within` glues the prologue in front.
-/

import EvmAsm.Codegen.Programs.ChainValidateGasUsedUnderLimitLoop

namespace EvmAsm.Codegen.ChainValidateGasUsedUnderLimitSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm
  (Saved savedFrame savedVals listNthFrame regsAt_listNthFrame
   frameSlotsSaved_listNthFrame)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom
   wordArrayFrom_append shiftLeft3_ofNat hdrOff hdrBaseAt hdrOff_succ hdrBaseAt_succ
   ofNat_ne_of_lt ofNat_succ_tie)

local macro "pcfx" : tactic =>
  `(tactic| repeat' first
      | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs | exact pcFree_memOwn | exact pcFree_emp | exact pcFree_pure
      | exact bytesRegion_pcFree _ _ | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_wordArray _ _ | exact pcFree_wordArrayFrom _ _ _ | unfold savedFrame
      | unfold EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame)

/-! ## Dispatch tail from the second call (`D+188` onward)

    From K34's field-9 `flatPost` at the `bne` return site (`D+188`) to the
    caller's post.  `flatPost_normalize` collapses the callee return into one
    `Result`-carrying shape; `bne x10, x0` splits on the gas-limit status; on
    success the reload/compare (`bltu gl, gu`) routes to violation or
    continue+loop, using the carried field-10 `Result` for `gu`. -/
set_option maxRecDepth 8000 in
theorem cvgulDispatch2
    (sp0 spC hdrBase lenBase validPtr firstBadPtr raIn : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) (i : Nat)
    (oldOff oldLen gu : Word) (nTail : Nat)
    (hi : i < lengths.length)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (halign : hdrOff lengths i % 8 = 0)
    (hlen : hdrOff lengths i ≤ bigBytes.length)
    (hResGu : EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
      (hdrBaseAt hdrBase lengths i) lengths[i]! 10 0 gu)
    (hprefix : ∀ j, j < i → hdrGasOk hdrBase bigBytes lengths j)
    (htail : (∀ j, j < i + 1 → hdrGasOk hdrBase bigBytes lengths j) →
      cpsTripleWithin nTail (D + 68) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths (i + 1))
        (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths)) :
    cpsTripleWithin (27 + nTail) (D + 188) raIn fullCode
      ((.x1 ↦ᵣ LinkRA2) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12))
          (hdrBaseAt hdrBase lengths i) oldOff oldLen
          (⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ :
            EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hdrBaseAt hdrBase lengths i, GasLimit,
            hdrBaseAt hdrBase lengths i, validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ : Saved)
          (bigBytes.drop (hdrOff lengths i)) lengths[i]! 9 **
        (GasUsed ↦ₘ gu) **
        (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        savedFrame spC csaved)
      (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) := by
  have hLi : lengths[i]! = lengths[i] := getElem!_pos lengths i hi
  have hHB : hdrBaseAt hdrBase lengths i = hdrBase + BitVec.ofNat 64 (hdrOff lengths i) := rfl
  have hsf : savedFrame spC csaved =
      ((spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) := by
    unfold savedFrame; rw [hraSaved]
  -- Normalize K34's flatPost, stripping the (status, value) existentials.
  refine cpsTripleWithin_weaken (fun h hp => ?hstrip) (fun _ hq => hq)
    (EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun status =>
      EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun value =>
        (show cpsTripleWithin (27 + nTail) (D + 188) raIn fullCode
          ((.x1 ↦ᵣ LinkRA2) **
            (dispNorm spC (spC + signExtend12 (-32 : BitVec 12)) (hdrBaseAt hdrBase lengths i)
                validPtr firstBadPtr (BitVec.ofNat 64 lengths.length) lenBase (BitVec.ofNat 64 i)
                LinkRA2 GasLimit value status (bigBytes.drop (hdrOff lengths i)) **
              ⌜EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
                (hdrBaseAt hdrBase lengths i) lengths[i]! 9 status value⌝) **
            ((GasUsed ↦ₘ gu) **
              (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              savedFrame spC csaved))
          (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
            firstBadPtr csaved bigBytes lengths) from ?core))))
  case hstrip =>
    obtain ⟨s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hfp, hREST⟩ := hp
    obtain ⟨status, value, hnorm⟩ := flatPost_normalize spC (hdrBaseAt hdrBase lengths i)
      validPtr firstBadPtr (BitVec.ofNat 64 lengths.length) lenBase (BitVec.ofNat 64 i)
      LinkRA2 GasLimit oldOff oldLen (bigBytes.drop (hdrOff lengths i)) lengths[i]! 9 s3 hfp
    exact ⟨status, value, s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hnorm, hREST⟩
  case core =>
    refine cpsTripleWithin_weaken (fun h hp => ?hpull) (fun _ hq => hq)
      (cpsTripleWithin_pure_pre
        (P := EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
          (hdrBaseAt hdrBase lengths i) lengths[i]! 9 status value)
        (H := (.x1 ↦ᵣ LinkRA2) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
          (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
          (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (.x10 ↦ᵣ status) **
          (.x0 ↦ᵣ (0 : Word)) ** (GasLimit ↦ₘ value) ** (GasUsed ↦ₘ gu) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
          EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
            ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
          (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
          ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
          wordArrayFrom lenBase 0 (lengths.take i) **
          wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
          bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
          (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
          savedFrame spC csaved)
        (fun hResult => ?body))
    case hpull =>
      unfold dispNorm at hp
      xperm_hyp hp
    case body =>
      rw [hsf]
      by_cases hstatus : status = 0
      · -- SUCCESS arm: gas-limit `bne` not taken → reload → value compare.
        subst hstatus
        set RframeOk : Assertion :=
          ((.x1 ↦ᵣ LinkRA2) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (GasLimit ↦ₘ value) **
            (GasUsed ↦ₘ gu) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
            ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
            wordArrayFrom lenBase 0 (lengths.take i) **
            wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
            bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
            (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
            ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
            ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) with hRframeOk
        have hbne := bne_spec_gen_within .x10 .x0 (96 : BitVec 13) (0 : Word) (0 : Word)
          (D + 188)
        have hbneC := cpsBranchWithin_extend_code cvgul_mono
          (cpsBranchWithin_extend_code (cr' := cvgulCode)
            (CodeReq.ofProg_mem_at D (D + 188) cvgulProg 47 (.BNE .x10 .x0 (96 : BitVec 13))
              (by bv_omega) (by rw [cvgul_length]; decide) rfl
              (by rw [cvgul_length]; decide)) hbne)
        have hntaken := cpsBranchWithin_ntakenStripPure2 hbneC (fun hp hq => by
          obtain ⟨_, _, _, _, _, hrest⟩ := hq
          exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
        rw [show (D + 188 + 4 : Word) = D + 192 from by bv_omega] at hntaken
        have hcont : cpsTripleWithin (26 + nTail) (D + 192) raIn fullCode
            (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** RframeOk)
            (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
              validPtr firstBadPtr csaved bigBytes lengths) := by
          rw [hRframeOk]
          refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
            (show cpsTripleWithin (26 + nTail) (D + 192) raIn fullCode
              (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA2) **
                (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
                (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
                (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (GasLimit ↦ₘ value) **
                (GasUsed ↦ₘ gu) **
                regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
                memOwn RfuOff ** memOwn RfuLen **
                stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                  ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                wordArrayFrom lenBase 0 (lengths.take i) **
                wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) **
                regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
                regOwn .x30 ** regOwn .x31)
              (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
                validPtr firstBadPtr csaved bigBytes lengths) from ?_)
          refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_of_forall_regIs_to_regOwn7
            (fun v5 v6 v7 v28 v29 v30 v31 => ?_)
          set Rreload : Assertion :=
            ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA2) ** (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) ** (.x19 ↦ᵣ validPtr) **
              (.x20 ↦ᵣ firstBadPtr) ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
              regOwn .x14 ** memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
              ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
              ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
              (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) with hRreload
          set Rstate2 : Assertion :=
            ((.x5 ↦ᵣ GasLimit) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) **
              (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) **
              (IterI ↦ₘ BitVec.ofNat 64 i) ** (GasUsed ↦ₘ gu) ** (GasLimit ↦ₘ value)) **
              Rreload with hRstate2
          have hreload := cpsTripleWithin_extend_code cvgul_mono
            (cvgulCompare (hdrBaseAt hdrBase lengths i) (BitVec.ofNat 64 i) gu value v5
              (hdrBaseAt hdrBase lengths i) (BitVec.ofNat 64 i) v6 v7)
          have hreloadF := cpsTripleWithin_frameR Rreload (by rw [hRreload]; pcfx) hreload
          have hbltu := bltu_spec_gen_within .x7 .x6 (28 : BitVec 13) value gu (D + 240)
          rw [show (D + 240) + signExtend13 (28 : BitVec 13) = D + 268 from by
            rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega] at hbltu
          have hbltuC := cpsBranchWithin_extend_code cvgul_mono
            (cpsBranchWithin_extend_code (cr' := cvgulCode)
              (CodeReq.ofProg_mem_at D (D + 240) cvgulProg 60 (.BLTU .x7 .x6 (28 : BitVec 13))
                (by bv_omega) (by rw [cvgul_length]; decide) rfl
                (by rw [cvgul_length]; decide)) hbltu)
          have hbltuF := cpsBranchWithin_frameR Rstate2 (by rw [hRstate2, hRreload]; pcfx) hbltuC
          have hbranch := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
            (fun h hp => by rw [hRstate2]; xperm_hyp hp) hreloadF hbltuF
          have h_t : cpsTripleWithin (13 + nTail) (D + 268) raIn fullCode
              (((.x7 ↦ᵣ value) ** (.x6 ↦ᵣ gu) ** ⌜BitVec.ult value gu⌝) ** Rstate2)
              (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
                validPtr firstBadPtr csaved bigBytes lengths) := by
            rw [hRstate2, hRreload]
            refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
              (cpsTripleWithin_pure_pre (P := BitVec.ult value gu)
                (H := (.x7 ↦ᵣ value) ** (.x6 ↦ᵣ gu) ** (.x5 ↦ᵣ GasLimit) **
                  (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  (GasUsed ↦ₘ gu) ** (GasLimit ↦ₘ value) ** (.x10 ↦ᵣ (0 : Word)) **
                  (.x0 ↦ᵣ (0 : Word)) **
                  (.x1 ↦ᵣ LinkRA2) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                  (.x9 ↦ᵣ lenBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
                  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
                  memOwn RfuOff ** memOwn RfuLen **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                    ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                  ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                  ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
                (fun hult => ?_))
            have hviol := cpsTripleWithin_extend_code cvgul_mono
              (retViolation sp0 spC raIn (BitVec.ofNat 64 i) validPtr firstBadPtr csaved
                ((.x7 ↦ᵣ value) ** (.x6 ↦ᵣ gu) ** (.x5 ↦ᵣ GasLimit) **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  (GasUsed ↦ₘ gu) ** (GasLimit ↦ₘ value) ** regOwn .x11 ** regOwn .x12 **
                  regOwn .x13 ** regOwn .x14 ** memOwn RfuOff ** memOwn RfuLen **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                    ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
                (by pcfx) (0 : Word) LinkRA2 (BitVec.ofNat 64 lengths.length) lenBase
                (hdrBaseAt hdrBase lengths i) hspC hraSaved hret)
            refine cpsTripleWithin_weaken (fun h hp => by
              have hp1 : ((validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                  ((.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
                    (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
                    (.x1 ↦ᵣ LinkRA2) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                    (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) **
                    (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                    ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                    ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                    ((.x7 ↦ᵣ value) ** (.x6 ↦ᵣ gu) ** (.x5 ↦ᵣ GasLimit) **
                      (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                      (GasUsed ↦ₘ gu) ** (GasLimit ↦ₘ value) ** regOwn .x11 ** regOwn .x12 **
                      regOwn .x13 ** regOwn .x14 ** memOwn RfuOff ** memOwn RfuLen **
                      stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                      bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                      EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame
                        (spC + signExtend12 (-32 : BitVec 12))
                        ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                      ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                      wordArrayFrom lenBase 0 (lengths.take i) **
                      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)))) h := by
                xperm_hyp hp
              have hp2 := sepConj_mono memIs_implies_memOwn
                (sepConj_mono memIs_implies_memOwn (fun _ x => x)) h hp1
              xperm_hyp hp2) (fun h hq => ?_)
              (cpsTripleWithin_mono_nSteps (show 13 ≤ 13 + nTail by omega) hviol)
            refine Or.inr (Or.inl ⟨i, ?_⟩)
            refine (sepConj_pure_left h).mpr ⟨⟨hi, hprefix, ⟨gu, value, hResGu, hResult, hult⟩⟩, ?_⟩
            unfold commonRet payload
            rw [hsf, hraSaved, wordArray_split lenBase lengths i hi,
              EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen, ← hHB]
            have hp1 : ((.x5 ↦ᵣ GasLimit) ** (.x6 ↦ᵣ gu) ** (.x7 ↦ᵣ value) **
                (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
                (GasUsed ↦ₘ gu) ** (GasLimit ↦ₘ value) **
                (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) **
                (IterI ↦ₘ BitVec.ofNat 64 i) **
                EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                  ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
                  (firstBadPtr ↦ₘ BitVec.ofNat 64 i) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
                  (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) ** (.x18 ↦ᵣ csaved.s2) **
                  (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
                  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                  ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                  ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                  (.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
                  regOwn .x14 ** memOwn RfuOff ** memOwn RfuLen **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)))) h := by
              rw [← hLi]; xperm_hyp hq
            have hp2 := sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono
              (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x7)
              (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x29)
              (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (regIs_implies_regOwn .x31)
              (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
              (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _)
              (fun _ x => x)))))))))))) h hp1
            xperm_hyp hp2
          have h_f : cpsTripleWithin (13 + nTail) (D + 244) raIn fullCode
              (((.x7 ↦ᵣ value) ** (.x6 ↦ᵣ gu) ** ⌜¬ BitVec.ult value gu⌝) ** Rstate2)
              (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
                validPtr firstBadPtr csaved bigBytes lengths) := by
            rw [hRstate2, hRreload]
            refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
              (cpsTripleWithin_pure_pre (P := ¬ BitVec.ult value gu)
                (H := (.x7 ↦ᵣ value) ** (.x6 ↦ᵣ gu) ** (.x5 ↦ᵣ GasLimit) **
                  (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  (GasUsed ↦ₘ gu) ** (GasLimit ↦ₘ value) ** (.x10 ↦ᵣ (0 : Word)) **
                  (.x0 ↦ᵣ (0 : Word)) **
                  (.x1 ↦ᵣ LinkRA2) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                  (.x9 ↦ᵣ lenBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
                  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
                  memOwn RfuOff ** memOwn RfuLen **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                    ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                  ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                  ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
                (fun hnult => ?_))
            have hprefix' : ∀ j, j < i + 1 → hdrGasOk hdrBase bigBytes lengths j := by
              intro j hj
              rcases (by omega : j < i ∨ j = i) with hlt | heq
              · exact hprefix j hlt
              · subst heq; exact ⟨gu, value, hResGu, hResult, hnult⟩
            have hadv := cpsTripleWithin_extend_code cvgul_mono
              (cvgulAdvance (hdrBaseAt hdrBase lengths i) lenBase (BitVec.ofNat 64 i)
                lengths[i]! v28 v29)
            rw [shiftLeft3_ofNat i] at hadv
            have hadvF := cpsTripleWithin_frameR
              ((.x7 ↦ᵣ value) ** (.x6 ↦ᵣ gu) ** (.x5 ↦ᵣ GasLimit) **
                (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                (GasUsed ↦ₘ gu) ** (GasLimit ↦ₘ value) ** (.x10 ↦ᵣ (0 : Word)) **
                (.x0 ↦ᵣ (0 : Word)) **
                (.x1 ↦ᵣ LinkRA2) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** regOwn .x11 ** regOwn .x12 **
                regOwn .x13 ** regOwn .x14 ** memOwn RfuOff ** memOwn RfuLen **
                stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                  ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                wordArrayFrom lenBase 0 (lengths.take i) **
                wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) (by pcfx) hadv
            refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
              (cpsTripleWithin_mono_nSteps (show 6 + nTail ≤ 13 + nTail by omega)
                (cpsTripleWithin_seq_perm_same_cr (fun h hp => by
                  unfold LoopInv payload scratchRegs
                  rw [hsf, wordArray_split lenBase lengths i hi,
                    EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen,
                    ← hHB, hdrBaseAt_succ hdrBase lengths i hi, ← ofNat_succ_tie i, ← hLi]
                  have hp1 : ((.x1 ↦ᵣ LinkRA2) ** (.x5 ↦ᵣ GasLimit) ** (.x6 ↦ᵣ gu) **
                      (.x7 ↦ᵣ value) ** (.x10 ↦ᵣ (0 : Word)) **
                      (.x28 ↦ᵣ (lenBase + BitVec.ofNat 64 (8 * i))) **
                      (.x29 ↦ᵣ BitVec.ofNat 64 lengths[i]!) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
                      (GasUsed ↦ₘ gu) ** (GasLimit ↦ₘ value) **
                      (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) **
                      (IterI ↦ₘ BitVec.ofNat 64 i) **
                      EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame
                        (spC + signExtend12 (-32 : BitVec 12))
                        ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                        (.x9 ↦ᵣ lenBase) **
                        (.x18 ↦ᵣ (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 lengths[i]!)) **
                        (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
                        (.x21 ↦ᵣ (BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12))) **
                        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
                        (.x0 ↦ᵣ (0 : Word)) ** memOwn RfuOff ** memOwn RfuLen **
                        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                        wordArrayFrom lenBase 0 (lengths.take i) **
                        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                        bytesRegion (hdrBaseAt hdrBase lengths i)
                          (bigBytes.drop (hdrOff lengths i)))) h := by
                    xperm_hyp hp
                  have hp2 := sepConj_mono (regIs_implies_regOwn .x1) (sepConj_mono
                    (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
                    (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x10)
                    (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x29)
                    (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (regIs_implies_regOwn .x31)
                    (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
                    (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
                    (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _)
                    (fun _ x => x)))))))))))))) h hp1
                  xperm_hyp hp2) hadvF (htail hprefix')))
          refine cpsTripleWithin_weaken (fun h hp => by rw [hRreload]; xperm_hyp hp)
            (fun _ hq => hq)
            (cpsTripleWithin_mono_nSteps (show 12 + 1 + (13 + nTail) ≤ 26 + nTail by omega)
              (cpsBranchWithin_merge_same_cr hbranch h_t h_f))
        have hntakenF := cpsTripleWithin_frameR RframeOk (by rw [hRframeOk]; pcfx) hntaken
        refine cpsTripleWithin_weaken (fun h hp => by rw [hRframeOk]; xperm_hyp hp)
          (fun _ hq => hq)
          (cpsTripleWithin_mono_nSteps (show 1 + (26 + nTail) ≤ 27 + nTail by omega)
            (cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hntakenF hcont))
      · -- PARSE-FAIL arm (gas_limit): `bne` taken → status ≠ 0 exit.
        have hbne := bne_spec_gen_within .x10 .x0 (96 : BitVec 13) status (0 : Word) (D + 188)
        have hbneC := cpsBranchWithin_extend_code cvgul_mono
          (cpsBranchWithin_extend_code (cr' := cvgulCode)
            (CodeReq.ofProg_mem_at D (D + 188) cvgulProg 47 (.BNE .x10 .x0 (96 : BitVec 13))
              (by bv_omega) (by rw [cvgul_length]; decide) rfl
              (by rw [cvgul_length]; decide)) hbne)
        have htaken := cpsBranchWithin_takenStripPure2 hbneC (fun hp hq => by
          obtain ⟨_, _, _, _, _, hrest⟩ := hq
          exact absurd ((sepConj_pure_right _).1 hrest).2 hstatus)
        rw [show (D + 188) + signExtend13 (96 : BitVec 13) = D + 284 from by
          rw [show signExtend13 (96 : BitVec 13) = (96 : Word) from by decide]; bv_omega] at htaken
        have htakenF := cpsTripleWithin_frameR
          ((.x1 ↦ᵣ LinkRA2) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (GasLimit ↦ₘ value) **
            (GasUsed ↦ₘ gu) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
            ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
            wordArrayFrom lenBase 0 (lengths.take i) **
            wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
            bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
            (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
            ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
            ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) (by pcfx) htaken
        have hpfC := cpsTripleWithin_extend_code cvgul_mono
          (retParseFail sp0 spC raIn (BitVec.ofNat 64 i) firstBadPtr csaved
            ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
              regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
              regOwn .x30 ** regOwn .x31 ** (GasLimit ↦ₘ value) ** (GasUsed ↦ₘ gu) **
              memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) ** (validPtr ↦ₘ (1 : Word)))
            (by pcfx) LinkRA2 (BitVec.ofNat 64 lengths.length) lenBase
            (hdrBaseAt hdrBase lengths i) validPtr status hspC hraSaved hret)
        have hcompose := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
          have hp1 : ((firstBadPtr ↦ₘ (0 : Word)) **
              ((.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (.x10 ↦ᵣ status) **
                (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ LinkRA2) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
                  regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
                  regOwn .x30 ** regOwn .x31 ** (GasLimit ↦ₘ value) ** (GasUsed ↦ₘ gu) **
                  memOwn RfuOff ** memOwn RfuLen **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                    ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (validPtr ↦ₘ (1 : Word))))) h := by xperm_hyp hp
          have hp2 := sepConj_mono_left memIs_implies_memOwn h hp1
          xperm_hyp hp2) htakenF hpfC
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
          (cpsTripleWithin_mono_nSteps (show 1 + 11 ≤ 27 + nTail by omega) hcompose)
        refine Or.inr (Or.inr ⟨i, status, ?_⟩)
        refine (sepConj_pure_left h).mpr
          ⟨⟨hi, hprefix, Or.inr ⟨gu, value, hResGu, hResult, hstatus⟩⟩, ?_⟩
        unfold commonRet payload
        rw [hsf, hraSaved, wordArray_split lenBase lengths i hi,
          EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen, ← hHB]
        have hp1 : ((GasLimit ↦ₘ value) ** (GasUsed ↦ₘ gu) **
            (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) **
            (IterI ↦ₘ BitVec.ofNat 64 i) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA2, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            ((.x10 ↦ᵣ status) ** (validPtr ↦ₘ (1 : Word)) **
              (firstBadPtr ↦ₘ BitVec.ofNat 64 i) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
              (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) ** (.x18 ↦ᵣ csaved.s2) **
              (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
              (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
              ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
              ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
              (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
              regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
              regOwn .x30 ** regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)))) h := by
          rw [← hLi]; xperm_hyp hq
        have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
          (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _) (fun _ x => x))))) h hp1
        xperm_hyp hp2

#print axioms cvgulDispatch2

/-! ## Call block 2 with the consumed scratch registers owned

    Mirror of `cvgulCall1Owned` for the second K34 call, presenting `cvgulCall2`'s
    registers as `regOwn` (matching the loop invariant).  Since `cvgulReloadSetup2`
    reloads `x18`/`x21` from the spill cells, they are two EXTRA owned peels on top
    of the call-1 set. -/

set_option maxRecDepth 8000 in
theorem cvgulCall2Owned (hbi lenBase spC iW : Word) (Li : Nat)
    (nN s3 s4 oldOut oldOff oldLen : Word) (bytes : List (BitVec 8)) (csaved : Saved)
    (hsalign : hbi.toNat % 8 = 0)
    (hslack : Li + 9 ≤ bytes.length)
    (hover : hbi.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (hbi + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (13 + 1 + nCall 9) (D + 132) (D + 188) fullCode
      ((((((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) **
            (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
            ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
            (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) **
            frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            (GasLimit ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
            bytesRegion hbi bytes ** savedFrame spC csaved) **
          regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x28) ** regOwn .x1) ** regOwn .x18) ** regOwn .x21)
      ((.x1 ↦ᵣ LinkRA2) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA2, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, GasLimit, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 9 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v21 => ?_)
  refine cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => h)
    (show cpsTripleWithin (13 + 1 + nCall 9) (D + 132) (D + 188) fullCode
      ((((((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) **
            (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
            ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
            (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) **
            frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            (GasLimit ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
            bytesRegion hbi bytes ** savedFrame spC csaved) **
          regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x28) ** regOwn .x1) ** (.x21 ↦ᵣ v21)) ** regOwn .x18)
      ((.x1 ↦ᵣ LinkRA2) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA2, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, GasLimit, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 9 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) from ?_)
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v18 => ?_)
  refine cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => h)
    (show cpsTripleWithin (13 + 1 + nCall 9) (D + 132) (D + 188) fullCode
      (((((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) **
            (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
            ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
            (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) **
            frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            (GasLimit ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
            bytesRegion hbi bytes ** savedFrame spC csaved) **
          regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x28) ** (.x21 ↦ᵣ v21) ** (.x18 ↦ᵣ v18)) ** regOwn .x1)
      ((.x1 ↦ᵣ LinkRA2) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA2, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, GasLimit, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 9 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) from ?_)
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v1 => ?_)
  refine cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => h)
    (show cpsTripleWithin (13 + 1 + nCall 9) (D + 132) (D + 188) fullCode
      (((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) **
          (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
          ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
          (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          (GasLimit ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
          bytesRegion hbi bytes ** savedFrame spC csaved ** (.x1 ↦ᵣ v1) **
          (.x18 ↦ᵣ v18) ** (.x21 ↦ᵣ v21)) **
        regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28)
      ((.x1 ↦ᵣ LinkRA2) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
          oldOff oldLen (⟨LinkRA2, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hbi, GasLimit, hbi, s3, s4, iW⟩ : Saved)
          bytes Li 9 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) from ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_of_forall_regIs_to_regOwn7
    (fun v5 v10 v11 v12 v13 v14 v28 => ?_)
  exact cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => by xperm_hyp h)
    (cvgulCall2 hbi lenBase spC iW Li nN s3 s4 oldOut oldOff oldLen v14 v1 v5 v10 v11 v12 v13
      v18 v21 v28 bytes csaved hsalign hslack hover hvalid)

#print axioms cvgulCall2Owned

/-! ## Dispatch from the first call (`D+128` onward): gas-used status + call 2

    From K34's field-10 `flatPost` at the first return site (`D+128`).  Normalize
    the callee return, `bne x10, x0` on the gas-used status: taken → parse-fail
    exit (field-10 status ≠ 0); not-taken (gas_used decoded to `gu`) → the second
    K34 call (`cvgulCall2Owned`) followed by `cvgulDispatch2` for the gas-limit
    field. -/
set_option maxRecDepth 8000 in
theorem cvgulDispatch1
    (sp0 spC hdrBase lenBase validPtr firstBadPtr raIn : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) (i : Nat)
    (oldOff oldLen oldLimit : Word) (nTail : Nat)
    (hi : i < lengths.length)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (halign : hdrOff lengths i % 8 = 0)
    (hlen : hdrOff lengths i ≤ bigBytes.length)
    (hsalign : (hdrBaseAt hdrBase lengths i).toNat % 8 = 0)
    (hslack : lengths[i]! + 9 ≤ (bigBytes.drop (hdrOff lengths i)).length)
    (hover : (hdrBaseAt hdrBase lengths i).toNat +
      (bigBytes.drop (hdrOff lengths i)).length < 2 ^ 64)
    (hvalid : ∀ k, k < (bigBytes.drop (hdrOff lengths i)).length →
      isValidByteAccess (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 k) = true)
    (hprefix : ∀ j, j < i → hdrGasOk hdrBase bigBytes lengths j)
    (htail : (∀ j, j < i + 1 → hdrGasOk hdrBase bigBytes lengths j) →
      cpsTripleWithin nTail (D + 68) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths (i + 1))
        (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths)) :
    cpsTripleWithin (1 + ((13 + 1 + nCall 9) + (27 + nTail))) (D + 128) raIn fullCode
      ((.x1 ↦ᵣ LinkRA1) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12))
          (hdrBaseAt hdrBase lengths i) oldOff oldLen
          (⟨LinkRA1, BitVec.ofNat 64 lengths.length, lenBase⟩ :
            EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hdrBaseAt hdrBase lengths i, GasUsed,
            hdrBaseAt hdrBase lengths i, validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ : Saved)
          (bigBytes.drop (hdrOff lengths i)) lengths[i]! 10 **
        (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        (GasLimit ↦ₘ oldLimit) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        savedFrame spC csaved)
      (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) := by
  have hLi : lengths[i]! = lengths[i] := getElem!_pos lengths i hi
  have hHB : hdrBaseAt hdrBase lengths i = hdrBase + BitVec.ofNat 64 (hdrOff lengths i) := rfl
  have hsf : savedFrame spC csaved =
      ((spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) := by
    unfold savedFrame; rw [hraSaved]
  refine cpsTripleWithin_weaken (fun h hp => ?hstrip) (fun _ hq => hq)
    (EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun status =>
      EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun value =>
        (show cpsTripleWithin (1 + ((13 + 1 + nCall 9) + (27 + nTail))) (D + 128) raIn fullCode
          ((.x1 ↦ᵣ LinkRA1) **
            (dispNorm spC (spC + signExtend12 (-32 : BitVec 12)) (hdrBaseAt hdrBase lengths i)
                validPtr firstBadPtr (BitVec.ofNat 64 lengths.length) lenBase (BitVec.ofNat 64 i)
                LinkRA1 GasUsed value status (bigBytes.drop (hdrOff lengths i)) **
              ⌜EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
                (hdrBaseAt hdrBase lengths i) lengths[i]! 10 status value⌝) **
            ((IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              (GasLimit ↦ₘ oldLimit) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              savedFrame spC csaved))
          (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
            firstBadPtr csaved bigBytes lengths) from ?core))))
  case hstrip =>
    obtain ⟨s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hfp, hREST⟩ := hp
    obtain ⟨status, value, hnorm⟩ := flatPost_normalize spC (hdrBaseAt hdrBase lengths i)
      validPtr firstBadPtr (BitVec.ofNat 64 lengths.length) lenBase (BitVec.ofNat 64 i)
      LinkRA1 GasUsed oldOff oldLen (bigBytes.drop (hdrOff lengths i)) lengths[i]! 10 s3 hfp
    exact ⟨status, value, s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hnorm, hREST⟩
  case core =>
    refine cpsTripleWithin_weaken (fun h hp => ?hpull) (fun _ hq => hq)
      (cpsTripleWithin_pure_pre
        (P := EvmAsm.Codegen.RlpFieldToU64SAsm.Result (bigBytes.drop (hdrOff lengths i))
          (hdrBaseAt hdrBase lengths i) lengths[i]! 10 status value)
        (H := (.x1 ↦ᵣ LinkRA1) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
          (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
          (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (.x10 ↦ᵣ status) **
          (.x0 ↦ᵣ (0 : Word)) ** (GasUsed ↦ₘ value) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
          EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
            ⟨LinkRA1, BitVec.ofNat 64 lengths.length, lenBase⟩ **
          (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
          ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
          wordArrayFrom lenBase 0 (lengths.take i) **
          wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
          bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
          (GasLimit ↦ₘ oldLimit) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
          savedFrame spC csaved)
        (fun hResult => ?body))
    case hpull =>
      unfold dispNorm at hp
      xperm_hyp hp
    case body =>
      by_cases hstatus : status = 0
      · -- SUCCESS arm: gas-used `bne` not taken → second K34 call → dispatch 2.
        subst hstatus
        set RframeOk1 : Assertion :=
          ((.x1 ↦ᵣ LinkRA1) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (GasUsed ↦ₘ value) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA1, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
            ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
            wordArrayFrom lenBase 0 (lengths.take i) **
            wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
            bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
            (GasLimit ↦ₘ oldLimit) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            savedFrame spC csaved) with hRframeOk1
        have hbne := bne_spec_gen_within .x10 .x0 (156 : BitVec 13) (0 : Word) (0 : Word)
          (D + 128)
        have hbneC := cpsBranchWithin_extend_code cvgul_mono
          (cpsBranchWithin_extend_code (cr' := cvgulCode)
            (CodeReq.ofProg_mem_at D (D + 128) cvgulProg 32 (.BNE .x10 .x0 (156 : BitVec 13))
              (by bv_omega) (by rw [cvgul_length]; decide) rfl
              (by rw [cvgul_length]; decide)) hbne)
        have hntaken := cpsBranchWithin_ntakenStripPure2 hbneC (fun hp hq => by
          obtain ⟨_, _, _, _, _, hrest⟩ := hq
          exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
        rw [show (D + 128 + 4 : Word) = D + 132 from by bv_omega] at hntaken
        have hcont : cpsTripleWithin ((13 + 1 + nCall 9) + (27 + nTail)) (D + 132) raIn fullCode
            (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** RframeOk1)
            (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
              validPtr firstBadPtr csaved bigBytes lengths) := by
          set BODY : Assertion :=
            ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA1) ** (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
              (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
              (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (GasUsed ↦ₘ value) **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
              regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
              regOwn .x31 ** stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA1, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              (GasLimit ↦ₘ oldLimit) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              savedFrame spC csaved) with hBODY
          refine cpsTripleWithin_weaken (fun h hp => by
            rw [hRframeOk1] at hp; rw [hBODY]; xperm_hyp hp) (fun _ hq => hq)
            (show cpsTripleWithin ((13 + 1 + nCall 9) + (27 + nTail)) (D + 132) raIn fullCode
              ((BODY ** memOwn RfuOff) ** memOwn RfuLen)
              (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
                validPtr firstBadPtr csaved bigBytes lengths) from ?_)
          refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldLen2 => ?_)
          refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
            (show cpsTripleWithin ((13 + 1 + nCall 9) + (27 + nTail)) (D + 132) raIn fullCode
              ((BODY ** (RfuLen ↦ₘ oldLen2)) ** memOwn RfuOff)
              (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase
                validPtr firstBadPtr csaved bigBytes lengths) from ?_)
          refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldOff2 => ?_)
          have hc2 := cvgulCall2Owned (hdrBaseAt hdrBase lengths i) lenBase spC
            (BitVec.ofNat 64 i) lengths[i]! (BitVec.ofNat 64 lengths.length) validPtr firstBadPtr
            oldLimit oldOff2 oldLen2 (bigBytes.drop (hdrOff lengths i)) csaved hsalign hslack
            hover hvalid
          rw [show (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) from shiftLeft3_ofNat i]
            at hc2
          have hc2F := cpsTripleWithin_frameR
            ((GasUsed ↦ₘ value) ** wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)))
            (by pcfx) hc2
          have hd2 := cvgulDispatch2 sp0 spC hdrBase lenBase validPtr firstBadPtr raIn csaved
            bigBytes lengths i oldOff2 oldLen2 value nTail hi hspC hraSaved hret halign hlen
            hResult hprefix htail
          refine cpsTripleWithin_weaken (fun h hp => by
            rw [hBODY] at hp
            have hp1 : ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA1) **
                (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
                EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                  ⟨LinkRA1, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x19 ↦ᵣ validPtr) **
                  (.x20 ↦ᵣ firstBadPtr) ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 **
                  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  (GasLimit ↦ₘ oldLimit) ** (RfuOff ↦ₘ oldOff2) ** (RfuLen ↦ₘ oldLen2) **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  savedFrame spC csaved **
                  regOwn .x5 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
                  regOwn .x28 **
                  (GasUsed ↦ₘ value) ** wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)))) h := by
              xperm_hyp hp
            have hp2 := sepConj_mono (regIs_implies_regOwn .x10) (sepConj_mono
              (regIs_implies_regOwn .x1) (sepConj_mono (regIs_implies_regOwn .x18)
              (sepConj_mono (regIs_implies_regOwn .x21)
              (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _) (fun _ x => x))))) h hp1
            xperm_hyp hp2) (fun _ hq => hq)
            (cpsTripleWithin_seq_perm_same_cr (fun h hq => by xperm_hyp hq) hc2F hd2)
        have hntakenF := cpsTripleWithin_frameR RframeOk1 (by rw [hRframeOk1]; pcfx) hntaken
        refine cpsTripleWithin_weaken (fun h hp => by rw [hRframeOk1]; xperm_hyp hp)
          (fun _ hq => hq)
          (cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hntakenF hcont)
      · -- PARSE-FAIL arm (gas_used): `bne` taken → status ≠ 0 exit.
        rw [hsf]
        have hbne := bne_spec_gen_within .x10 .x0 (156 : BitVec 13) status (0 : Word) (D + 128)
        have hbneC := cpsBranchWithin_extend_code cvgul_mono
          (cpsBranchWithin_extend_code (cr' := cvgulCode)
            (CodeReq.ofProg_mem_at D (D + 128) cvgulProg 32 (.BNE .x10 .x0 (156 : BitVec 13))
              (by bv_omega) (by rw [cvgul_length]; decide) rfl
              (by rw [cvgul_length]; decide)) hbne)
        have htaken := cpsBranchWithin_takenStripPure2 hbneC (fun hp hq => by
          obtain ⟨_, _, _, _, _, hrest⟩ := hq
          exact absurd ((sepConj_pure_right _).1 hrest).2 hstatus)
        rw [show (D + 128) + signExtend13 (156 : BitVec 13) = D + 284 from by
          rw [show signExtend13 (156 : BitVec 13) = (156 : Word) from by decide]; bv_omega] at htaken
        have htakenF := cpsTripleWithin_frameR
          ((.x1 ↦ᵣ LinkRA1) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
            (GasUsed ↦ₘ value) ** (GasLimit ↦ₘ oldLimit) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA1, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
            ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
            wordArrayFrom lenBase 0 (lengths.take i) **
            wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
            bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
            (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
            ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
            ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) (by pcfx) htaken
        have hpfC := cpsTripleWithin_extend_code cvgul_mono
          (retParseFail sp0 spC raIn (BitVec.ofNat 64 i) firstBadPtr csaved
            ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
              regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
              regOwn .x30 ** regOwn .x31 ** (GasUsed ↦ₘ value) ** (GasLimit ↦ₘ oldLimit) **
              memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA1, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) ** (validPtr ↦ₘ (1 : Word)))
            (by pcfx) LinkRA1 (BitVec.ofNat 64 lengths.length) lenBase
            (hdrBaseAt hdrBase lengths i) validPtr status hspC hraSaved hret)
        have hcompose := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
          have hp1 : ((firstBadPtr ↦ₘ (0 : Word)) **
              ((.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (.x10 ↦ᵣ status) **
                (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ LinkRA1) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
                  regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
                  regOwn .x30 ** regOwn .x31 ** (GasUsed ↦ₘ value) ** (GasLimit ↦ₘ oldLimit) **
                  memOwn RfuOff ** memOwn RfuLen **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                    ⟨LinkRA1, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (validPtr ↦ₘ (1 : Word))))) h := by xperm_hyp hp
          have hp2 := sepConj_mono_left memIs_implies_memOwn h hp1
          xperm_hyp hp2) htakenF hpfC
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
          (cpsTripleWithin_mono_nSteps
            (show 1 + 11 ≤ 1 + ((13 + 1 + nCall 9) + (27 + nTail)) by omega) hcompose)
        refine Or.inr (Or.inr ⟨i, status, ?_⟩)
        refine (sepConj_pure_left h).mpr
          ⟨⟨hi, hprefix, Or.inl ⟨value, hResult, hstatus⟩⟩, ?_⟩
        unfold commonRet payload
        rw [hsf, hraSaved, wordArray_split lenBase lengths i hi,
          EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen, ← hHB]
        have hp1 : ((GasUsed ↦ₘ value) ** (GasLimit ↦ₘ oldLimit) **
            (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) **
            (IterI ↦ₘ BitVec.ofNat 64 i) **
            EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA1, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            ((.x10 ↦ᵣ status) ** (validPtr ↦ₘ (1 : Word)) **
              (firstBadPtr ↦ₘ BitVec.ofNat 64 i) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
              (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) ** (.x18 ↦ᵣ csaved.s2) **
              (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
              (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
              ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
              ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
              (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
              regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
              regOwn .x30 ** regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)))) h := by
          rw [← hLi]; xperm_hyp hq
        have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
          (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _) (fun _ x => x))))) h hp1
        xperm_hyp hp2

#print axioms cvgulDispatch1

/-! ## One full iteration: guard → call 1 → dispatch 1 (`D+68 → raIn`, `i < N`)

    Shapes `LoopInv i` into `cvgulIterEntry`'s split precondition (splitting the
    arrays and peeling the four K34 scratch cells to arbitrary incumbents), runs
    the entry half to K34's first `flatPost`, then the two-call dispatch. -/

set_option maxRecDepth 8000 in
theorem cvgulIter (sp0 spC hdrBase lenBase validPtr firstBadPtr raIn : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) (i nTail : Nat)
    (hi : i < lengths.length)
    (hN : lengths.length < 2 ^ 64)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (halign : hdrOff lengths i % 8 = 0)
    (hlen : hdrOff lengths i ≤ bigBytes.length)
    (hsalign : (hdrBaseAt hdrBase lengths i).toNat % 8 = 0)
    (hslack : lengths[i]! + 9 ≤ (bigBytes.drop (hdrOff lengths i)).length)
    (hover : (hdrBaseAt hdrBase lengths i).toNat +
      (bigBytes.drop (hdrOff lengths i)).length < 2 ^ 64)
    (hvalid : ∀ k, k < (bigBytes.drop (hdrOff lengths i)).length →
      isValidByteAccess (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 k) = true)
    (hprefix : ∀ j, j < i → hdrGasOk hdrBase bigBytes lengths j)
    (htail : (∀ j, j < i + 1 → hdrGasOk hdrBase bigBytes lengths j) →
      cpsTripleWithin nTail (D + 68) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths (i + 1))
        (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths)) :
    cpsTripleWithin ((1 + (13 + 1 + nCall 10)) +
        (1 + ((13 + 1 + nCall 9) + (27 + nTail)))) (D + 68) raIn fullCode
      (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths i)
      (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) := by
  have hLi : lengths[i]! = lengths[i] := getElem!_pos lengths i hi
  have hHB : hdrBaseAt hdrBase lengths i = hdrBase + BitVec.ofNat 64 (hdrOff lengths i) := rfl
  set EBody : Assertion :=
    ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
      (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
      (.x21 ↦ᵣ BitVec.ofNat 64 i) ** savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) **
      (firstBadPtr ↦ₘ (0 : Word)) ** wordArrayFrom lenBase 0 (lengths.take i) **
      ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
      bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
      memOwn IterPtr ** memOwn IterI ** regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
      stackFree (spC + signExtend12 (-32 : BitVec 12)) 8) with hEBody
  refine cpsTripleWithin_weaken (fun h hp => by
    unfold LoopInv payload scratchRegs at hp
    rw [wordArray_split lenBase lengths i hi,
      EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen,
      ← hHB, ← hLi] at hp
    rw [hEBody]; xperm_hyp hp) (fun _ hq => hq)
    (show cpsTripleWithin ((1 + (13 + 1 + nCall 10)) +
        (1 + ((13 + 1 + nCall 9) + (27 + nTail)))) (D + 68) raIn fullCode
      ((((EBody ** memOwn GasUsed) ** memOwn GasLimit) ** memOwn RfuOff) ** memOwn RfuLen)
      (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) from ?_)
  refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldLen => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (show cpsTripleWithin ((1 + (13 + 1 + nCall 10)) +
        (1 + ((13 + 1 + nCall 9) + (27 + nTail)))) (D + 68) raIn fullCode
      ((((EBody ** (RfuLen ↦ₘ oldLen)) ** memOwn GasUsed) ** memOwn GasLimit) ** memOwn RfuOff)
      (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) from ?_)
  refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldOff => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (show cpsTripleWithin ((1 + (13 + 1 + nCall 10)) +
        (1 + ((13 + 1 + nCall 9) + (27 + nTail)))) (D + 68) raIn fullCode
      ((((EBody ** (RfuLen ↦ₘ oldLen)) ** (RfuOff ↦ₘ oldOff)) ** memOwn GasUsed) **
        memOwn GasLimit)
      (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) from ?_)
  refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldLimit => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (show cpsTripleWithin ((1 + (13 + 1 + nCall 10)) +
        (1 + ((13 + 1 + nCall 9) + (27 + nTail)))) (D + 68) raIn fullCode
      ((((EBody ** (RfuLen ↦ₘ oldLen)) ** (RfuOff ↦ₘ oldOff)) ** (GasLimit ↦ₘ oldLimit)) **
        memOwn GasUsed)
      (cvgulPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) from ?_)
  refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldOut => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by rw [hEBody] at hp; xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_seq_same_cr
      (cvgulIterEntry spC hdrBase lenBase validPtr firstBadPtr csaved bigBytes lengths i
        oldOut oldLimit oldOff oldLen hi hN hsalign hslack hover hvalid)
      (cvgulDispatch1 sp0 spC hdrBase lenBase validPtr firstBadPtr raIn csaved bigBytes lengths i
        oldOff oldLen oldLimit nTail hi hspC hraSaved hret halign hlen hsalign hslack hover
        hvalid hprefix htail))

#print axioms cvgulIter

end EvmAsm.Codegen.ChainValidateGasUsedUnderLimitSpec
