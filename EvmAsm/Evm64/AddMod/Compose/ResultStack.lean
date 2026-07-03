/-
  EvmAsm.Evm64.AddMod.Compose.ResultStack

  Clean-`evmStackIs` result-post twin of the unconditional total ADDMOD
  witness `evm_addmod_total_stack_spec_within` (P4, issue #9704).

  Reshapes that witness's limb-cell pre into the public EVM form
  `evmStackIs sp [a, b, N]` (via `evmStackIs_triple_flat` + the `evmWordIs`
  unfold), and its `addmodLdResultOwned` post into the ADDMOD result word
  sitting on the EVM stack at `sp+64`
  (`evmStackIs (sp + 64) [EvmWord.addmod a b N]`), matching the public form
  of the SDIV/SMOD `_result_stack` witnesses. The modulus is folded from its
  four limb cells via `fromLimbs_getLimbN_vec`; everything the opcode
  clobbers is carried as the owned frame `addmodResultOwnedFrame`.
-/

import EvmAsm.Evm64.AddMod.Compose.TotalDispatch

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- Owned frame of the clean ADDMOD result post: every register and scratch
    cell the opcode clobbers, shed to ownership, at the post-prologue frame
    base `F = sp + 32`. This is `addmodLdResultOwned` minus its leading
    `x12`/result-word atoms (which the public post states explicitly). -/
def addmodResultOwnedFrame (F : Word) : Assertion :=
  regOwn .x0 ** regOwn .x1 ** regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x9 ** regOwn .x10 ** regOwn .x11 **
  divScratchOwnCallNoX1 F ** memOwn (F + signExtend12 (3936 : BitVec 12)) **
  evmWordOwn F **
  memOwn (F + signExtend12 (3872 : BitVec 12)) ** memOwn (F + signExtend12 (3880 : BitVec 12)) **
  memOwn (F + signExtend12 (3888 : BitVec 12)) ** memOwn (F + signExtend12 (3896 : BitVec 12)) **
  memOwn (F + signExtend12 (3840 : BitVec 12)) ** memOwn (F + signExtend12 (3848 : BitVec 12)) **
  memOwn (F + signExtend12 (3856 : BitVec 12)) ** memOwn (F + signExtend12 (3864 : BitVec 12)) **
  memOwn (F + signExtend12 (3904 : BitVec 12)) ** memOwn (F + signExtend12 (3912 : BitVec 12)) **
  memOwn (F + signExtend12 (3920 : BitVec 12)) ** memOwn (F + signExtend12 (3928 : BitVec 12))

/-- **The public total ADDMOD result-stack spec** (byte 0 → 864 over the total
    program ∪ v5 MOD callable): from `evmStackIs sp [a, b, N]` — the three
    operands on the EVM stack — plus the dispatcher register frame and the
    park/callable-scratch cells, to `evmStackIs (sp + 64) [EvmWord.addmod a b N]`
    with `x12 = sp + 64` (popped 3, pushed 1) and the clobbered state shed to
    `addmodResultOwnedFrame`. Unconditional in `a`, `b`, `N` — the `N = 0`,
    no-carry, and carry-out branches are all covered; the only hypotheses are
    the dispatcher-pinned code-layout side conditions. -/
theorem evm_addmod_total_result_stack_spec_within
    (bt sp : Word)
    (x1v x2v x5v x6v x7v x9v x10v x11v : Word) (a b N : EvmWord)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (hoffset1 : (bt + 244) + signExtend21 mo1 = calleeEntry)
    (callerAlign1 : ((bt + 244) + 4) &&& ~~~(1 : Word) = (bt + 244) + 4)
    (hoffset2 : (bt + 348) + signExtend21 mo2 = calleeEntry)
    (callerAlign2 : ((bt + 348) + 4) &&& ~~~(1 : Word) = (bt + 348) + 4)
    (hoffset3 : (bt + 452) + signExtend21 mo3 = calleeEntry)
    (callerAlign3 : ((bt + 452) + 4) &&& ~~~(1 : Word) = (bt + 452) + 4)
    (hoffsetNC : (bt + 836) + signExtend21 moNC = calleeEntry)
    (callerAlignNC : ((bt + 836) + 4) &&& ~~~(1 : Word) = (bt + 836) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj1 : (CodeReq.singleton (bt + 244) (.JAL .x1 mo1)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj2 : (CodeReq.singleton (bt + 348) (.JAL .x1 mo2)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj3 : (CodeReq.singleton (bt + 452) (.JAL .x1 mo3)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjNC : (CodeReq.singleton (bt + 836) (.JAL .x1 moNC)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin
      (((30 + 1) + 8) +
        (1 + ((((((21 + (1 + (unifiedDivBound + 1))) + 1)
            + (((24 + (1 + (unifiedDivBound + 1))) + 1)))
            + ((24 + (1 + (unifiedDivBound + 1))) + 1))
          + (((8 + 30) + 25) + 30)) + 1)))
      bt (bt + 864)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      ((((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1v) ** (.x2 ↦ᵣ x2v) **
         (.x5 ↦ᵣ x5v) ** (.x6 ↦ᵣ x6v) ** (.x7 ↦ᵣ x7v) ** (.x9 ↦ᵣ x9v) **
         (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v)) **
        evmStackIs sp [a, b, N]) **
       ((((sp + 32) + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
        (((sp + 32) + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
        (((sp + 32) + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
        (((sp + 32) + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
        (((sp + 32) + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
        (((sp + 32) + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
        (((sp + 32) + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
        (((sp + 32) + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3) **
        (((sp + 32) + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
        (((sp + 32) + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
        (((sp + 32) + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
        (((sp + 32) + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
        (((sp + 32) + signExtend12 (4056 : BitVec 12)) ↦ₘ u0) **
        (((sp + 32) + signExtend12 (4048 : BitVec 12)) ↦ₘ u1) **
        (((sp + 32) + signExtend12 (4040 : BitVec 12)) ↦ₘ u2) **
        (((sp + 32) + signExtend12 (4032 : BitVec 12)) ↦ₘ u3) **
        (((sp + 32) + signExtend12 (4024 : BitVec 12)) ↦ₘ u4) **
        (((sp + 32) + signExtend12 (4016 : BitVec 12)) ↦ₘ u5) **
        (((sp + 32) + signExtend12 (4008 : BitVec 12)) ↦ₘ u6) **
        (((sp + 32) + signExtend12 (4000 : BitVec 12)) ↦ₘ u7) **
        (((sp + 32) + signExtend12 (3992 : BitVec 12)) ↦ₘ shiftMem) **
        (((sp + 32) + signExtend12 (3984 : BitVec 12)) ↦ₘ nMem) **
        (((sp + 32) + signExtend12 (3976 : BitVec 12)) ↦ₘ jMem) **
        (((sp + 32) + signExtend12 (3968 : BitVec 12)) ↦ₘ retMem) **
        (((sp + 32) + signExtend12 (3960 : BitVec 12)) ↦ₘ dMem) **
        (((sp + 32) + signExtend12 (3952 : BitVec 12)) ↦ₘ dloMem) **
        (((sp + 32) + signExtend12 (3944 : BitVec 12)) ↦ₘ scratch_un0) **
        (((sp + 32) + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)))
      (((.x12 ↦ᵣ (sp + 64)) ** evmStackIs (sp + 64) [EvmWord.addmod a b N]) **
       addmodResultOwnedFrame (sp + 32)) := by
  have h := evm_addmod_total_stack_spec_within bt sp
    x1v x2v x5v x6v x7v x9v x10v x11v a b
    (N.getLimbN 0) (N.getLimbN 1) (N.getLimbN 2) (N.getLimbN 3)
    sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
    u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
    scratch_un0 scratchMem mo1 mo2 mo3 moNC calleeEntry
    hoffset1 callerAlign1 hoffset2 callerAlign2 hoffset3 callerAlign3
    hoffsetNC callerAlignNC retAlign hdisj1 hdisj2 hdisj3 hdisjNC hdisjTC
  rw [fromLimbs_getLimbN_vec] at h
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h
  · -- PRE: the public `evmStackIs sp [a, b, N]` form → `addmodTotalEntry`
    rw [evmStackIs_triple] at hp
    simp only [addmodTotalEntry, evmWordIs,
      signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
      BitVec.add_assoc, BitVec.reduceAdd] at hp ⊢
    xperm_hyp hp
  · -- POST: `addmodLdResultOwned` → the clean `evmStackIs` result form
    simp only [addmodLdResultOwned] at hq
    rw [show ((sp + 32) + 32 : Word) = sp + 64 from by bv_omega] at hq
    rw [evmStackIs_single]
    simp only [addmodResultOwnedFrame]
    xperm_hyp hq

end EvmAsm.Evm64.AddMod.Compose
