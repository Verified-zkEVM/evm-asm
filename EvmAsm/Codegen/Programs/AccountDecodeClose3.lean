/-
  `accountDecode_prog` caller-contract composition, part 3 — the return-edge
  tails: each status store (`a0 := 0`/`a0 := 1`) stitched to the shared ABI
  epilogue (`adEpilogue`, `AB+508 → saved.ra`).  Both land the restored
  caller-register/frame state with the appropriate `a0`.

  Mirrors `WithdrawalDecodeSpec.wdSuccessEpi`/`wdFailEpi`, but uses the 7-slot
  `adEpilogue` (account decode restores `x1/x8/x9/x18/x19/x20/x21`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeClose2
import EvmAsm.Codegen.Programs.AccountDecodeFrame

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm (Saved savedVals listNthFrame savedFrame)

set_option maxRecDepth 8000 in
/-- Failure return `AB+504 → saved.ra`: store `a0 := 1` and run the epilogue.
    Generic over the caller's remaining footprint `F`. -/
theorem adFailEpi (sp0 newSp v10old : Word) (saved : Saved) (F : Assertion) (hF : F.pcFree)
    (hnewSp : newSp = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin (1 + 9) (AB + 552) saved.ra fullCode
      (((.x10 : Reg) ↦ᵣ v10old) **
       (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt listNthFrame ** savedFrame newSp saved) ** F)
      (((.x10 : Reg) ↦ᵣ (1 : Word)) **
       (((.x2 : Reg) ↦ᵣ sp0) ** regsAt listNthFrame (savedVals saved) **
        savedFrame newSp saved) ** F) := by
  have hft := adFailTail v10old
    ((((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt listNthFrame ** savedFrame newSp saved) ** F)
    (by unfold savedFrame; repeat' first
        | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact pcFree_regsOwnAt _ | apply pcFree_sepConj)
  have hepi := adEpilogue sp0 newSp saved (((.x10 : Reg) ↦ᵣ (1 : Word)) ** F)
    (by exact pcFree_sepConj pcFree_regIs hF) hnewSp hret
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hft hepi)

#print axioms adFailEpi

set_option maxRecDepth 8000 in
/-- Success return `AB+496 → saved.ra`: store `a0 := 0`, jump past the failure
    `li`, and run the epilogue.  Generic over the caller's footprint `F`. -/
theorem adSuccessEpi (sp0 newSp v10old : Word) (saved : Saved) (F : Assertion) (hF : F.pcFree)
    (hnewSp : newSp = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin (2 + 9) (AB + 544) saved.ra fullCode
      (((.x10 : Reg) ↦ᵣ v10old) **
       (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt listNthFrame ** savedFrame newSp saved) ** F)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) **
       (((.x2 : Reg) ↦ᵣ sp0) ** regsAt listNthFrame (savedVals saved) **
        savedFrame newSp saved) ** F) := by
  have hst := adSuccessTail v10old
    ((((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt listNthFrame ** savedFrame newSp saved) ** F)
    (by unfold savedFrame; repeat' first
        | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact pcFree_regsOwnAt _ | apply pcFree_sepConj)
  have hepi := adEpilogue sp0 newSp saved (((.x10 : Reg) ↦ᵣ (0 : Word)) ** F)
    (by exact pcFree_sepConj pcFree_regIs hF) hnewSp hret
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hst hepi)

#print axioms adSuccessEpi

end EvmAsm.Codegen.AccountDecodeSpec
