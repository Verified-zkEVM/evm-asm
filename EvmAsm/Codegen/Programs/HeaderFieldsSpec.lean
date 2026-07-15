/-
  EvmAsm.Codegen.Programs.HeaderFieldsSpec

  Caller `Fn.Spec`-shaped contracts (raw pinned `cpsTripleWithin`) for the
  migrated RLP-header-field extractors in `HeaderFields.lean`:

    * `header_extract_state_root`      (field 3  = rlp_walk_init + 4 rlp_walk_next)
    * `header_extract_receipts_root`   (field 5  = init + 6)
    * `header_extract_withdrawals_root`(field 16 = init + 17)

  Each body is proven as a raw `cpsTripleWithin` over
  `CodeReq.ofProg base headerExtract*_prog`: ABI prologue/frame → one
  `rlp_walk_init` call → N sequential `rlp_walk_next` calls (composed via
  `EvmAsm.Codegen.RlpWalkCallSAsm.walk_init_next_N`, threading the strict
  `StrictListPayload`/`StrictPrefix`/`rlpWalkNextOk` invariants each next's
  precondition needs) → the status/length branch → the fixed 32-byte LBU/SB
  copy loop (the alignment-free re-emit, modeled on `mset_memcpy`) → the
  restore/return epilogue.

  This file is PROOF-ONLY over the already-emitted (LBU-fixed) bytes; it changes
  no guest bytes. Classical-3 axioms only; no `sorry`/`native_decide`/`bv_decide`.
-/
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.RlpWalkCallSAsm
import EvmAsm.Codegen.Programs.RlpWalkInitFlatSAsm
import EvmAsm.Codegen.Programs.RlpWalkNextFlatSAsm
import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase
import EvmAsm.Codegen.Programs.AccountBalanceHelperSpec
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.LaResolve
import EvmAsm.Codegen.Programs.HeaderFieldsSpecDispatch2

namespace EvmAsm.Codegen.HeaderFieldsSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- Discharge a `.pcFree` side goal over frames of `bytesRegion`/`regIs`/`memIs`
    cells (local re-declaration of the `mset_memcpy` helper macro). -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

set_option maxRecDepth 8000 in
/-- The whole-program `header_extract_state_root` caller `Fn.Spec`: a single
    raw-pinned `cpsTripleWithin` over all 68 instructions from `hesrBase` to the
    function return (`saved.ra &&& ~~~1`), composing the ABI prologue [0]-[9]
    with the init-call dispatch (`hesrInitDispatch`).  `listLen = ofNat listLenN`. -/
theorem header_extract_state_root_fnspec
    (sp0 newSp listBase outPtr : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    {cr : CodeReq}
    (hcr_prog : ∀ a i, hesrCode a = some i → cr a = some i)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_wi : ∀ a i,
      (CodeReq.singleton (hesrBase + 40) (.JAL .x1 hesrInitOffset)).union
        (rlp_walk_init_code wiBase) a = some i → cr a = some i)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_slack : listLenN + 9 ≤ headerBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hbound : ∀ o next len, o ≤ listLenN →
      rlpItemDecode headerBytes o (listBase + BitVec.ofNat 64 o)
        (listBase + BitVec.ofNat 64 listLenN) next len →
      (next - len - listBase).toNat + 32 ≤ headerBytes.length)
    (h_newSp : newSp = sp0 + signExtend12 (-48 : BitVec 12)) :
    cpsTripleWithin
      (10 + (1 + 81 + (1 + (4 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 +
        (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))))))))))))))
      hesrBase (saved.ra &&& ~~~(1 : Word)) cr
      (((.x2 ↦ᵣ sp0) ** regsAt hxFrame (savedVals saved) ** frameSlotsOwn hxFrame newSp **
        (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLenN) ** (.x12 ↦ᵣ outPtr) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
        memOwn hesrOffAddr ** memOwn hesrLenAddr ** memOwn (newSp + 32) ** memOwn (newSp + 40)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31)
      (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLenN 3
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** memOwn (newSp + 40))) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn7
  intro v5 v6 v7 v28 v29 v30 v31
  have hpro := cpsTripleWithin_extend_code hcr_prog
    (hesrPrologue sp0 newSp listBase (BitVec.ofNat 64 listLenN) outPtr saved h_newSp)
  have hproF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
     memOwn hesrOffAddr ** memOwn hesrLenAddr ** memOwn (newSp + 32) ** memOwn (newSp + 40))
    (by pcFreeR) hpro
  have hdisp := hesrInitDispatch listBase outPtr newSp saved.ra v5 v6 v7 v28 v29 v30 v31 saved
    headerBytes outBytes listLenN hcr_prog hcr_wn hcr_wi h_src_align h_dst_align h_slack
    h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound
  have hcomp := cpsTripleWithin_seq_perm_same_cr
    (fun h hq => by unfold hesrAmbient; xperm_chunked hq) hproF hdisp
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h) hcomp

#print axioms header_extract_state_root_fnspec

end EvmAsm.Codegen.HeaderFieldsSpec
