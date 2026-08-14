/-
  EvmAsm.Codegen.Programs.HeaderWithdrawalsRootSpec

  The whole-program caller `Fn.Spec` for `header_extract_withdrawals_root`
  (RLP field index 16 = `rlp_walk_init` + 17×`rlp_walk_next`), assembled from the
  extractor-parametric generic spine (`hfPrologue` ;; `hfInitDispatch` with a
  17-stage walk chain built out of `hfStageRec`/`hfStageSel`) and the concrete
  withdrawals success tail (`hewrSuccessTailBundled`).

  The 17-stage chain is factored across `HeaderWithdrawalsRootChain` (one theorem
  per stage) so no single elaboration nests all stages.  Mirrors
  `header_extract_receipts_root_fnspec` (field 5) with index 16 and the withdrawals
  base/prog/scratch addresses.

  Classical-3 axioms only; no `sorry`/`native_decide`/`bv_decide`.
-/
import EvmAsm.Codegen.Programs.HeaderWithdrawalsRootChain

namespace EvmAsm.Codegen.HeaderWithdrawalsRootSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.HeaderFieldsSpec
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

set_option maxRecDepth 8000

/-- The `jal ra, rlp_walk_init` immediate at instruction [10] (`hewrBase+40`). -/
def hewrInitOffset : BitVec 21 :=
  jalOff Codegen.GuestAddrs.rlp_walk_init (Codegen.GuestAddrs.header_extract_withdrawals_root + 40)

set_option maxRecDepth 8000 in
/-- The whole-program `header_extract_withdrawals_root` caller `Fn.Spec`: a single
    raw-pinned `cpsTripleWithin` over all 133 instructions from `hewrBase` to the
    function return (`saved.ra &&& ~~~1`), composing the ABI prologue [0]-[9] with
    the init-call dispatch (`hfInitDispatch`) whose success continuation is the
    17-stage generic walk chain (`hewrStage0Chain`) selecting RLP field index 16. -/
theorem header_extract_withdrawals_root_fnspec
    (sp0 newSp listBase outPtr : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    {cr : CodeReq}
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_wi : ∀ a i,
      (CodeReq.singleton (hewrBase + 40) (.JAL .x1 hewrInitOffset)).union
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
      (10 + (1 + 81 + (1 + (4 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      hewrBase (saved.ra &&& ~~~(1 : Word)) cr
      (((.x2 ↦ᵣ sp0) ** regsAt hxFrame (savedVals saved) ** frameSlotsOwn hxFrame newSp **
        (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLenN) ** (.x12 ↦ᵣ outPtr) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
        memOwn hewrOffAddr ** memOwn hewrLenAddr ** memOwn (newSp + 32) ** memOwn (newSp + 40)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31)
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** memOwn (newSp + 40))) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn7
  intro v5 v6 v7 v28 v29 v30 v31
  -- shared status-1 return membership (status1PC = hewrBase + 496)
  have hs0 := hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 496) 124 (.LI .x10 (1 : Word))
    (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl
  have hs1 := hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 496 + 4) 125 (.JAL .x0 (8 : BitVec 21))
    (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl
  have hs2 := hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 496 + 12) 127 (.LD .x1 .x2 (0 : BitVec 12))
    (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl
  have hs3 := hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 496 + 16) 128 (.LD .x8 .x2 (8 : BitVec 12))
    (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl
  have hs4 := hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 496 + 20) 129 (.LD .x9 .x2 (16 : BitVec 12))
    (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl
  have hs5 := hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 496 + 24) 130 (.LD .x18 .x2 (24 : BitVec 12))
    (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl
  have hs6 := hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 496 + 28) 131 (.ADDI .x2 .x2 (48 : BitVec 12))
    (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl
  have hs7 := hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 496 + 32) 132 (.JALR .x0 .x1 (0 : BitVec 12))
    (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl
  -- prologue [0]-[9]
  have h_storeMono : ∀ a i,
      CodeReq.ofProg (hewrBase + 4) (storeProg hxFrame) a = some i → hewrCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub hewrBase (hewrBase + 4)
      Codegen.headerExtractWithdrawalsRoot_prog (storeProg hxFrame) 1 (by bv_omega) rfl
      (by rw [hewr_prog_length]; simp [hxFrame])
      (by rw [hewr_prog_length]; norm_num) a i h_mem
  have hpro := cpsTripleWithin_extend_code hcr_prog
    (hfPrologue (code := hewrCode) hewrBase sp0 newSp listBase (BitVec.ofNat 64 listLenN) outPtr saved
      h_newSp
      (CodeReq.ofProg_mem_at hewrBase hewrBase Codegen.headerExtractWithdrawalsRoot_prog 0
        (.ADDI .x2 .x2 (-48 : BitVec 12)) (by bv_omega)
        (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num))
      h_storeMono
      (CodeReq.ofProg_mem_at hewrBase (hewrBase + 20) Codegen.headerExtractWithdrawalsRoot_prog 5
        (.MV .x8 .x10) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num))
      (CodeReq.ofProg_mem_at hewrBase (hewrBase + 24) Codegen.headerExtractWithdrawalsRoot_prog 6
        (.MV .x9 .x11) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num))
      (CodeReq.ofProg_mem_at hewrBase (hewrBase + 28) Codegen.headerExtractWithdrawalsRoot_prog 7
        (.MV .x18 .x12) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num))
      (CodeReq.ofProg_mem_at hewrBase (hewrBase + 32) Codegen.headerExtractWithdrawalsRoot_prog 8
        (.MV .x10 .x8) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num))
      (CodeReq.ofProg_mem_at hewrBase (hewrBase + 36) Codegen.headerExtractWithdrawalsRoot_prog 9
        (.MV .x11 .x9) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)))
  have hproF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
     memOwn hewrOffAddr ** memOwn hewrLenAddr ** memOwn (newSp + 32) ** memOwn (newSp + 40))
    (by repeat' first
      | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj) hpro
  -- init dispatch with the 17-stage chain as hstage1
  have hdisp := hfInitDispatch (code := cr) hewrBase hewrOffAddr hewrLenAddr listBase outPtr newSp
    saved.ra v5 v6 v7 v28 v29 v30 v31 saved headerBytes outBytes listLenN 16 (by omega)
    (hewrBase + 496) (452 : BitVec 13) hewrInitOffset h_src_align h_slack h_src_over h_src_valid
    (by simp only [hewrInitOffset, wiBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [hewrInitOffset, wiBase, hewrBase]
        exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcr_wi
    (by rw [show signExtend13 (452 : BitVec 13) = (452 : Word) from by decide]; bv_omega)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 44) 11 (.BNE .x12 .x0 (452 : BitVec 13))
      (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 48) 12 (.SD .x2 .x10 (32 : BitVec 12))
      (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 52) 13 (.SD .x2 .x11 (40 : BitVec 12))
      (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 56) 14 (.LD .x10 .x2 (32 : BitVec 12))
      (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 60) 15 (.LD .x11 .x2 (40 : BitVec 12))
      (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage0Chain listBase outPtr newSp saved headerBytes outBytes listLenN
      hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over
      h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7)
  have hcomp := cpsTripleWithin_seq_perm_same_cr
    (fun h hq => by unfold hfAmbient; xperm_chunked hq) hproF hdisp
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h) hcomp

/-! ## Guest-image specialization (`hewrFullCode`) — same shape as state_root (#12313). -/

def hewrCalleeCode : CodeReq :=
  (rlp_walk_init_code wiBase).union (rlp_walk_next_code wnBase)

def hewrFullCode : CodeReq := hewrCode.union hewrCalleeCode

theorem hewr_walk_init_disjoint :
    hewrCode.Disjoint (rlp_walk_init_code wiBase) := by
  unfold hewrCode rlp_walk_init_code wiBase hewrBase
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hewr_prog_length]; decide
  · rw [rlp_walk_init_prog_length]; decide
  · rw [hewr_prog_length, rlp_walk_init_prog_length]; decide

theorem hewr_walk_next_disjoint :
    hewrCode.Disjoint (rlp_walk_next_code wnBase) := by
  unfold hewrCode rlp_walk_next_code wnBase hewrBase
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hewr_prog_length]; decide
  · rw [rlp_walk_next_prog_length]; decide
  · rw [hewr_prog_length, rlp_walk_next_prog_length]; decide

theorem hewr_callee_disjoint : hewrCode.Disjoint hewrCalleeCode := by
  unfold hewrCalleeCode
  exact CodeReq.Disjoint.union_right hewr_walk_init_disjoint hewr_walk_next_disjoint

theorem hewr_hcr_prog :
    ∀ a i, hewrCode a = some i → hewrFullCode a = some i := by
  intro a i hi
  unfold hewrFullCode
  exact CodeReq.union_mono_left a i hi

theorem hewr_hcr_wn :
    ∀ a i, rlp_walk_next_code wnBase a = some i → hewrFullCode a = some i := by
  intro a i hi
  unfold hewrFullCode hewrCalleeCode
  exact CodeReq.mono_union_right hewr_walk_next_disjoint
    (fun a i h =>
      CodeReq.mono_union_right walk_init_next_disjoint (fun _ _ h' => h') a i h)
    a i hi

theorem hewr_hcr_wi :
    ∀ a i,
      (CodeReq.singleton (hewrBase + 40) (.JAL .x1 hewrInitOffset)).union
        (rlp_walk_init_code wiBase) a = some i → hewrFullCode a = some i := by
  intro a i h
  refine CodeReq.union_split_mono ?hsing ?hwi a i h
  · intro a i hs
    apply hewr_hcr_prog
    exact CodeReq.ofProg_mem_at hewrBase (hewrBase + 40)
      Codegen.headerExtractWithdrawalsRoot_prog 10 (.JAL .x1 hewrInitOffset)
      (by bv_omega) (by rw [hewr_prog_length]; decide) rfl
      (by rw [hewr_prog_length]; decide) a i hs
  · intro a i hi
    unfold hewrFullCode hewrCalleeCode
    exact CodeReq.mono_union_right hewr_walk_init_disjoint
      (fun a i h => CodeReq.union_mono_left a i h) a i hi

/-- Flat guest-image triple for `header_extract_withdrawals_root`. Residual gate: `hbound`. -/
theorem header_extract_withdrawals_root_spec_within
    (sp0 newSp listBase outPtr : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
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
      (10 + (1 + 81 + (1 + (4 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      hewrBase (saved.ra &&& ~~~(1 : Word)) hewrFullCode
      (((.x2 ↦ᵣ sp0) ** regsAt hxFrame (savedVals saved) ** frameSlotsOwn hxFrame newSp **
        (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLenN) ** (.x12 ↦ᵣ outPtr) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
        memOwn hewrOffAddr ** memOwn hewrLenAddr ** memOwn (newSp + 32) ** memOwn (newSp + 40)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31)
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** memOwn (newSp + 40))) :=
  header_extract_withdrawals_root_fnspec sp0 newSp listBase outPtr saved
    headerBytes outBytes listLenN
    hewr_hcr_prog hewr_hcr_wn hewr_hcr_wi
    h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound
    h_src_valid h_dst_valid hbound h_newSp

end EvmAsm.Codegen.HeaderWithdrawalsRootSpec
