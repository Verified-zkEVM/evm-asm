/-
  EvmAsm.Codegen.Programs.HeaderReceiptsRootSpec

  The whole-program caller `Fn.Spec` for `header_extract_receipts_root`
  (RLP field index 5 = `rlp_walk_init` + 6×`rlp_walk_next`), assembled from the
  extractor-parametric generic spine (`hfPrologue` ;; `hfInitDispatch` with a
  6-deep nested walk-stage chain built out of `hfStageRec`/`hfStageSel`) and the
  concrete receipts success tail (`herrSuccessTailBundled`).

  Mirrors `header_extract_state_root_fnspec` (field 3) with index 5 and the
  receipts base/prog/scratch addresses.

  Classical-3 axioms only; no `sorry`/`native_decide`/`bv_decide`.
-/
import EvmAsm.Codegen.Programs.HeaderReceiptsRootTail

namespace EvmAsm.Codegen.HeaderReceiptsRootSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.HeaderFieldsSpec
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- The `jal ra, rlp_walk_init` immediate at instruction [10] (`herrBase+40`). -/
def herrInitOffset : BitVec 21 :=
  jalOff Codegen.GuestAddrs.rlp_walk_init (Codegen.GuestAddrs.header_extract_receipts_root + 40)

/-- Discharge one `CodeReq.singleton A ins → cr` membership fact for the receipts
    program via `ofProg_mem_at` composed with the caller `hcr_prog`. -/
private theorem herrMem {cr : CodeReq} (prog : List Instr)
    (hprog : prog = Codegen.headerExtractReceiptsRoot_prog)
    (hcr_prog : ∀ a i, herrCode a = some i → cr a = some i)
    (A : Word) (k : Nat) (ins : Instr)
    (hk : k < prog.length)
    (hA : A = herrBase + BitVec.ofNat 64 (4 * k))
    (hins : prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → cr a = some i := by
  subst hprog
  exact fun a i hs => hcr_prog a i
    (CodeReq.ofProg_mem_at herrBase A Codegen.headerExtractReceiptsRoot_prog k ins hA hk hins
      (by rw [herr_prog_length]; norm_num) a i hs)

/-- From the final decode of a strict `index`-th item (in a `listLen`-window list),
    extract the last item's decode at some offset `off ≤ listLen`.  Used to feed the
    caller's `hbound` at the success tail (which only sees the abstract `Success`). -/
private theorem herrLastDecodeBound {base : Word} {bytes : List (BitVec 8)}
    {endOff : Nat} (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    ∀ {index startOff : Nat} {next len : Word},
      RlpListNthItemSAsm.StrictNthItem bytes base (base + BitVec.ofNat 64 endOff)
        index startOff next len →
      startOff ≤ endOff →
      ∃ off, off ≤ endOff ∧ rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
        (base + BitVec.ofNat 64 endOff) next len := by
  intro index startOff next len h
  induction h with
  | zero off n l hi => exact fun hst => ⟨off, hst, hi⟩
  | succ i off n l fn fl hi hrest ih =>
      intro hst
      exact ih (EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_advance hi hst hover).2.2

set_option maxRecDepth 8000 in
/-- The whole-program `header_extract_receipts_root` caller `Fn.Spec`: a single
    raw-pinned `cpsTripleWithin` over all 78 instructions from `herrBase` to the
    function return (`saved.ra &&& ~~~1`), composing the ABI prologue [0]-[9] with
    the init-call dispatch (`hfInitDispatch`) whose success continuation is the
    6-deep generic walk-stage chain selecting RLP field index 5. -/
theorem header_extract_receipts_root_fnspec
    (sp0 newSp listBase outPtr : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    {cr : CodeReq}
    (hcr_prog : ∀ a i, herrCode a = some i → cr a = some i)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_wi : ∀ a i,
      (CodeReq.singleton (herrBase + 40) (.JAL .x1 herrInitOffset)).union
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
      (10 + (1 + 81 + (1 + (4 +
        (1 + 87 + (1 + (3 +
        (1 + 87 + (1 + (3 +
        (1 + 87 + (1 + (3 +
        (1 + 87 + (1 + (3 +
        (1 + 87 + (1 + (3 +
        (1 + 87 + (1 + (9 + 4 + (1 + 204)))))))))))))))))))))))
      herrBase (saved.ra &&& ~~~(1 : Word)) cr
      (((.x2 ↦ᵣ sp0) ** regsAt hxFrame (savedVals saved) ** frameSlotsOwn hxFrame newSp **
        (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLenN) ** (.x12 ↦ᵣ outPtr) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
        memOwn herrOffAddr ** memOwn herrLenAddr ** memOwn (newSp + 32) ** memOwn (newSp + 40)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31)
      (hfRetPost herrOffAddr herrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 5
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** memOwn (newSp + 40))) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn7
  intro v5 v6 v7 v28 v29 v30 v31
  -- shared status-1 return membership (status1PC = herrBase + 276)
  have hs0 := herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 276) 69 (.LI .x10 (1 : Word))
    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl
  have hs1 := herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 276 + 4) 70 (.JAL .x0 (8 : BitVec 21))
    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl
  have hs2 := herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 276 + 12) 72 (.LD .x1 .x2 (0 : BitVec 12))
    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl
  have hs3 := herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 276 + 16) 73 (.LD .x8 .x2 (8 : BitVec 12))
    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl
  have hs4 := herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 276 + 20) 74 (.LD .x9 .x2 (16 : BitVec 12))
    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl
  have hs5 := herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 276 + 24) 75 (.LD .x18 .x2 (24 : BitVec 12))
    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl
  have hs6 := herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 276 + 28) 76 (.ADDI .x2 .x2 (48 : BitVec 12))
    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl
  have hs7 := herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 276 + 32) 77 (.JALR .x0 .x1 (0 : BitVec 12))
    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl
  -- prologue [0]-[9]
  have h_storeMono : ∀ a i,
      CodeReq.ofProg (herrBase + 4) (storeProg hxFrame) a = some i → herrCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub herrBase (herrBase + 4)
      Codegen.headerExtractReceiptsRoot_prog (storeProg hxFrame) 1 (by bv_omega) rfl
      (by rw [herr_prog_length]; simp [hxFrame])
      (by rw [herr_prog_length]; norm_num) a i h_mem
  have hpro := cpsTripleWithin_extend_code hcr_prog
    (hfPrologue (code := herrCode) herrBase sp0 newSp listBase (BitVec.ofNat 64 listLenN) outPtr saved
      h_newSp
      (CodeReq.ofProg_mem_at herrBase herrBase Codegen.headerExtractReceiptsRoot_prog 0
        (.ADDI .x2 .x2 (-48 : BitVec 12)) (by bv_omega)
        (by rw [herr_prog_length]; norm_num) rfl (by rw [herr_prog_length]; norm_num))
      h_storeMono
      (CodeReq.ofProg_mem_at herrBase (herrBase + 20) Codegen.headerExtractReceiptsRoot_prog 5
        (.MV .x8 .x10) (by bv_omega) (by rw [herr_prog_length]; norm_num) rfl (by rw [herr_prog_length]; norm_num))
      (CodeReq.ofProg_mem_at herrBase (herrBase + 24) Codegen.headerExtractReceiptsRoot_prog 6
        (.MV .x9 .x11) (by bv_omega) (by rw [herr_prog_length]; norm_num) rfl (by rw [herr_prog_length]; norm_num))
      (CodeReq.ofProg_mem_at herrBase (herrBase + 28) Codegen.headerExtractReceiptsRoot_prog 7
        (.MV .x18 .x12) (by bv_omega) (by rw [herr_prog_length]; norm_num) rfl (by rw [herr_prog_length]; norm_num))
      (CodeReq.ofProg_mem_at herrBase (herrBase + 32) Codegen.headerExtractReceiptsRoot_prog 8
        (.MV .x10 .x8) (by bv_omega) (by rw [herr_prog_length]; norm_num) rfl (by rw [herr_prog_length]; norm_num))
      (CodeReq.ofProg_mem_at herrBase (herrBase + 36) Codegen.headerExtractReceiptsRoot_prog 9
        (.MV .x11 .x9) (by bv_omega) (by rw [herr_prog_length]; norm_num) rfl (by rw [herr_prog_length]; norm_num)))
  have hproF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
     memOwn herrOffAddr ** memOwn herrLenAddr ** memOwn (newSp + 32) ** memOwn (newSp + 40))
    (by repeat' first
      | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj) hpro
  -- init dispatch with the nested 6-stage chain as hstage1
  have hdisp := hfInitDispatch (code := cr) herrBase herrOffAddr herrLenAddr listBase outPtr newSp
    saved.ra v5 v6 v7 v28 v29 v30 v31 saved headerBytes outBytes listLenN 5 (by omega)
    (herrBase + 276) (232 : BitVec 13) herrInitOffset h_src_align h_slack h_src_over h_src_valid
    (by simp only [herrInitOffset, wiBase, herrBase]; decide)
    (by simp only [herrBase]; decide)
    (by simp only [herrInitOffset, wiBase, herrBase]
        exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcr_wi
    (by rw [show signExtend13 (232 : BitVec 13) = (232 : Word) from by decide]; bv_omega)
    (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 44) 11 (.BNE .x12 .x0 (232 : BitVec 13))
      (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
    (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 48) 12 (.SD .x2 .x10 (32 : BitVec 12))
      (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
    (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 52) 13 (.SD .x2 .x11 (40 : BitVec 12))
      (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
    (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 56) 14 (.LD .x10 .x2 (32 : BitVec 12))
      (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
    (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 60) 15 (.LD .x11 .x2 (40 : BitVec 12))
      (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    -- hstage1: stage 1 (Rec, count 0) @ +64
    (fun cursorOff hpayload w5 w6 w7 w28 w29 w30 w31 =>
      cpsTripleWithin_weaken (fun h hp => by simp only [sepConj_emp_right']; xperm_chunked hp)
        (fun _ h => h)
        (hfStageRec (code := cr) herrOffAddr herrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
          outPtr newSp cursorOff listLenN cursorOff 0 5 (herrBase + 44) (0 : Word)
          w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
          empAssertion pcFree_emp (by omega)
          (herrBase + 64) (herrBase + 276) (208 : BitVec 13)
          (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_receipts_root + 64))
          hcr_wn
          (by simp only [wnBase, herrBase]; decide)
          (by simp only [herrBase]; decide)
          (by simp only [wnBase, herrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
          (by rw [show signExtend13 (208 : BitVec 13) = (208 : Word) from by decide]; bv_omega)
          h_src_align h_slack h_src_over h_src_valid
          (by omega) hpayload RlpListNthItemSAsm.StrictPrefix.zero hpayload.cursor_le
          (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 64) 16
            (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_receipts_root + 64)))
            (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
          (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 64 + 4) 17 (.BNE .x11 .x0 (208 : BitVec 13))
            (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
          (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 64 + 8) 18 (.SD .x2 .x10 (32 : BitVec 12))
            (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
          (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 64 + 12) 19 (.LD .x10 .x2 (32 : BitVec 12))
            (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
          (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 64 + 16) 20 (.LD .x11 .x2 (40 : BitVec 12))
            (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
          hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
          -- stage 2 (Rec, count 1) @ +84
          (fun offK1 len1 hle1 hp1 w5 w6 w7 w28 w29 w30 w31 =>
            cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
              (hfStageRec (code := cr) herrOffAddr herrLenAddr listBase
                (listBase + BitVec.ofNat 64 listLenN) outPtr newSp offK1 listLenN cursorOff 1 5
                (herrBase + 64 + 4) len1 w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN)
                saved headerBytes outBytes empAssertion pcFree_emp (by omega)
                (herrBase + 84) (herrBase + 276) (188 : BitVec 13)
                (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_receipts_root + 84))
                hcr_wn
                (by simp only [wnBase, herrBase]; decide)
                (by simp only [herrBase]; decide)
                (by simp only [wnBase, herrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
                (by rw [show signExtend13 (188 : BitVec 13) = (188 : Word) from by decide]; bv_omega)
                h_src_align h_slack h_src_over h_src_valid
                (by omega) hpayload hp1 hle1
                (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 84) 21
                  (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_receipts_root + 84)))
                  (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 84 + 4) 22 (.BNE .x11 .x0 (188 : BitVec 13))
                  (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 84 + 8) 23 (.SD .x2 .x10 (32 : BitVec 12))
                  (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 84 + 12) 24 (.LD .x10 .x2 (32 : BitVec 12))
                  (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 84 + 16) 25 (.LD .x11 .x2 (40 : BitVec 12))
                  (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
                -- stage 3 (Rec, count 2) @ +104
                (fun offK2 len2 hle2 hp2 w5 w6 w7 w28 w29 w30 w31 =>
                  cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
                    (hfStageRec (code := cr) herrOffAddr herrLenAddr listBase
                      (listBase + BitVec.ofNat 64 listLenN) outPtr newSp offK2 listLenN cursorOff 2 5
                      (herrBase + 84 + 4) len2 w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN)
                      saved headerBytes outBytes empAssertion pcFree_emp (by omega)
                      (herrBase + 104) (herrBase + 276) (168 : BitVec 13)
                      (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_receipts_root + 104))
                      hcr_wn
                      (by simp only [wnBase, herrBase]; decide)
                      (by simp only [herrBase]; decide)
                      (by simp only [wnBase, herrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
                      (by rw [show signExtend13 (168 : BitVec 13) = (168 : Word) from by decide]; bv_omega)
                      h_src_align h_slack h_src_over h_src_valid
                      (by omega) hpayload hp2 hle2
                      (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 104) 26
                        (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_receipts_root + 104)))
                        (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                      (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 104 + 4) 27 (.BNE .x11 .x0 (168 : BitVec 13))
                        (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                      (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 104 + 8) 28 (.SD .x2 .x10 (32 : BitVec 12))
                        (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                      (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 104 + 12) 29 (.LD .x10 .x2 (32 : BitVec 12))
                        (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                      (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 104 + 16) 30 (.LD .x11 .x2 (40 : BitVec 12))
                        (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
                      -- stage 4 (Rec, count 3) @ +124
                      (fun offK3 len3 hle3 hp3 w5 w6 w7 w28 w29 w30 w31 =>
                        cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
                          (hfStageRec (code := cr) herrOffAddr herrLenAddr listBase
                            (listBase + BitVec.ofNat 64 listLenN) outPtr newSp offK3 listLenN cursorOff 3 5
                            (herrBase + 104 + 4) len3 w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN)
                            saved headerBytes outBytes empAssertion pcFree_emp (by omega)
                            (herrBase + 124) (herrBase + 276) (148 : BitVec 13)
                            (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_receipts_root + 124))
                            hcr_wn
                            (by simp only [wnBase, herrBase]; decide)
                            (by simp only [herrBase]; decide)
                            (by simp only [wnBase, herrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
                            (by rw [show signExtend13 (148 : BitVec 13) = (148 : Word) from by decide]; bv_omega)
                            h_src_align h_slack h_src_over h_src_valid
                            (by omega) hpayload hp3 hle3
                            (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 124) 31
                              (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_receipts_root + 124)))
                              (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                            (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 124 + 4) 32 (.BNE .x11 .x0 (148 : BitVec 13))
                              (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                            (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 124 + 8) 33 (.SD .x2 .x10 (32 : BitVec 12))
                              (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                            (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 124 + 12) 34 (.LD .x10 .x2 (32 : BitVec 12))
                              (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                            (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 124 + 16) 35 (.LD .x11 .x2 (40 : BitVec 12))
                              (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                            hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
                            -- stage 5 (Rec, count 4) @ +144
                            (fun offK4 len4 hle4 hp4 w5 w6 w7 w28 w29 w30 w31 =>
                              cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
                                (hfStageRec (code := cr) herrOffAddr herrLenAddr listBase
                                  (listBase + BitVec.ofNat 64 listLenN) outPtr newSp offK4 listLenN cursorOff 4 5
                                  (herrBase + 124 + 4) len4 w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN)
                                  saved headerBytes outBytes empAssertion pcFree_emp (by omega)
                                  (herrBase + 144) (herrBase + 276) (128 : BitVec 13)
                                  (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_receipts_root + 144))
                                  hcr_wn
                                  (by simp only [wnBase, herrBase]; decide)
                                  (by simp only [herrBase]; decide)
                                  (by simp only [wnBase, herrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
                                  (by rw [show signExtend13 (128 : BitVec 13) = (128 : Word) from by decide]; bv_omega)
                                  h_src_align h_slack h_src_over h_src_valid
                                  (by omega) hpayload hp4 hle4
                                  (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 144) 36
                                    (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_receipts_root + 144)))
                                    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                                  (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 144 + 4) 37 (.BNE .x11 .x0 (128 : BitVec 13))
                                    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                                  (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 144 + 8) 38 (.SD .x2 .x10 (32 : BitVec 12))
                                    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                                  (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 144 + 12) 39 (.LD .x10 .x2 (32 : BitVec 12))
                                    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                                  (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 144 + 16) 40 (.LD .x11 .x2 (40 : BitVec 12))
                                    (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                                  hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
                                  -- stage 6 (Sel, index 5, count 5) @ +164
                                  (fun offK5 len5 hle5 hp5 w5 w6 w7 w28 w29 w30 w31 =>
                                    cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp)
                                      (fun h hq => hfRetPost_frame_mono
                                        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                                          (fun h' hh => by
                                            unfold hesrSpill at hh
                                            rw [sepConj_emp_right'] at hh
                                            exact sepConj_mono memIs_implies_memOwn
                                              (fun h'' hb => by rw [sepConj_emp_right']; exact hb) h' hh))))
                                        h hq)
                                      (hfStageSel (code := cr) (nTail := 9 + 4 + (1 + 204)) herrOffAddr herrLenAddr listBase
                                        (listBase + BitVec.ofNat 64 listLenN) outPtr newSp offK5 listLenN
                                        cursorOff 5 (herrBase + 144 + 4) len5 w5 w6 w7 w28 w29 w30 w31
                                        (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
                                        (hesrSpill newSp (listBase + BitVec.ofNat 64 offK5)
                                          (listBase + BitVec.ofNat 64 listLenN) ** empAssertion)
                                        (by repeat' first
                                          | exact pcFree_hesrSpill _ _ _ | exact pcFree_emp
                                          | apply pcFree_sepConj)
                                        (by omega)
                                        (herrBase + 164) (herrBase + 276) (108 : BitVec 13)
                                        (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_receipts_root + 164))
                                        hcr_wn
                                        (by simp only [wnBase, herrBase]; decide)
                                        (by simp only [herrBase]; decide)
                                        (by simp only [wnBase, herrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
                                        (by rw [show signExtend13 (108 : BitVec 13) = (108 : Word) from by decide]; bv_omega)
                                        h_src_align h_slack h_src_over h_src_valid hpayload hp5 hle5
                                        (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 164) 41
                                          (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_receipts_root + 164)))
                                          (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                                        (herrMem Codegen.headerExtractReceiptsRoot_prog rfl hcr_prog (herrBase + 164 + 4) 42 (.BNE .x11 .x0 (108 : BitVec 13))
                                          (by rw [herr_prog_length]; norm_num) (by bv_omega) rfl)
                                        hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
                                        -- success tail: herrSuccessTailBundled, with the h_src_bound
                                        -- derived from the abstract Success fact via hbound.
                                        (fun next len hSucc => by
                                          obtain ⟨c0, ep, n', hpay', hnth, hoffeq⟩ := hSucc
                                          have hend' : ep = listBase + BitVec.ofNat 64 listLenN :=
                                            hpay'.end_eq
                                          subst hend'
                                          have hover' : listBase.toNat + listLenN + 9 < 2 ^ 64 := by omega
                                          obtain ⟨off, hoff, hdec⟩ :=
                                            herrLastDecodeBound hover' hnth hpay'.cursor_le
                                          have hb : (n' - len - listBase).toNat + 32 ≤ headerBytes.length :=
                                            hbound off n' len hoff hdec
                                          have hb' : (next - len - listBase).toNat + 32 ≤ headerBytes.length := by
                                            rw [hoffeq]; exact hb
                                          rw [show (herrBase + 164 + 8 : Word) = herrBase + 172 from by bv_omega]
                                          exact cpsTripleWithin_extend_code hcr_prog
                                            (herrSuccessTailBundled next len listBase outPtr newSp
                                              (herrBase + 164 + 4) (BitVec.ofNat 64 listLenN) saved
                                              headerBytes outBytes listLenN
                                              (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
                                                (hesrSpill newSp (listBase + BitVec.ofNat 64 offK5)
                                                  (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))
                                              (by repeat' first
                                                | exact pcFree_regOwn | exact pcFree_hesrSpill _ _ _
                                                | exact pcFree_emp | apply pcFree_sepConj)
                                              h_src_align h_dst_align hb' h_dst_bound h_src_over h_dst_over
                                              h_src_valid h_dst_valid
                                              ⟨c0, listBase + BitVec.ofNat 64 listLenN, n', hpay', hnth,
                                                hoffeq⟩))))))))))))))
  have hcomp := cpsTripleWithin_seq_perm_same_cr
    (fun h hq => by unfold hfAmbient; xperm_chunked hq) hproF hdisp
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h) hcomp

/-! ## Guest-image specialization (`herrFullCode`) — same shape as state_root (#12313). -/

def herrCalleeCode : CodeReq :=
  (rlp_walk_init_code wiBase).union (rlp_walk_next_code wnBase)

def herrFullCode : CodeReq := herrCode.union herrCalleeCode

theorem herr_walk_init_disjoint :
    herrCode.Disjoint (rlp_walk_init_code wiBase) := by
  unfold herrCode rlp_walk_init_code wiBase herrBase
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [herr_prog_length]; decide
  · rw [rlp_walk_init_prog_length]; decide
  · rw [herr_prog_length, rlp_walk_init_prog_length]; decide

theorem herr_walk_next_disjoint :
    herrCode.Disjoint (rlp_walk_next_code wnBase) := by
  unfold herrCode rlp_walk_next_code wnBase herrBase
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [herr_prog_length]; decide
  · rw [rlp_walk_next_prog_length]; decide
  · rw [herr_prog_length, rlp_walk_next_prog_length]; decide

theorem herr_callee_disjoint : herrCode.Disjoint herrCalleeCode := by
  unfold herrCalleeCode
  exact CodeReq.Disjoint.union_right herr_walk_init_disjoint herr_walk_next_disjoint

theorem herr_hcr_prog :
    ∀ a i, herrCode a = some i → herrFullCode a = some i := by
  intro a i hi
  unfold herrFullCode
  exact CodeReq.union_mono_left a i hi

theorem herr_hcr_wn :
    ∀ a i, rlp_walk_next_code wnBase a = some i → herrFullCode a = some i := by
  intro a i hi
  unfold herrFullCode herrCalleeCode
  exact CodeReq.mono_union_right herr_walk_next_disjoint
    (fun a i h =>
      CodeReq.mono_union_right walk_init_next_disjoint (fun _ _ h' => h') a i h)
    a i hi

theorem herr_hcr_wi :
    ∀ a i,
      (CodeReq.singleton (herrBase + 40) (.JAL .x1 herrInitOffset)).union
        (rlp_walk_init_code wiBase) a = some i → herrFullCode a = some i := by
  intro a i h
  refine CodeReq.union_split_mono ?hsing ?hwi a i h
  · intro a i hs
    apply herr_hcr_prog
    exact CodeReq.ofProg_mem_at herrBase (herrBase + 40)
      Codegen.headerExtractReceiptsRoot_prog 10 (.JAL .x1 herrInitOffset)
      (by bv_omega) (by rw [herr_prog_length]; decide) rfl
      (by rw [herr_prog_length]; decide) a i hs
  · intro a i hi
    unfold herrFullCode herrCalleeCode
    exact CodeReq.mono_union_right herr_walk_init_disjoint
      (fun a i h => CodeReq.union_mono_left a i h) a i hi

/-- Flat guest-image triple for `header_extract_receipts_root`. Residual gate: `hbound`. -/
theorem header_extract_receipts_root_spec_within
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
      (10 + (1 + 81 + (1 + (4 +
        (1 + 87 + (1 + (3 +
        (1 + 87 + (1 + (3 +
        (1 + 87 + (1 + (3 +
        (1 + 87 + (1 + (3 +
        (1 + 87 + (1 + (3 +
        (1 + 87 + (1 + (9 + 4 + (1 + 204)))))))))))))))))))))))
      herrBase (saved.ra &&& ~~~(1 : Word)) herrFullCode
      (((.x2 ↦ᵣ sp0) ** regsAt hxFrame (savedVals saved) ** frameSlotsOwn hxFrame newSp **
        (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLenN) ** (.x12 ↦ᵣ outPtr) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
        memOwn herrOffAddr ** memOwn herrLenAddr ** memOwn (newSp + 32) ** memOwn (newSp + 40)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31)
      (hfRetPost herrOffAddr herrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 5
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** memOwn (newSp + 40))) :=
  header_extract_receipts_root_fnspec sp0 newSp listBase outPtr saved
    headerBytes outBytes listLenN
    herr_hcr_prog herr_hcr_wn herr_hcr_wi
    h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound
    h_src_valid h_dst_valid hbound h_newSp

end EvmAsm.Codegen.HeaderReceiptsRootSpec
