/-
  EvmAsm.Codegen.Programs.HeaderWithdrawalsRootChain

  The 17 per-stage walk-dispatch helper theorems for the
  `header_extract_withdrawals_root` caller `Fn.Spec` (RLP field index 16).

  Each `hewrStage{k}Chain` produces the triple for "stage k .. stage 16 + success
  tail" and invokes `hewrStage{k+1}Chain` as its continuation, so that no single
  elaboration nests all 17 walk stages (which would blow the whnf/heartbeat budget).
  Stages 0..15 are `hfStageRec`; stage 16 is `hfStageSel` (selecting index 16) with
  `hewrSuccessTailBundled` as its success tail.  Each helper's stated type is exactly
  the `hcont`/`hstage1` continuation type expected by its parent, so it plugs in
  directly.

  Classical-3 axioms only; no `sorry`/`native_decide`/`bv_decide`.
-/
import EvmAsm.Codegen.Programs.HeaderWithdrawalsRootTail

namespace EvmAsm.Codegen.HeaderWithdrawalsRootSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.HeaderFieldsSpec
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

set_option maxRecDepth 8000

/-- Discharge one `CodeReq.singleton A ins → cr` membership fact for the withdrawals
    program via `ofProg_mem_at` composed with the caller `hcr_prog`. -/
theorem hewrMem {cr : CodeReq} (prog : List Instr)
    (hprog : prog = Codegen.headerExtractWithdrawalsRoot_prog)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
    (A : Word) (k : Nat) (ins : Instr)
    (hk : k < prog.length)
    (hA : A = hewrBase + BitVec.ofNat 64 (4 * k))
    (hins : prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → cr a = some i := by
  subst hprog
  exact fun a i hs => hcr_prog a i
    (CodeReq.ofProg_mem_at hewrBase A Codegen.headerExtractWithdrawalsRoot_prog k ins hA hk hins
      (by rw [hewr_prog_length]; norm_num) a i hs)

/-- From the final decode of a strict `index`-th item (in a `listLen`-window list),
    extract the last item's decode at some offset `off ≤ listLen`. -/
private theorem hewrLastDecodeBound {base : Word} {bytes : List (BitVec 8)}
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


/-- Stage 16 (`hfStageSel`, count 16 → RLP index 16) at `hewrBase+384`: selects the
    withdrawals-root field and runs the concrete success tail. -/
theorem hewrStage16Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 16 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 307 (hewrBase + 384) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 368)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp)
    (fun h hq => hfRetPost_frame_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (fun h' hh => by
          unfold hesrSpill at hh
          rw [sepConj_emp_right'] at hh
          exact sepConj_mono memIs_implies_memOwn
            (fun h'' hb => by rw [sepConj_emp_right']; exact hb) h' hh))))
      h hq)
    (hfStageSel (code := cr) (nTail := 9 + 4 + (1 + 204)) hewrOffAddr hewrLenAddr listBase
    (listBase + BitVec.ofNat 64 listLenN) outPtr newSp offK listLenN cursorOff 16
    (hewrBase + 368) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    (hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion)
    (by repeat' first | exact pcFree_hesrSpill _ _ _ | exact pcFree_emp | apply pcFree_sepConj)
    (by omega)
    (hewrBase + 384) (hewrBase + 496) (108 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 384))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (108 : BitVec 13) = (108 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 384) 96 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 384))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 388) 97 (.BNE .x11 .x0 (108 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (fun next len hSucc => by
      obtain ⟨c0, ep, n', hpay', hnth, hoffeq⟩ := hSucc
      have hend' : ep = listBase + BitVec.ofNat 64 listLenN := hpay'.end_eq
      subst hend'
      have hover' : listBase.toNat + listLenN + 9 < 2 ^ 64 := by omega
      obtain ⟨off, hoff, hdec⟩ := hewrLastDecodeBound hover' hnth hpay'.cursor_le
      have hb : (n' - len - listBase).toNat + 32 ≤ headerBytes.length := hbound off n' len hoff hdec
      have hb' : (next - len - listBase).toNat + 32 ≤ headerBytes.length := by rw [hoffeq]; exact hb
      rw [show (hewrBase + 384 + 8 : Word) = hewrBase + 392 from by bv_omega]
      exact cpsTripleWithin_extend_code hcr_prog
        (hewrSuccessTailBundled next len listBase outPtr newSp (hewrBase + 388) (BitVec.ofNat 64 listLenN) saved
          headerBytes outBytes listLenN
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** (hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))
          (by repeat' first | exact pcFree_regOwn | exact pcFree_hesrSpill _ _ _ | exact pcFree_emp | apply pcFree_sepConj)
          h_src_align h_dst_align hb' h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
          ⟨c0, listBase + BitVec.ofNat 64 listLenN, n', hpay', hnth, hoffeq⟩)))


/-- Stage 15 (`hfStageRec`, count 15) at `hewrBase+364`. -/
theorem hewrStage15Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 15 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 399 (hewrBase + 364) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 348)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 15 16
    (hewrBase + 348) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 364) (hewrBase + 496) (128 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 364))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (128 : BitVec 13) = (128 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 364) 91 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 364))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 368) 92 (.BNE .x11 .x0 (128 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 372) 93 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 376) 94 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 380) 95 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage16Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 14 (`hfStageRec`, count 14) at `hewrBase+344`. -/
theorem hewrStage14Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 14 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 491 (hewrBase + 344) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 328)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 14 16
    (hewrBase + 328) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 344) (hewrBase + 496) (148 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 344))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (148 : BitVec 13) = (148 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 344) 86 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 344))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 348) 87 (.BNE .x11 .x0 (148 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 352) 88 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 356) 89 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 360) 90 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage15Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 13 (`hfStageRec`, count 13) at `hewrBase+324`. -/
theorem hewrStage13Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 13 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 583 (hewrBase + 324) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 308)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 13 16
    (hewrBase + 308) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 324) (hewrBase + 496) (168 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 324))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (168 : BitVec 13) = (168 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 324) 81 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 324))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 328) 82 (.BNE .x11 .x0 (168 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 332) 83 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 336) 84 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 340) 85 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage14Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 12 (`hfStageRec`, count 12) at `hewrBase+304`. -/
theorem hewrStage12Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 12 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 675 (hewrBase + 304) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 288)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 12 16
    (hewrBase + 288) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 304) (hewrBase + 496) (188 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 304))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (188 : BitVec 13) = (188 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 304) 76 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 304))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 308) 77 (.BNE .x11 .x0 (188 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 312) 78 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 316) 79 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 320) 80 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage13Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 11 (`hfStageRec`, count 11) at `hewrBase+284`. -/
theorem hewrStage11Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 11 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 767 (hewrBase + 284) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 268)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 11 16
    (hewrBase + 268) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 284) (hewrBase + 496) (208 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 284))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (208 : BitVec 13) = (208 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 284) 71 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 284))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 288) 72 (.BNE .x11 .x0 (208 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 292) 73 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 296) 74 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 300) 75 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage12Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 10 (`hfStageRec`, count 10) at `hewrBase+264`. -/
theorem hewrStage10Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 10 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 859 (hewrBase + 264) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 248)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 10 16
    (hewrBase + 248) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 264) (hewrBase + 496) (228 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 264))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (228 : BitVec 13) = (228 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 264) 66 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 264))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 268) 67 (.BNE .x11 .x0 (228 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 272) 68 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 276) 69 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 280) 70 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage11Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 9 (`hfStageRec`, count 9) at `hewrBase+244`. -/
theorem hewrStage9Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 9 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 951 (hewrBase + 244) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 228)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 9 16
    (hewrBase + 228) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 244) (hewrBase + 496) (248 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 244))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (248 : BitVec 13) = (248 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 244) 61 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 244))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 248) 62 (.BNE .x11 .x0 (248 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 252) 63 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 256) 64 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 260) 65 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage10Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 8 (`hfStageRec`, count 8) at `hewrBase+224`. -/
theorem hewrStage8Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 8 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 1043 (hewrBase + 224) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 208)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 8 16
    (hewrBase + 208) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 224) (hewrBase + 496) (268 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 224))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (268 : BitVec 13) = (268 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 224) 56 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 224))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 228) 57 (.BNE .x11 .x0 (268 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 232) 58 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 236) 59 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 240) 60 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage9Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 7 (`hfStageRec`, count 7) at `hewrBase+204`. -/
theorem hewrStage7Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 7 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 1135 (hewrBase + 204) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 188)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 7 16
    (hewrBase + 188) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 204) (hewrBase + 496) (288 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 204))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (288 : BitVec 13) = (288 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 204) 51 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 204))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 208) 52 (.BNE .x11 .x0 (288 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 212) 53 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 216) 54 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 220) 55 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage8Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 6 (`hfStageRec`, count 6) at `hewrBase+184`. -/
theorem hewrStage6Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 6 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 1227 (hewrBase + 184) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 168)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 6 16
    (hewrBase + 168) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 184) (hewrBase + 496) (308 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 184))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (308 : BitVec 13) = (308 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 184) 46 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 184))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 188) 47 (.BNE .x11 .x0 (308 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 192) 48 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 196) 49 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 200) 50 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage7Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 5 (`hfStageRec`, count 5) at `hewrBase+164`. -/
theorem hewrStage5Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 5 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 1319 (hewrBase + 164) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 148)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 5 16
    (hewrBase + 148) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 164) (hewrBase + 496) (328 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 164))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (328 : BitVec 13) = (328 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 164) 41 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 164))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 168) 42 (.BNE .x11 .x0 (328 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 172) 43 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 176) 44 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 180) 45 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage6Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 4 (`hfStageRec`, count 4) at `hewrBase+144`. -/
theorem hewrStage4Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 4 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 1411 (hewrBase + 144) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 128)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 4 16
    (hewrBase + 128) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 144) (hewrBase + 496) (348 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 144))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (348 : BitVec 13) = (348 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 144) 36 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 144))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 148) 37 (.BNE .x11 .x0 (348 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 152) 38 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 156) 39 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 160) 40 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage5Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 3 (`hfStageRec`, count 3) at `hewrBase+124`. -/
theorem hewrStage3Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 3 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 1503 (hewrBase + 124) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 108)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 3 16
    (hewrBase + 108) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 124) (hewrBase + 496) (368 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 124))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (368 : BitVec 13) = (368 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 124) 31 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 124))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 128) 32 (.BNE .x11 .x0 (368 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 132) 33 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 136) 34 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 140) 35 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage4Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 2 (`hfStageRec`, count 2) at `hewrBase+104`. -/
theorem hewrStage2Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 2 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 1595 (hewrBase + 104) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 88)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 2 16
    (hewrBase + 88) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 104) (hewrBase + 496) (388 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 104))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (388 : BitVec 13) = (388 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 104) 26 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 104))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 108) 27 (.BNE .x11 .x0 (388 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 112) 28 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 116) 29 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 120) 30 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage3Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 1 (`hfStageRec`, count 1) at `hewrBase+84`. -/
theorem hewrStage1Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (offK : Nat) (len : Word)
    (hle : offK ≤ listLenN)
    (hp : RlpListNthItemSAsm.StrictPrefix headerBytes listBase (listBase + BitVec.ofNat 64 listLenN) cursorOff 1 offK)
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 1687 (hewrBase + 84) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 68)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offK) (listBase + BitVec.ofNat 64 listLenN) ** empAssertion))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp offK listLenN cursorOff 1 16
    (hewrBase + 68) len w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 84) (hewrBase + 496) (408 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 84))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (408 : BitVec 13) = (408 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload hp hle
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 84) 21 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 84))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 88) 22 (.BNE .x11 .x0 (408 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 92) 23 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 96) 24 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 100) 25 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage2Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

/-- Stage 0 (`hfStageRec`, count 0) at `hewrBase+64`; matches `hfInitDispatch`'s `hstage1`. -/
theorem hewrStage0Chain
    {cr : CodeReq}
    (listBase outPtr newSp : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_prog : ∀ a i, hewrCode a = some i → cr a = some i)
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
    (hs0 : ∀ a i, CodeReq.singleton (hewrBase + 496) (.LI .x10 (1 : Word)) a = some i → cr a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → cr a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → cr a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → cr a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → cr a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → cr a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → cr a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (hewrBase + 496 + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → cr a = some i)
    (cursorOff : Nat)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff (listBase + BitVec.ofNat 64 listLenN))
    (w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 1779 (hewrBase + 64) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ (hewrBase + 44)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ (0 : Word)) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient hewrOffAddr hewrLenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 cursorOff) (listBase + BitVec.ofNat 64 listLenN)))) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLenN 16
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) := by
  exact cpsTripleWithin_weaken (fun h hp => by simp only [sepConj_emp_right']; xperm_chunked hp) (fun _ h => h)
    (hfStageRec (code := cr) hewrOffAddr hewrLenAddr listBase (listBase + BitVec.ofNat 64 listLenN)
    outPtr newSp cursorOff listLenN cursorOff 0 16
    (hewrBase + 44) (0 : Word) w5 w6 w7 w28 w29 w30 w31 (BitVec.ofNat 64 listLenN) saved headerBytes outBytes
    empAssertion pcFree_emp (by omega)
    (hewrBase + 64) (hewrBase + 496) (428 : BitVec 13)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 64))
    hcr_wn
    (by simp only [wnBase, hewrBase]; decide)
    (by simp only [hewrBase]; decide)
    (by simp only [wnBase, hewrBase]; exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by rw [show signExtend13 (428 : BitVec 13) = (428 : Word) from by decide]; bv_omega)
    h_src_align h_slack h_src_over h_src_valid
    (by omega) hpayload RlpListNthItemSAsm.StrictPrefix.zero hpayload.cursor_le
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 64) 16 (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_withdrawals_root + 64))) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 68) 17 (.BNE .x11 .x0 (428 : BitVec 13)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 72) 18 (.SD .x2 .x10 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 76) 19 (.LD .x10 .x2 (32 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    (hewrMem Codegen.headerExtractWithdrawalsRoot_prog rfl hcr_prog (hewrBase + 80) 20 (.LD .x11 .x2 (40 : BitVec 12)) (by rw [hewr_prog_length]; norm_num) (by bv_omega) rfl)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    (hewrStage1Chain listBase outPtr newSp saved headerBytes outBytes listLenN hcr_wn hcr_prog h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound h_src_valid h_dst_valid hbound hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 cursorOff hpayload))

end EvmAsm.Codegen.HeaderWithdrawalsRootSpec
