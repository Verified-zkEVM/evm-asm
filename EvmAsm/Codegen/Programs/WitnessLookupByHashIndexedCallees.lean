/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedCallees

  Lift existing `widx_cmp32` / `widx_record_ptr` machine triples onto guest-
  linked PCs and into `WitnessLookupByHashIndexedSpec.fullCode` for callWithin.

  **Depends on PR #12169.** NEW file only — does not edit any #12169 path.
-/
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedSpec
import EvmAsm.Codegen.Proofs.MptWitnessIndexSpec
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.WitnessLookupByHashIndexedCallees

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
open EvmAsm.Crypto
open EvmAsm.Evm64
open EvmAsm.Codegen (laHi laLo)

/-- Guest-linked `widx_cmp32` triple, CodeReq widened to the indexed full image. -/
theorem widx_cmp32_guest_spec
    (ret ptrA ptrB : Word) (as bs : List (BitVec 8))
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignA : ptrA.toNat % 8 = 0) (halignB : ptrB.toNat % 8 = 0)
    (hovA : ptrA.toNat + 32 < 2 ^ 64)
    (hovB : ptrB.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 →
      isValidByteAccess (ptrA + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 →
      isValidByteAccess (ptrB + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 293 (Cmp32B : Word) ret fullCode
      (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA as ** bytesRegion ptrB bs)
      (widxCmp32Post ptrA ptrB ret as bs) := by
  have h0 := widx_cmp32_spec (Cmp32B : Word) ret ptrA ptrB as bs
    hlenA hlenB halignA halignB hovA hovB hvalidA hvalidB halignRet
  have hcr :
      CodeReq.ofProg (Cmp32B : Word) widxCmp32Prog =
      CodeReq.ofProg (Cmp32B : Word) widxCmp32_prog := by
    rw [widxCmp32Prog_eq_guest]
  have h0' :
      cpsTripleWithin 293 (Cmp32B : Word) ret
        (CodeReq.ofProg (Cmp32B : Word) widxCmp32_prog)
        (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA as ** bytesRegion ptrB bs)
        (widxCmp32Post ptrA ptrB ret as bs) := by
    rw [← hcr]; exact h0
  exact cpsTripleWithin_extend_code cmp32_in_fullCode h0'

/-! ## `widx_record_ptr` guest lift -/

abbrev recordPtrHi : BitVec 20 :=
  laHi GuestAddrs.widx_records (GuestAddrs.widx_record_ptr + 12)

abbrev recordPtrLo : BitVec 12 :=
  laLo GuestAddrs.widx_records (GuestAddrs.widx_record_ptr + 12)

/-- Guest Program is the parameterized body at this linked layout. -/
theorem widxRecordPtr_prog_eq_param :
    widxRecordPtr_prog = widxRecordPtrProg recordPtrHi recordPtrLo := by
  rfl

/-- `widx_record_ptr` at the guest PC, CodeReq widened to fullCode. -/
theorem widx_record_ptr_guest_spec
    (ret : Word) (rf : RegFile)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 7 (RecordPtrB : Word) ret fullCode
      (regAtoms rf exposedRegs ** ((.x1 : Reg) ↦ᵣ ret))
      (regAtoms (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo rf)
        exposedRegs ** ((.x1 : Reg) ↦ᵣ ret)) := by
  have h0 := widx_record_ptr_spec (RecordPtrB : Word) ret recordPtrHi recordPtrLo rf
    halignRet
  have hcr :
      CodeReq.ofProg (RecordPtrB : Word) (widxRecordPtrProg recordPtrHi recordPtrLo) =
      CodeReq.ofProg (RecordPtrB : Word) widxRecordPtr_prog := by
    rw [widxRecordPtr_prog_eq_param]
  have h0' :
      cpsTripleWithin 7 (RecordPtrB : Word) ret
        (CodeReq.ofProg (RecordPtrB : Word) widxRecordPtr_prog)
        (regAtoms rf exposedRegs ** ((.x1 : Reg) ↦ᵣ ret))
        (regAtoms (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo rf)
          exposedRegs ** ((.x1 : Reg) ↦ᵣ ret)) := by
    rw [← hcr]; exact h0
  exact cpsTripleWithin_extend_code record_ptr_in_fullCode h0'

/-! la of `widx_records` from AUIPC PC = RecordPtrB+12 resolves to WidxRecordsBase. -/
set_option maxRecDepth 8000 in
theorem record_ptr_la_eq_base :
    ((RecordPtrB : Word) + 12) +
        ((recordPtrHi.zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 recordPtrLo =
      WidxRecordsBase := by
  simp only [RecordPtrB, recordPtrHi, recordPtrLo, WidxRecordsBase,
    GuestAddrs.widx_record_ptr, GuestAddrs.widx_records, laHi, laLo]
  decide

/-- Index 0: after `widx_record_ptr`, a0 = WidxRecordsBase. -/
theorem widxRecordPtrResult_zero_a0 (rf : RegFile)
    (hidx : rf.get .x10 = (0 : Word)) :
    (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo rf).get .x10 =
      WidxRecordsBase := by
  -- get_set_ne rf r r' v (h : r' ≠ r); get_set_self rf r v (h : r ≠ x0)
  have n10_5 : (.x10 : Reg) ≠ .x5 := by decide
  have n5_6 : (.x5 : Reg) ≠ .x6 := by decide
  have n5_10 : (.x5 : Reg) ≠ .x10 := by decide
  have n5_0 : (.x5 : Reg) ≠ .x0 := by decide
  have n6_0 : (.x6 : Reg) ≠ .x0 := by decide
  have n10_0 : (.x10 : Reg) ≠ .x0 := by decide
  set auipc : Word :=
    (RecordPtrB : Word) + 4 + 4 + 4 +
      ((recordPtrHi.zeroExtend 32 <<< 12).signExtend 64)
  set laV : Word := auipc + signExtend12 recordPtrLo
  -- Named pipeline matching widxRecordPtrResult
  let s1 := rf.set .x5 (rf.get .x10 <<< 5)
  let s2 := s1.set .x6 (s1.get .x10 <<< 4)
  let s3 := s2.set .x5 (s2.get .x5 + s2.get .x6)
  let s4 := s3.set .x10 auipc
  let s5 := s4.set .x10 laV
  let s6 := s5.set .x10 (s5.get .x10 + s5.get .x5)
  -- Goal is s6.get x10 after unfold
  change s6.get .x10 = WidxRecordsBase
  have hs6 : s6.get .x10 = s5.get .x10 + s5.get .x5 :=
    RegFile.get_set_self s5 .x10 _ n10_0
  have hs5_10 : s5.get .x10 = laV := RegFile.get_set_self s4 .x10 laV n10_0
  have hs5_5 : s5.get .x5 = s4.get .x5 :=
    RegFile.get_set_ne s4 .x10 .x5 laV n5_10
  have hs4_5 : s4.get .x5 = s3.get .x5 :=
    RegFile.get_set_ne s3 .x10 .x5 auipc n5_10
  have hs3_5 : s3.get .x5 = s2.get .x5 + s2.get .x6 :=
    RegFile.get_set_self s2 .x5 _ n5_0
  have hs2_5 : s2.get .x5 = s1.get .x5 :=
    RegFile.get_set_ne s1 .x6 .x5 _ n5_6
  have hs2_6 : s2.get .x6 = s1.get .x10 <<< 4 :=
    RegFile.get_set_self s1 .x6 _ n6_0
  have hs1_5 : s1.get .x5 = rf.get .x10 <<< 5 :=
    RegFile.get_set_self rf .x5 _ n5_0
  have hs1_10 : s1.get .x10 = rf.get .x10 :=
    RegFile.get_set_ne rf .x5 .x10 _ n10_5
  have hsum : s5.get .x10 + s5.get .x5 = laV := by
    rw [hs5_10, hs5_5, hs4_5, hs3_5, hs2_5, hs2_6, hs1_5, hs1_10, hidx]
    simp [BitVec.zero_shiftLeft, BitVec.add_zero]
  have hla : laV = WidxRecordsBase := by
    -- Concrete linked layout: discharge by decide on the full la expression.
    simp only [laV, auipc, RecordPtrB, recordPtrHi, recordPtrLo, WidxRecordsBase,
      GuestAddrs.widx_record_ptr, GuestAddrs.widx_records, laHi, laLo]
    decide
  rw [hs6, hsum, hla]

/-! ## Zero-index regAtoms form (for callWithin from one-hit path) -/

/-- Build a RegFile with a0=0 and optional x5/x6 seeds; other regs zero. -/
def zeroIdxRf (v5 v6 : Word) : RegFile :=
  RegFile.set (RegFile.set (RegFile.set (fun _ : Reg => (0 : Word)) .x10 (0 : Word))
    .x5 v5) .x6 v6

theorem zeroIdxRf_x10 (v5 v6 : Word) : (zeroIdxRf v5 v6).get .x10 = (0 : Word) := by
  simp [zeroIdxRf, RegFile.get, RegFile.set]

/-- `widx_record_ptr` with a0=0 via guest regAtoms triple. Fuel 7. -/
theorem widx_record_ptr_zero_sep
    (ret v5 v6 : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 7 (RecordPtrB : Word) ret fullCode
      (regAtoms (zeroIdxRf v5 v6) exposedRegs ** ((.x1 : Reg) ↦ᵣ ret))
      (regAtoms (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo
          (zeroIdxRf v5 v6))
        exposedRegs ** ((.x1 : Reg) ↦ᵣ ret)) :=
  widx_record_ptr_guest_spec ret (zeroIdxRf v5 v6) halignRet

/-- After zero-index call, a0 is WidxRecordsBase. -/
theorem widx_record_ptr_zero_a0_of_result (v5 v6 : Word) :
    (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo
      (zeroIdxRf v5 v6)).get .x10 = WidxRecordsBase :=
  widxRecordPtrResult_zero_a0 (zeroIdxRf v5 v6) (zeroIdxRf_x10 v5 v6)

/-- Opaque post RegFile after zero-index `widx_record_ptr` (hides la/result reduce). -/
@[irreducible] def widxRecordPtrZeroPostRf : RegFile :=
  widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo
    (zeroIdxRf (0 : Word) (0 : Word))

theorem widxRecordPtrZeroPostRf_a0 :
    widxRecordPtrZeroPostRf.get .x10 = WidxRecordsBase := by
  unfold widxRecordPtrZeroPostRf
  exact widx_record_ptr_zero_a0_of_result (0 : Word) (0 : Word)

/-- Entry atoms for zero-index call. -/
def widxRecordPtrZeroPreAtoms : Assertion :=
  regAtoms (zeroIdxRf (0 : Word) (0 : Word)) exposedRegs

/-- Exit atoms for zero-index call. -/
def widxRecordPtrZeroPostAtoms : Assertion :=
  regAtoms widxRecordPtrZeroPostRf exposedRegs

theorem widxRecordPtrZeroPreAtoms_pcFree :
    widxRecordPtrZeroPreAtoms.pcFree :=
  pcFree_regAtoms _ _

theorem widxRecordPtrZeroPostAtoms_pcFree :
    widxRecordPtrZeroPostAtoms.pcFree :=
  pcFree_regAtoms _ _

/-- callWithin-ready zero-index `widx_record_ptr` framed by arbitrary `F`.
    Post uses irreducible `widxRecordPtrZeroPostRf` so callers avoid la/result whnf. -/
theorem widx_record_ptr_zero_callWithin
    (callerPC raOld : Word) (offset : BitVec 21) (F : Assertion)
    (hF : F.pcFree)
    (htarget : callerPC + signExtend21 offset = (RecordPtrB : Word))
    (hmem : ∀ a i,
      CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → fullCode a = some i)
    (hret : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4) :
    cpsTripleWithin 8 callerPC (callerPC + 4) fullCode
      (((.x1 : Reg) ↦ᵣ raOld) ** widxRecordPtrZeroPreAtoms ** F)
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** widxRecordPtrZeroPostAtoms ** F) := by
  have hcal0 := widx_record_ptr_zero_sep (callerPC + 4) (0 : Word) (0 : Word) hret
  -- Name the concrete atoms, then reshape (atoms**ra) → (ra**atoms)
  have hcal : cpsTripleWithin 7 (RecordPtrB : Word) (callerPC + 4) fullCode
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** widxRecordPtrZeroPreAtoms)
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** widxRecordPtrZeroPostAtoms) := by
    have h0 : cpsTripleWithin 7 (RecordPtrB : Word) (callerPC + 4) fullCode
        (widxRecordPtrZeroPreAtoms ** ((.x1 : Reg) ↦ᵣ (callerPC + 4)))
        (widxRecordPtrZeroPostAtoms ** ((.x1 : Reg) ↦ᵣ (callerPC + 4))) := by
      -- unfold opaque post rf into Result so hcal0 matches
      simpa [widxRecordPtrZeroPreAtoms, widxRecordPtrZeroPostAtoms,
        widxRecordPtrZeroPostRf] using hcal0
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp [widxRecordPtrZeroPreAtoms] at hp ⊢
        -- (atoms ** ra) → (ra ** atoms)
        xperm_chunked hp)
      (fun _ hq => by
        dsimp [widxRecordPtrZeroPostAtoms] at hq ⊢
        xperm_chunked hq) h0
  have hcall := callWithin_spec callerPC (RecordPtrB : Word) raOld offset 7
    htarget hmem widxRecordPtrZeroPreAtoms_pcFree hcal
  have hf := cpsTripleWithin_frameR F hF hcall
  -- frameR yields left-pair ((ra**atoms)**F); flatten + fuel 1+7=8
  have hn : 1 + 7 = 8 := rfl
  rw [hn] at hf
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hf

/-! ## Post peel: a0 = WidxRecordsBase + owns on other exposed -/

/-- Exposed regs without a0 — residual ownership after pealing concrete a0. -/
def exposedWithoutX10 : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Simplified post: concrete a0 + owns on the rest of exposed. -/
def widxRecordPtrZeroPostSimple : Assertion :=
  ((.x10 : Reg) ↦ᵣ WidxRecordsBase) ** regOwns exposedWithoutX10

theorem widxRecordPtrZeroPostSimple_pcFree :
    widxRecordPtrZeroPostSimple.pcFree :=
  pcFree_sepConj pcFree_regIs (pcFree_regOwns _)

/-- Extract one concrete register from `regAtomsOf`, owning the rest. -/
private theorem regAtomsOf_extract (vf : Reg → Word) (rs : List Reg) (r : Reg)
    (hin : r ∈ rs) (hnd : rs.Nodup) :
    ∀ h, regAtomsOf vf rs h →
      (((r : Reg) ↦ᵣ vf r) ** regOwns (rs.erase r)) h := by
  induction rs with
  | nil => simp at hin
  | cons r' rs ih =>
    intro h hp
    rw [regAtomsOf_cons] at hp
    by_cases heq : r' = r
    · -- Head is the target: own the tail. erase head = tail when head = r.
      have herase : (r' :: rs).erase r = rs := by
        simp [List.erase, heq]
      rw [herase]
      -- After heq, head atom is r ↦ vf r.
      have hp' : (((r : Reg) ↦ᵣ vf r) ** regAtomsOf vf rs) h := by
        rw [← heq]; exact hp
      exact sepConj_mono_right (regAtomsOf_to_regOwns vf rs) h hp'
    · -- Head is other: own head, IH on tail, xperm.
      have hin' : r ∈ rs := by
        have hmem := List.mem_cons.mp hin
        exact hmem.resolve_left (fun h => heq h.symm)
      have hnd' : rs.Nodup := (List.nodup_cons.mp hnd).2
      have ih' := ih hin' hnd'
      have hpOwn := sepConj_mono_left (regIs_to_regOwn r' (vf r')) h hp
      have hpIH := sepConj_mono_right ih' h hpOwn
      have herase : (r' :: rs).erase r = r' :: rs.erase r := by
        -- r' == r is false
        simp only [List.erase]
        have hbeq : (r' == r) = false := by
          rw [beq_eq_false_iff_ne]; exact heq
        simp [hbeq]
      rw [herase]
      -- hpIH : own r' ** (r↦ ** owns erase)
      -- want: r↦ ** (own r' ** owns erase)
      have hpFlat :
          (regOwn r' ** (((r : Reg) ↦ᵣ vf r) ** regOwns (rs.erase r))) h := by
        simpa using hpIH
      exact
        (show ((((r : Reg) ↦ᵣ vf r) ** (regOwn r' ** regOwns (rs.erase r))) h) from by
          xperm_chunked hpFlat)

/-- Drop zero-index post atoms to a0 = WidxRecordsBase + owns. -/
theorem widxRecordPtrZeroPostAtoms_to_simple :
    ∀ h, widxRecordPtrZeroPostAtoms h → widxRecordPtrZeroPostSimple h := by
  intro h hp
  dsimp [widxRecordPtrZeroPostAtoms, widxRecordPtrZeroPostSimple] at hp ⊢
  have ha0 := widxRecordPtrZeroPostRf_a0
  have hx0 : Reg.x0 ∉ exposedRegs := by decide
  rw [regAtoms_eq_regAtomsOf widxRecordPtrZeroPostRf exposedRegs hx0] at hp
  set vf : Reg → Word := fun r =>
    if r = (.x10 : Reg) then WidxRecordsBase else widxRecordPtrZeroPostRf.get r
  have hcongr : ∀ r ∈ exposedRegs, widxRecordPtrZeroPostRf.get r = vf r := by
    intro r _hr
    dsimp [vf]; split_ifs with hx
    · subst hx; exact ha0
    · rfl
  have hpV : regAtomsOf vf exposedRegs h := by
    have hc := regAtomsOf_congr
      (fun r => widxRecordPtrZeroPostRf.get r) vf exposedRegs hcongr
    rw [← hc]; exact hp
  have hin : (.x10 : Reg) ∈ exposedRegs := by decide
  have hnd : exposedRegs.Nodup := by decide
  have hex := regAtomsOf_extract vf exposedRegs .x10 hin hnd h hpV
  have hvf : vf .x10 = WidxRecordsBase := by simp [vf]
  have hex' :
      (((.x10 : Reg) ↦ᵣ WidxRecordsBase) ** regOwns (exposedRegs.erase .x10)) h := by
    rw [← hvf]; exact hex
  have herase : exposedRegs.erase (.x10 : Reg) = exposedWithoutX10 := by decide
  rw [herase] at hex'
  exact hex'

/-- callWithin zero-index with simplified post (a0 concrete). -/
theorem widx_record_ptr_zero_callWithin_simple
    (callerPC raOld : Word) (offset : BitVec 21) (F : Assertion)
    (hF : F.pcFree)
    (htarget : callerPC + signExtend21 offset = (RecordPtrB : Word))
    (hmem : ∀ a i,
      CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → fullCode a = some i)
    (hret : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4) :
    cpsTripleWithin 8 callerPC (callerPC + 4) fullCode
      (((.x1 : Reg) ↦ᵣ raOld) ** widxRecordPtrZeroPreAtoms ** F)
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** widxRecordPtrZeroPostSimple ** F) := by
  have h0 := widx_record_ptr_zero_callWithin callerPC raOld offset F hF
    htarget hmem hret
  -- Post is ra ** postAtoms ** F  (right-assoc)
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun h hq =>
      sepConj_mono_right
        (fun h hq =>
          sepConj_mono_left widxRecordPtrZeroPostAtoms_to_simple h hq)
        h hq)
    h0

/-! ## Live-ambient a0=0 callWithin (preserves non-a0 exposed values) -/

/-- callWithin `widx_record_ptr` with arbitrary exposed `rf` where a0=0.
    Post peels a0=WidxRecordsBase + owns other exposed. Fuel 8. -/
theorem widx_record_ptr_a0zero_callWithin_simple
    (callerPC raOld : Word) (rf : RegFile) (offset : BitVec 21)
    (F : Assertion) (hF : F.pcFree)
    (ha0 : rf.get .x10 = (0 : Word))
    (htarget : callerPC + signExtend21 offset = (RecordPtrB : Word))
    (hmem : ∀ a i,
      CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → fullCode a = some i)
    (hret : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4) :
    cpsTripleWithin 8 callerPC (callerPC + 4) fullCode
      (((.x1 : Reg) ↦ᵣ raOld) ** regAtoms rf exposedRegs ** F)
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
       ((.x10 : Reg) ↦ᵣ WidxRecordsBase) ** regOwns exposedWithoutX10 ** F) := by
  have hcal0 := widx_record_ptr_guest_spec (callerPC + 4) rf hret
  have hcal : cpsTripleWithin 7 (RecordPtrB : Word) (callerPC + 4) fullCode
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** regAtoms rf exposedRegs)
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
       regAtoms (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo rf)
         exposedRegs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hcal0
  have hcall := callWithin_spec callerPC (RecordPtrB : Word) raOld offset 7
    htarget hmem (pcFree_regAtoms _ _) hcal
  have hf := cpsTripleWithin_frameR F hF hcall
  have hn : 1 + 7 = 8 := rfl
  rw [hn] at hf
  -- peel post atoms → a0=Base ** owns rest (same extract as PostAtoms_to_simple)
  have hpeel :
      ∀ h, regAtoms (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo rf)
          exposedRegs h →
        (((.x10 : Reg) ↦ᵣ WidxRecordsBase) ** regOwns exposedWithoutX10) h := by
    intro h hp
    have hpV : regAtomsOf
        (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo rf).get
        exposedRegs h := by
      simpa [regAtoms_eq_regAtomsOf] using hp
    have hin : (.x10 : Reg) ∈ exposedRegs := by decide
    have hnd : exposedRegs.Nodup := by decide
    have hex := regAtomsOf_extract
      (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo rf).get
      exposedRegs .x10 hin hnd h hpV
    have hvf : (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo rf).get .x10 =
        WidxRecordsBase :=
      widxRecordPtrResult_zero_a0 rf ha0
    have hex' :
        (((.x10 : Reg) ↦ᵣ WidxRecordsBase) ** regOwns (exposedRegs.erase .x10)) h := by
      rw [← hvf]; exact hex
    have herase : exposedRegs.erase (.x10 : Reg) = exposedWithoutX10 := by decide
    rw [herase] at hex'
    exact hex'
  -- Flatten frameR then mono peel atoms (mirror zero_callWithin_simple)
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun h hq => by
      have hq1 : (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
          regAtoms (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo rf)
            exposedRegs ** F) h := by xperm_chunked hq
      have hq2 :=
        sepConj_mono_right
          (fun h' hq' =>
            sepConj_mono_left hpeel h' hq') h hq1
      -- mono leaves ((a0**owns)**F); flatten to a0**owns**F
      xperm_chunked hq2) hf

/-! ## cmp32 equal-hash callWithin (coverHit path) -/

/-- Pre-focus for equal-hash cmp32 (caller supplies a0/a1 + owns temps + bytes). -/
def widxCmp32EqPre (ptrA ptrB : Word) (hs : List (BitVec 8)) : Assertion :=
  ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  bytesRegion ptrA hs ** bytesRegion ptrB hs

/-- Post after equal-hash cmp32: a0=1, a1 owned, bytes preserved. -/
def widxCmp32EqPost (ptrA ptrB : Word) (hs : List (BitVec 8)) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
  bytesRegion ptrA hs ** bytesRegion ptrB hs

theorem widxCmp32EqPre_pcFree (ptrA ptrB : Word) (hs : List (BitVec 8)) :
    (widxCmp32EqPre ptrA ptrB hs).pcFree := by
  dsimp [widxCmp32EqPre]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regOwn
          (pcFree_sepConj pcFree_regOwn
            (pcFree_sepConj pcFree_regOwn
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (bytesRegion_pcFree _ _)))))))

theorem widxCmp32EqPost_pcFree (ptrA ptrB : Word) (hs : List (BitVec 8)) :
    (widxCmp32EqPost ptrA ptrB hs).pcFree := by
  dsimp [widxCmp32EqPost]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regOwn
        (pcFree_sepConj pcFree_regOwn
          (pcFree_sepConj pcFree_regOwn
            (pcFree_sepConj pcFree_regOwn
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (bytesRegion_pcFree _ _)))))))

/-- Equal 32-byte hashes: cmp32 returns a0=1. Fuel 294 = 1+293.
    `offset` is the JAL immediate at `callerPC` (site supplies via jalOff). -/
theorem widx_cmp32_eq_callWithin
    (callerPC raOld ptrA ptrB : Word) (hs : List (BitVec 8))
    (offset : BitVec 21) (F : Assertion) (hF : F.pcFree)
    (hlen : hs.length = 32)
    (halignA : ptrA.toNat % 8 = 0) (halignB : ptrB.toNat % 8 = 0)
    (hovA : ptrA.toNat + 32 < 2 ^ 64) (hovB : ptrB.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 →
      isValidByteAccess (ptrA + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 →
      isValidByteAccess (ptrB + BitVec.ofNat 64 k) = true)
    (htarget : callerPC + signExtend21 offset = (Cmp32B : Word))
    (hmem : ∀ a i,
      CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → fullCode a = some i)
    (hret : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4) :
    cpsTripleWithin 294 callerPC (callerPC + 4) fullCode
      (((.x1 : Reg) ↦ᵣ raOld) ** widxCmp32EqPre ptrA ptrB hs ** F)
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
       widxCmp32EqPost ptrA ptrB hs ** F) := by
  have hcal0 := widx_cmp32_guest_spec (callerPC + 4) ptrA ptrB hs hs
    hlen hlen halignA halignB hovA hovB hvalidA hvalidB hret
  have hpostEq :
      widxCmp32Post ptrA ptrB (callerPC + 4) hs hs =
        (((.x10 : Reg) ↦ᵣ (1 : Word)) **
         ((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x11 **
         bytesRegion ptrA hs ** bytesRegion ptrB hs) := by
    simp only [widxCmp32Post]
    -- as = bs → if true branch
    have : hs = hs := rfl
    simp only [↓if_true]
  have hcal : cpsTripleWithin 293 (Cmp32B : Word) (callerPC + 4) fullCode
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** widxCmp32EqPre ptrA ptrB hs)
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
       widxCmp32EqPost ptrA ptrB hs) := by
    have h0 : cpsTripleWithin 293 (Cmp32B : Word) (callerPC + 4) fullCode
        (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
         ((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA hs ** bytesRegion ptrB hs)
        (widxCmp32Post ptrA ptrB (callerPC + 4) hs hs) := hcal0
    rw [hpostEq] at h0
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp [widxCmp32EqPre] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        dsimp [widxCmp32EqPost] at hq ⊢
        xperm_chunked hq) h0
  have hcall := callWithin_spec callerPC (Cmp32B : Word) raOld offset 293
    htarget hmem (widxCmp32EqPre_pcFree ptrA ptrB hs) hcal
  have hf := cpsTripleWithin_frameR F hF hcall
  have hn : 1 + 293 = 294 := rfl
  rw [hn] at hf
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hf

end EvmAsm.Codegen.WitnessLookupByHashIndexedCallees
