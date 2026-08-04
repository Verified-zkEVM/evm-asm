/-
  EvmAsm.Codegen.Programs.HeaderExtractNumberSAsm

  Machine side of #11351.  `header_extract_number` is an eight-instruction
  wrapper that saves `ra` in a 16-byte frame, moves the caller's output
  pointer from `a2` to `a3`, pins the field index to 8, tail-calls
  `rlp_field_to_u64`, then restores and returns.

  The code-region shape mirrors `RlpFieldToU256BeSAsm`: this routine's own
  program unioned with the whole `rlp_field_to_u64` closure.  The frame is
  smaller than `rlpFieldToU64`'s own (only `ra` is spilled, into 16 bytes
  rather than `s0`-`s5` into 32), so that routine's `setupPrologue` /
  `restoreAll` primitives are frame-shaped for it and are not reusable here;
  the analogues below are correspondingly simpler.
-/

import EvmAsm.Codegen.Programs.HeaderU64
import EvmAsm.Codegen.Programs.RlpFieldToU64FlatSAsm

namespace EvmAsm.Codegen.HeaderExtractNumberSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

abbrev B : Word := (GuestAddrs.header_extract_number : Word)

theorem program_length : headerExtractNumber_prog.length = 8 := by decide

def wrapperCode : CodeReq := CodeReq.ofProg B headerExtractNumber_prog

/-- The entire `rlp_field_to_u64` closure this wrapper calls, plus the wrapper.
    Callee first, matching `RlpFieldToU256BeSAsm`: `CodeReq.union` is
    left-biased, and `mono_union_right` is stated for that orientation. -/
def code : CodeReq := EvmAsm.Codegen.RlpFieldToU64SAsm.code.union wrapperCode

/-! ## Code-region disjointness -/

theorem u64Wrapper_disjoint :
    EvmAsm.Codegen.RlpFieldToU64SAsm.wrapperCode.Disjoint wrapperCode := by
  unfold EvmAsm.Codegen.RlpFieldToU64SAsm.wrapperCode wrapperCode
    EvmAsm.Codegen.RlpFieldToU64SAsm.B B
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [EvmAsm.Codegen.RlpFieldToU64SAsm.program_length]; decide
  · rw [program_length]; decide
  · rw [EvmAsm.Codegen.RlpFieldToU64SAsm.program_length, program_length]; decide

theorem nthWrapper_disjoint :
    EvmAsm.Codegen.RlpListNthItemSAsm.code.Disjoint wrapperCode := by
  unfold EvmAsm.Codegen.RlpListNthItemSAsm.code wrapperCode
    EvmAsm.Codegen.RlpListNthItemSAsm.B B
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · rw [program_length]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length, program_length]; decide

theorem contentWrapper_disjoint :
    EvmAsm.Codegen.RlpFieldToU64SAsm.contentCode.Disjoint wrapperCode := by
  unfold EvmAsm.Codegen.RlpFieldToU64SAsm.contentCode wrapperCode
    EvmAsm.Codegen.RlpFieldToU64SAsm.C64B rlp_content_to_u64_code B
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [rlp_content_to_u64_prog_length]; decide
  · rw [program_length]; decide
  · rw [rlp_content_to_u64_prog_length, program_length]; decide

theorem calleeCode_wrapper_disjoint :
    EvmAsm.Codegen.RlpFieldToU64SAsm.code.Disjoint wrapperCode := by
  unfold EvmAsm.Codegen.RlpFieldToU64SAsm.code
  exact CodeReq.Disjoint.union_left u64Wrapper_disjoint
    (CodeReq.Disjoint.union_left nthWrapper_disjoint contentWrapper_disjoint)

theorem wrapperCode_mono : ∀ a i, wrapperCode a = some i → code a = some i := by
  intro a i hi
  unfold code
  exact CodeReq.mono_union_right calleeCode_wrapper_disjoint (fun _ _ h => h) a i hi

theorem calleeCode_mono :
    ∀ a i, EvmAsm.Codegen.RlpFieldToU64SAsm.code a = some i → code a = some i := by
  intro a i hi
  unfold code
  simp [CodeReq.union, hi]

/-! ## Prologue: instructions [0]-[3]

`addi sp,sp,-16 ; sd ra,0(sp) ; mv a3,a2 ; li a2,8`.  The output pointer
arrives in `a2` and the callee expects it in `a3`, and the field index 8 is
what makes this routine `number` rather than any other `_decode_header`
field. -/

theorem prologue
    (spOuter raIn outPtr old13 oldSlot newSp : Word)
    (hnewSp : newSp = spOuter + signExtend12 (-16 : BitVec 12)) :
    cpsTripleWithin 4 B (B + 16) code
      ((.x2 ↦ᵣ spOuter) ** (.x1 ↦ᵣ raIn) ** (.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ old13) **
        ((newSp + signExtend12 (0 : BitVec 12)) ↦ₘ oldSlot))
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raIn) ** (.x12 ↦ᵣ (8 : Word)) ** (.x13 ↦ᵣ outPtr) **
        ((newSp + signExtend12 (0 : BitVec 12)) ↦ₘ raIn)) := by
  -- [0] addi sp, sp, -16
  have h0 := addi_spec_gen_same_within .x2 spOuter (-16 : BitVec 12) B (by decide)
  rw [← hnewSp] at h0
  have h0c := cpsTripleWithin_extend_code (cr' := code) (fun a i hi =>
    wrapperCode_mono a i (CodeReq.ofProg_mem_at B B headerExtractNumber_prog 0
      (.ADDI .x2 .x2 (-16 : BitVec 12)) rfl (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide) a i hi)) h0
  have h0f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ old13) **
      ((newSp + signExtend12 (0 : BitVec 12)) ↦ₘ oldSlot))
    (by pcf) h0c
  -- [1] sd ra, 0(sp)
  have h1 := sd_spec_gen_within .x2 .x1 newSp raIn oldSlot (0 : BitVec 12) (B + 4)
  have h1c := cpsTripleWithin_extend_code (cr' := code) (fun a i hi =>
    wrapperCode_mono a i (CodeReq.ofProg_mem_at B (B + 4) headerExtractNumber_prog 1
      (.SD .x2 .x1 (0 : BitVec 12)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide) a i hi)) h1
  have h1f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ old13)) (by pcf) h1c
  -- [2] mv a3, a2
  have h2 := mv_spec_gen_within .x13 .x12 outPtr old13 (B + 8) (by decide)
  have h2c := cpsTripleWithin_extend_code (cr' := code) (fun a i hi =>
    wrapperCode_mono a i (CodeReq.ofProg_mem_at B (B + 8) headerExtractNumber_prog 2
      (.MV .x13 .x12) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide) a i hi)) h2
  have h2f := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raIn) **
      ((newSp + signExtend12 (0 : BitVec 12)) ↦ₘ raIn)) (by pcf) h2c
  -- [3] li a2, 8
  have h3 := li_spec_gen_within .x12 outPtr (8 : Word) (B + 12) (by decide)
  have h3c := cpsTripleWithin_extend_code (cr' := code) (fun a i hi =>
    wrapperCode_mono a i (CodeReq.ofProg_mem_at B (B + 12) headerExtractNumber_prog 3
      (.LI .x12 (8 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide) a i hi)) h3
  have h3f := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raIn) ** (.x13 ↦ᵣ outPtr) **
      ((newSp + signExtend12 (0 : BitVec 12)) ↦ₘ raIn)) (by pcf) h3c
  -- compose [0];[1];[2];[3]
  have s01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0f h1f
  have s012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s01 h2f
  have s0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s012 h3f
  rw [show (B + 12 + 4 : Word) = B + 16 from by bv_omega] at s0123
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) s0123

/-! ## The call: instruction [4]

`jal ra, rlp_field_to_u64`.  The callee's link register is pinned to `B + 20`,
the instruction after the call, which is what `callWithin_spec` requires. -/

open EvmAsm.Codegen.RlpFieldToU64SAsm in
set_option maxRecDepth 8000 in
theorem callStep
    (spW newSpC listBase listLenW outPtr oldOut oldOffset oldLen old14 : Word)
    (s0v s1v s2 s3 s4 s5 vOld : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (hnewSpC : newSpC = spW + signExtend12 (-32 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let outer : Saved := ⟨B + 20, s0v, s1v⟩
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, s0 := listBase, s1 := outPtr,
        s2 := s2, s3 := s3, s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (8 + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5
    cpsTripleWithin (1 + ((7 + 4 + callSteps) + ((1 + tailSteps) + 5)))
      (B + 16) (B + 20) code
      ((.x1 ↦ᵣ vOld) **
        flatPre spW newSpC listBase listLenW (8 : Word) outPtr oldOut
          oldOffset oldLen old14 outer s2 s3 s4 s5 bytes)
      ((.x1 ↦ᵣ (B + 20)) **
        flatPost spW newSpC listBase oldOffset oldLen outer saved bytes listLen 8) := by
  dsimp
  have hflat := rlpFieldToU64_flat_spec_within spW newSpC listBase listLenW
    (8 : Word) outPtr oldOut oldOffset oldLen old14 ⟨B + 20, s0v, s1v⟩
    s2 s3 s4 s5 bytes listLen 8 hnewSpC hlistLenW (by decide) (by norm_num)
    hsalign hslack hover hvalid
    (by show (B + 20) &&& ~~~(1 : Word) = B + 20; decide)
  have hflatC := cpsTripleWithin_extend_code calleeCode_mono hflat
  exact callWithin_spec (B + 16) EvmAsm.Codegen.RlpFieldToU64SAsm.B vOld
    (jalOff GuestAddrs.rlp_field_to_u64 (GuestAddrs.header_extract_number + 16))
    _ (by decide)
    (fun a i hi => wrapperCode_mono a i
      (CodeReq.ofProg_mem_at B (B + 16) headerExtractNumber_prog 4
        (.JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64
          (GuestAddrs.header_extract_number + 16)))
        (by bv_omega) (by rw [program_length]; decide) rfl
        (by rw [program_length]; decide) a i hi))
    (by unfold flatPre wholeRest; pcf) hflatC

/-! ## Epilogue: instructions [5]-[7]

`ld ra,0(sp) ; addi sp,sp,16 ; jalr x0,ra,0`.  The callee restored `sp` to the
wrapper's frame pointer, and its own frame sat strictly below that, so the
spilled `ra` is still intact. -/

theorem epilogue
    (spOuter newSp0 raIn : Word) (F : Assertion) (hF : F.pcFree)
    (hnewSp0 : newSp0 = spOuter + signExtend12 (-16 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 3 (B + 20) raIn code
      ((.x2 ↦ᵣ newSp0) ** (.x1 ↦ᵣ (B + 20)) **
        ((newSp0 + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) ** F)
      ((.x2 ↦ᵣ spOuter) ** (.x1 ↦ᵣ raIn) **
        ((newSp0 + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) ** F) := by
  have hsp : newSp0 + signExtend12 (16 : BitVec 12) = spOuter := by
    have h1 : signExtend12 (-16 : BitVec 12) = (-16 : Word) := by decide
    have h2 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
    rw [hnewSp0, h1, h2]; bv_omega
  -- [5] ld ra, 0(sp)
  have h5 := ld_spec_gen_within .x1 .x2 newSp0 (B + 20) raIn (0 : BitVec 12)
    (B + 20) (by decide)
  have h5c := cpsTripleWithin_extend_code (cr' := code) (fun a i hi =>
    wrapperCode_mono a i (CodeReq.ofProg_mem_at B (B + 20) headerExtractNumber_prog 5
      (.LD .x1 .x2 (0 : BitVec 12)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide) a i hi)) h5
  have h5f := cpsTripleWithin_frameR F hF h5c
  -- [6] addi sp, sp, 16
  have h6 := addi_spec_gen_same_within .x2 newSp0 (16 : BitVec 12) (B + 24) (by decide)
  rw [hsp] at h6
  have h6c := cpsTripleWithin_extend_code (cr' := code) (fun a i hi =>
    wrapperCode_mono a i (CodeReq.ofProg_mem_at B (B + 24) headerExtractNumber_prog 6
      (.ADDI .x2 .x2 (16 : BitVec 12)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide) a i hi)) h6
  have h6f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** ((newSp0 + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) ** F)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_memIs hF)) h6c
  -- [7] jalr x0, ra, 0  (ret)
  have h7 := EvmAsm.Rv64.SAsm.Fn.jalr_ret_spec (B + 28) raIn hret
    (P := (.x2 ↦ᵣ spOuter) ** ((newSp0 + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) ** F)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_memIs hF))
  have h7c := cpsTripleWithin_extend_code (cr' := code) (fun a i hi =>
    wrapperCode_mono a i (CodeReq.ofProg_mem_at B (B + 28) headerExtractNumber_prog 7
      (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide) a i hi)) h7
  -- compose [5];[6];[7]
  have s56 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h5f h6f
  have s567 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s56 h7c
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) s567

/-! ## Whole-routine triple

Everything the callee's `flatPre` needs but the prologue never touches is
carried through it as a frame; the wrapper's own spilled-`ra` slot is
correspondingly framed through the call. -/

open EvmAsm.Codegen.RlpFieldToU64SAsm in
/-- The callee's untouched context, framed through this wrapper's prologue.
    `abbrev` rather than `def`: `xperm` matches atoms syntactically and treats an
    opaque definition as a single atom, so the prologue frame and `flatPre` must
    present the same *unfolded* atom list. -/
abbrev calleeCtx (listBase listLenW outPtr oldOut oldOffset oldLen old14 : Word)
    (s0v s1v s2 s3 s4 s5 newSpC : Word) (bytes : List (BitVec 8)) : Assertion :=
  (.x8 ↦ᵣ s0v) ** (.x9 ↦ᵣ s1v) **
  frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame newSpC ** stackFree newSpC 8 **
  (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x14 ↦ᵣ old14) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  (outPtr ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen)

theorem calleeCtx_pcFree (listBase listLenW outPtr oldOut oldOffset oldLen old14
    s0v s1v s2 s3 s4 s5 newSpC : Word) (bytes : List (BitVec 8)) :
    (calleeCtx listBase listLenW outPtr oldOut oldOffset oldLen old14
      s0v s1v s2 s3 s4 s5 newSpC bytes).pcFree := by
  unfold calleeCtx
  pcf

/-! ## Normalising `flatPost` before the epilogue

The three segments do not compose directly: after the call `x2` sits **inside**
`flatPost`, which is a disjunction (success / failure) of existentials, so it
cannot be handed to `epilogue` as a separate conjunct the way `prologue` hands
it over, and `xperm` rightly refuses to match it.

`postRest` is `flatPost` with the `x2` cell removed, and `flatPost_split`
factors it out — the analogue of the model's `allRestoreReady`
(`RlpFieldToU64WholeSAsm.lean:7`).  Both disjuncts are destructured and
re-associated; the existential witnesses stay inside the residual heap, which
is why the split is possible at all. -/

open EvmAsm.Codegen.RlpFieldToU64SAsm in
/-- `flatPost` minus the stack-pointer cell. -/
def postRest (newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h =>
    (∃ offset len v12 x5 scalarStatus wrapperStatus outputValue,
      (((.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) ** savedFrame newSp outer) **
        successPayload newSp listBase offset len v12 x5 scalarStatus wrapperStatus
          outputValue saved bytes listLen index) h) ∨
    (∃ v11 v12,
      (((.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) ** savedFrame newSp outer) **
        failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes
          listLen index) h)

open EvmAsm.Codegen.RlpFieldToU64SAsm in
theorem postRest_pcFree (newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    (postRest newSp listBase oldOffset oldLen outer saved bytes listLen index).pcFree := by
  intro h hh
  rcases hh with ⟨_, _, _, _, _, _, _, hp⟩ | ⟨_, _, hp⟩
  · exact (pcFree_sepConj (by pcf) (by unfold successPayload; pcf)) h hp
  · exact (pcFree_sepConj (by pcf) (by unfold failurePayload; pcf)) h hp

open EvmAsm.Codegen.RlpFieldToU64SAsm in
/-- Factor the stack-pointer cell out of `flatPost`. -/
theorem flatPost_split (spOuter newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    flatPost spOuter newSp listBase oldOffset oldLen outer saved bytes listLen index h →
    ((.x2 ↦ᵣ spOuter) **
      postRest newSp listBase oldOffset oldLen outer saved bytes listLen index) h := by
  intro h hp
  unfold flatPost at hp
  rcases hp with hs | hf
  · unfold flatSuccessReturned at hs
    obtain ⟨offset, len, v12, x5, ss, ws, ov, hs⟩ := hs
    have hfix : ((.x2 ↦ᵣ spOuter) **
        (((.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) ** savedFrame newSp outer) **
          successPayload newSp listBase offset len v12 x5 ss ws ov saved bytes
            listLen index)) h := by
      xperm_hyp hs
    exact sepConj_mono_right
      (fun _ hp' => Or.inl ⟨offset, len, v12, x5, ss, ws, ov, hp'⟩) h hfix
  · unfold flatFailureReturned at hf
    obtain ⟨v11, v12, hf⟩ := hf
    have hfix : ((.x2 ↦ᵣ spOuter) **
        (((.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) ** savedFrame newSp outer) **
          failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes
            listLen index)) h := by
      xperm_hyp hf
    exact sepConj_mono_right (fun _ hp' => Or.inr ⟨v11, v12, hp'⟩) h hfix

/-! ## Whole-routine triple

`prologue ;; callStep ;; epilogue`, from the entry point to the caller's return
address.  The prologue carries `calleeCtx` (everything `flatPre` needs that the
prologue never touches); the call carries this wrapper's own spilled-`ra` slot;
`flatPost_split` hands the epilogue the `x2` cell it needs. -/

/-! ## Prologue ;; call

Named separately, mirroring `RlpFieldToU64WholeSAsm`'s
`prologueAndMoves` / `setupAndCall` / `dispatchAndRestore` layering, so that a
shape mismatch localises to one composition rather than the whole routine. -/

open EvmAsm.Codegen.RlpFieldToU64SAsm in
set_option maxRecDepth 8000 in
theorem setupAndCall
    (spOuter raIn listBase listLenW outPtr old13 oldSlot oldOut oldOffset oldLen
      old14 s0v s1v s2 s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat) (newSp0 newSpC : Word)
    (hnewSp0 : newSp0 = spOuter + signExtend12 (-16 : BitVec 12))
    (hnewSpC : newSpC = newSp0 + signExtend12 (-32 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let outer : Saved := ⟨B + 20, s0v, s1v⟩
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, s0 := listBase, s1 := outPtr,
        s2 := s2, s3 := s3, s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (8 + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5
    cpsTripleWithin
      (4 + (1 + ((7 + 4 + callSteps) + ((1 + tailSteps) + 5)))) B (B + 20) code
      (((.x2 ↦ᵣ spOuter) ** (.x1 ↦ᵣ raIn) ** (.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ old13) **
        ((newSp0 + signExtend12 (0 : BitVec 12)) ↦ₘ oldSlot)) **
        calleeCtx listBase listLenW outPtr oldOut oldOffset oldLen old14
          s0v s1v s2 s3 s4 s5 newSpC bytes)
      (((.x1 ↦ᵣ (B + 20)) **
        flatPost newSp0 newSpC listBase oldOffset oldLen outer saved bytes listLen 8) **
        ((newSp0 + signExtend12 (0 : BitVec 12)) ↦ₘ raIn)) := by
  dsimp
  have hp := prologue spOuter raIn outPtr old13 oldSlot newSp0 hnewSp0
  have hpF := cpsTripleWithin_frameR
    (calleeCtx listBase listLenW outPtr oldOut oldOffset oldLen old14
      s0v s1v s2 s3 s4 s5 newSpC bytes)
    (calleeCtx_pcFree listBase listLenW outPtr oldOut oldOffset oldLen old14
      s0v s1v s2 s3 s4 s5 newSpC bytes) hp
  have hc := callStep newSp0 newSpC listBase listLenW outPtr oldOut oldOffset oldLen
    old14 s0v s1v s2 s3 s4 s5 raIn bytes listLen hnewSpC hlistLenW hsalign hslack
    hover hvalid
  have hcF := cpsTripleWithin_frameR
    ((newSp0 + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) (by pcf) hc
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hq => by
    unfold flatPre wholeRest
    xperm_hyp hq) hpF hcF

/-! ## Whole-routine triple -/

open EvmAsm.Codegen.RlpFieldToU64SAsm in
set_option maxRecDepth 8000 in
/-- Whole-routine triple for `header_extract_number`: entry point to the
    caller's return address, delegating to `rlp_field_to_u64` at field index 8
    (`number`). -/
theorem headerExtractNumber_spec_within
    (spOuter raIn listBase listLenW outPtr old13 oldSlot oldOut oldOffset oldLen
      old14 s0v s1v s2 s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat) (newSp0 newSpC : Word)
    (hnewSp0 : newSp0 = spOuter + signExtend12 (-16 : BitVec 12))
    (hnewSpC : newSpC = newSp0 + signExtend12 (-32 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    let outer : Saved := ⟨B + 20, s0v, s1v⟩
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, s0 := listBase, s1 := outPtr,
        s2 := s2, s3 := s3, s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (8 + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5
    cpsTripleWithin
      ((4 + (1 + ((7 + 4 + callSteps) + ((1 + tailSteps) + 5)))) + 3) B raIn code
      (((.x2 ↦ᵣ spOuter) ** (.x1 ↦ᵣ raIn) ** (.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ old13) **
        ((newSp0 + signExtend12 (0 : BitVec 12)) ↦ₘ oldSlot)) **
        calleeCtx listBase listLenW outPtr oldOut oldOffset oldLen old14
          s0v s1v s2 s3 s4 s5 newSpC bytes)
      ((.x2 ↦ᵣ spOuter) ** (.x1 ↦ᵣ raIn) **
        ((newSp0 + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
        postRest newSpC listBase oldOffset oldLen outer saved bytes listLen 8) := by
  dsimp
  have hsc := setupAndCall spOuter raIn listBase listLenW outPtr old13 oldSlot oldOut
    oldOffset oldLen old14 s0v s1v s2 s3 s4 s5 bytes listLen newSp0 newSpC
    hnewSp0 hnewSpC hlistLenW hsalign hslack hover hvalid
  -- expose the callee's restored `x2` so the epilogue can consume it
  have hsc' := cpsTripleWithin_weaken
    (Q' := (.x2 ↦ᵣ newSp0) ** (.x1 ↦ᵣ (B + 20)) **
      ((newSp0 + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
      postRest newSpC listBase oldOffset oldLen ⟨B + 20, s0v, s1v⟩
        { ra := EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, s0 := listBase, s1 := outPtr,
          s2 := s2, s3 := s3, s4 := s4, s5 := s5 } bytes listLen 8)
    (fun _ hp => hp) (fun h hq => by
    have h1 := sepConj_mono_left
      (sepConj_mono_right (flatPost_split newSp0 newSpC listBase oldOffset oldLen
        ⟨B + 20, s0v, s1v⟩
        { ra := EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, s0 := listBase, s1 := outPtr,
          s2 := s2, s3 := s3, s4 := s4, s5 := s5 } bytes listLen 8)) h hq
    xperm_hyp h1) hsc
  have he := epilogue spOuter newSp0 raIn
    (postRest newSpC listBase oldOffset oldLen ⟨B + 20, s0v, s1v⟩
      { ra := EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, s0 := listBase, s1 := outPtr,
        s2 := s2, s3 := s3, s4 := s4, s5 := s5 } bytes listLen 8)
    (postRest_pcFree newSpC listBase oldOffset oldLen ⟨B + 20, s0v, s1v⟩
      { ra := EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, s0 := listBase, s1 := outPtr,
        s2 := s2, s3 := s3, s4 := s4, s5 := s5 } bytes listLen 8) hnewSp0 hret
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq) hsc' he

end EvmAsm.Codegen.HeaderExtractNumberSAsm
