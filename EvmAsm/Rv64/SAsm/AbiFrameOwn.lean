/-
  EvmAsm.Rv64.SAsm.AbiFrameOwn

  `abiFrame_spec` with an OWNERSHIP-level body post (bead evm-asm-4ch8f.43.5).

  `abiFrame_spec` requires the body triple to pin every saved register to a
  fixed `vals'` at the body exit.  For data-dependent validators (the `.43`
  BAL family), the callee-saved registers hold input-dependent junk at the
  body exit (`s3`/`s4` carry the last decoded span), so no single `vals'`
  fits both the success and reject paths.  The epilogue loads overwrite the
  registers anyway, so ownership suffices: this file re-derives the frame
  contract with the body post exposing `regsOwnAt frame` (mere ownership)
  instead of `regsAt frame vals'`.

  Additive: nothing in `AbiFrame.lean` is touched; `loadSeq_spec_own` is a
  fresh induction (the head `ld` step introduces the owned register's value
  via `cpsTripleWithin_of_forall_regIs_to_regOwn`), and `abiFrame_spec_own`
  replays the six-segment composition with the own-level segment 4.
-/

import EvmAsm.Rv64.SAsm.AbiFrame

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

/-- The saved registers as mere ownership atoms (the body-exit shape: their
    values are dead — the epilogue overwrites them). -/
def regsOwnAt (frame : FrameDesc) : Assertion :=
  frame.foldr (fun p acc => regOwn p.1 ** acc) empAssertion

@[simp] theorem regsOwnAt_nil : regsOwnAt [] = empAssertion := rfl
@[simp] theorem regsOwnAt_cons (p : Reg × BitVec 12) (rest : FrameDesc) :
    regsOwnAt (p :: rest) = (regOwn p.1 ** regsOwnAt rest) := rfl

theorem pcFree_regsOwnAt (frame : FrameDesc) : (regsOwnAt frame).pcFree := by
  induction frame with
  | nil => intro h hp; rw [hp]; rfl
  | cons p rest ih => exact pcFree_sepConj pcFree_regOwn ih

/-- Pinned registers weaken to owned registers. -/
theorem regsAt_implies_regsOwnAt (frame : FrameDesc) (vals : Reg → Word) :
    ∀ h, regsAt frame vals h → regsOwnAt frame h := by
  induction frame with
  | nil => intro h hp; exact hp
  | cons p rest ih =>
    intro h hp
    exact sepConj_mono (regIs_implies_regOwn p.1) ih h hp

-- Local copies of `AbiFrame.lean`'s private address helpers.
private theorem add_ofNat_add_ofNat' (b : Word) (i j : Nat) :
    (b + BitVec.ofNat 64 i) + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem word_four_eq' : (4 : Word) = BitVec.ofNat 64 4 := rfl

private theorem abiFrame_piece_mem' {base : Word} {pre mid suf prog : List Instr}
    {cr : CodeReq}
    (hprog : prog = pre ++ mid ++ suf)
    (hbound : 4 * prog.length < 2 ^ 64)
    (hsub : ∀ a i, CodeReq.ofProg base prog a = some i → cr a = some i) :
    ∀ a i, CodeReq.ofProg (base + BitVec.ofNat 64 (4 * pre.length)) mid a = some i →
           cr a = some i := by
  intro a i h
  apply hsub
  have hb' : 4 * (pre ++ mid ++ suf).length < 2 ^ 64 := by rw [← hprog]; exact hbound
  rw [hprog]
  exact CodeReq.ofProg_mono_subrange base pre mid suf hb' a i h

/-- `loadSeq_spec` from OWNED registers: the epilogue restores each saved
    register from its slot regardless of the (dead, unpinned) current
    values. -/
theorem loadSeq_spec_own (frame : FrameDesc) (newSp : Word) (vals : Reg → Word)
    (startAddr : Word) (hbound : 4 * frame.length < 2 ^ 64)
    (hne : ∀ p ∈ frame, p.1 ≠ .x0) :
    cpsTripleWithin frame.length startAddr
        (startAddr + BitVec.ofNat 64 (4 * frame.length))
      (CodeReq.ofProg startAddr (loadProg frame))
      ((.x2 ↦ᵣ newSp) ** regsOwnAt frame ** frameSlotsSaved frame newSp vals)
      ((.x2 ↦ᵣ newSp) ** regsAt frame vals ** frameSlotsSaved frame newSp vals) := by
  induction frame generalizing startAddr with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, loadProg_nil, CodeReq.ofProg_nil,
      regsAt_nil, regsOwnAt_nil, frameSlotsSaved_nil]
    rw [show startAddr + BitVec.ofNat 64 0 = startAddr from by
      apply BitVec.eq_of_toNat_eq; simp]
    exact cpsTripleWithin_refl (fun _ hp => hp)
  | cons p rest ih =>
    obtain ⟨r, ofs⟩ := p
    have hb' : 4 * rest.length < 2 ^ 64 := by
      have h := hbound; rw [List.length_cons] at h; omega
    have hne_r : r ≠ .x0 := hne (r, ofs) (List.mem_cons_self ..)
    have hne_rest : ∀ q ∈ rest, q.1 ≠ .x0 :=
      fun q hq => hne q (List.mem_cons_of_mem _ hq)
    -- Head load from an OWNED register: introduce its current value.
    have head : cpsTripleWithin 1 startAddr (startAddr + 4)
        (CodeReq.singleton startAddr (.LD r .x2 ofs))
        (((.x2 ↦ᵣ newSp) ** ((newSp + signExtend12 ofs) ↦ₘ vals r)) ** regOwn r)
        ((.x2 ↦ᵣ newSp) ** (r ↦ᵣ vals r) ** ((newSp + signExtend12 ofs) ↦ₘ vals r)) := by
      refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun vOld => ?_)
      have h := ld_spec_gen_within r .x2 newSp vOld (vals r) ofs startAddr hne_r
      exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq) h
    have head_framed := cpsTripleWithin_frameR
      (regsOwnAt rest ** frameSlotsSaved rest newSp vals)
      (pcFree_sepConj (pcFree_regsOwnAt _) (pcFree_frameSlotsSaved _ _ _)) head
    have tail := ih (startAddr + 4) hb' hne_rest
    have tail_framed := cpsTripleWithin_frameL
      ((r ↦ᵣ vals r) ** ((newSp + signExtend12 ofs) ↦ₘ vals r))
      (pcFree_sepConj pcFree_regIs pcFree_memIs) tail
    have hnone : CodeReq.ofProg (startAddr + 4) (loadProg rest) startAddr = none := by
      apply CodeReq.ofProg_none_range
      intro k hk heq
      rw [loadProg_length] at hk
      have hb2 : (4 : Nat) * (k + 1) < 2 ^ 64 := by omega
      have hcontra := congrArg BitVec.toNat heq
      simp only [word_four_eq', BitVec.toNat_add, BitVec.toNat_ofNat] at hcontra
      omega
    have hd : (CodeReq.singleton startAddr (.LD r .x2 ofs)).Disjoint
        (CodeReq.ofProg (startAddr + 4) (loadProg rest)) :=
      CodeReq.Disjoint.singleton_ofProg hnone
    have composed := cpsTripleWithin_seq_with_perm hd
      (Q1 := ((.x2 ↦ᵣ newSp) ** (r ↦ᵣ vals r)
                ** ((newSp + signExtend12 ofs) ↦ₘ vals r))
              ** (regsOwnAt rest ** frameSlotsSaved rest newSp vals))
      (Q2 := ((r ↦ᵣ vals r) ** ((newSp + signExtend12 ofs) ↦ₘ vals r))
              ** ((.x2 ↦ᵣ newSp) ** regsOwnAt rest ** frameSlotsSaved rest newSp vals))
      (by xsimp) head_framed tail_framed
    rw [← CodeReq.ofProg_cons] at composed
    have hnat : 4 + 4 * rest.length = 4 * (rest.length + 1) := by omega
    have hexit : (startAddr + 4) + BitVec.ofNat 64 (4 * rest.length)
        = startAddr + BitVec.ofNat 64 (4 * (rest.length + 1)) := by
      rw [word_four_eq', add_ofNat_add_ofNat', hnat]
    rw [hexit] at composed
    have hlen : (1 : Nat) + rest.length = (rest.length + 1) := by omega
    rw [hlen] at composed
    simp only [loadProg_cons, regsAt_cons, regsOwnAt_cons, frameSlotsSaved_cons,
      List.length_cons]
    exact cpsTripleWithin_weaken (by xsimp) (by xsimp) composed

/-- **The ownership-post ABI-frame contract**: `abiFrame_spec` with the body
    post exposing the callee-saved registers as `regsOwnAt frame` (their
    body-exit values are dead — the epilogue overwrites them).  Everything
    else is identical to `abiFrame_spec`. -/
theorem abiFrame_spec_own
    (base sp0 ret : Word) (negImm posImm : BitVec 12)
    (frame : FrameDesc) (raOfs : BitVec 12) (sregs : FrameDesc)
    (vals : Reg → Word)
    (body : List Instr) (bodySteps : Nat)
    (callerPre callerPost : Assertion)
    (cr : CodeReq)
    (hframe : frame = (.x1, raOfs) :: sregs)
    (hne : ∀ p ∈ frame, p.1 ≠ .x0)
    (hbound : 4 * frame.length < 2 ^ 64)
    (hprogBound : 4 * (abiFrameProg negImm posImm frame body).length < 2 ^ 64)
    (hret : vals .x1 = ret)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hframeRestore : (sp0 + signExtend12 negImm) + signExtend12 posImm = sp0)
    (hcpF : callerPre.pcFree) (hcpF' : callerPost.pcFree)
    (hsub : ∀ a i,
      CodeReq.ofProg base (abiFrameProg negImm posImm frame body) a = some i → cr a = some i)
    (hbody : cpsTripleWithin bodySteps
        (base + BitVec.ofNat 64 (4 * (1 + frame.length)))
        (base + BitVec.ofNat 64 (4 * (1 + frame.length + body.length)))
        cr
        ((.x2 ↦ᵣ (sp0 + signExtend12 negImm)) ** regsAt frame vals
          ** frameSlotsSaved frame (sp0 + signExtend12 negImm) vals ** callerPre)
        ((.x2 ↦ᵣ (sp0 + signExtend12 negImm)) ** regsOwnAt frame
          ** frameSlotsSaved frame (sp0 + signExtend12 negImm) vals ** callerPost)) :
    cpsTripleWithin (1 + frame.length + bodySteps + frame.length + 1 + 1) base ret cr
      ((.x2 ↦ᵣ sp0) ** regsAt frame vals
        ** frameSlotsOwn frame (sp0 + signExtend12 negImm) ** callerPre)
      ((.x2 ↦ᵣ sp0) ** regsAt frame vals
        ** frameSlotsSaved frame (sp0 + signExtend12 negImm) vals ** callerPost) := by
  set newSp := sp0 + signExtend12 negImm with hNS
  have hpcRegs := pcFree_regsAt frame vals
  have hpcOwnRegs := pcFree_regsOwnAt frame
  have hpcOwn := pcFree_frameSlotsOwn frame newSp
  have hpcSaved := pcFree_frameSlotsSaved frame newSp vals
  set A1 := base + BitVec.ofNat 64 (4 * 1) with hA1
  set A2 := base + BitVec.ofNat 64 (4 * (1 + frame.length)) with hA2
  set A3 := base + BitVec.ofNat 64 (4 * (1 + frame.length + body.length)) with hA3
  set A4 := base + BitVec.ofNat 64 (4 * (1 + frame.length + body.length + frame.length)) with hA4
  set A5 := base + BitVec.ofNat 64 (4 * (1 + frame.length + body.length + frame.length + 1)) with hA5
  have brAlloc : base + 4 = A1 := by
    rw [hA1]; apply BitVec.eq_of_toNat_eq
    simp only [word_four_eq', BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mul_one]
  have brStore : A1 + BitVec.ofNat 64 (4 * frame.length) = A2 := by
    rw [hA1, hA2, add_ofNat_add_ofNat',
      show 4 * 1 + 4 * frame.length = 4 * (1 + frame.length) from by omega]
  have brLoad : A3 + BitVec.ofNat 64 (4 * frame.length) = A4 := by
    rw [hA3, hA4, add_ofNat_add_ofNat',
      show 4 * (1 + frame.length + body.length) + 4 * frame.length
        = 4 * (1 + frame.length + body.length + frame.length) from by omega]
  have brDealloc : A4 + 4 = A5 := by
    rw [hA4, hA5, word_four_eq', add_ofNat_add_ofNat',
      show 4 * (1 + frame.length + body.length + frame.length) + 4
        = 4 * (1 + frame.length + body.length + frame.length + 1) from by omega]
  have hprogS : abiFrameProg negImm posImm frame body
      = [.ADDI .x2 .x2 negImm] ++ storeProg frame
          ++ (body ++ (loadProg frame ++ [.ADDI .x2 .x2 posImm]) ++ [.JALR .x0 .x1 0]) := by
    simp [abiFrameProg, framePrologue, frameEpilogue, List.append_assoc]
  have hprogL : abiFrameProg negImm posImm frame body
      = ([.ADDI .x2 .x2 negImm] ++ storeProg frame ++ body) ++ loadProg frame
          ++ ([.ADDI .x2 .x2 posImm] ++ [.JALR .x0 .x1 0]) := by
    simp [abiFrameProg, framePrologue, frameEpilogue, List.append_assoc]
  have hprogD : abiFrameProg negImm posImm frame body
      = ([.ADDI .x2 .x2 negImm] ++ storeProg frame ++ body ++ loadProg frame)
          ++ [.ADDI .x2 .x2 posImm] ++ [.JALR .x0 .x1 0] := by
    simp [abiFrameProg, framePrologue, frameEpilogue, List.append_assoc]
  have hprogR : abiFrameProg negImm posImm frame body
      = ([.ADDI .x2 .x2 negImm] ++ storeProg frame ++ body
            ++ (loadProg frame ++ [.ADDI .x2 .x2 posImm])) ++ [.JALR .x0 .x1 0] ++ [] := by
    simp [abiFrameProg, framePrologue, frameEpilogue, List.append_assoc]
  have hlookA : CodeReq.ofProg base (abiFrameProg negImm posImm frame body) base
      = some (.ADDI .x2 .x2 negImm) := by
    rw [show abiFrameProg negImm posImm frame body
          = .ADDI .x2 .x2 negImm
              :: (storeProg frame ++ body ++ frameEpilogue posImm frame ++ [.JALR .x0 .x1 0])
        from by simp [abiFrameProg, framePrologue, List.append_assoc]]
    rw [CodeReq.ofProg_cons]
    simp [CodeReq.union, CodeReq.singleton]
  have mAlloc := CodeReq.singleton_mono (hsub base _ hlookA)
  have mStore := abiFrame_piece_mem' hprogS hprogBound hsub
  simp only [List.length_singleton] at mStore
  have mLoad := abiFrame_piece_mem' hprogL hprogBound hsub
  simp only [List.length_append, List.length_singleton, storeProg_length] at mLoad
  have mDealloc := abiFrame_piece_mem' hprogD hprogBound hsub
  simp only [List.length_append, List.length_singleton, storeProg_length,
    loadProg_length] at mDealloc
  rw [CodeReq.ofProg_singleton] at mDealloc
  have mRet := abiFrame_piece_mem' hprogR hprogBound hsub
  simp only [List.length_append, List.length_singleton, storeProg_length,
    loadProg_length] at mRet
  rw [CodeReq.ofProg_singleton] at mRet
  -- ===================== segment 1: allocate frame =====================
  have alloc0 := addi_spec_gen_same_within .x2 sp0 negImm base (by decide)
  rw [← hNS] at alloc0
  have alloc1 := cpsTripleWithin_frameR
    (regsAt frame vals ** frameSlotsOwn frame newSp ** callerPre)
    (pcFree_sepConj hpcRegs (pcFree_sepConj hpcOwn hcpF)) alloc0
  rw [brAlloc] at alloc1
  have seg1 := cpsTripleWithin_extend_code mAlloc alloc1
  -- ===================== segment 2: save registers =====================
  have store0 := storeSeq_spec frame newSp vals A1 hbound
  have store1 := cpsTripleWithin_frameR callerPre hcpF store0
  rw [brStore] at store1
  have seg2 := cpsTripleWithin_extend_code mStore store1
  -- ===================== segment 4: restore registers (OWN level) ======
  have load0 := loadSeq_spec_own frame newSp vals A3 hbound hne
  have load1 := cpsTripleWithin_frameR callerPost hcpF' load0
  rw [brLoad] at load1
  have seg4 := cpsTripleWithin_extend_code mLoad load1
  -- ===================== segment 5: deallocate frame ===================
  have dealloc0 := addi_spec_gen_same_within .x2 newSp posImm A4 (by decide)
  rw [hframeRestore] at dealloc0
  have dealloc1 := cpsTripleWithin_frameR
    (regsAt frame vals ** frameSlotsSaved frame newSp vals ** callerPost)
    (pcFree_sepConj hpcRegs (pcFree_sepConj hpcSaved hcpF')) dealloc0
  rw [brDealloc] at dealloc1
  have seg5 := cpsTripleWithin_extend_code mDealloc dealloc1
  -- ===================== segment 6: ret ================================
  have hReg : regsAt frame vals = ((.x1 ↦ᵣ ret) ** regsAt sregs vals) := by
    rw [hframe]; simp only [regsAt_cons, hret]
  have jalr0 := Fn.jalr_ret_spec A5 ret halign
    (P := (.x2 ↦ᵣ sp0) ** regsAt sregs vals ** frameSlotsSaved frame newSp vals ** callerPost)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj (pcFree_regsAt sregs vals)
      (pcFree_sepConj hpcSaved hcpF')))
  have seg6 := cpsTripleWithin_extend_code mRet jalr0
  -- ===================== chain the segments ============================
  have h12 := cpsTripleWithin_seq_perm_same_cr (by xsimp) seg1 seg2
  have h123 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h12 hbody
  have h1234 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h123 seg4
  have h12345 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h1234 seg5
  rw [hReg] at h12345
  have hfull := cpsTripleWithin_seq_perm_same_cr (by xsimp) h12345 seg6
  refine cpsTripleWithin_weaken ?_ ?_ hfull
  · rw [hReg]; xsimp
  · rw [hReg]; xsimp

end EvmAsm.Rv64.SAsm
