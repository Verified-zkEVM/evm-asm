/-
  EvmAsm.Rv64.SAsm.RaSpill

  Packaging a verified *caller* (a function whose body contains calls) as a
  callee `FnHandle` (docs/sasm-design.md §3.6).  A caller clobbers `ra` at
  its call sites, so the packaged code spills `ra` to a dword slot of the
  function's writable region on entry and restores it before returning:

      SD rs, x1, sofs ; <body> ; LD x1, rs, sofs ; JALR x0, x1, 0

  `rs` is an exposed register that the pre- (and post-) condition pin to the
  spill slot's address.  The return address is threaded through the body as
  a ghost word: `Fn.retSpecR` consumes a *family* of caller-shaped body
  specs indexed by the spilled value, whose pre/post state that the slot
  holds it — slot preservation is exactly the caller's own `.post` VC.

  The two one-step lemmas here are the `ra` analogues of
  `regFile_store_spec_within` / `regFile_load_spec_within`: `x1` is not an
  exposed register, so its value comes from (and goes to) the separate
  `.x1 ↦ᵣ _` atom rather than the `regFileIs` atom.
-/

import EvmAsm.Rv64.SAsm.Fn

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- Byte-list helpers
-- ============================================================================

/-- Packing a dword's own little-endian bytes gives it back. -/
theorem packBytes_dwordBytes (v : Word) : packBytes (dwordBytes v) = v := by
  symm
  apply eq_of_forall_extractByte
  intro j hj
  rw [extractByte_packBytes_total _ j hj]
  interval_cases j <;> simp [dwordBytes, getByteAt]

/-- The freshly spliced window holds exactly the payload. -/
theorem setBytes_slot (ws ns : List (BitVec 8)) (k : Nat)
    (h : k + ns.length ≤ ws.length) :
    ((setBytes ws k ns).drop k).take ns.length = ns := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, length_setBytes]
    omega
  · intro j hj1 hj2
    rw [List.getElem_take, List.getElem_drop]
    have hlt : k + j < (setBytes ws k ns).length := by
      rw [length_setBytes]
      omega
    have hj : j < ns.length := by
      simp only [List.length_take, List.length_drop, length_setBytes] at hj1
      omega
    have hb : getByteAt (setBytes ws k ns) (k + j) = getByteAt ns j := by
      rw [getByteAt_setBytes ns ws k (k + j) h, if_pos ⟨by omega, by omega⟩,
        show k + j - k = j from by omega]
    unfold getByteAt at hb
    rw [dif_pos hlt, dif_pos hj] at hb
    exact hb

/-- Transport `RwRegion.wf` to the current contents viewed as a region. -/
theorem RwRegion.wf_toRegion {rw : RwRegion} {ws : List (BitVec 8)}
    (hrw : rw.wf) (hlen : ws.length = rw.len) :
    (Region.mk rw.base ws).wf := by
  refine ⟨hrw.1, ?_, ?_⟩
  · show rw.base.toNat + ws.length < 2 ^ 64
    have := hrw.2.1
    omega
  · intro k hk
    have hk' : k < ws.length := hk
    exact hrw.2.2 k (by omega)

-- ============================================================================
-- Spill and restore: one-step triples for `ra` against the writable region
-- ============================================================================

/-- Spill `ra`: `SD rs, x1, sofs` writes the (separately owned) return
    address into the writable region; the register file and `ra` itself are
    untouched. -/
theorem sd_ra_spec_within (rs : Reg) (sofs : BitVec 12) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (ret : Word) (base : Word)
    (hrs : (Reg.isExposed rs || rs == .x0) = true)
    (hwf : (Region.mk rwBase ws).wf)
    (hin : inRw rwBase ws (rf.get rs + signExtend12 sofs) 8)
    (hdvd : 8 ∣ ((rf.get rs + signExtend12 sofs) - rwBase).toNat) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.SD rs .x1 sofs))
      (((.x1 : Reg) ↦ᵣ ret) ** ((regFileIs rf) ** bytesRegion rwBase ws))
      (((.x1 : Reg) ↦ᵣ ret) ** ((regFileIs rf) ** bytesRegion rwBase
        (setBytes ws ((rf.get rs + signExtend12 sofs) - rwBase).toNat
          (dwordBytes ret)))) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SD rs .x1 sofs) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  rw [sepConj_assoc'] at hPR
  -- hPR : ((.x1 ↦ᵣ ret) ** ((regFileIs ** bytesRegion) ** R))
  have hx1 : s.getReg .x1 = ret :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR)
  rw [sepConj_left_comm, sepConj_assoc'] at hPR
  -- hPR : (regFileIs ** (bytesRegion ** ((.x1) ** R)))
  have hrsv : s.getReg rs = rf.get rs := holdsFor_regFileIs_agree hPR hrs
  rw [sepConj_left_comm] at hPR
  -- hPR : (bytesRegion ** (regFileIs ** ((.x1) ** R)))
  set addr := rf.get rs + signExtend12 sofs with haddr_def
  unfold inRw at hin
  set i0 := (addr - rwBase).toNat with hi0_def
  have hi0lt : i0 < ws.length := by omega
  have haddr_eq : addr = rwBase + BitVec.ofNat 64 i0 := by
    rw [hi0_def]
    bv_omega
  have hover : rwBase.toNat + i0 < 2 ^ 64 := by
    have h1 : rwBase.toNat + ws.length < 2 ^ 64 := hwf.2.1
    omega
  have haddr_toNat : addr.toNat = rwBase.toNat + i0 := by
    rw [haddr_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hvalidmem : isValidMemAddr addr = true := by
    rw [haddr_eq]
    exact hwf.2.2 _ hi0lt
  have hb8 : rwBase.toNat % 8 = 0 := hwf.1
  have h80 : i0 % 8 = 0 := by omega
  have hi08 : 8 * (i0 / 8) = i0 := by omega
  have hvalid : isValidDwordAccess (s.getReg rs + signExtend12 sofs) = true := by
    rw [hrsv]
    show isValidDwordAccess addr = true
    simp only [isValidDwordAccess_eq, Bool.and_eq_true]
    refine ⟨hvalidmem, ?_⟩
    simp only [isAligned8, beq_iff_eq]
    omega
  have hstep' : step s = some (execInstrBr s (.SD rs .x1 sofs)) :=
    step_sd hfetch hvalid
  have hexec : execInstrBr s (.SD rs .x1 sofs)
      = (s.setMem (rwBase + BitVec.ofNat 64 (8 * (i0 / 8)))
          (packBytes (setBytes ((ws.drop (8 * (i0 / 8))).take 8) (i0 % 8)
            (dwordBytes ret)))).setPC (s.pc + 4) := by
    simp only [execInstrBr]
    rw [hrsv, hx1]
    show (s.setMem addr ret).setPC (s.pc + 4) = _
    rw [h80,
      show addr = rwBase + BitVec.ofNat 64 (8 * (i0 / 8)) from by
        rw [haddr_eq, hi08],
      ← packBytes_setBytes_dword ((ws.drop (8 * (i0 / 8))).take 8) ret (by
        simp only [List.length_take, List.length_drop]
        omega)]
  have hupd := holdsFor_bytesRegion_setBytes
    (i := i0) (ns := dwordBytes ret) hPR
    (by simp [dwordBytes])
    (by simp only [length_dwordBytes]; omega)
    (by simp only [length_dwordBytes]; omega)
  refine ⟨1, Nat.le_refl 1,
    (s.setMem (rwBase + BitVec.ofNat 64 (8 * (i0 / 8)))
      (packBytes (setBytes ((ws.drop (8 * (i0 / 8))).take 8) (i0 % 8)
        (dwordBytes ret)))).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec]; rfl
  · rw [sepConj_left_comm,
      sepConj_left_comm (bytesRegion rwBase (setBytes ws i0 (dwordBytes ret)))
        ((.x1 : Reg) ↦ᵣ ret) R,
      sepConj_left_comm,
      ← sepConj_assoc' (regFileIs rf)
        (bytesRegion rwBase (setBytes ws i0 (dwordBytes ret))) R,
      ← sepConj_assoc'] at hupd
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (by pcFree)
        (pcFree_sepConj (pcFree_regFileIs _) (bytesRegion_pcFree _ _))) hR)
      hupd

/-- Restore `ra`: `LD x1, rs, sofs` loads the spill slot back into the
    (separately owned) `ra`; everything else is untouched. -/
theorem ld_ra_spec_within (rs : Reg) (sofs : BitVec 12) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (old : Word) (base : Word)
    (hrs : (Reg.isExposed rs || rs == .x0) = true)
    (hwf : (Region.mk rwBase ws).wf)
    (hin : inRw rwBase ws (rf.get rs + signExtend12 sofs) 8)
    (hdvd : 8 ∣ ((rf.get rs + signExtend12 sofs) - rwBase).toNat) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.LD .x1 rs sofs))
      (((.x1 : Reg) ↦ᵣ old) ** ((regFileIs rf) ** bytesRegion rwBase ws))
      (((.x1 : Reg) ↦ᵣ packBytes
          ((ws.drop ((rf.get rs + signExtend12 sofs) - rwBase).toNat).take 8))
        ** ((regFileIs rf) ** bytesRegion rwBase ws)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LD .x1 rs sofs) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  rw [sepConj_assoc'] at hPR
  -- hPR : ((.x1 ↦ᵣ old) ** ((regFileIs ** bytesRegion) ** R))
  have hPR1 := hPR
  rw [sepConj_left_comm, sepConj_assoc'] at hPR1
  -- hPR1 : (regFileIs ** (bytesRegion ** ((.x1) ** R)))
  have hrsv : s.getReg rs = rf.get rs := holdsFor_regFileIs_agree hPR1 hrs
  have hPR2 := hPR1
  rw [sepConj_left_comm] at hPR2
  -- hPR2 : (bytesRegion ** (regFileIs ** ((.x1) ** R)))
  set addr := rf.get rs + signExtend12 sofs with haddr_def
  unfold inRw at hin
  set i0 := (addr - rwBase).toNat with hi0_def
  have hi0lt : i0 < ws.length := by omega
  have haddr_eq : addr = rwBase + BitVec.ofNat 64 i0 := by
    rw [hi0_def]
    bv_omega
  have hover : rwBase.toNat + i0 < 2 ^ 64 := by
    have h1 : rwBase.toNat + ws.length < 2 ^ 64 := hwf.2.1
    omega
  have haddr_toNat : addr.toNat = rwBase.toNat + i0 := by
    rw [haddr_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hvalidmem : isValidMemAddr addr = true := by
    rw [haddr_eq]
    exact hwf.2.2 _ hi0lt
  have hb8 : rwBase.toNat % 8 = 0 := hwf.1
  have h80 : i0 % 8 = 0 := by omega
  have hvalid : isValidDwordAccess (s.getReg rs + signExtend12 sofs) = true := by
    rw [hrsv]
    show isValidDwordAccess addr = true
    simp only [isValidDwordAccess_eq, Bool.and_eq_true]
    refine ⟨hvalidmem, ?_⟩
    simp only [isAligned8, beq_iff_eq]
    omega
  have hstep' : step s = some (execInstrBr s (.LD .x1 rs sofs)) :=
    step_ld hfetch hvalid
  have hexec : execInstrBr s (.LD .x1 rs sofs)
      = (s.setReg .x1 (packBytes ((ws.drop i0).take 8))).setPC (s.pc + 4) := by
    simp only [execInstrBr]
    rw [hrsv]
    show (s.setReg .x1 (s.getMem addr)).setPC (s.pc + 4) = _
    rw [show s.getMem addr = packBytes ((ws.drop i0).take 8) from by
      conv_lhs => rw [haddr_eq]
      exact holdsFor_bytesRegion_getMem hPR2 hdvd hi0lt]
  refine ⟨1, Nat.le_refl 1,
    (s.setReg .x1 (packBytes ((ws.drop i0).take 8))).setPC (s.pc + 4),
    ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec]; rfl
  · have h1 := holdsFor_sepConj_regIs_setReg
      (v' := packBytes ((ws.drop i0).take 8))
      (show (.x1 : Reg) ≠ .x0 from by decide) hPR
    rw [← sepConj_assoc'] at h1
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (by pcFree)
        (pcFree_sepConj (pcFree_regFileIs _) (bytesRegion_pcFree _ _))) hR)
      h1

-- ============================================================================
-- Existential-precondition splitters with the `ra` atom alongside
-- ============================================================================

/-- Split an `asrtR` precondition into a per-symbolic-state family, including
    a concrete value for the owned `ra`. -/
theorem cpsTripleWithin_exists_pre_R {n : Nat} {entry exit_ : Word}
    {cr : CodeReq} {reg : Region} {rw : RwRegion} {reach : Reach}
    {Q : Assertion}
    (h : ∀ rf ws (A : Assertion) (v : Word), ws.length = rw.len → A.pcFree →
      reach rf ws A →
      cpsTripleWithin n entry exit_ cr
        ((((regFileIs rf) ** bytesRegion rw.base ws) ** A) **
          (bytesRegion reg.base reg.bytes ** ((.x1 : Reg) ↦ᵣ v))) Q) :
    cpsTripleWithin n entry exit_ cr (asrtR reg rw reach) Q := by
  show cpsTripleWithin n entry exit_ cr (asrtM reg rw reach ** regOwn .x1) Q
  apply cpsTripleWithin_regOwn_right_pre
  intro v
  exact cpsTripleWithin_exists_pre_M_frame
    (fun rf ws A hlen hApc hreach => h rf ws A v hlen hApc hreach)

-- ============================================================================
-- Packaging a verified caller as a callee handle
-- ============================================================================

namespace Fn

/-- The caller's code wrapped with the `ra`-spill prologue and the
    restore-and-return epilogue.  The body is flattened at `base + 4`. -/
def programRetR (f : Fn) (rs : Reg) (sofs : BitVec 12) (base : Word) : Program :=
  .SD rs .x1 sofs ::
    (f.body.flatten (base + 4) ++ [.LD .x1 rs sofs, .JALR .x0 .x1 0])

/-- A verified caller, wrapped with the `ra`-spill prologue/epilogue,
    satisfies the `FnHandle` calling contract.

    The spill slot is the dword at index `k` of the writable region; `rs` is
    an exposed register that `pre` pins to its address (and that the body,
    per the strengthened post, restores).  `spre`/`spost` are the
    ghost-indexed body conditions: `spre v`/`spost v` additionally record
    that the slot holds `v` (the caller's own `.post` VC proves the body
    preserves it); `hbody` is the caller-shaped body spec at each ghost
    value, obtained from `Fn.soundR` of the ghost-indexed function. -/
theorem retSpecR (f : Fn) (base : Word) (cr : CodeReq)
    (rs : Reg) (sofs : BitVec 12) (k : Nat)
    (spre spost : Word → Reach)
    (hrs : (Reg.isExposed rs || rs == .x0) = true)
    (hrw : f.rw.wf)
    (hk : 8 ∣ k) (hk8 : k + 8 ≤ f.rw.len)
    (hsz : 4 * (f.body.size + 3) ≤ 2 ^ 64)
    (hbody : ∀ v : Word, cpsTripleWithin f.body.steps (base + 4)
        ((base + 4) + BitVec.ofNat 64 (4 * f.body.size)) cr
        (asrtR f.region f.rw (spre v)) (asrtR f.region f.rw (spost v)))
    (hcode : ∀ a i, CodeReq.ofProg base (f.programRetR rs sofs base) a = some i →
        cr a = some i)
    (haddr : ∀ rf ws A, f.pre rf ws A →
        rf.get rs + signExtend12 sofs = f.rw.base + BitVec.ofNat 64 k)
    (haddrPost : ∀ v rf ws A, spost v rf ws A →
        rf.get rs + signExtend12 sofs = f.rw.base + BitVec.ofNat 64 k)
    (hspre : ∀ v rf ws A, f.pre rf ws A → ws.length = f.rw.len →
        spre v rf (setBytes ws k (dwordBytes v)) A)
    (hspost : ∀ v rf ws A, spost v rf ws A → f.post rf ws A)
    (hslot : ∀ v rf ws A, spost v rf ws A → ws.length = f.rw.len →
        (ws.drop k).take 8 = dwordBytes v) :
    ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin (1 + f.body.steps + 2) base ret cr
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM f.region f.rw f.pre)
        (((.x1 : Reg) ↦ᵣ ret) ** asrtM f.region f.rw f.post) := by
  intro ret halign
  have hk64 : k < 2 ^ 64 := by
    have := hrw.2.1
    omega
  have hlflat : (f.body.flatten (base + 4)).length = f.body.size :=
    Stmt.flatten_length ..
  -- code containment for the three wrapper instructions
  have hcodeSD : ∀ a i, CodeReq.singleton base (.SD rs .x1 sofs) a = some i →
      cr a = some i := by
    intro a i h
    apply hcode
    show CodeReq.ofProg base (.SD rs .x1 sofs ::
      (f.body.flatten (base + 4) ++ [.LD .x1 rs sofs, .JALR .x0 .x1 0]))
      a = some i
    exact ofProg_head a i h
  have hcodeLD : ∀ a i, CodeReq.singleton
      ((base + 4) + BitVec.ofNat 64 (4 * f.body.size)) (.LD .x1 rs sofs)
      a = some i → cr a = some i := by
    intro a i h
    apply hcode
    show CodeReq.ofProg base (.SD rs .x1 sofs ::
      (f.body.flatten (base + 4) ++ [.LD .x1 rs sofs, .JALR .x0 .x1 0]))
      a = some i
    apply ofProg_cons_tail (by simp only [List.length_append, List.length_cons, List.length_nil, hlflat]; omega)
    apply ofProg_mono_right
      (p1 := f.body.flatten (base + 4))
      (p2 := [.LD .x1 rs sofs, .JALR .x0 .x1 0])
      (by simp only [List.length_cons, List.length_nil, hlflat]; omega)
    rw [hlflat]
    exact ofProg_head a i h
  have hcodeJ : ∀ a i, CodeReq.singleton
      (((base + 4) + BitVec.ofNat 64 (4 * f.body.size)) + 4) (.JALR .x0 .x1 0)
      a = some i → cr a = some i := by
    intro a i h
    apply hcode
    show CodeReq.ofProg base (.SD rs .x1 sofs ::
      (f.body.flatten (base + 4) ++ [.LD .x1 rs sofs, .JALR .x0 .x1 0]))
      a = some i
    apply ofProg_cons_tail (by simp only [List.length_append, List.length_cons, List.length_nil, hlflat]; omega)
    apply ofProg_mono_right
      (p1 := f.body.flatten (base + 4))
      (p2 := [.LD .x1 rs sofs, .JALR .x0 .x1 0])
      (by simp only [List.length_cons, List.length_nil, hlflat]; omega)
    rw [hlflat]
    apply ofProg_mono_right (p1 := [.LD .x1 rs sofs]) (p2 := [.JALR .x0 .x1 0])
      (by simp only [List.length_cons, List.length_nil]; omega)
    rw [CodeReq.ofProg_singleton]
    exact h
  -- restore + return: from the ghost-indexed body post back to the contract
  have hRest : cpsTripleWithin 2 ((base + 4) + BitVec.ofNat 64 (4 * f.body.size))
      ret cr (asrtR f.region f.rw (spost ret))
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM f.region f.rw f.post) := by
    apply cpsTripleWithin_exists_pre_R
    intro rf ws A v hlen hApc hreach
    have haddr' : rf.get rs + signExtend12 sofs
        = f.rw.base + BitVec.ofNat 64 k := haddrPost ret rf ws A hreach
    have hidx : ((rf.get rs + signExtend12 sofs) - f.rw.base).toNat = k := by
      rw [haddr']
      bv_omega
    have hwf' : (Region.mk f.rw.base ws).wf := RwRegion.wf_toRegion hrw hlen
    have hin' : inRw f.rw.base ws (rf.get rs + signExtend12 sofs) 8 := by
      unfold inRw
      rw [hidx]
      omega
    have hld := ld_ra_spec_within rs sofs f.rw.base rf ws v
      ((base + 4) + BitVec.ofNat 64 (4 * f.body.size)) hrs hwf' hin'
      (by rw [hidx]; exact hk)
    rw [hidx, hslot ret rf ws A hreach hlen, packBytes_dwordBytes] at hld
    have hld' := cpsTripleWithin_extend_code hcodeLD hld
    have hldA := cpsTripleWithin_frameR A hApc hld'
    have hld'' := cpsTripleWithin_frameR
      (bytesRegion f.region.base f.region.bytes) (bytesRegion_pcFree _ _) hldA
    -- JALR
    have hjal := jalr_ret_spec (((base + 4) + BitVec.ofNat 64 (4 * f.body.size)) + 4)
      ret halign
      (P := (((regFileIs rf) ** bytesRegion f.rw.base ws) ** A) **
        bytesRegion f.region.base f.region.bytes)
      (pcFree_sepConj (pcFree_sepConj (pcFree_sepConj (pcFree_regFileIs _)
        (bytesRegion_pcFree _ _)) hApc) (bytesRegion_pcFree _ _))
    have hjal' := cpsTripleWithin_extend_code hcodeJ hjal
    have hseq := cpsTripleWithin_seq_same_cr
      (cpsTripleWithin_weaken
        (P := ((((.x1 : Reg) ↦ᵣ v) ** ((regFileIs rf) ** bytesRegion f.rw.base ws))
          ** A) ** bytesRegion f.region.base f.region.bytes)
        (P' := (((regFileIs rf) ** bytesRegion f.rw.base ws) ** A) **
          (bytesRegion f.region.base f.region.bytes ** ((.x1 : Reg) ↦ᵣ v)))
        (Q' := ((.x1 : Reg) ↦ᵣ ret) **
          ((((regFileIs rf) ** bytesRegion f.rw.base ws) ** A) **
            bytesRegion f.region.base f.region.bytes))
        (fun hp hh => by
          have h1 := sc_to_swap hp hh
          rw [sepConj_assoc' ((regFileIs rf) ** bytesRegion f.rw.base ws) A
              ((.x1 : Reg) ↦ᵣ v),
            sepConj_comm' A ((.x1 : Reg) ↦ᵣ v),
            sepConj_left_comm ((regFileIs rf) ** bytesRegion f.rw.base ws)
              ((.x1 : Reg) ↦ᵣ v) A,
            ← sepConj_assoc' ((.x1 : Reg) ↦ᵣ v)
              ((regFileIs rf) ** bytesRegion f.rw.base ws) A] at h1
          exact h1)
        (fun hp hh => by
          rw [sepConj_assoc'
              (((.x1 : Reg) ↦ᵣ ret) ** ((regFileIs rf) ** bytesRegion f.rw.base ws))
              A (bytesRegion f.region.base f.region.bytes),
            sepConj_assoc' ((.x1 : Reg) ↦ᵣ ret)
              ((regFileIs rf) ** bytesRegion f.rw.base ws),
            ← sepConj_assoc' ((regFileIs rf) ** bytesRegion f.rw.base ws) A
              (bytesRegion f.region.base f.region.bytes)] at hh
          exact hh)
        hld'')
      hjal'
    refine cpsTripleWithin_weaken (fun hp hh => hh) ?_ hseq
    -- ((.x1 ↦ ret) ** (((RF ** BW) ** A) ** RO)) → ((.x1 ↦ ret) ** asrtM post)
    intro hp hh
    refine sepConj_mono_right (fun hq hx => ?_) hp hh
    show asrtM f.region f.rw f.post hq
    exact sepConj_mono_left
      (fun hv hy => ⟨rf, ws, A, hlen, hApc, hspost ret rf ws A hreach, hy⟩) hq hx
  -- spill + body
  have hMain : cpsTripleWithin (1 + f.body.steps) base
      ((base + 4) + BitVec.ofNat 64 (4 * f.body.size)) cr
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM f.region f.rw f.pre)
      (asrtR f.region f.rw (spost ret)) := by
    rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret) (asrtM f.region f.rw f.pre)]
    apply cpsTripleWithin_exists_pre_M_frame
    intro rf ws A hlen hApc hreach
    have haddr' : rf.get rs + signExtend12 sofs
        = f.rw.base + BitVec.ofNat 64 k := haddr rf ws A hreach
    have hidx : ((rf.get rs + signExtend12 sofs) - f.rw.base).toNat = k := by
      rw [haddr']
      bv_omega
    have hwf' : (Region.mk f.rw.base ws).wf := RwRegion.wf_toRegion hrw hlen
    have hin' : inRw f.rw.base ws (rf.get rs + signExtend12 sofs) 8 := by
      unfold inRw
      rw [hidx]
      omega
    have hsd := sd_ra_spec_within rs sofs f.rw.base rf ws ret base hrs hwf' hin'
      (by rw [hidx]; exact hk)
    rw [hidx] at hsd
    have hsd' := cpsTripleWithin_extend_code hcodeSD hsd
    have hsdA := cpsTripleWithin_frameR A hApc hsd'
    have hsd'' := cpsTripleWithin_frameR
      (bytesRegion f.region.base f.region.bytes) (bytesRegion_pcFree _ _) hsdA
    have hsdW := cpsTripleWithin_weaken
      (P := ((((.x1 : Reg) ↦ᵣ ret) ** ((regFileIs rf) ** bytesRegion f.rw.base ws))
        ** A) ** bytesRegion f.region.base f.region.bytes)
      (P' := (((regFileIs rf) ** bytesRegion f.rw.base ws) ** A) **
        (bytesRegion f.region.base f.region.bytes ** ((.x1 : Reg) ↦ᵣ ret)))
      (Q' := asrtR f.region f.rw (spre ret))
      (fun hp hh => by
        have h1 := sc_to_swap hp hh
        rw [sepConj_assoc' ((regFileIs rf) ** bytesRegion f.rw.base ws) A
            ((.x1 : Reg) ↦ᵣ ret),
          sepConj_comm' A ((.x1 : Reg) ↦ᵣ ret),
          sepConj_left_comm ((regFileIs rf) ** bytesRegion f.rw.base ws)
            ((.x1 : Reg) ↦ᵣ ret) A,
          ← sepConj_assoc' ((.x1 : Reg) ↦ᵣ ret)
            ((regFileIs rf) ** bytesRegion f.rw.base ws) A] at h1
        exact h1)
      (fun hp hh => by
        rw [sepConj_assoc' ((.x1 : Reg) ↦ᵣ ret)
          ((regFileIs rf) ** bytesRegion f.rw.base (setBytes ws k (dwordBytes ret)))
          A] at hh
        have h1 := sepConj_mono_left
          (fun hq hx => sepConj_mono_left
            (fun hv (hy : ((.x1 : Reg) ↦ᵣ ret) hv) =>
              (⟨ret, hy⟩ : regOwn .x1 hv)) hq hx) hp hh
        have h2 := sepConj_mono_left
          (fun hq hx => sepConj_mono_right
            (fun hv hy =>
              (⟨rf, setBytes ws k (dwordBytes ret), A,
                by rw [length_setBytes]; exact hlen, hApc,
                hspre ret rf ws A hreach hlen, hy⟩ :
                asrtOf f.rw (spre ret) hv)) hq hx) hp h1
        rw [sepConj_assoc', sepConj_comm'] at h2
        exact h2)
      hsd''
    exact cpsTripleWithin_seq_same_cr hsdW (hbody ret)
  exact cpsTripleWithin_seq_same_cr hMain hRest

/-- Package a verified caller as a callee handle: the handle's code is the
    ambient `cr` (the wrapper's own code plus every callee's). -/
def toHandleR (f : Fn) (base : Word) (cr : CodeReq)
    (rs : Reg) (sofs : BitVec 12) (k : Nat)
    (spre spost : Word → Reach)
    (hrs : (Reg.isExposed rs || rs == .x0) = true)
    (hrw : f.rw.wf)
    (hk : 8 ∣ k) (hk8 : k + 8 ≤ f.rw.len)
    (hsz : 4 * (f.body.size + 3) ≤ 2 ^ 64)
    (hbody : ∀ v : Word, cpsTripleWithin f.body.steps (base + 4)
        ((base + 4) + BitVec.ofNat 64 (4 * f.body.size)) cr
        (asrtR f.region f.rw (spre v)) (asrtR f.region f.rw (spost v)))
    (hcode : ∀ a i, CodeReq.ofProg base (f.programRetR rs sofs base) a = some i →
        cr a = some i)
    (haddr : ∀ rf ws A, f.pre rf ws A →
        rf.get rs + signExtend12 sofs = f.rw.base + BitVec.ofNat 64 k)
    (haddrPost : ∀ v rf ws A, spost v rf ws A →
        rf.get rs + signExtend12 sofs = f.rw.base + BitVec.ofNat 64 k)
    (hspre : ∀ v rf ws A, f.pre rf ws A → ws.length = f.rw.len →
        spre v rf (setBytes ws k (dwordBytes v)) A)
    (hspost : ∀ v rf ws A, spost v rf ws A → f.post rf ws A)
    (hslot : ∀ v rf ws A, spost v rf ws A → ws.length = f.rw.len →
        (ws.drop k).take 8 = dwordBytes v) : FnHandle where
  entry := base
  code := cr
  nSteps := 1 + f.body.steps + 2
  region := f.region
  rw := f.rw
  pre := f.pre
  post := f.post
  sound := f.retSpecR base cr rs sofs k spre spost hrs hrw hk hk8 hsz hbody
    hcode haddr haddrPost hspre hspost hslot

end Fn

end SAsm
end EvmAsm.Rv64
