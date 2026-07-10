/-
  EvmAsm.Codegen.Programs.Bls12Fq12SetOneSAsm

  **A tactic-driven cross-call sp-frame port** (bead
  evm-asm-4ch8f.58.3.23, unblocked by the `abiFrameCall_spec` bridge and the
  `FramePort` automation): `blq_set_one`, byte-TRANSPARENT (the existing
  emitted `blqSetOne_prog` already IS an `abiFrameProg` flatten — no re-emit,
  no guest-byte change):

      blq_set_one:  addi sp, sp, -16
                    sd   ra, 0(sp)
                    sd   s0, 8(sp)
                    mv   s0, a0            -- clobbers callee-saved s0
                    jal  ra, blq_zero      -- zero all 72 dwords (clobbers ra!)
                    li   t0, 1
                    sd   t0 -> 0(s0)       -- coefficient 0 := 1
                    ld   ra, 0(sp)
                    ld   s0, 8(sp)
                    addi sp, sp, +16
                    ret

  The callee `blq_zero`'s FLAT whole-routine contract (`blqZeroFlat_spec`)
  — the `cpsTripleWithin` shape `callWithin_spec` consumes — is DERIVED
  from the structured `Bls12Fq12Zero576SAsm.blqZeroFn_spec` by the
  flat-contract adapter (`Fn.retSpecFlat`, bead evm-asm-el1w2): no
  hand-written per-callee loop proof.  The adapter carries the leaf's own
  post faithfully (advanced `a0`, zeroed window) and surfaces the callee's
  full exposed-register footprint as `regOwns blqScratch` riders — the
  inherent width of an `Fn.Spec`-derived contract (see `FnFlat.lean`).

  `blqSetOneFrame_spec` is the whole-routine ABI contract, wrapped by
  `abi_frame`: on return `sp`, `ra` (clobbered by the real `jal`!), and `s0`
  (clobbered by the body) are restored to entry, and the FQ12 at the entry
  `a0` holds ONE — dword 0 = 1, the other 71 dwords = 0 — the genuine,
  unweakened semantics.  `a0` itself ends at `dst + 576` (advanced by
  `blq_zero`), exactly as the machine leaves it.

  Byte-tie: `#guard`/`rfl` against the emitted `blqSetOne_prog` (including
  the concrete guest-linked `jalOff`) and the `GuestAddrs` anchors.
-/

import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.Bls12Fq12
import EvmAsm.Codegen.Programs.Bls12Fq12ZeroSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.Tactics

namespace Bls12Fq12SetOneSAsm

-- ============================================================================
-- Anchors and byte-ties.
-- ============================================================================

-- The two routines are adjacent in the guest text: `blq_zero` (6 slots)
-- immediately precedes `blq_set_one`.
#guard GuestAddrs.blq_zero = 0x80034b28
#guard GuestAddrs.blq_set_one = 0x80034b40
#guard GuestAddrs.blq_zero + 4 * blqZero_prog.length = GuestAddrs.blq_set_one

/-- The caller's 2-slot frame: `ra` at 0, `s0` at 8. -/
def setOneFrame : FrameDesc := [(.x1, 0), (.x8, 8)]

/-- The caller body: pointer copy, the cross-call, the coefficient-0 store. -/
def setOneBody : List Instr :=
  [ .MV .x8 .x10,
    .JAL .x1 (jalOff GuestAddrs.blq_zero (GuestAddrs.blq_set_one + 16)),
    .LI .x5 (1 : Word),
    .SD .x8 .x5 (0 : BitVec 12) ]

-- Byte-transparency: the emitted `blqSetOne_prog` IS the abiFrameProg
-- flatten of this frame + body — verified == emitted, bytes unchanged.
#guard abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) setOneFrame setOneBody
  = blqSetOne_prog

/-- Byte-transparency, kernel-checked. -/
theorem setOneProg_eq :
    abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) setOneFrame setOneBody
      = blqSetOne_prog := rfl

/-- The verification `CodeReq`: both adjacent routines, at their guest
    addresses. -/
def blqCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.blq_zero : Word) (blqZero_prog ++ blqSetOne_prog)

-- ============================================================================
-- Word / list helpers.
-- ============================================================================

private theorem add_sext0 (x : Word) : x + signExtend12 (0 : BitVec 12) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show (signExtend12 (0 : BitVec 12)).toNat = 0 from by decide,
      Nat.add_zero, Nat.mod_eq_of_lt x.isLt]

private theorem add_ofNat_zero (x : Word) : x + BitVec.ofNat 64 0 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero,
      Nat.mod_eq_of_lt x.isLt]

-- ============================================================================
-- The callee's flat contract, DERIVED from its `Fn.Spec` by the adapter
-- (`Fn.retSpecFlat`, bead evm-asm-el1w2) — no hand-written loop proof here.
-- ============================================================================

/-- The exposed registers other than `a0` — the callee owns the whole exposed
    file (that is what its `Fn.Spec` claims), surfaced as `regOwn` riders. -/
def blqScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Split the full exposed file into the `a0` atom plus the scratch atoms. -/
private theorem exposedRegs_split (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf blqScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [blqScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_scratch : (.x10 : Reg) ∉ blqScratch := by decide

def blqZeroSteps (dst : Word) (vs : List Word) : Nat :=
  (Bls12Fq12Zero576SAsm.blqZeroFn dst (vs.flatMap dwordBytes)).body.steps + 1

/-- **The flat whole-routine contract for `blq_zero`** — the exact
    `cpsTripleWithin` shape `callWithin_spec` consumes, now DERIVED from the
    structured `Bls12Fq12Zero576SAsm.blqZeroFn_spec` by `Fn.retSpecFlat`:
    entered at its guest address with any aligned return address in `ra`, a
    buffer pointer in `a0`, ownership of the remaining exposed registers,
    and 72 owned dwords, it returns with all 72 dwords zero, `a0` advanced
    past the buffer, and `ra` intact. -/
theorem blqZeroFlat_spec (ret dst : Word) (vs : List Word)
    (hlen : vs.length = 72)
    (hwf : RwRegion.wf ⟨dst, 576⟩)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (blqZeroSteps dst vs) (GuestAddrs.blq_zero : Word) ret blqCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** regOwns blqScratch
        ** dwordsIs dst vs)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ (dst + BitVec.ofNat 64 576))
        ** regOwns blqScratch
        ** dwordsIs dst (List.replicate 72 (0 : Word))) := by
  -- Surface the scratch registers at concrete (peeled) valuations.
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns blqScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** dwordsIs dst vs)
      (fun vf => ?_))
  -- The adapter, at the packed register file.
  have hlenB : (vs.flatMap dwordBytes).length = 576 := by
    rw [length_flatMap_dwordBytes, hlen]
  have had := Fn.retSpecFlat (Bls12Fq12Zero576SAsm.blqZeroFn dst (vs.flatMap dwordBytes))
    (GuestAddrs.blq_zero : Word)
    (Bls12Fq12Zero576SAsm.blqZeroFn_spec dst (vs.flatMap dwordBytes) hwf
      (GuestAddrs.blq_zero : Word))
    (by show 4 * (5 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then dst else vf r)
    (vs.flatMap dwordBytes)
    hlenB
    (by
      refine ⟨?_, rfl, hlenB, rfl⟩
      show RegFile.get (fun r => if r = .x10 then dst else vf r) .x10 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl)
    (fun _ _ _ h => h.2.2.2)
    (Q := (.x10 ↦ᵣ (dst + BitVec.ofNat 64 576)) ** regOwns blqScratch
      ** dwordsIs dst (List.replicate 72 (0 : Word)))
    (fun rf' ws' hlen' hpost' hp hh => by
      obtain ⟨hx10', hx7', hws', -⟩ := hpost'
      subst hws'
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split,
        show List.replicate 576 (0 : BitVec 8)
          = (List.replicate 72 (0 : Word)).flatMap dwordBytes from by
            rw [replicate_zero_flatMap_dwordBytes],
        ← dwordsIs_eq_bytesRegion,
        show rf' .x10 = dst + BitVec.ofNat 64 576 from by
          rw [show rf' .x10 = rf'.get .x10 from by
            rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
          exact hx10'] at hh
      have hh2 := sepConj_mono_left
        (sepConj_mono_right (regAtomsOf_to_regOwns (fun r => rf' r) blqScratch))
        hp hh
      xperm_hyp hh2)
  -- The adapter's CodeReq is exactly `blq_zero`'s program; lift into `blqCr`.
  rw [show (Bls12Fq12Zero576SAsm.blqZeroFn dst (vs.flatMap dwordBytes)).programRet (GuestAddrs.blq_zero : Word)
      = blqZero_prog from rfl] at had
  have hadC := liftCode (cr' := blqCr) had (by code_mem)
  -- Reshape: strip the empty read-only region, unpack the register file.
  rw [show (Bls12Fq12Zero576SAsm.blqZeroFn dst (vs.flatMap dwordBytes)).region = Region.empty from rfl]
    at hadC
  rw [show bytesRegion Region.empty.base Region.empty.bytes = empAssertion from
    bytesRegion_nil _] at hadC
  rw [sepConj_emp_right', sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split,
    show (if (Reg.x10 : Reg) = .x10 then dst else vf .x10) = dst from if_pos rfl,
    regAtomsOf_congr (fun r => if r = .x10 then dst else vf r) vf blqScratch
      (fun r hr => by
        show (if r = .x10 then dst else vf r) = vf r
        exact if_neg (fun (hc : r = .x10) => x10_notin_scratch (hc ▸ hr))),
    show (Bls12Fq12Zero576SAsm.blqZeroFn dst (vs.flatMap dwordBytes)).rw.base = dst from rfl,
    ← dwordsIs_eq_bytesRegion] at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

-- ============================================================================
-- The caller: `blq_set_one` via the frame + cross-call composition.
-- ============================================================================

/-- The exposed registers the caller does not track across the call
    (`blqScratch` minus `t0`/`t2`, which the caller's statement names). -/
def blqRiders : List Reg :=
  [.x6, .x28, .x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Entry values of the saved registers. -/
def setOneVals (ret arb8 : Word) : Reg → Word :=
  fun r => match r with | .x1 => ret | .x8 => arb8 | _ => 0

/-- Post-body values: `ra` holds the call's link address (genuinely
    clobbered by the `jal`; the epilogue restores it from the slot), `s0`
    the buffer pointer. -/
def setOneVals' (dst : Word) : Reg → Word :=
  fun r => match r with | .x1 => ((GuestAddrs.blq_zero + 44) : Word) | .x8 => dst | _ => 0

/-- **The whole-routine ABI contract for `blq_set_one`.**  On return `sp`,
    `ra`, and `s0` are restored to ENTRY values (`ra` was clobbered by the
    real cross-call; `s0` by the body), and the FQ12 at the entry `a0` holds
    ONE: dword 0 = 1, dwords 1–71 = 0 — the genuine, unweakened semantics.
    `a0` ends at `dst + 576` exactly as `blq_zero` leaves it.

    The callee contract is the adapter-derived `blqZeroFlat_spec`, so the
    caller owns the callee's full exposed-register footprint across the
    call: the untracked registers ride as `regOwns blqRiders`. -/
theorem blqSetOneFrame_spec (sp0 ret dst arb8 v5 v7 : Word) (vs : List Word)
    (hlen : vs.length = 72)
    (hwf : RwRegion.wf ⟨dst, 576⟩)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      (1 + setOneFrame.length + (1 + (1 + blqZeroSteps dst vs) + 1 + 1)
        + setOneFrame.length + 1 + 1)
      ((GuestAddrs.blq_zero + 24) : Word) ret blqCr
      ((.x2 ↦ᵣ sp0) ** regsAt setOneFrame (setOneVals ret arb8)
        ** frameSlotsOwn setOneFrame (sp0 + signExtend12 (-16 : BitVec 12))
        ** ((.x10 ↦ᵣ dst) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7)
          ** regOwns blqRiders
          ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs dst vs))
      ((.x2 ↦ᵣ sp0) ** regsAt setOneFrame (setOneVals ret arb8)
        ** frameSlotsSaved setOneFrame (sp0 + signExtend12 (-16 : BitVec 12))
            (setOneVals ret arb8)
        ** ((.x10 ↦ᵣ (dst + BitVec.ofNat 64 576)) ** regOwn .x5 ** regOwn .x7
          ** regOwns blqRiders
          ** (Reg.x0 ↦ᵣ (0 : Word))
          ** dwordsIs dst ((1 : Word) :: List.replicate 71 (0 : Word)))) := by
  -- ---- the single-exit body: mv ; call ; li ; sd ----
  -- mv s0, a0
  have hmv := mv_spec_gen_within .x8 .x10 dst arb8 ((GuestAddrs.blq_zero + 36) : Word) (by decide)
  rw [show ((GuestAddrs.blq_zero + 36) : Word) + 4 = ((GuestAddrs.blq_zero + 40) : Word) from by decide] at hmv
  have hmvC := liftCode (cr' := blqCr) hmv (by code_mem)
  have hmvF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** regOwns blqRiders
      ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs dst vs)
    (by pcf) hmvC
  -- jal ra, blq_zero: the cross-call (adapter-derived callee contract).
  have hcallee := blqZeroFlat_spec (((GuestAddrs.blq_zero + 40) : Word) + 4) dst vs hlen hwf (by decide)
  have hcall := callWithin_spec ((GuestAddrs.blq_zero + 40) : Word) (GuestAddrs.blq_zero : Word) ret
    (jalOff GuestAddrs.blq_zero (GuestAddrs.blq_set_one + 16)) (blqZeroSteps dst vs)
    (by decide) (by code_mem) (by pcf) hcallee
  rw [show ((GuestAddrs.blq_zero + 40) : Word) + 4 = ((GuestAddrs.blq_zero + 44) : Word) from by decide] at hcall
  -- the caller tracks t0/t2 by value; hand them to the callee as ownership
  have hcallW := cpsTripleWithin_weaken
    (P' := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7)
      ** regOwns blqRiders ** dwordsIs dst vs)
    (fun h hp => by
      simp only [blqScratch, blqRiders, regOwns_cons, regOwns_nil] at hp ⊢
      have hp1 : ((.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7)
          ** (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst)
            ** regOwn .x6 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30
            ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13
            ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17
            ** empAssertion ** dwordsIs dst vs)) h := by
        xperm_hyp hp
      have hp2 := sepConj_mono (regIs_to_regOwn .x5 v5)
        (sepConj_mono (regIs_to_regOwn .x7 v7) (fun _ hh => hh)) h hp1
      xperm_hyp hp2)
    (fun _ hq => hq) hcall
  have hcallF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ dst) ** (Reg.x0 ↦ᵣ (0 : Word))) (by pcf) hcallW
  -- li t0, 1 (t0 comes back from the callee as ownership)
  have hli := li_spec_gen_own_within .x5 (1 : Word) ((GuestAddrs.blq_zero + 44) : Word) (by decide)
  rw [show ((GuestAddrs.blq_zero + 44) : Word) + 4 = ((GuestAddrs.blq_zero + 48) : Word) from by decide] at hli
  have hliC := liftCode (cr' := blqCr) hli (by code_mem)
  have hliF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ((GuestAddrs.blq_zero + 44) : Word)) ** (.x8 ↦ᵣ dst)
      ** (.x10 ↦ᵣ (dst + BitVec.ofNat 64 576))
      ** regOwn .x7 ** regOwns blqRiders
      ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs dst (List.replicate 72 (0 : Word)))
    (by pcf) hliC
  -- sd t0 -> 0(s0): coefficient 0 := 1.
  obtain ⟨front, rest, hf, hr, heq1, heq2⟩ :=
    dwordsIs_at_set dst (List.replicate 72 (0 : Word)) 0 1 (by decide)
  have hcell0 : dst + BitVec.ofNat 64 (8 * 0) = dst := by
    rw [show (8 * 0 : Nat) = 0 from rfl]
    exact add_ofNat_zero dst
  rw [hcell0] at heq1 heq2
  have hone : (List.replicate 72 (0 : Word)).set 0 1
      = ((1 : Word) :: List.replicate 71 (0 : Word)) := by decide
  rw [hone] at heq2
  have hsd := sd_spec_gen_within .x8 .x5 dst (1 : Word)
    ((List.replicate 72 (0 : Word)).getD 0 0) (0 : BitVec 12) ((GuestAddrs.blq_zero + 48) : Word)
  rw [add_sext0] at hsd
  rw [show ((GuestAddrs.blq_zero + 48) : Word) + 4 = ((GuestAddrs.blq_zero + 52) : Word) from by decide] at hsd
  have hsdC := liftCode (cr' := blqCr) hsd (by code_mem)
  have hsdF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ((GuestAddrs.blq_zero + 44) : Word))
      ** (.x10 ↦ᵣ (dst + BitVec.ofNat 64 576))
      ** regOwn .x7 ** regOwns blqRiders
      ** (Reg.x0 ↦ᵣ (0 : Word)) ** front ** rest)
    (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact pcFree_regOwns _
        | exact hf
        | exact hr) hsdC
  -- unpack the returned scratch fold into t0-ownership + the riders
  have hscr : regOwns blqScratch
      = (regOwn .x5 ** regOwn .x7 ** regOwns blqRiders) := by
    simp only [blqScratch, blqRiders, regOwns_cons, regOwns_nil]
    xperm
  -- chain: mv ; call ; li ; sd
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmvF hcallF
  have s2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [hscr] at hp; xperm_hyp hp) s1 hliF
  have s3 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [heq1] at hp; xperm_hyp hp) s2 hsdF
  -- the single-exit body triple, in `abiFrame_spec` shape
  have hbody : cpsTripleWithin (1 + (1 + blqZeroSteps dst vs) + 1 + 1)
      (((GuestAddrs.blq_zero + 24) : Word) + BitVec.ofNat 64 (4 * (1 + setOneFrame.length)))
      (((GuestAddrs.blq_zero + 24) : Word)
        + BitVec.ofNat 64 (4 * (1 + setOneFrame.length + setOneBody.length)))
      blqCr
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-16 : BitVec 12)))
        ** regsAt setOneFrame (setOneVals ret arb8)
        ** frameSlotsSaved setOneFrame (sp0 + signExtend12 (-16 : BitVec 12))
            (setOneVals ret arb8)
        ** ((.x10 ↦ᵣ dst) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7)
          ** regOwns blqRiders
          ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs dst vs))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-16 : BitVec 12)))
        ** regsAt setOneFrame (setOneVals' dst)
        ** frameSlotsSaved setOneFrame (sp0 + signExtend12 (-16 : BitVec 12))
            (setOneVals ret arb8)
        ** ((.x10 ↦ᵣ (dst + BitVec.ofNat 64 576)) ** regOwn .x5 ** regOwn .x7
          ** regOwns blqRiders
          ** (Reg.x0 ↦ᵣ (0 : Word))
          ** dwordsIs dst ((1 : Word) :: List.replicate 71 (0 : Word)))) := by
    have hentry : ((GuestAddrs.blq_zero + 24) : Word) + BitVec.ofNat 64 (4 * (1 + setOneFrame.length))
        = ((GuestAddrs.blq_zero + 36) : Word) := by decide
    have hexit : ((GuestAddrs.blq_zero + 24) : Word)
          + BitVec.ofNat 64 (4 * (1 + setOneFrame.length + setOneBody.length))
        = ((GuestAddrs.blq_zero + 52) : Word) := by decide
    rw [hentry, hexit]
    simp only [setOneFrame, regsAt, frameSlotsSaved, setOneVals, setOneVals',
      List.foldr_cons, List.foldr_nil, sepConj_emp_right']
    have hchainF := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-16 : BitVec 12)))
        ** (((sp0 + signExtend12 (-16 : BitVec 12))
              + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
        ** (((sp0 + signExtend12 (-16 : BitVec 12))
              + signExtend12 (8 : BitVec 12)) ↦ₘ arb8))
      (by pcf) s3
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_)
      hchainF
    -- release t0 (`↦ 1`) to ownership; reassemble the ONE array.
    have hq1 : ((.x5 ↦ᵣ (1 : Word))
        ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.blq_zero + 44) : Word)) ** (.x8 ↦ᵣ dst)
        ** (.x10 ↦ᵣ (dst + BitVec.ofNat 64 576))
        ** regOwn .x7 ** regOwns blqRiders
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** dwordsIs dst ((1 : Word) :: List.replicate 71 (0 : Word))
        ** (.x2 ↦ᵣ (sp0 + signExtend12 (-16 : BitVec 12)))
        ** (((sp0 + signExtend12 (-16 : BitVec 12))
              + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
        ** (((sp0 + signExtend12 (-16 : BitVec 12))
              + signExtend12 (8 : BitVec 12)) ↦ₘ arb8))) h := by
      rw [heq2]
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _) (fun _ hh => hh) h hq1
    xperm_hyp hq2
  abi_frame (16 : BitVec 12) halign hbody


end Bls12Fq12SetOneSAsm

end EvmAsm.Codegen
