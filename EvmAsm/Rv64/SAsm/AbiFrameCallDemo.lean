/-
  EvmAsm.Rv64.SAsm.AbiFrameCallDemo

  End-to-end regression witness for the frame + cross-call composition
  (`AbiFrameCall.lean`, bead evm-asm-4ch8f.76 follow-up): a framed caller
  invokes a framed callee TWICE via real `jal ra` instructions.

  The callee (`bump`, at `0x2000`) increments the dword at `[a0]`.  It uses
  `s0` as a scratch pointer copy — a callee-saved register — so it has its
  own 16-byte frame (saving `ra` + `s0`), carved from the CALLER's free
  stack (`stackFree newSp 2`) and released on return; its whole-routine
  contract is itself an `abiFrame_spec` instance:

      bump:  addi sp, sp, -16
             sd   ra, 0(sp)
             sd   s0, 8(sp)
             mv   s0, a0          -- clobbers callee-saved s0
             ld   a1, 0(s0)
             addi a1, a1, 1
             sd   a1 -> 0(s0)     -- [a0] += 1
             ld   ra, 0(sp)
             ld   s0, 8(sp)
             addi sp, sp, +16
             ret

  The caller (`twice`, at `0x1000`) saves only `ra` (each `jal` genuinely
  clobbers it — the second call's link overwrites the first's) and calls
  `bump` twice:

      twice: addi sp, sp, -8
             sd   ra, 0(sp)
             jal  ra, bump        -- ra := 0x100C
             jal  ra, bump        -- ra := 0x1010
             ld   ra, 0(sp)
             addi sp, sp, +8
             ret

  `twiceFrame_spec` proves the whole ABI contract: on return `sp` and `ra`
  equal their ENTRY values (the body clobbered `ra` twice; restoration is
  *derived* from the caller's saved-`ra` slot, which both callees provably
  could not touch — it is framed out of their footprint), the dword at
  `[a0]` holds `v + 1 + 1`, `s0` (used and restored by the callee, twice)
  still holds the caller's value, and the free stack the callees borrowed is
  owned again.  Byte-transparency: `#guard`/`rfl` tie both `abiFrameProg`
  flattens to the spelled-out programs.
-/

import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64
namespace SAsm
namespace AbiFrameCallDemo

open EvmAsm.Rv64.Tactics

-- ============================================================================
-- The callee: `bump` (own frame, increments `[a0]`, clobbers s0).
-- ============================================================================

/-- The callee's 2-slot frame: `ra` at 0, `s0` at 8. -/
def bumpFrame : FrameDesc := [(.x1, 0), (.x8, 8)]

/-- Callee body: copy the pointer into (callee-saved) `s0`, load, increment,
    store back. -/
def bumpBody : List Instr :=
  [ .MV .x8 .x10,
    .LD .x11 .x8 (0 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .SD .x8 .x11 (0 : BitVec 12) ]

/-- The whole callee routine (11 instructions), as an `abiFrameProg`. -/
def bumpProg : List Instr :=
  abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) bumpFrame bumpBody

/-- The same 11 instructions spelled out. -/
def bumpProgList : List Instr :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x10,
    .LD .x11 .x8 (0 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .SD .x8 .x11 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

#guard bumpProg = bumpProgList

/-- Byte-transparency of the callee, kernel-checked. -/
theorem bumpProg_eq : bumpProg = bumpProgList := rfl

-- ============================================================================
-- The caller: `twice` (saves only ra, two real `jal ra` calls).
-- ============================================================================

/-- The caller's 1-slot frame: just `ra` (the calls clobber nothing else it
    must preserve). -/
def twiceFrame : FrameDesc := [(.x1, 0)]

/-- Caller body: two direct calls to `bump` (`0x1008 + 0xFF8 = 0x2000`,
    `0x100C + 0xFF4 = 0x2000`). -/
def twiceBody : List Instr :=
  [ .JAL .x1 (0xFF8 : BitVec 21),
    .JAL .x1 (0xFF4 : BitVec 21) ]

/-- The whole caller routine (7 instructions), as an `abiFrameProg`. -/
def twiceProg : List Instr :=
  abiFrameProg (-8 : BitVec 12) (8 : BitVec 12) twiceFrame twiceBody

/-- The same 7 instructions spelled out. -/
def twiceProgList : List Instr :=
  [ .ADDI .x2 .x2 (-8 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .JAL .x1 (0xFF8 : BitVec 21),
    .JAL .x1 (0xFF4 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (8 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

#guard twiceProg = twiceProgList

/-- Byte-transparency of the caller, kernel-checked. -/
theorem twiceProg_eq : twiceProg = twiceProgList := rfl

/-- The demo CodeReq: caller at `0x1000`, callee at `0x2000`. -/
def callDemoCr : CodeReq :=
  (CodeReq.ofProg 0x1000 twiceProgList).union (CodeReq.ofProg 0x2000 bumpProgList)

/-- Caller code containment. -/
private theorem twiceSub :
    ∀ a i, CodeReq.ofProg 0x1000 twiceProgList a = some i → callDemoCr a = some i := by
  intro a i h
  simp only [callDemoCr, CodeReq.union, h]

/-- Callee code containment (the caller's 7 slots never alias the callee's
    11 slots). -/
private theorem bumpSub :
    ∀ a i, CodeReq.ofProg 0x2000 bumpProgList a = some i → callDemoCr a = some i := by
  intro a i h
  obtain ⟨k, hk, rfl⟩ := ofProg_some_range h
  have hk11 : k < 11 := hk
  have hnone : CodeReq.ofProg 0x1000 twiceProgList
      ((0x2000 : Word) + BitVec.ofNat 64 (4 * k)) = none := by
    apply CodeReq.ofProg_none_range
    intro k' hk' heq
    have : k' < 7 := hk'
    bv_omega
  simp only [callDemoCr, CodeReq.union, hnone, h]

/-- Code-membership: instruction `idx` of the caller sits in `callDemoCr`. -/
private theorem twiceAt (idx : Nat) (addr : Word) (instr : Instr)
    (hk : idx < twiceProgList.length) (hbound : 4 * twiceProgList.length < 2 ^ 64)
    (haddr : addr = (0x1000 : Word) + BitVec.ofNat 64 (4 * idx))
    (hget : twiceProgList.get ⟨idx, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i → callDemoCr a = some i := by
  have m := CodeReq.ofProg_lookup_addr (0x1000 : Word) twiceProgList idx addr hk hbound haddr
  rw [hget] at m
  exact fun a i h => twiceSub a i (CodeReq.singleton_mono m a i h)

-- ============================================================================
-- Address / word helpers.
-- ============================================================================

private theorem add_sext0 (x : Word) : x + signExtend12 (0 : BitVec 12) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show (signExtend12 (0 : BitVec 12)).toNat = 0 from by decide,
      Nat.add_zero, Nat.mod_eq_of_lt x.isLt]

/-- The callee's slot 0 is the deepest free-stack cell. -/
private theorem slot0_addr (sp : Word) :
    (sp + signExtend12 (-16 : BitVec 12)) + signExtend12 (0 : BitVec 12)
      = sp - BitVec.ofNat 64 (8 * 2) := by
  rw [show signExtend12 (-16 : BitVec 12) = (-16 : Word) from by decide,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show BitVec.ofNat 64 (8 * 2) = (16 : Word) from by decide]
  bv_omega

/-- The callee's slot 8 is the shallow free-stack cell. -/
private theorem slot8_addr (sp : Word) :
    (sp + signExtend12 (-16 : BitVec 12)) + signExtend12 (8 : BitVec 12)
      = sp - BitVec.ofNat 64 (8 * 1) := by
  rw [show signExtend12 (-16 : BitVec 12) = (-16 : Word) from by decide,
      show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
      show BitVec.ofNat 64 (8 * 1) = (8 : Word) from by decide]
  bv_omega

private theorem frameRestore16 (sp : Word) :
    (sp + signExtend12 (-16 : BitVec 12)) + signExtend12 (16 : BitVec 12) = sp := by
  rw [show signExtend12 (-16 : BitVec 12) = (-16 : Word) from by decide,
      show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
  bv_omega

private theorem frameRestore8 (sp : Word) :
    (sp + signExtend12 (-8 : BitVec 12)) + signExtend12 (8 : BitVec 12) = sp := by
  rw [show signExtend12 (-8 : BitVec 12) = (-8 : Word) from by decide,
      show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
  bv_omega

-- ============================================================================
-- The callee's whole-routine calling contract (an `abiFrame_spec` instance,
-- reshaped onto the free-stack region).
-- ============================================================================

/-- Callee entry register values: `ra ↦ ret`, `s0 ↦ arb8` (the caller's
    callee-saved value, arbitrary — the body clobbers it). -/
def bumpVals (ret arb8 : Word) : Reg → Word :=
  fun r => match r with | .x1 => ret | .x8 => arb8 | _ => 0

/-- Post-body values: `ra` untouched, `s0 ↦ ptr` (the body's pointer copy). -/
def bumpVals' (ret ptr : Word) : Reg → Word :=
  fun r => match r with | .x1 => ret | .x8 => ptr | _ => 0

/-- **The callee's calling contract**: entered at `0x2000` with any aligned
    return address in `ra`, any `sp`, and TWO owned free-stack dwords below
    `sp` (its frame space), it returns to `ra` with `sp`/`ra`/`s0` intact,
    the free stack released (owned again), and `[a0]` incremented.  Derived
    from `abiFrame_spec`; the exact `hcallee` shape `abiFrameCall_spec`
    consumes. -/
theorem bumpCall_spec (spVal ret ptr arb8 arb11 v : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 11 (0x2000 : Word) ret callDemoCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) ** stackFree spVal 2
        ** ((.x8 ↦ᵣ arb8) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ arb11) ** (ptr ↦ₘ v)))
      (((.x1 : Reg) ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) ** stackFree spVal 2
        ** ((.x8 ↦ᵣ arb8) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (v + 1))
          ** (ptr ↦ₘ (v + 1)))) := by
  -- The body core: mv ; ld ; addi ; sd over the callee's slice.
  have hcore : cpsTripleWithin 4 (0x200C : Word) (0x201C : Word) callDemoCr
      ((.x8 ↦ᵣ arb8) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ arb11) ** (ptr ↦ₘ v))
      ((.x8 ↦ᵣ ptr) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (v + 1)) ** (ptr ↦ₘ (v + 1))) := by
    refine cpsTripleWithin_extend_code
      (fun a i h => bumpSub a i
        (CodeReq.ofProg_mono_sub (0x2000 : Word) (0x200C : Word) bumpProgList
          bumpBody 3 (by decide) (by rfl) (by decide) (by decide) a i h)) ?_
    show cpsTripleWithin 4 (0x200C : Word) (0x201C : Word)
      (CodeReq.ofProg (0x200C : Word) bumpBody) _ _
    simp only [bumpBody]
    simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
    have hmv := mv_spec_gen_within .x8 .x10 ptr arb8 (0x200C : Word) (by decide)
    have hld := ld_spec_gen_within .x11 .x8 ptr arb11 v (0 : BitVec 12)
      (0x2010 : Word) (by decide)
    rw [add_sext0] at hld
    have haddi := addi_spec_gen_same_within .x11 v (1 : BitVec 12) (0x2014 : Word)
      (by decide)
    rw [show v + signExtend12 (1 : BitVec 12) = v + 1 from by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]] at haddi
    have hsd := sd_spec_gen_within .x8 .x11 ptr (v + 1) v (0 : BitVec 12)
      (0x2018 : Word)
    rw [add_sext0] at hsd
    runBlock hmv hld haddi hsd
  -- The abiFrame instance.
  have h := abiFrame_spec (base := 0x2000) (sp0 := spVal) (ret := ret)
    (negImm := -16) (posImm := 16)
    (frame := bumpFrame) (raOfs := 0) (sregs := [(.x8, 8)])
    (vals := bumpVals ret arb8) (vals' := bumpVals' ret ptr)
    (body := bumpBody) (bodySteps := 4)
    (callerPre := (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ arb11) ** (ptr ↦ₘ v))
    (callerPost := (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (v + 1)) ** (ptr ↦ₘ (v + 1)))
    (cr := callDemoCr)
    (hframe := rfl)
    (hne := by decide)
    (hbound := by decide)
    (hprogBound := by decide)
    (hret := rfl)
    (halign := halign)
    (hframeRestore := frameRestore16 spVal)
    (hcpF := by pcFree)
    (hcpF' := by pcFree)
    (hsub := fun a i h => bumpSub a i h)
    (hbody := by
      have hentry : (0x2000 : Word) + BitVec.ofNat 64 (4 * (1 + bumpFrame.length))
          = (0x200C : Word) := by decide
      have hexit : (0x2000 : Word)
            + BitVec.ofNat 64 (4 * (1 + bumpFrame.length + bumpBody.length))
          = (0x201C : Word) := by decide
      rw [hentry, hexit]
      simp only [bumpFrame, regsAt, frameSlotsSaved, bumpVals, bumpVals',
        List.foldr_cons, List.foldr_nil, sepConj_emp_right']
      have hframed := cpsTripleWithin_frameR
        ((.x2 ↦ᵣ (spVal + signExtend12 (-16 : BitVec 12))) ** ((.x1 : Reg) ↦ᵣ ret)
          ** (((spVal + signExtend12 (-16 : BitVec 12))
                + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
          ** (((spVal + signExtend12 (-16 : BitVec 12))
                + signExtend12 (8 : BitVec 12)) ↦ₘ arb8))
        (by pcFree) hcore
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) hframed)
  -- Reshape: `frameSlotsOwn`/`frameSlotsSaved` ↔ the free-stack region.
  rw [show (11 : Nat) = 1 + bumpFrame.length + 4 + bumpFrame.length + 1 + 1 from rfl]
  refine cpsTripleWithin_weaken (fun h2 hp => ?_) (fun h2 hq => ?_) h
  · -- pre: contract shape ⊢ abiFrame shape (stackFree → frameSlotsOwn).
    simp only [bumpFrame, regsAt, frameSlotsOwn, bumpVals, List.foldr_cons,
      List.foldr_nil, sepConj_emp_right', slot0_addr spVal, slot8_addr spVal]
    simp only [stackFree_succ, stackFree_zero, sepConj_emp_right'] at hp
    xperm_hyp hp
  · -- post: abiFrame shape ⊢ contract shape (frameSlotsSaved → stackFree).
    simp only [bumpFrame, regsAt, frameSlotsSaved, bumpVals, List.foldr_cons,
      List.foldr_nil, sepConj_emp_right'] at hq
    -- pull the two saved-value cells to the front, release them to ownership
    have hq1 : ((((spVal + signExtend12 (-16 : BitVec 12))
            + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
          ** (((spVal + signExtend12 (-16 : BitVec 12))
            + signExtend12 (8 : BitVec 12)) ↦ₘ arb8)
          ** (.x2 ↦ᵣ spVal) ** ((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ arb8)
          ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (v + 1)) ** (ptr ↦ₘ (v + 1))) h2 := by
      xperm_hyp hq
    rw [slot0_addr spVal, slot8_addr spVal] at hq1
    have hq2 := sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn (fun _ hh => hh)) h2 hq1
    simp only [stackFree_succ, stackFree_zero, sepConj_emp_right']
    xperm_hyp hq2

-- ============================================================================
-- The caller: two composed calls inside its own frame.
-- ============================================================================

/-- Caller entry values: just `ra ↦ ret`. -/
def twiceVals (ret : Word) : Reg → Word :=
  fun r => match r with | .x1 => ret | _ => 0

/-- Post-body values: `ra` holds the SECOND call's link address — the body
    genuinely clobbered it twice; the epilogue restores from the slot. -/
def twiceVals' : Reg → Word :=
  fun r => match r with | .x1 => (0x1010 : Word) | _ => 0

/-- **The whole-caller ABI contract.**  Running `twice` from `0x1000` with an
    aligned return address, a stack pointer `sp0`, its own 1-slot frame
    space, and TWO further free-stack dwords below its frame (the callee's
    space), returns to `ret` with:

    * `sp` and `ra` restored to ENTRY values — `ra` was genuinely clobbered
      by both `jal`s (`vals' .x1 = 0x1010`, the second link); restoration is
      derived from the caller's saved-`ra` slot, which both callee runs
      provably could not touch (it is framed out of their footprint);
    * the dword at `[a0]` incremented twice (`v + 1 + 1`) — the composed
      callee effects;
    * `s0` still `arb8` (the callee clobbered and restored it, twice), and
      the borrowed free stack owned again. -/
theorem twiceFrame_spec (sp0 ret ptr arb8 arb11 v : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 29 (0x1000 : Word) ret callDemoCr
      ((.x2 ↦ᵣ sp0) ** regsAt twiceFrame (twiceVals ret)
        ** frameSlotsOwn twiceFrame (sp0 + signExtend12 (-8 : BitVec 12))
        ** (stackFree (sp0 + signExtend12 (-8 : BitVec 12)) 2
          ** (.x8 ↦ᵣ arb8) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ arb11) ** (ptr ↦ₘ v)))
      ((.x2 ↦ᵣ sp0) ** regsAt twiceFrame (twiceVals ret)
        ** frameSlotsSaved twiceFrame (sp0 + signExtend12 (-8 : BitVec 12))
            (twiceVals ret)
        ** (stackFree (sp0 + signExtend12 (-8 : BitVec 12)) 2
          ** (.x8 ↦ᵣ arb8) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (v + 1 + 1))
          ** (ptr ↦ₘ (v + 1 + 1)))) := by
  set newSp := sp0 + signExtend12 (-8 : BitVec 12) with hNS
  -- ---- the two composed calls (the abiFrame body) ----
  -- call 1: jal at 0x1008 → bump, back to 0x100C.
  have hb1 := bumpCall_spec newSp ((0x1008 : Word) + 4) ptr arb8 arb11 v
    (by decide)
  have hcall1 := abiFrameCall_spec (cr := callDemoCr)
    (A := 0x1008) (calleeEntry := 0x2000) (vOld := ret) (spVal := newSp)
    (offset := (0xFF8 : BitVec 21)) (m := 2) (n := 11)
    (calleePre := (.x8 ↦ᵣ arb8) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ arb11) ** (ptr ↦ₘ v))
    (calleePost := (.x8 ↦ᵣ arb8) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (v + 1))
      ** (ptr ↦ₘ (v + 1)))
    (F := ((newSp + signExtend12 (0 : BitVec 12)) ↦ₘ ret))
    (by decide)
    (twiceAt 2 (0x1008 : Word) (.JAL .x1 (0xFF8 : BitVec 21)) (by decide) (by decide)
      (by decide) (by rfl))
    (by pcFree) (by pcFree)
    hb1
  -- call 2: jal at 0x100C → bump, back to 0x1010.
  have hb2 := bumpCall_spec newSp ((0x100C : Word) + 4) ptr arb8 (v + 1) (v + 1)
    (by decide)
  have hcall2 := abiFrameCall_spec (cr := callDemoCr)
    (A := 0x100C) (calleeEntry := 0x2000) (vOld := (0x1008 : Word) + 4)
    (spVal := newSp) (offset := (0xFF4 : BitVec 21)) (m := 2) (n := 11)
    (calleePre := (.x8 ↦ᵣ arb8) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (v + 1))
      ** (ptr ↦ₘ (v + 1)))
    (calleePost := (.x8 ↦ᵣ arb8) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (v + 1 + 1))
      ** (ptr ↦ₘ (v + 1 + 1)))
    (F := ((newSp + signExtend12 (0 : BitVec 12)) ↦ₘ ret))
    (by decide)
    (twiceAt 3 (0x100C : Word) (.JAL .x1 (0xFF4 : BitVec 21)) (by decide) (by decide)
      (by decide) (by rfl))
    (by pcFree) (by pcFree)
    hb2
  -- chain the two calls
  have hchain := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hcall1 hcall2
  rw [show (0x100C : Word) + 4 = (0x1010 : Word) from by decide] at hchain
  -- ---- the abiFrame wrapper ----
  have h := abiFrame_spec (base := 0x1000) (sp0 := sp0) (ret := ret)
    (negImm := -8) (posImm := 8)
    (frame := twiceFrame) (raOfs := 0) (sregs := [])
    (vals := twiceVals ret) (vals' := twiceVals')
    (body := twiceBody) (bodySteps := (1 + 11) + (1 + 11))
    (callerPre := stackFree newSp 2 ** (.x8 ↦ᵣ arb8) ** (.x10 ↦ᵣ ptr)
      ** (.x11 ↦ᵣ arb11) ** (ptr ↦ₘ v))
    (callerPost := stackFree newSp 2 ** (.x8 ↦ᵣ arb8) ** (.x10 ↦ᵣ ptr)
      ** (.x11 ↦ᵣ (v + 1 + 1)) ** (ptr ↦ₘ (v + 1 + 1)))
    (cr := callDemoCr)
    (hframe := rfl)
    (hne := by decide)
    (hbound := by decide)
    (hprogBound := by decide)
    (hret := rfl)
    (halign := halign)
    (hframeRestore := frameRestore8 sp0)
    (hcpF := pcFree_sepConj (pcFree_stackFree _ _) (by pcFree))
    (hcpF' := pcFree_sepConj (pcFree_stackFree _ _) (by pcFree))
    (hsub := fun a i h => twiceSub a i h)
    (hbody := by
      have hentry : (0x1000 : Word) + BitVec.ofNat 64 (4 * (1 + twiceFrame.length))
          = (0x1008 : Word) := by decide
      have hexit : (0x1000 : Word)
            + BitVec.ofNat 64 (4 * (1 + twiceFrame.length + twiceBody.length))
          = (0x1010 : Word) := by decide
      rw [hentry, hexit]
      simp only [twiceFrame, regsAt, frameSlotsSaved, twiceVals, twiceVals',
        List.foldr_cons, List.foldr_nil, sepConj_emp_right']
      refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hchain
      · rw [← hNS] at hp
        xperm_hyp hp
      · rw [← hNS]
        xperm_hyp hq)
  rw [show (29 : Nat)
      = 1 + twiceFrame.length + ((1 + 11) + (1 + 11)) + twiceFrame.length + 1 + 1
    from rfl]
  exact h

#print axioms twiceFrame_spec
#print axioms bumpCall_spec

end AbiFrameCallDemo
end SAsm
end EvmAsm.Rv64
