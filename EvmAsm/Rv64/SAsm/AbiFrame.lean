/-
  EvmAsm.Rv64.SAsm.AbiFrame

  ABI stack-frame support for SAsm (bead evm-asm-4ch8f.76, extending .3).

  Bead .3 modelled frames as *static* stack-arena windows and deliberately
  deferred the guest's *dynamic* C-ABI leaf frames — the `addi sp, sp, -N`
  prologue that saves `ra`/callee-saved `s`-registers, uses them as locals,
  restores them, and `addi sp, sp, +N` before `ret`.  The SAsm block engine
  (`Sym.lean`) cannot express these: `sp` (x2) and the `s`-registers
  (x8/x9/x18–x27) are outside `Reg.isExposed`, and the stack frame is memory
  below `sp` that no `Region`/`RwRegion` owns.  See `FrameConv.lean` for the
  register-preservation conventions that story replaced.

  This file supplies the missing capability as a **machine-level frame
  construct**, built directly on `cpsTripleWithin` (the same layer the whole
  codebase trusts) rather than as a new `Stmt` node.  This keeps the existing
  caller-only static-`rw` soundness path (`Stmt.sound`/`soundR`, `blockOk`)
  completely untouched (the "additive" invariant) while modelling exactly the
  three pieces a real frame needs:

  1. **A frame-region assertion** (`frameSlotsOwn`): the allocated slots below
     `sp` as *genuinely owned* dword cells (`memOwn`), carved from the caller's
     stack space, disjoint (by `**`) from every register atom, the caller's
     `rw`/`ro` regions, and the ambient — no arbitrary stack read/write.
  2. **Proven callee-saved preservation**: the prologue stores the *entry*
     value of each saved register into its slot; the body runs with those
     slots *framed* (in the `cpsTripleWithin` frame `R`, hence untouched by the
     body's own scratch use of the `s`-registers); the epilogue reads the entry
     value straight back.  Preservation is therefore *derived* from the frame
     rule, never assumed.
  3. **Frame-scoped `s`-register exposure**: inside the frame body the saved
     registers are ordinary owned `↦ᵣ` atoms — usable and clobberable as
     locals — while *outside* a frame they remain unowned by the SAsm state
     (they are not in `Reg.isExposed`, exactly as before).

  ## Generality (bead evm-asm-4ch8f.76 main deliverable)

  The construct is parameterized over a **saved-register set** given as an
  explicit `List (Reg × BitVec 12)` of `(register, byte-offset-from-new-sp)`
  slot descriptors (`ra` plus up to seven callee-saved `s`-registers).  The
  store/load sequences that fill and drain the frame are proven **by induction
  over that list** (`storeSeq_spec`/`loadSeq_spec`), and the end-to-end
  contract `abiFrame_spec` composes prologue · body · epilogue · `ret` for a
  *free* entry `sp0`, a *free* frame descriptor, and an arbitrary single-exit
  body supplied as a `cpsTripleWithin` hypothesis.  `AbiFrameDemo.lean` derives
  the original 3-register demo (`demoFrame_spec`) as a one-shot instantiation.

  Byte-transparency: `abiFrameProg` is literally
  `prologue ++ body ++ epilogue ++ [ret]`, reproduced by `#guard` against a
  hand-written program (`AbiFrameDemo.lean`).
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.Program

namespace EvmAsm.Rv64
namespace SAsm

open EvmAsm.Rv64.Tactics

-- ============================================================================
-- The emitted prologue / epilogue (byte-transparent), parameterized by the
-- saved-register set.
-- ============================================================================

/-- A saved-register frame descriptor: a list of `(register, byte-offset)`
    pairs.  The offset is measured from the *new* stack pointer (`sp` after the
    prologue `addi`), so slot `(r, ofs)` lives at `newSp + signExtend12 ofs`. -/
abbrev FrameDesc := List (Reg × BitVec 12)

/-- The store sequence saving each frame register into its slot:
    `sd r, ofs(sp)` for each `(r, ofs)`. -/
def storeProg (frame : FrameDesc) : List Instr :=
  frame.map (fun p => .SD .x2 p.1 p.2)

/-- The load sequence restoring each frame register from its slot:
    `ld r, ofs(sp)` for each `(r, ofs)`. -/
def loadProg (frame : FrameDesc) : List Instr :=
  frame.map (fun p => .LD p.1 .x2 p.2)

@[simp] theorem storeProg_nil : storeProg [] = [] := rfl
@[simp] theorem storeProg_cons (p : Reg × BitVec 12) (rest : FrameDesc) :
    storeProg (p :: rest) = .SD .x2 p.1 p.2 :: storeProg rest := rfl
@[simp] theorem loadProg_nil : loadProg [] = [] := rfl
@[simp] theorem loadProg_cons (p : Reg × BitVec 12) (rest : FrameDesc) :
    loadProg (p :: rest) = .LD p.1 .x2 p.2 :: loadProg rest := rfl

@[simp] theorem storeProg_length (frame : FrameDesc) :
    (storeProg frame).length = frame.length := by
  simp [storeProg]
@[simp] theorem loadProg_length (frame : FrameDesc) :
    (loadProg frame).length = frame.length := by
  simp [loadProg]

/-- Standard leaf-frame prologue: allocate `N` bytes (`negImm` is the negative
    immediate), then save each frame register into its slot. -/
def framePrologue (negImm : BitVec 12) (frame : FrameDesc) : List Instr :=
  .ADDI .x2 .x2 negImm :: storeProg frame

/-- The matching epilogue: restore each frame register, then deallocate the
    frame (`posImm` is the positive immediate). -/
def frameEpilogue (posImm : BitVec 12) (frame : FrameDesc) : List Instr :=
  loadProg frame ++ [.ADDI .x2 .x2 posImm]

/-- A full leaf ABI-frame routine: prologue, body, epilogue, `ret`.  This is
    the byte-transparent flatten of the frame construct. -/
def abiFrameProg (negImm posImm : BitVec 12) (frame : FrameDesc)
    (body : List Instr) : List Instr :=
  framePrologue negImm frame ++ body ++ frameEpilogue posImm frame ++ [.JALR .x0 .x1 0]

/-- Byte-transparency: the frame flatten is exactly prologue ++ body ++
    epilogue ++ ret, by definition. -/
theorem abiFrameProg_eq (negImm posImm : BitVec 12) (frame : FrameDesc)
    (body : List Instr) :
    abiFrameProg negImm posImm frame body
      = framePrologue negImm frame ++ body ++ frameEpilogue posImm frame
          ++ [.JALR .x0 .x1 0] :=
  rfl

-- ============================================================================
-- The frame-region assertions (the new memory-model piece), as folds over the
-- frame descriptor.
-- ============================================================================

/-- The saved registers as owned `↦ᵣ` atoms holding their `vals` values. -/
def regsAt (frame : FrameDesc) (vals : Reg → Word) : Assertion :=
  frame.foldr (fun p acc => (p.1 ↦ᵣ vals p.1) ** acc) empAssertion

/-- The frame slots as *genuinely owned* dword cells with arbitrary contents
    (`memOwn`), each at `newSp + signExtend12 ofs`.  Being ordinary owned-memory
    atoms they are disjoint (through `**`) from the register atoms, the caller's
    regions, and the ambient — no arbitrary stack read/write. -/
def frameSlotsOwn (frame : FrameDesc) (newSp : Word) : Assertion :=
  frame.foldr (fun p acc => memOwn (newSp + signExtend12 p.2) ** acc) empAssertion

/-- The same slots after the prologue has saved each entry value: slot
    `(r, ofs)` holds `vals r`. -/
def frameSlotsSaved (frame : FrameDesc) (newSp : Word) (vals : Reg → Word) :
    Assertion :=
  frame.foldr (fun p acc => ((newSp + signExtend12 p.2) ↦ₘ vals p.1) ** acc)
    empAssertion

@[simp] theorem regsAt_nil (vals : Reg → Word) : regsAt [] vals = empAssertion := rfl
@[simp] theorem regsAt_cons (p : Reg × BitVec 12) (rest : FrameDesc)
    (vals : Reg → Word) :
    regsAt (p :: rest) vals = ((p.1 ↦ᵣ vals p.1) ** regsAt rest vals) := rfl
@[simp] theorem frameSlotsOwn_nil (newSp : Word) :
    frameSlotsOwn [] newSp = empAssertion := rfl
@[simp] theorem frameSlotsOwn_cons (p : Reg × BitVec 12) (rest : FrameDesc)
    (newSp : Word) :
    frameSlotsOwn (p :: rest) newSp
      = (memOwn (newSp + signExtend12 p.2) ** frameSlotsOwn rest newSp) := rfl
@[simp] theorem frameSlotsSaved_nil (newSp : Word) (vals : Reg → Word) :
    frameSlotsSaved [] newSp vals = empAssertion := rfl
@[simp] theorem frameSlotsSaved_cons (p : Reg × BitVec 12) (rest : FrameDesc)
    (newSp : Word) (vals : Reg → Word) :
    frameSlotsSaved (p :: rest) newSp vals
      = (((newSp + signExtend12 p.2) ↦ₘ vals p.1) ** frameSlotsSaved rest newSp vals) :=
  rfl

theorem pcFree_regsAt (frame : FrameDesc) (vals : Reg → Word) :
    (regsAt frame vals).pcFree := by
  induction frame with
  | nil => intro h hp; rw [hp]; rfl
  | cons p rest ih => exact pcFree_sepConj pcFree_regIs ih

theorem pcFree_frameSlotsOwn (frame : FrameDesc) (newSp : Word) :
    (frameSlotsOwn frame newSp).pcFree := by
  induction frame with
  | nil => intro h hp; rw [hp]; rfl
  | cons p rest ih => exact pcFree_sepConj pcFree_memOwn ih

theorem pcFree_frameSlotsSaved (frame : FrameDesc) (newSp : Word)
    (vals : Reg → Word) : (frameSlotsSaved frame newSp vals).pcFree := by
  induction frame with
  | nil => intro h hp; rw [hp]; rfl
  | cons p rest ih => exact pcFree_sepConj pcFree_memIs ih

-- ============================================================================
-- Address arithmetic helper
-- ============================================================================

/-- Fold two `ofNat` offsets from the same base into one (pure wrap-around
    BitVec arithmetic — no overflow side condition). -/
private theorem add_ofNat_add_ofNat (b : Word) (i j : Nat) :
    (b + BitVec.ofNat 64 i) + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem word_four_eq : (4 : Word) = BitVec.ofNat 64 4 := rfl

-- ============================================================================
-- The store sequence: fill the frame slots with the entry register values.
-- ============================================================================

/-- Running the prologue store sequence (`sd r, ofs(sp)` for each frame slot)
    from `startAddr`, with `sp = newSp`, the saved registers holding `vals`, and
    the slots *owned*, leaves the slots holding the saved values.  Proven by
    induction over the frame descriptor. -/
theorem storeSeq_spec (frame : FrameDesc) (newSp : Word) (vals : Reg → Word)
    (startAddr : Word) (hbound : 4 * frame.length < 2 ^ 64) :
    cpsTripleWithin frame.length startAddr
        (startAddr + BitVec.ofNat 64 (4 * frame.length))
      (CodeReq.ofProg startAddr (storeProg frame))
      ((.x2 ↦ᵣ newSp) ** regsAt frame vals ** frameSlotsOwn frame newSp)
      ((.x2 ↦ᵣ newSp) ** regsAt frame vals ** frameSlotsSaved frame newSp vals) := by
  induction frame generalizing startAddr with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, storeProg_nil, CodeReq.ofProg_nil,
      regsAt_nil, frameSlotsOwn_nil, frameSlotsSaved_nil]
    rw [show startAddr + BitVec.ofNat 64 0 = startAddr from by
      apply BitVec.eq_of_toNat_eq; simp]
    exact cpsTripleWithin_refl (fun _ hp => hp)
  | cons p rest ih =>
    obtain ⟨r, ofs⟩ := p
    have hb' : 4 * rest.length < 2 ^ 64 := by
      have h := hbound; rw [List.length_cons] at h; omega
    -- Head store: sd r, ofs(sp) at startAddr.
    have head := sd_spec_gen_own_within .x2 r newSp (vals r) ofs startAddr
    have head_framed := cpsTripleWithin_frameR
      (regsAt rest vals ** frameSlotsOwn rest newSp)
      (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsOwn _ _)) head
    -- Tail: the rest of the stores.
    have tail := ih (startAddr + 4) hb'
    have tail_framed := cpsTripleWithin_frameL
      ((r ↦ᵣ vals r) ** ((newSp + signExtend12 ofs) ↦ₘ vals r))
      (pcFree_sepConj pcFree_regIs pcFree_memIs) tail
    -- Disjointness of the head singleton from the tail program.
    have hnone : CodeReq.ofProg (startAddr + 4) (storeProg rest) startAddr = none := by
      apply CodeReq.ofProg_none_range
      intro k hk heq
      rw [storeProg_length] at hk
      have hb2 : (4 : Nat) * (k + 1) < 2 ^ 64 := by omega
      have hcontra := congrArg BitVec.toNat heq
      simp only [word_four_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hcontra
      omega
    have hd : (CodeReq.singleton startAddr (.SD .x2 r ofs)).Disjoint
        (CodeReq.ofProg (startAddr + 4) (storeProg rest)) :=
      CodeReq.Disjoint.singleton_ofProg hnone
    -- Compose head ; tail.
    have composed := cpsTripleWithin_seq_with_perm hd
      (Q1 := ((.x2 ↦ᵣ newSp) ** (r ↦ᵣ vals r)
                ** ((newSp + signExtend12 ofs) ↦ₘ vals r))
              ** (regsAt rest vals ** frameSlotsOwn rest newSp))
      (Q2 := ((r ↦ᵣ vals r) ** ((newSp + signExtend12 ofs) ↦ₘ vals r))
              ** ((.x2 ↦ᵣ newSp) ** regsAt rest vals ** frameSlotsOwn rest newSp))
      (by xsimp) head_framed tail_framed
    -- Massage cr, step count, exit address, and pre/post shapes.
    rw [← CodeReq.ofProg_cons] at composed
    have hnat : 4 + 4 * rest.length = 4 * (rest.length + 1) := by omega
    have hexit : (startAddr + 4) + BitVec.ofNat 64 (4 * rest.length)
        = startAddr + BitVec.ofNat 64 (4 * (rest.length + 1)) := by
      rw [word_four_eq, add_ofNat_add_ofNat, hnat]
    rw [hexit] at composed
    have hlen : (1 : Nat) + rest.length = (rest.length + 1) := by omega
    rw [hlen] at composed
    simp only [storeProg_cons, regsAt_cons, frameSlotsOwn_cons, frameSlotsSaved_cons,
      List.length_cons]
    exact cpsTripleWithin_weaken (by xsimp) (by xsimp) composed

-- ============================================================================
-- The load sequence: restore each saved register from its (untouched) slot.
-- ============================================================================

/-- Running the epilogue load sequence (`ld r, ofs(sp)` for each frame slot)
    from `startAddr`, with `sp = newSp` and the slots still holding the saved
    values `vals`, restores each saved register to its entry value regardless of
    the (arbitrary, body-clobbered) input values `vals'`.  The slots are read
    only, so they are unchanged.  Proven by induction over the frame
    descriptor. -/
theorem loadSeq_spec (frame : FrameDesc) (newSp : Word) (vals vals' : Reg → Word)
    (startAddr : Word) (hbound : 4 * frame.length < 2 ^ 64)
    (hne : ∀ p ∈ frame, p.1 ≠ .x0) :
    cpsTripleWithin frame.length startAddr
        (startAddr + BitVec.ofNat 64 (4 * frame.length))
      (CodeReq.ofProg startAddr (loadProg frame))
      ((.x2 ↦ᵣ newSp) ** regsAt frame vals' ** frameSlotsSaved frame newSp vals)
      ((.x2 ↦ᵣ newSp) ** regsAt frame vals ** frameSlotsSaved frame newSp vals) := by
  induction frame generalizing startAddr with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, loadProg_nil, CodeReq.ofProg_nil,
      regsAt_nil, frameSlotsSaved_nil]
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
    -- Head load: ld r, ofs(sp) at startAddr.
    have head := ld_spec_gen_within r .x2 newSp (vals' r) (vals r) ofs startAddr hne_r
    have head_framed := cpsTripleWithin_frameR
      (regsAt rest vals' ** frameSlotsSaved rest newSp vals)
      (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsSaved _ _ _)) head
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
      simp only [word_four_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hcontra
      omega
    have hd : (CodeReq.singleton startAddr (.LD r .x2 ofs)).Disjoint
        (CodeReq.ofProg (startAddr + 4) (loadProg rest)) :=
      CodeReq.Disjoint.singleton_ofProg hnone
    have composed := cpsTripleWithin_seq_with_perm hd
      (Q1 := ((.x2 ↦ᵣ newSp) ** (r ↦ᵣ vals r)
                ** ((newSp + signExtend12 ofs) ↦ₘ vals r))
              ** (regsAt rest vals' ** frameSlotsSaved rest newSp vals))
      (Q2 := ((r ↦ᵣ vals r) ** ((newSp + signExtend12 ofs) ↦ₘ vals r))
              ** ((.x2 ↦ᵣ newSp) ** regsAt rest vals' ** frameSlotsSaved rest newSp vals))
      (by xsimp) head_framed tail_framed
    rw [← CodeReq.ofProg_cons] at composed
    have hnat : 4 + 4 * rest.length = 4 * (rest.length + 1) := by omega
    have hexit : (startAddr + 4) + BitVec.ofNat 64 (4 * rest.length)
        = startAddr + BitVec.ofNat 64 (4 * (rest.length + 1)) := by
      rw [word_four_eq, add_ofNat_add_ofNat, hnat]
    rw [hexit] at composed
    have hlen : (1 : Nat) + rest.length = (rest.length + 1) := by omega
    rw [hlen] at composed
    simp only [loadProg_cons, regsAt_cons, frameSlotsSaved_cons, List.length_cons]
    exact cpsTripleWithin_weaken (by xsimp) (by xsimp) composed

-- ============================================================================
-- Code-membership helper: a contiguous slice of the flattened routine sits in
-- any CodeReq that contains the whole routine.
-- ============================================================================

/-- If `prog = pre ++ mid ++ suf` and `cr` contains `ofProg base prog`, then
    `cr` contains the middle slice `ofProg (base + 4*pre.length) mid`. -/
private theorem abiFrame_piece_mem {base : Word} {pre mid suf prog : List Instr}
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

-- ============================================================================
-- The end-to-end ABI-frame contract (bead evm-asm-4ch8f.76 main deliverable).
-- ============================================================================

/-- **The reusable, parameterized ABI-frame soundness lemma.**

    Given an arbitrary single-exit `body` (as a `cpsTripleWithin` hypothesis)
    that runs with the callee-saved registers exposed as owned `↦ᵣ` atoms and
    the save slots framed (`frameSlotsSaved`, hence unchanged), the framed
    routine `prologue · body · epilogue · ret`:

    * restores `sp` (`x2`) and every saved register (`ra` = `x1` plus the
      `s`-registers in `sregs`) to its **entry** value `vals`;
    * releases the frame with the slots holding the saved values
      (`frameSlotsSaved`);
    * preserves the body's caller effect (`callerPre ↦ callerPost`).

    `sp0`, the frame descriptor (`raOfs`, `sregs`), the frame size (`negImm` /
    `posImm`), and the body are all FREE.  Callee-saved preservation is
    *derived* from the frame rule (`storeSeq_spec`/`loadSeq_spec` + the
    `cpsTripleWithin` frame `R` around the body), never assumed; the frame slots
    stay genuinely owned throughout (no arbitrary-stack-read hole). -/
theorem abiFrame_spec
    (base sp0 ret : Word) (negImm posImm : BitVec 12)
    (frame : FrameDesc) (raOfs : BitVec 12) (sregs : FrameDesc)
    (vals vals' : Reg → Word)
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
        ((.x2 ↦ᵣ (sp0 + signExtend12 negImm)) ** regsAt frame vals'
          ** frameSlotsSaved frame (sp0 + signExtend12 negImm) vals ** callerPost)) :
    cpsTripleWithin (1 + frame.length + bodySteps + frame.length + 1 + 1) base ret cr
      ((.x2 ↦ᵣ sp0) ** regsAt frame vals
        ** frameSlotsOwn frame (sp0 + signExtend12 negImm) ** callerPre)
      ((.x2 ↦ᵣ sp0) ** regsAt frame vals
        ** frameSlotsSaved frame (sp0 + signExtend12 negImm) vals ** callerPost) := by
  set newSp := sp0 + signExtend12 negImm with hNS
  -- pcFree facts for the caller/frame assertions.
  have hpcRegs := pcFree_regsAt frame vals
  have hpcRegs' := pcFree_regsAt frame vals'
  have hpcOwn := pcFree_frameSlotsOwn frame newSp
  have hpcSaved := pcFree_frameSlotsSaved frame newSp vals
  -- Canonical instruction-offset addresses.
  set A1 := base + BitVec.ofNat 64 (4 * 1) with hA1
  set A2 := base + BitVec.ofNat 64 (4 * (1 + frame.length)) with hA2
  set A3 := base + BitVec.ofNat 64 (4 * (1 + frame.length + body.length)) with hA3
  set A4 := base + BitVec.ofNat 64 (4 * (1 + frame.length + body.length + frame.length)) with hA4
  set A5 := base + BitVec.ofNat 64 (4 * (1 + frame.length + body.length + frame.length + 1)) with hA5
  -- Address bridges.
  have brAlloc : base + 4 = A1 := by
    rw [hA1]; apply BitVec.eq_of_toNat_eq
    simp only [word_four_eq, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mul_one]
  have brStore : A1 + BitVec.ofNat 64 (4 * frame.length) = A2 := by
    rw [hA1, hA2, add_ofNat_add_ofNat,
      show 4 * 1 + 4 * frame.length = 4 * (1 + frame.length) from by omega]
  have brLoad : A3 + BitVec.ofNat 64 (4 * frame.length) = A4 := by
    rw [hA3, hA4, add_ofNat_add_ofNat,
      show 4 * (1 + frame.length + body.length) + 4 * frame.length
        = 4 * (1 + frame.length + body.length + frame.length) from by omega]
  have brDealloc : A4 + 4 = A5 := by
    rw [hA4, hA5, word_four_eq, add_ofNat_add_ofNat,
      show 4 * (1 + frame.length + body.length + frame.length) + 4
        = 4 * (1 + frame.length + body.length + frame.length + 1) from by omega]
  -- Program decompositions for the code-membership subranges.
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
  -- Code memberships.
  have hlookA : CodeReq.ofProg base (abiFrameProg negImm posImm frame body) base
      = some (.ADDI .x2 .x2 negImm) := by
    rw [show abiFrameProg negImm posImm frame body
          = .ADDI .x2 .x2 negImm
              :: (storeProg frame ++ body ++ frameEpilogue posImm frame ++ [.JALR .x0 .x1 0])
        from by simp [abiFrameProg, framePrologue, List.append_assoc]]
    rw [CodeReq.ofProg_cons]
    simp [CodeReq.union, CodeReq.singleton]
  have mAlloc := CodeReq.singleton_mono (hsub base _ hlookA)
  have mStore := abiFrame_piece_mem hprogS hprogBound hsub
  simp only [List.length_singleton] at mStore
  have mLoad := abiFrame_piece_mem hprogL hprogBound hsub
  simp only [List.length_append, List.length_singleton, storeProg_length] at mLoad
  have mDealloc := abiFrame_piece_mem hprogD hprogBound hsub
  simp only [List.length_append, List.length_singleton, storeProg_length,
    loadProg_length] at mDealloc
  rw [CodeReq.ofProg_singleton] at mDealloc
  have mRet := abiFrame_piece_mem hprogR hprogBound hsub
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
  -- ===================== segment 3: body (hypothesis) ==================
  -- hbody is already at [A2, A3] under cr.
  -- ===================== segment 4: restore registers ==================
  have load0 := loadSeq_spec frame newSp vals vals' A3 hbound hne
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
  -- Expose `.x1 ↦ ret` in the segment-5 post before the ret step.
  rw [hReg] at h12345
  have hfull := cpsTripleWithin_seq_perm_same_cr (by xsimp) h12345 seg6
  -- Reconcile the final pre/post shapes (unfold `regsAt frame` via `hReg`).
  refine cpsTripleWithin_weaken ?_ ?_ hfull
  · rw [hReg]; xsimp
  · rw [hReg]; xsimp

end SAsm
end EvmAsm.Rv64
