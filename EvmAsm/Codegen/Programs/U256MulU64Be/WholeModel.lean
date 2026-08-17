/-
  EvmAsm.Codegen.Programs.U256MulU64Be.Whole

  Structured whole-routine shape for `u256_mul_u64_be`.  The small files in
  this directory establish the frame, zero-fill and pure ripple facts; this
  file is the single byte-identity seam where those pieces meet the linked
  88-instruction program.
-/
import EvmAsm.Codegen.Programs.U256MulU64Be.Common
import EvmAsm.Codegen.Programs.U256MulU64Be.ZeroLoop
import EvmAsm.Codegen.Programs.U256MulU64Be.OuterLoop
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.BeqLimitLoop
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.MemSat

set_option maxRecDepth 8000

namespace EvmAsm.Codegen.U256MulU64Be

open EvmAsm Rv64 Rv64.SAsm Rv64.SAsm.Stmt

/-! ## Pure result model -/

/-- One complete outer-loop iteration, including the zero-byte skip.  The
    accumulator is little-endian and has eight spare bytes for carry/overflow.
    The machine's ripple loop is modelled by `rippleState`; the final MULHU
    byte is the next byte after the ripple window. -/
def mulOuterStep (a : List (BitVec 8)) (b : Word)
    (acc : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  let byte := a.getD (31 - i) 0
  if byte = 0 then acc
  else
    let m := byte.toNat * b.toNat
    let lo := m % 2 ^ 64
    let r := rippleState acc lo i 8
    let j := i + 8
    let hi := m / 2 ^ 64 + mulCarry acc lo i 8 + (r.getD j 0).toNat
    r.set j (BitVec.ofNat 8 hi)

/-- Accumulator after `i` big-endian input bytes have been folded. -/
def mulState (a : List (BitVec 8)) (b : Word) (i : Nat) : List (BitVec 8) :=
  match i with
  | 0 => List.replicate 40 (0 : BitVec 8)
  | k + 1 => mulOuterStep a b (mulState a b k) k

theorem mulState_len (a : List (BitVec 8)) (b : Word) (i : Nat) :
    (mulState a b i).length = 40 := by
  have hstep : ∀ (xs : List (BitVec 8)) (j : Nat),
      (mulOuterStep a b xs j).length = xs.length := by
    intro xs j
    dsimp [mulOuterStep]
    split
    · rfl
    · rw [List.length_set, length_rippleState]
  induction i with
  | zero => simp [mulState]
  | succ i ih => rw [mulState, hstep, ih]

/-! Regression control for the annotation above.  The old unannotated sum was
    coerced through `BitVec 8`; this concrete product has a nonzero high half,
    so the guard below would have caught that model drift even though a small
    or zero-high witness would not. -/

def mulOuterStep_unannotated (a : List (BitVec 8)) (b : Word)
    (acc : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  let byte := a.getD (31 - i) 0
  if byte = 0 then acc
  else
    let m := byte.toNat * b.toNat
    let lo := m % 2 ^ 64
    let r := rippleState acc lo i 8
    let j := i + 8
    let hi := (m / 2 ^ 64 + mulCarry acc lo i 8 + r.getD j 0).toNat
    r.set j (BitVec.ofNat 8 hi)

def highHalfWitnessInput : List (BitVec 8) :=
  List.replicate 31 (0 : BitVec 8) ++ [255]

#guard (mulOuterStep highHalfWitnessInput (BitVec.ofNat 64 (2 ^ 63))
    (List.replicate 40 (0 : BitVec 8)) 0).getD 8 0 = (127 : BitVec 8)
#guard mulOuterStep highHalfWitnessInput (BitVec.ofNat 64 (2 ^ 63))
    (List.replicate 40 (0 : BitVec 8)) 0 ≠
  mulOuterStep_unannotated highHalfWitnessInput (BitVec.ofNat 64 (2 ^ 63))
    (List.replicate 40 (0 : BitVec 8)) 0

/-- The 32-byte big-endian output copied from the low 32 accumulator bytes. -/
def mulOutputBytes (a : List (BitVec 8)) (b : Word) : List (BitVec 8) :=
  (mulState a b 32).take 32 |>.reverse

/-- The returned flag: a nonzero high accumulator byte means 256-bit overflow. -/
def mulOverflow (a : List (BitVec 8)) (b : Word) : Word :=
  if ∀ x ∈ (mulState a b 32).drop 32, x = 0 then 0 else 1

/-! ## Structured machine body -/

def mulRippleBody : Stmt :=
  .block "ripple.body"
    [.LBU .x31 .x28 (0 : BitVec 12),
     .ANDI .x13 .x6 (255 : BitVec 12),
     .ADD .x31 .x31 .x13,
     .ADD .x31 .x31 .x30,
     .ANDI .x13 .x31 (255 : BitVec 12),
     .SB .x28 .x13 (0 : BitVec 12),
     .SRLI .x30 .x31 (8 : BitVec 6),
     .SRLI .x6 .x6 (8 : BitVec 6),
     .ADDI .x28 .x28 (1 : BitVec 12),
     .ADDI .x29 .x29 (-1 : BitVec 12)]

def mulCarryBody : Stmt :=
  .block "carry.body"
    [.LBU .x31 .x28 (0 : BitVec 12),
     .ADD .x31 .x31 .x30,
     .ANDI .x13 .x31 (255 : BitVec 12),
     .SB .x28 .x13 (0 : BitVec 12),
     .SRLI .x30 .x31 (8 : BitVec 6),
     .ADDI .x28 .x28 (1 : BitVec 12)]

def mulNonzeroBody : Stmt :=
  .block "mul.init"
    [.MUL .x6 .x5 .x9,
     .MULHU .x7 .x5 .x9,
     .ADD .x28 .x19 .x20,
     .LI .x29 (8 : Word),
     .LI .x30 (0 : Word)] ;;;
  .«doWhile» "ripple" (.bne .x29 .x0) 8
    (fun _ _ _ _ => True) mulRippleBody ;;;
  .block "mul.high"
    [.LBU .x31 .x28 (0 : BitVec 12),
     .ADD .x31 .x31 .x7,
     .ADD .x31 .x31 .x30,
     .ANDI .x13 .x31 (255 : BitVec 12),
     .SB .x28 .x13 (0 : BitVec 12),
     .SRLI .x30 .x31 (8 : BitVec 6),
     .ADDI .x28 .x28 (1 : BitVec 12)] ;;;
  .«while» "carry" (.bne .x30 .x0) 1
    (fun _ _ _ _ => True) mulCarryBody

def mulOuterBody : Stmt :=
  .block "outer.byte"
    [.LI .x5 (31 : Word),
     .SUB .x5 .x5 .x20,
     .ADD .x5 .x8 .x5,
     .LBU .x5 .x5 (0 : BitVec 12)] ;;;
  .when "outer.nonzero" (.bne .x5 .x0) mulNonzeroBody ;;;
  .block "outer.next" [.ADDI .x20 .x20 (1 : BitVec 12)]

def mulOuterLoop : Stmt :=
  .whileHeader "outer"
    (.block "outer.header" [.LI .x5 (32 : Word)])
    (.bne .x20 .x5) 32
    (fun _ _ _ _ => True)
    mulOuterBody

def mulCopyBody : Stmt :=
  .block "copy.body"
    [.ADDI .x6 .x6 (-1 : BitVec 12),
     .LBU .x28 .x5 (0 : BitVec 12),
     .SB .x6 .x28 (0 : BitVec 12),
     .ADDI .x5 .x5 (1 : BitVec 12),
     .ADDI .x7 .x7 (-1 : BitVec 12)]

def mulOverflowBody : Stmt :=
  .block "overflow.raw"
    [.BEQ .x6 .x0 (32 : BitVec 13),
     .LBU .x28 .x5 (0 : BitVec 12),
     .BEQ .x28 .x0 (12 : BitVec 13),
     .LI .x10 (1 : Word),
     .JAL .x0 (16 : BitVec 21),
     .ADDI .x5 .x5 (1 : BitVec 12),
     .ADDI .x6 .x6 (-1 : BitVec 12),
     .JAL .x0 (-28 : BitVec 21)]

def mulCoreBody : Stmt :=
  .block "zero.init" [.MV .x5 .x19, .LI .x6 (5 : Word)] ;;;
  .«while» "zero" (.bne .x6 .x0) 5
    (fun _ _ _ _ => True)
    (.block "zero.body"
      [.SD .x5 .x0 (0 : BitVec 12),
       .ADDI .x5 .x5 (8 : BitVec 12),
       .ADDI .x6 .x6 (-1 : BitVec 12)]) ;;;
  .block "outer.init" [.LI .x20 (0 : Word)] ;;;
  mulOuterLoop ;;;
  .block "copy.init"
    [.MV .x5 .x19, .ADDI .x6 .x18 (32 : BitVec 12), .LI .x7 (32 : Word)] ;;;
  .«while» "copy" (.bne .x7 .x0) 32
    (fun _ _ _ _ => True) mulCopyBody ;;;
  .block "overflow.init" [.LI .x6 (8 : Word), .LI .x10 (0 : Word)] ;;;
  mulOverflowBody

/-! The first version intentionally pins only the layout seam.  The semantic
    invariants are supplied below as the loop VCs are discharged; keeping this
    equality here makes any instruction-count or branch-shape drift immediate.
-/
def mulCoreProgram : Program := mulCoreBody.flatten (mulBase + 48)

#guard mulCoreBody.size = 68
#guard mulCoreProgram.length = 68
#guard (u256MulU64Be_prog.drop 12).take 68 = mulCoreProgram

/-! ## Inductive outer-loop state

`whileHeader` invariants are checked after the header reload and at the guard,
not at the first instruction of the body.  `beqLimitLoop_spec` exposes the
counter and limit as separate atoms, so `outerLoopInv` deliberately excludes
`x20`/`x5`; `outerHeaderInv` adds them back to name the complete guard state.
The same indexed assertion serves the entry instance (`i = 0`) and every
loop-back instance (`i + 1`).  Immediately before the next header, the
back-edge has `x20 = i + 1` and may leave `x5` clobbered; the next header
reload is what restores `x5 = 32`.  The callee-saved/context registers are
framed through the cycle; only the listed scratch registers are owned by the
cycle body. -/

def outerLoopInv
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) (i : Nat) : Assertion :=
  F ** bytesRegion aPtr aBytes **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
    ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) **
    ((.x12 : Reg) ↦ᵣ outPtr) **
    regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    bytesRegion accBase (mulState aBytes b i) **
    frameSlots spNew vRa v8 v9 v18 v19 v20

def outerHeaderInv
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) (i : Nat) : Assertion :=
  ((.x20 : Reg) ↦ᵣ (BitVec.ofNat 64 i)) **
    ((.x5 : Reg) ↦ᵣ (32 : Word)) **
    outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i

theorem mulOuterGuard_mem :
    ∀ a i,
      CodeReq.singleton (mulBase + 84)
          (.BEQ .x20 .x5 (156 : BitVec 13)) a = some i →
        mulCR a = some i := by
  intro a i h
  exact CodeReq.ofProg_mem_at mulBase (mulBase + 84) mulProg 21
    (.BEQ .x20 .x5 (156 : BitVec 13)) (by decide) (by decide) (by decide)
    (by decide) a i h

theorem mulOuter_exit :
    mulBase + 84 + Rv64.signExtend13 (156 : BitVec 13) = mulBase + 240 := by
  decide

/-! The control skeleton is now expressed by the typed equality-limit loop
combinator.  The remaining `hbody` is intentionally the semantic obligation
for one real multiply cycle; the combinator itself discharges the header,
guard, back-edge, exact `i = 32` exit, and the 32-step induction. -/
theorem outerLoop_control_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (bodyStep : Nat)
    (hbody : ∀ i, i < 32 →
      cpsTripleWithin bodyStep (mulBase + 88) (mulBase + 84) mulCR
        (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i)
        (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr (i + 1))) :
    cpsTripleWithin (32 * (bodyStep + 1) + 1) (mulBase + 84) (mulBase + 240) mulCR
      (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr 0)
      (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr 32) := by
  have hpcFree : ∀ i,
      (outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i).pcFree := by
    intro i
    dsimp [outerLoopInv]
    exact pcFree_sepConj hF (by pcf)
  exact beqCountLoop_spec mulCR (mulBase + 84) (mulBase + 240) .x20 .x5
    (156 : BitVec 13) bodyStep 32
    (outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr)
    (by decide) mulOuter_exit hpcFree mulOuterGuard_mem (by
      intro i hi
      exact hbody i hi)

theorem outer_zero_frame_eq :
    frameSlots (BitVec.ofNat 64 0xa0050000)
        (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) =
      bytesRegion (BitVec.ofNat 64 0xa0050000) (List.replicate 48 0) := by
  funext h
  simp [frameSlots, bytesRegion, bytesRegionAux, packBytes, getByteAt,
    packDword, Rv64.signExtend12, sepConj_emp_right']

/-! The guard invariant is inhabited by an explicit entry resource set.  This
    is deliberately proved before the outer-cycle VC: the cycle proof must not
    be the first evidence that its indexed precondition describes any state. -/
theorem outerHeaderInv_satisfiable :
    ∃ h, outerHeaderInv empAssertion (List.replicate 32 0)
      (BitVec.ofNat 64 0xa0050000) 0 0 0 0 0 0
      (BitVec.ofNat 64 0x40000000) 1
      (BitVec.ofNat 64 0xa0100000) 0 h := by
  let fixedRegs : List (Reg × Word) :=
    [(.x20, 0), (.x5, 32), (.x2, BitVec.ofNat 64 0xa0050000),
     (.x1, 0), (.x8, BitVec.ofNat 64 0x40000000), (.x9, 1),
     (.x18, BitVec.ofNat 64 0xa0100000), (.x19, BitVec.ofNat 64 0xa4386860),
     (.x0, 0), (.x10, BitVec.ofNat 64 0x40000000), (.x11, 1),
     (.x12, BitVec.ofNat 64 0xa0100000)]
  let scratchRegs : List Reg := [.x6, .x7, .x13, .x28, .x29, .x30, .x31]
  let fixedHeap : (Reg × Word) → PartialState :=
    fun p => PartialState.singletonReg p.1 p.2
  let scratchHeap : Reg → PartialState :=
    fun r => PartialState.singletonReg r 0
  have singletonReg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
      (hne : r1 ≠ r2) :
      (PartialState.singletonReg r1 v1).Disjoint
        (PartialState.singletonReg r2 v2) := by
    refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
      Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    intro r
    by_cases h : r = r1
    · subst r
      right
      simp [PartialState.singletonReg, hne]
    · left
      simp [PartialState.singletonReg, h]
  have hFixed :
      (fixedRegs.foldr (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion)
        (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro p hp
      simp [fixedHeap, regIs]
    · exact List.Pairwise.imp (fun {p q} hpq => singletonReg_disjoint hpq)
        (by decide)
  have hScratch :
      (scratchRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)
        (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro r hr
      exact ⟨0, by simp [scratchHeap, regIs]⟩
    · exact List.Pairwise.imp (fun {r1 r2} hne => singletonReg_disjoint hne)
        (by decide)
  let hRegsState :=
    (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
      PartialState.empty).union
      (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
        PartialState.empty)
  have hRegs :
      ((fixedRegs.foldr (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion) **
        (scratchRegs.foldr (fun r acc => regOwn r ** acc) empAssertion))
        hRegsState := by
    exact sepConj_foldr_cross_satisfiable
      (atomL := fun p : Reg × Word => p.1 ↦ᵣ p.2) (heapL := fixedHeap)
      (xs := fixedRegs) (atomR := fun r : Reg => regOwn r)
      (heapR := scratchHeap) (ys := scratchRegs) hFixed hScratch (by
        intro p hp r hr
        apply singletonReg_disjoint
        simp [fixedRegs] at hp
        simp [scratchRegs] at hr
        aesop)
  have hA :
      (bytesRegion (BitVec.ofNat 64 0x40000000) (List.replicate 32 0)).SatWithin
        0x40000000 0x40000020 := by
    have h := satWithin_bytesRegion (BitVec.ofNat 64 0x40000000)
      (List.replicate 32 0) (fun k hk => by
        simp at hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hk' with rfl | rfl | rfl | rfl <;> decide)
    simpa using h
  have hFrame :
      frameSlots (BitVec.ofNat 64 0xa0050000) 0 0 0 0 0 0 |>.SatWithin
        0xa0050000 0xa0050030 := by
    rw [outer_zero_frame_eq]
    have h := satWithin_bytesRegion (BitVec.ofNat 64 0xa0050000)
      (List.replicate 48 0) (fun k hk => by
        simp at hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
          omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    simpa using h
  have hAcc :
      (bytesRegion accBase (List.replicate 40 0)).SatWithin
        0xa4386860 0xa4386888 := by
    have h := satWithin_bytesRegion accBase (List.replicate 40 0)
      (fun k hk => by
        simp at hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl <;> decide)
    simpa [accBase] using h
  have hMem :
      (bytesRegion (BitVec.ofNat 64 0x40000000) (List.replicate 32 0) **
        (bytesRegion accBase (List.replicate 40 0) **
          frameSlots (BitVec.ofNat 64 0xa0050000) 0 0 0 0 0 0)).SatWithin
        0x40000000 0xa4386888 := by
    have hFrame' :
        (frameSlots (BitVec.ofNat 64 0xa0050000) 0 0 0 0 0 0).SatWithin
          0xa0050000 0xa4386860 :=
      hFrame.mono (by decide) (by decide)
    have hFA := hFrame'.sepConj hAcc (by decide) (by decide)
    rw [sepConj_comm'
      (frameSlots (BitVec.ofNat 64 0xa0050000) 0 0 0 0 0 0)
      (bytesRegion accBase (List.replicate 40 0))] at hFA
    have hA' :
        (bytesRegion (BitVec.ofNat 64 0x40000000) (List.replicate 32 0)).SatWithin
          0x40000000 0xa0050000 :=
      hA.mono (by decide) (by decide)
    exact hA'.sepConj hFA (by decide) (by decide)
  have foldReg_no_fields :
      ∀ {α : Type} (xs : List α) (reg : α → Reg) (val : α → Word),
        (∀ a, (xs.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).mem a = none) ∧
        (∀ a, (xs.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).code a = none) ∧
        (xs.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).pc = none ∧
        (xs.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).publicValues = none ∧
        (xs.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).privateInput = none ∧
        (xs.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).inputBufBase = none := by
    intro α xs reg val
    induction xs with
    | nil => simp [PartialState.empty]
    | cons p ps ih =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro a
        change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).mem a = none
        exact ih.1 a
      · intro a
        change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).code a = none
        exact ih.2.1 a
      · change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).pc = none
        exact ih.2.2.1
      · change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).publicValues = none
        exact ih.2.2.2.1
      · change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).privateInput = none
        exact ih.2.2.2.2.1
      · change (ps.foldr
          (fun p acc => (PartialState.singletonReg (reg p) (val p)).union acc)
          PartialState.empty).inputBufBase = none
        exact ih.2.2.2.2.2
  have hFixedNo := foldReg_no_fields fixedRegs (fun p => p.1) (fun p => p.2)
  have hScratchNo := foldReg_no_fields scratchRegs (fun r => r) (fun _ => 0)
  have hFixedNo' :
      (∀ a, (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
        PartialState.empty).mem a = none) ∧
      (∀ a, (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
        PartialState.empty).code a = none) ∧
      (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
        PartialState.empty).pc = none ∧
      (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
        PartialState.empty).publicValues = none ∧
      (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
        PartialState.empty).privateInput = none ∧
      (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
        PartialState.empty).inputBufBase = none := by
    simpa [fixedHeap] using hFixedNo
  have hScratchNo' :
      (∀ a, (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
        PartialState.empty).mem a = none) ∧
      (∀ a, (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
        PartialState.empty).code a = none) ∧
      (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
        PartialState.empty).pc = none ∧
      (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
        PartialState.empty).publicValues = none ∧
      (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
        PartialState.empty).privateInput = none ∧
      (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
        PartialState.empty).inputBufBase = none := by
    simpa [scratchHeap] using hScratchNo
  have hAll :
      ∃ h, outerHeaderInv empAssertion (List.replicate 32 0)
        (BitVec.ofNat 64 0xa0050000) 0 0 0 0 0 0
        (BitVec.ofNat 64 0x40000000) 1
        (BitVec.ofNat 64 0xa0100000) 0 h := by
    obtain ⟨hMemState, hMemSat, hMemOnly⟩ := hMem
    have hRegNo :
        (∀ a, hRegsState.mem a = none) ∧
      (∀ a, hRegsState.code a = none) ∧
        hRegsState.pc = none ∧ hRegsState.publicValues = none ∧
        hRegsState.privateInput = none ∧ hRegsState.inputBufBase = none := by
      have hmem : ∀ a, hRegsState.mem a = none := by
        intro a
        change (match
          (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
            PartialState.empty).mem a with
          | some v => some v
          | none =>
            (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
              PartialState.empty).mem a) = none
        rw [hFixedNo'.1 a, hScratchNo'.1 a]
      have hcode : ∀ a, hRegsState.code a = none := by
        intro a
        change (match
          (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
            PartialState.empty).code a with
          | some v => some v
          | none =>
            (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
              PartialState.empty).code a) = none
        rw [hFixedNo'.2.1 a, hScratchNo'.2.1 a]
      have hpc : hRegsState.pc = none := by
        change (match
          (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
            PartialState.empty).pc with
          | some v => some v
          | none =>
            (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
              PartialState.empty).pc) = none
        rw [hFixedNo'.2.2.1, hScratchNo'.2.2.1]
      have hpublic : hRegsState.publicValues = none := by
        change (match
          (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
            PartialState.empty).publicValues with
          | some v => some v
          | none =>
            (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
              PartialState.empty).publicValues) = none
        rw [hFixedNo'.2.2.2.1, hScratchNo'.2.2.2.1]
      have hprivate : hRegsState.privateInput = none := by
        change (match
          (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
            PartialState.empty).privateInput with
          | some v => some v
          | none =>
            (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
              PartialState.empty).privateInput) = none
        rw [hFixedNo'.2.2.2.2.1, hScratchNo'.2.2.2.2.1]
      have hinput : hRegsState.inputBufBase = none := by
        change (match
          (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
            PartialState.empty).inputBufBase with
          | some v => some v
          | none =>
            (scratchRegs.foldr (fun r acc => (scratchHeap r).union acc)
              PartialState.empty).inputBufBase) = none
        rw [hFixedNo'.2.2.2.2.2, hScratchNo'.2.2.2.2.2]
      exact ⟨hmem, hcode, hpc, hpublic, hprivate, hinput⟩
    have hdisj : hRegsState.Disjoint hMemState := by
      refine ⟨fun _ => Or.inr (hMemOnly.regs _),
        fun a => Or.inl (hRegNo.1 a),
        fun a => Or.inl (hRegNo.2.1 a),
        Or.inl hRegNo.2.2.1, Or.inl hRegNo.2.2.2.1,
        Or.inl hRegNo.2.2.2.2.1, Or.inl hRegNo.2.2.2.2.2⟩
    let oldFixedRegs : List (Reg × Word) :=
      [(.x2, BitVec.ofNat 64 0xa0050000),
       (.x1, 0), (.x8, BitVec.ofNat 64 0x40000000), (.x9, 1),
       (.x18, BitVec.ofNat 64 0xa0100000), (.x19, BitVec.ofNat 64 0xa4386860),
       (.x0, 0), (.x10, BitVec.ofNat 64 0x40000000), (.x11, 1),
       (.x12, BitVec.ofNat 64 0xa0100000)]
    let inputAssert : Assertion :=
      bytesRegion (BitVec.ofNat 64 0x40000000) (List.replicate 32 0)
    let fixedAssert : Assertion :=
      ((.x20 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ (32 : Word)) **
          oldFixedRegs.foldr (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion
    let scratchAssert : Assertion :=
      scratchRegs.foldr (fun r acc => regOwn r ** acc) empAssertion
    let tailAssert : Assertion :=
      bytesRegion accBase (List.replicate 40 0) **
        frameSlots (BitVec.ofNat 64 0xa0050000) 0 0 0 0 0 0
    have hRegs' : (fixedAssert ** scratchAssert) hRegsState := by
      simpa [fixedAssert, oldFixedRegs, fixedRegs, scratchAssert, scratchRegs]
        using hRegs
    have hJoined :
        ((fixedAssert ** scratchAssert) ** (inputAssert ** tailAssert))
          (hRegsState.union hMemState) := by
      exact ⟨hRegsState, hMemState, hdisj, rfl, hRegs', hMemSat⟩
    have hReordered := hJoined
    rw [sepConj_assoc' fixedAssert scratchAssert (inputAssert ** tailAssert),
      sepConj_left_comm' scratchAssert inputAssert tailAssert,
      sepConj_left_comm' fixedAssert inputAssert (scratchAssert ** tailAssert)]
      at hReordered
    dsimp [fixedAssert] at hReordered
    refine ⟨hRegsState.union hMemState, ?_⟩
    rw [outerHeaderInv, outerLoopInv, sepConj_emp_left']
    simp only [mulState]
    simp only [inputAssert, oldFixedRegs, scratchAssert, scratchRegs,
      tailAssert, List.foldr, sepConj_emp_right'] at hReordered ⊢
    have h32 : (32 : Word) = BitVec.ofNat 64 32 := by decide
    rw [h32] at ⊢
    simp only [accBase] at hReordered ⊢
    have hAccBase : (BitVec.ofNat 64 0xa4386860 : Word) =
        (GuestAddrs.u256m_acc : Word) := by decide
    rw [hAccBase] at hReordered
    xperm_hyp hReordered
  exact hAll

/-! `LBU x5, x5` needs a one-register rule: the ordinary generic load rule
    owns the base register and destination register as separate atoms, which
    is impossible when the instruction uses the same register for both. -/

theorem bytesRegion_lbu_same_reg_within
    (regionBase base : Word) (bs : List (BitVec 8)) (i : Nat)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.LBU .x5 .x5 0))
      (((.x5 : Reg) ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
        bytesRegion regionBase bs)
      (((.x5 : Reg) ↦ᵣ (bs[i]'hi).zeroExtend 64) **
        bytesRegion regionBase bs) := by
  obtain ⟨front, rest, hf, hr, heq⟩ := bytesRegion_dword_at regionBase bs (i / 8) (by omega)
  let dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8))
  let wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8)
  have hzero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr : regionBase + BitVec.ofNat 64 i + signExtend12 (0 : BitVec 12) =
      regionBase + BitVec.ofNat 64 i := by
    rw [hzero]
    exact BitVec.add_zero _
  have halign' : alignToDword (regionBase + BitVec.ofNat 64 i) = dwordAddr := by
    dsimp [dwordAddr]
    exact alignToDword_add_ofNat_of_aligned halign hover
  have hbyte : extractByte wordVal (byteOffset (regionBase + BitVec.ofNat 64 i)) = bs[i]'hi := by
    dsimp [wordVal]
    rw [byteOffset_add_ofNat_of_aligned halign hover,
      extractByte_packBytes _ _ (by omega)
        (by rw [List.length_take, List.length_drop]; omega),
      List.getElem_take, List.getElem_drop]
    congr 1
    omega
  intro R hR s hcr hPR hpc
  subst hpc
  have hfetch : s.code s.pc = some (.LBU .x5 .x5 0) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hPR0 := holdsFor_sepConj_elim_left hPR
  have hptr : s.getReg .x5 = regionBase + BitVec.ofNat 64 i :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR0)
  have hregion := holdsFor_sepConj_elim_right hPR0
  rw [heq] at hregion
  have hmem : s.getMem dwordAddr = wordVal :=
    holdsFor_memIs_getMem
      (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right hregion))
  have hstep' : step s = some (execInstrBr s (.LBU .x5 .x5 0)) :=
    step_lbu hfetch (hptr ▸ (by
      rw [haddr]
      exact hvalid))
  have hexec' : execInstrBr s (.LBU .x5 .x5 0) =
      (s.setReg .x5 ((bs[i]'hi).zeroExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hptr, getByte_eq]
    rw [haddr, halign', hmem, hbyte]
  refine ⟨1, Nat.le_refl 1,
    (s.setReg .x5 ((bs[i]'hi).zeroExtend 64)).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']
    rfl
  · have hset0 := holdsFor_sepConj_regIs_setReg
      (v' := (bs[i]'hi).zeroExtend 64) (by decide)
      (holdsFor_sepConj_assoc.mp hPR)
    have hset := holdsFor_sepConj_assoc.mpr hset0
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) hR) hset

/-! The outer cycle starts with four instructions that derive the selected
    input byte.  This prefix is kept separate because it is the load-bearing
    bridge from the header invariant to the zero/nonzero branch: the cycle
    owns `x5` while it is being derived, whereas `x20`, `x8`, `x9`, `x18`, and
    `x19` are framed through the body. -/

theorem outerBytePrefix_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes : List (BitVec 8)) (hlen : aBytes.length = 32)
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (hi : i < 32)
    (halignA : aPtr.toNat % 8 = 0)
    (hoverA : aPtr.toNat + (31 - i) < 2 ^ 64)
    (hvalidA : isValidByteAccess (aPtr + BitVec.ofNat 64 (31 - i)) = true) :
    cpsTripleWithin 4 (mulBase + 88) (mulBase + 104) mulCR
      (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i)
      (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
        ((.x5 : Reg) ↦ᵣ (aBytes[31 - i]'(by omega)).zeroExtend 64) **
        outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i) := by
  let P := outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i
  let P2 := F ** bytesRegion aPtr aBytes **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x9 : Reg) ↦ᵣ b) ** ((.x18 : Reg) ↦ᵣ outPtr) **
    ((.x19 : Reg) ↦ᵣ accBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) **
    ((.x12 : Reg) ↦ᵣ outPtr) **
    regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    bytesRegion accBase (mulState aBytes b i) **
    frameSlots spNew vRa v8 v9 v18 v19 v20
  let P3 := F **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
    ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
    ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
    regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    bytesRegion accBase (mulState aBytes b i) **
    frameSlots spNew vRa v8 v9 v18 v19 v20
  have hP : P.pcFree := by
    dsimp [P, outerLoopInv]
    exact pcFree_sepConj hF (by pcf)
  have hPF : (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** P).pcFree := by
    exact pcFree_sepConj (by pcf) hP
  have hP2 : P2.pcFree := by
    dsimp [P2]
    exact pcFree_sepConj hF (by pcf)
  have hPF2 : (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** P2).pcFree := by
    exact pcFree_sepConj (by pcf) hP2
  have hP3 : P3.pcFree := by
    dsimp [P3]
    exact pcFree_sepConj hF (by pcf)
  have hPF3 : (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** P3).pcFree := by
    exact pcFree_sepConj (by pcf) hP3
  have h0 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (li_spec_gen_within .x5 (32 : Word) (31 : Word) (mulBase + 88) (by decide))
  rw [show mulBase + 88 + 4 = mulBase + 92 from by decide] at h0
  have h0F := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** P) hPF h0
  have h1 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (sub_spec_gen_rd_eq_rs1_within .x5 .x20 (31 : Word)
      (BitVec.ofNat 64 i)
      (mulBase + 92) (by decide))
  rw [show mulBase + 92 + 4 = mulBase + 96 from by decide,
    sub_31_ofNat i hi] at h1
  have h1F := cpsTripleWithin_frameR
    P hP h1
  have h2 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (add_spec_gen_rd_eq_rs2_within .x5 .x8 aPtr
      (BitVec.ofNat 64 (31 - i)) (mulBase + 96) (by decide))
  rw [show mulBase + 96 + 4 = mulBase + 100 from by decide] at h2
  have h2F := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** P2) hPF2 h2
  have h3 := bytesRegion_lbu_same_reg_within aPtr (mulBase + 100)
      aBytes (31 - i) halignA (by rw [hlen]; omega) hoverA hvalidA
  rw [show mulBase + 100 + 4 = mulBase + 104 from by decide] at h3
  have h3e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h3
  have h3F := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** P3) hPF3 h3e
  have h01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [P, outerLoopInv] at hp ⊢
      xperm_hyp hp) h0F h1F
  have h012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [P, P2, outerLoopInv] at hp ⊢
      xperm_hyp hp) h01 h2F
  have h0123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [P, P2, P3, outerLoopInv] at hp ⊢
      xperm_hyp hp) h012 h3F
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h0123
  · dsimp [outerHeaderInv, P, P2, P3, outerLoopInv] at hp ⊢
    xperm_hyp hp
  · dsimp [P, P2, P3, outerLoopInv] at hq ⊢
    xperm_hyp hq

/-! ## One nonzero multiply cycle

The nonzero arm keeps the full product split explicit.  `x6` carries the
low 64-bit product through the ripple, while `x7` carries `M / 2^64`; the
accumulator invariant therefore uses `M % 2^64` for the eight low-byte
rounds and adds the high half at the ninth byte. -/

def outerStableNoAcc
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) : Assertion :=
  F ** bytesRegion aPtr aBytes **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
    ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) **
    ((.x12 : Reg) ↦ᵣ outPtr) **
    frameSlots spNew vRa v8 v9 v18 v19 v20

def rippleBase
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (byte : Word) (m : Nat) (k : Nat) : Assertion :=
    outerStableNoAcc F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
    ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) **
    ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64)) **
    ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 ((m % 2 ^ 64) / 256 ^ k)) **
    ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (i + k))) **
    ((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
    ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64
      (mulCarry (mulState aBytes b i) (m % 2 ^ 64) i k)) **
    bytesRegion accBase (rippleState (mulState aBytes b i) (m % 2 ^ 64) i k)

def rippleFrame
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (byte : Word) (m : Nat) (k : Nat) : Assertion :=
    rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i byte m k **
    regOwn .x13

def outerStableNoX9
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) : Assertion :=
  F ** bytesRegion aPtr aBytes **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ aPtr) **
    ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) **
    ((.x12 : Reg) ↦ᵣ outPtr) **
    frameSlots spNew vRa v8 v9 v18 v19 v20

def outerStableNoX9NoX19
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) : Assertion :=
  F ** bytesRegion aPtr aBytes **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x18 : Reg) ↦ᵣ outPtr) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) **
    ((.x12 : Reg) ↦ᵣ outPtr) **
    frameSlots spNew vRa v8 v9 v18 v19 v20

/-! The five instructions before the ripple loop split the selected byte's
    product into MUL/MULHU halves and initialize the ripple cursor, remaining
    count, and carry.  Keep this transition separate from the loop: it is the
    point where the outer-loop register ownership becomes the exact
    `rippleBase` state consumed by `rippleBody_exact`. -/

theorem mulInit_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (byte : Word) (hbyte : byte.toNat ≤ 255) (m : Nat)
    (hm : m = byte.toNat * b.toNat) :
    cpsTripleWithin 5 (mulBase + 108) (mulBase + 128) mulCR
      (((.x5 : Reg) ↦ᵣ byte) **
      ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
      outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i)
      (rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i byte m 0 **
        regOwn .x13 ** regOwn .x31) := by
  let A : Assertion :=
    outerStableNoX9NoX19 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      regOwn .x13 ** regOwn .x31 **
      bytesRegion accBase (mulState aBytes b i)
  have hStable : (outerStableNoX9NoX19 F aBytes spNew vRa v8 v9 v18 v19 v20
      aPtr b outPtr).pcFree := by
    dsimp [outerStableNoX9NoX19]
    apply pcFree_sepConj hF
    pcf
  have hA : A.pcFree := by
    dsimp [A]
    exact pcFree_sepConj hStable (by pcf)
  have hmul : byte * b = BitVec.ofNat 64 (m % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq
    simp [hm]
  have hq_le : m / 2 ^ 64 ≤ 254 := by
    rw [hm]
    exact mulhu_le_254 byte b hbyte
  have hq_word : Rv64.rv64_mulhu byte b =
      BitVec.ofNat 64 (m / 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [mulhu_toNat, BitVec.toNat_ofNat, hm]
    exact (Nat.mod_eq_of_lt
      (by omega : byte.toNat * b.toNat / 2 ^ 64 < 2 ^ 64)).symm
  let P0 : Assertion :=
    ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x19 : Reg) ↦ᵣ accBase) ** A **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30
  have hP0 : P0.pcFree := by
    dsimp only [P0]
    apply pcFree_sepConj
    · pcf
    · apply pcFree_sepConj
      · pcf
      · apply pcFree_sepConj hA
        pcf
  have h0 : ∀ old6, cpsTripleWithin 1 (mulBase + 108) (mulBase + 112) mulCR
      (((P0 ** ((.x5 : Reg) ↦ᵣ byte)) ** ((.x9 : Reg) ↦ᵣ b)) **
        ((.x6 : Reg) ↦ᵣ old6))
      (((P0 ** ((.x5 : Reg) ↦ᵣ byte)) ** ((.x9 : Reg) ↦ᵣ b)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m % 2 ^ 64))) := by
    intro old6
    have h0raw := mul_spec_gen_within .x6 .x5 .x9 old6 byte b
      (mulBase + 108) (by decide)
    rw [show mulBase + 108 + 4 = mulBase + 112 from by decide, hmul] at h0raw
    have h0e := cpsTripleWithin_extend_code (cr' := mulCR)
      (hmono := by code_mem) h0raw
    have h0f := cpsTripleWithin_frameR P0 hP0 h0e
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [P0] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp only [P0] at hq ⊢
      xperm_hyp hq) h0f
  have h0' : cpsTripleWithin 1 (mulBase + 108) (mulBase + 112) mulCR
      (((P0 ** ((.x5 : Reg) ↦ᵣ byte)) ** ((.x9 : Reg) ↦ᵣ b)) ** regOwn .x6)
      (((P0 ** ((.x5 : Reg) ↦ᵣ byte)) ** ((.x9 : Reg) ↦ᵣ b)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m % 2 ^ 64))) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn
      (nSteps := 1) (entry := mulBase + 108) (exit_ := mulBase + 112)
      (cr := mulCR) (r := .x6)
      (P := (P0 ** ((.x5 : Reg) ↦ᵣ byte)) ** ((.x9 : Reg) ↦ᵣ b))
      (Q := ((P0 ** ((.x5 : Reg) ↦ᵣ byte)) ** ((.x9 : Reg) ↦ᵣ b)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m % 2 ^ 64))) h0
  let P1 : Assertion :=
    ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x19 : Reg) ↦ᵣ accBase) ** A **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m % 2 ^ 64)) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30
  have hP1 : P1.pcFree := by
    dsimp only [P1]
    apply pcFree_sepConj
    · pcf
    · apply pcFree_sepConj
      · pcf
      · apply pcFree_sepConj hA
        pcf
  have h1 : ∀ old7, cpsTripleWithin 1 (mulBase + 112) (mulBase + 116) mulCR
      (((P1 ** ((.x5 : Reg) ↦ᵣ byte)) ** ((.x9 : Reg) ↦ᵣ b)) **
        ((.x7 : Reg) ↦ᵣ old7))
      (((P1 ** ((.x5 : Reg) ↦ᵣ byte)) ** ((.x9 : Reg) ↦ᵣ b)) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64))) := by
    intro old7
    have h1raw := mulhu_spec_gen_within .x7 .x5 .x9 old7 byte b
      (mulBase + 112) (by decide)
    rw [show mulBase + 112 + 4 = mulBase + 116 from by decide, hq_word] at h1raw
    have h1e := cpsTripleWithin_extend_code (cr' := mulCR)
      (hmono := by code_mem) h1raw
    have h1f := cpsTripleWithin_frameR P1 hP1 h1e
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [P1] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp only [P1] at hq ⊢
      xperm_hyp hq) h1f
  have h1' : cpsTripleWithin 1 (mulBase + 112) (mulBase + 116) mulCR
      (((P1 ** ((.x5 : Reg) ↦ᵣ byte)) ** ((.x9 : Reg) ↦ᵣ b)) ** regOwn .x7)
      (((P1 ** ((.x5 : Reg) ↦ᵣ byte)) ** ((.x9 : Reg) ↦ᵣ b)) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64))) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn
      (nSteps := 1) (entry := mulBase + 112) (exit_ := mulBase + 116)
      (cr := mulCR) (r := .x7)
      (P := (P1 ** ((.x5 : Reg) ↦ᵣ byte)) ** ((.x9 : Reg) ↦ᵣ b))
      (Q := ((P1 ** ((.x5 : Reg) ↦ᵣ byte)) ** ((.x9 : Reg) ↦ᵣ b)) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64))) h1
  let P2 : Assertion :=
    ((.x5 : Reg) ↦ᵣ byte) ** ((.x9 : Reg) ↦ᵣ b) **
      A **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m % 2 ^ 64)) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64)) **
      regOwn .x29 ** regOwn .x30
  have hP2 : P2.pcFree := by
    dsimp only [P2]
    apply pcFree_sepConj
    · pcf
    · apply pcFree_sepConj
      · pcf
      · apply pcFree_sepConj hA
        pcf
  have h2 : ∀ old28, cpsTripleWithin 1 (mulBase + 116) (mulBase + 120) mulCR
      (((P2 ** ((.x19 : Reg) ↦ᵣ accBase)) **
        ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i)) **
        ((.x28 : Reg) ↦ᵣ old28))
      (((P2 ** ((.x19 : Reg) ↦ᵣ accBase)) **
        ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i)) **
        ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 i))) := by
    intro old28
    have h2raw := add_spec_gen_within .x28 .x19 .x20 accBase
      (BitVec.ofNat 64 i) old28 (mulBase + 116) (by decide)
    rw [show mulBase + 116 + 4 = mulBase + 120 from by decide] at h2raw
    have h2e := cpsTripleWithin_extend_code (cr' := mulCR)
      (hmono := by
        intro a ins h
        exact CodeReq.ofProg_mem_at mulBase (mulBase + 116) mulProg 29
          (.ADD .x28 .x19 .x20) (by decide) (by decide) (by decide)
          (by decide) a ins h) h2raw
    have h2f := cpsTripleWithin_frameR P2 hP2 h2e
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [P2] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp only [P2] at hq ⊢
      xperm_hyp hq) h2f
  have h2' := cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x28)
    (P := (P2 ** ((.x19 : Reg) ↦ᵣ accBase)) **
      ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i)) h2
  let P3 : Assertion :=
    ((.x5 : Reg) ↦ᵣ byte) ** ((.x9 : Reg) ↦ᵣ b) **
      ((.x19 : Reg) ↦ᵣ accBase) ** A **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m % 2 ^ 64)) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64)) **
      ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
      ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 i)) ** regOwn .x30
  have hP3 : P3.pcFree := by
    dsimp only [P3]
    apply pcFree_sepConj
    · pcf
    · apply pcFree_sepConj
      · pcf
      · apply pcFree_sepConj
        · pcf
        · apply pcFree_sepConj hA
          pcf
  have h3raw := li_spec_gen_own_within .x29 (8 : Word) (mulBase + 120) (by decide)
  rw [show mulBase + 120 + 4 = mulBase + 124 from by decide] at h3raw
  have h3e := cpsTripleWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem) h3raw
  have h3f := cpsTripleWithin_frameR P3 hP3 h3e
  have h3 : cpsTripleWithin 1 (mulBase + 120) (mulBase + 124) mulCR
      (P3 ** regOwn .x29) (P3 ** ((.x29 : Reg) ↦ᵣ (8 : Word))) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [P3] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp only [P3] at hq ⊢
      xperm_hyp hq) h3f
  let P4 : Assertion :=
    ((.x5 : Reg) ↦ᵣ byte) ** ((.x9 : Reg) ↦ᵣ b) **
      ((.x19 : Reg) ↦ᵣ accBase) ** A **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m % 2 ^ 64)) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64)) **
      ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
      ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 i)) **
      ((.x29 : Reg) ↦ᵣ (8 : Word))
  have hP4 : P4.pcFree := by
    dsimp only [P4]
    apply pcFree_sepConj
    · pcf
    · apply pcFree_sepConj
      · pcf
      · apply pcFree_sepConj
        · pcf
        · apply pcFree_sepConj hA
          pcf
  have h4raw := li_spec_gen_own_within .x30 (0 : Word) (mulBase + 124) (by decide)
  rw [show mulBase + 124 + 4 = mulBase + 128 from by decide] at h4raw
  have h4e := cpsTripleWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem) h4raw
  have h4f := cpsTripleWithin_frameR P4 hP4 h4e
  have h4 : cpsTripleWithin 1 (mulBase + 124) (mulBase + 128) mulCR
      (P4 ** regOwn .x30) (P4 ** ((.x30 : Reg) ↦ᵣ (0 : Word))) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [P4] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp only [P4] at hq ⊢
      xperm_hyp hq) h4f
  have hseq01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h0' h1'
  have hseq012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hseq01 h2'
  have hseq0123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hseq012 h3
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hseq0123 h4
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hseq
  · dsimp [outerLoopInv, P0, P1, P2, P3, P4, A,
      outerStableNoX9NoX19] at hp ⊢
    xperm_hyp hp
  · dsimp [rippleBase, P4, A, outerStableNoAcc,
      outerStableNoX9NoX19] at hq ⊢
    simp [mulCarry]
    xperm_hyp hq


end EvmAsm.Codegen.U256MulU64Be
