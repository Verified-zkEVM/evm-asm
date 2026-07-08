/-
  EvmAsm.Rv64.SAsm.AbiFrameDemo

  End-to-end regression witness for the ABI-frame construct
  (bead evm-asm-4ch8f.76), now derived as a one-shot instantiation of the
  reusable, parameterized `abiFrame_spec`.

  A synthetic leaf routine with a standard C-ABI frame:

      addi sp, sp, -24      -- allocate frame
      sd   ra, 0(sp)        -- save ra
      sd   s0, 8(sp)        -- save s0 (callee-saved)
      sd   s1, 16(sp)       -- save s1 (callee-saved)
      add  s0, a0, a1       -- body: s0 := a0 + a1   (s0 used as a LOCAL)
      add  s1, s0, a0       -- body: s1 := s0 + a0   (s1 clobbered, uses s0)
      sd   a2, s0 -> [a2]   -- body: store s0 to the caller's rw dword
      ld   ra, 0(sp)        -- restore ra
      ld   s0, 8(sp)        -- restore s0
      ld   s1, 16(sp)       -- restore s1
      addi sp, sp, +24      -- deallocate frame
      ret

  The post proves the ABI contract: on return `sp`, `ra`, `s0`, `s1` all equal
  their ENTRY values (the body clobbered `s0`/`s1` but the caller sees them
  preserved), while the routine's real effect — the rw dword at `[a2]` now
  holds `a0 + a1` — holds.  Preservation is derived from the frame rule inside
  `abiFrame_spec`, never assumed.
-/

import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64
namespace SAsm
namespace AbiFrameDemo

open EvmAsm.Rv64.Tactics

/-- The 3-slot demo frame: `ra` at 0, `s0` at 8, `s1` at 16. -/
def demoFrame : FrameDesc := [(.x1, 0), (.x8, 8), (.x9, 16)]

/-- Body: use the callee-saved registers as locals and write the result to the
    caller's rw dword (held in `a2`). -/
def demoBody : List Instr :=
  [ .ADD .x8 .x10 .x11,     -- s0 := a0 + a1
    .ADD .x9 .x8 .x10,      -- s1 := s0 + a0
    .SD .x12 .x8 0 ]        -- store s0 to [a2]

/-- The full frame routine (12 instructions), as an `abiFrameProg`. -/
def demoProg : List Instr :=
  abiFrameProg (-24 : BitVec 12) (24 : BitVec 12) demoFrame demoBody

/-- The same 12 instructions spelled out (used for the routine `CodeReq`). -/
def demoProgList : List Instr :=
  [ .ADDI .x2 .x2 (-24 : BitVec 12),
    .SD .x2 .x1 0,
    .SD .x2 .x8 8,
    .SD .x2 .x9 16,
    .ADD .x8 .x10 .x11,
    .ADD .x9 .x8 .x10,
    .SD .x12 .x8 0,
    .LD .x1 .x2 0,
    .LD .x8 .x2 8,
    .LD .x9 .x2 16,
    .ADDI .x2 .x2 (24 : BitVec 12),
    .JALR .x0 .x1 0 ]

-- Byte-transparency: the frame routine is exactly prologue ++ body ++
-- epilogue ++ ret, spelled out.
#guard demoProg = demoProgList

/-- Byte-transparency as a `rfl`-checked theorem (kernel-verified, not just
    `#guard`): the `abiFrameProg` flatten equals the hand-written program. -/
theorem demoProg_eq : demoProg = demoProgList := rfl

/-- Entry register values: `ra ↦ ret`, `s0 ↦ v0`, `s1 ↦ v1`. -/
def demoVals (ret v0 v1 : Word) : Reg → Word := fun r =>
  match r with | .x1 => ret | .x8 => v0 | .x9 => v1 | _ => 0

/-- Post-body register values: `ra` untouched (`ret`), `s0 ↦ a0+a1`,
    `s1 ↦ (a0+a1)+a0`. -/
def demoVals' (ret va0 va1 : Word) : Reg → Word := fun r =>
  match r with | .x1 => ret | .x8 => va0 + va1 | .x9 => (va0 + va1) + va0 | _ => 0

/-- Caller footprint before the body: `a0`, `a1`, the rw pointer `a2`, and the
    rw dword (arbitrary contents `jt`). -/
def demoCallerPre (va0 va1 jt : Word) : Assertion :=
  (.x10 ↦ᵣ va0) ** (.x11 ↦ᵣ va1) ** (.x12 ↦ᵣ (0x31000 : Word)) ** ((0x31000 : Word) ↦ₘ jt)

/-- Caller footprint after the body: the rw dword now holds `a0+a1`. -/
def demoCallerPost (va0 va1 : Word) : Assertion :=
  (.x10 ↦ᵣ va0) ** (.x11 ↦ᵣ va1) ** (.x12 ↦ᵣ (0x31000 : Word))
    ** ((0x31000 : Word) ↦ₘ (va0 + va1))

/-- The routine CodeReq: exactly the flattened routine at `0x1000`. -/
def demoCr : CodeReq := CodeReq.ofProg 0x1000 demoProgList

/-- The body's straight-line effect (explicit atoms), proved by `runBlock`.
    `ra`, `sp`, and the three frame slots are framed (untouched). -/
theorem demoBody_spec (ret v0 v1 va0 va1 jt : Word) :
    cpsTripleWithin 3 0x1010 0x101C demoCr
      ((.x2 ↦ᵣ (0x2FFE8 : Word)) ** (.x1 ↦ᵣ ret)
        ** ((0x2FFE8 : Word) ↦ₘ ret) ** ((0x2FFF0 : Word) ↦ₘ v0) ** ((0x2FFF8 : Word) ↦ₘ v1)
        ** (.x8 ↦ᵣ v0) ** (.x9 ↦ᵣ v1) ** (.x10 ↦ᵣ va0) ** (.x11 ↦ᵣ va1)
        ** (.x12 ↦ᵣ (0x31000 : Word)) ** ((0x31000 : Word) ↦ₘ jt))
      ((.x2 ↦ᵣ (0x2FFE8 : Word)) ** (.x1 ↦ᵣ ret)
        ** ((0x2FFE8 : Word) ↦ₘ ret) ** ((0x2FFF0 : Word) ↦ₘ v0) ** ((0x2FFF8 : Word) ↦ₘ v1)
        ** (.x8 ↦ᵣ (va0 + va1)) ** (.x9 ↦ᵣ ((va0 + va1) + va0)) ** (.x10 ↦ᵣ va0) ** (.x11 ↦ᵣ va1)
        ** (.x12 ↦ᵣ (0x31000 : Word)) ** ((0x31000 : Word) ↦ₘ (va0 + va1))) := by
  simp only [demoCr, demoProgList, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]
  have s5 := add_spec_gen_within .x8 .x10 .x11 va0 va1 v0 0x1010 (by decide)
  have s6 := add_spec_gen_within .x9 .x8 .x10 (va0 + va1) va0 v1 0x1014 (by decide)
  have s7 := sd_spec_gen_within .x12 .x8 (0x31000 : Word) (va0 + va1) jt 0 0x1018
  have ed : (0x31000 : Word) + signExtend12 (0 : BitVec 12) = (0x31000 : Word) := by decide
  rw [ed] at s7
  runBlock s5 s6 s7

/-- **The ABI-frame contract, derived from `abiFrame_spec`.**  Running the whole
    routine from entry `0x1000` returns to `ret` within 12 steps with `sp`,
    `ra`, `s0`, `s1` all restored to their entry values and the rw dword at
    `[a2]` (`0x31000`) holding `a0 + a1`. -/
theorem demoFrame_spec (ret v0 v1 va0 va1 jt : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (1 + demoFrame.length + 3 + demoFrame.length + 1 + 1) 0x1000 ret demoCr
      ((.x2 ↦ᵣ (0x30000 : Word)) ** regsAt demoFrame (demoVals ret v0 v1)
        ** frameSlotsOwn demoFrame ((0x30000 : Word) + signExtend12 (-24 : BitVec 12))
        ** demoCallerPre va0 va1 jt)
      ((.x2 ↦ᵣ (0x30000 : Word)) ** regsAt demoFrame (demoVals ret v0 v1)
        ** frameSlotsSaved demoFrame ((0x30000 : Word) + signExtend12 (-24 : BitVec 12))
            (demoVals ret v0 v1)
        ** demoCallerPost va0 va1) := by
  have hbody :
      cpsTripleWithin 3
        ((0x1000 : Word) + BitVec.ofNat 64 (4 * (1 + demoFrame.length)))
        ((0x1000 : Word) + BitVec.ofNat 64 (4 * (1 + demoFrame.length + demoBody.length)))
        demoCr
        ((.x2 ↦ᵣ ((0x30000 : Word) + signExtend12 (-24 : BitVec 12)))
          ** regsAt demoFrame (demoVals ret v0 v1)
          ** frameSlotsSaved demoFrame ((0x30000 : Word) + signExtend12 (-24 : BitVec 12))
              (demoVals ret v0 v1)
          ** demoCallerPre va0 va1 jt)
        ((.x2 ↦ᵣ ((0x30000 : Word) + signExtend12 (-24 : BitVec 12)))
          ** regsAt demoFrame (demoVals' ret va0 va1)
          ** frameSlotsSaved demoFrame ((0x30000 : Word) + signExtend12 (-24 : BitVec 12))
              (demoVals ret v0 v1)
          ** demoCallerPost va0 va1) := by
    have hentry : (0x1000 : Word) + BitVec.ofNat 64 (4 * (1 + demoFrame.length))
        = (0x1010 : Word) := by decide
    have hexit : (0x1000 : Word) + BitVec.ofNat 64 (4 * (1 + demoFrame.length + demoBody.length))
        = (0x101C : Word) := by decide
    have hns : (0x30000 : Word) + signExtend12 (-24 : BitVec 12) = (0x2FFE8 : Word) := by decide
    rw [hentry, hexit, hns]
    simp only [demoFrame, regsAt, frameSlotsSaved, demoVals, demoVals',
      demoCallerPre, demoCallerPost, List.foldr_cons, List.foldr_nil, sepConj_emp_right']
    rw [show (0x2FFE8 : Word) + signExtend12 (0 : BitVec 12) = (0x2FFE8 : Word) from by decide,
        show (0x2FFE8 : Word) + signExtend12 (8 : BitVec 12) = (0x2FFF0 : Word) from by decide,
        show (0x2FFE8 : Word) + signExtend12 (16 : BitVec 12) = (0x2FFF8 : Word) from by decide]
    exact cpsTripleWithin_weaken (by xsimp) (by xsimp) (demoBody_spec ret v0 v1 va0 va1 jt)
  have h := abiFrame_spec (base := 0x1000) (sp0 := 0x30000) (ret := ret)
    (negImm := -24) (posImm := 24)
    (frame := demoFrame) (raOfs := 0) (sregs := [(.x8, 8), (.x9, 16)])
    (vals := demoVals ret v0 v1) (vals' := demoVals' ret va0 va1)
    (body := demoBody) (bodySteps := 3)
    (callerPre := demoCallerPre va0 va1 jt) (callerPost := demoCallerPost va0 va1)
    (cr := demoCr)
    (hframe := rfl)
    (hne := by decide)
    (hbound := by decide)
    (hprogBound := by decide)
    (hret := rfl)
    (halign := halign)
    (hframeRestore := by decide)
    (hcpF := by
      simp only [demoCallerPre]
      exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs pcFree_memIs)))
    (hcpF' := by
      simp only [demoCallerPost]
      exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs pcFree_memIs)))
    (hsub := fun a i h => h)
    (hbody := hbody)
  exact h

#print axioms demoBody_spec
#print axioms demoFrame_spec

end AbiFrameDemo
end SAsm
end EvmAsm.Rv64
