/-
  EvmAsm.Rv64.SAsm.RegFile

  The exposed register file for the SAsm structured-assembly DSL.

  SAsm basic blocks compute over a fixed set of *exposed* registers
  (t0–t6 and a0–a7).  `x0` is hardwired zero, `x1`/`x2` (ra/sp) are owned
  by the call machinery, and the s-registers are left to the ambient frame
  (a leaf SAsm function neither reads nor writes them).

  A `RegFile` is a total valuation of registers; the exposure discipline is
  enforced where it matters: `regFileIs` (M2) owns exactly the exposed set,
  and the block engine (M2) rejects reads/writes outside it.  Keeping the
  carrier total makes `get`/`set` and condition denotations simple.

  See docs/sasm-design.md §3.1.
-/

import EvmAsm.Rv64.Basic

namespace EvmAsm.Rv64
namespace SAsm

/-- Registers whose values SAsm basic blocks may read and write:
    t0–t6 (scratch) and a0–a7 (arguments/returns). -/
def exposedRegs : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Decidable membership in the exposed set. -/
def Reg.isExposed (r : Reg) : Bool :=
  match r with
  | .x5 | .x6 | .x7 | .x28 | .x29 | .x30 | .x31 => true
  | .x10 | .x11 | .x12 | .x13 | .x14 | .x15 | .x16 | .x17 => true
  | _ => false

theorem Reg.isExposed_iff_mem (r : Reg) :
    Reg.isExposed r = true ↔ r ∈ exposedRegs := by
  cases r <;> simp [Reg.isExposed, exposedRegs]

/-- A symbolic valuation of the register file.  The values of non-exposed
    registers are irrelevant to SAsm (never read through `get` on well-formed
    programs, never owned by `regFileIs`). -/
def RegFile := Reg → Word

namespace RegFile

/-- Read a register.  `x0` always reads as zero, matching the machine. -/
def get (rf : RegFile) (r : Reg) : Word :=
  if r = .x0 then 0 else rf r

/-- Write a register.  Writes to `x0` are dropped, matching the machine. -/
def set (rf : RegFile) (r : Reg) (v : Word) : RegFile :=
  fun r' => if r' = r ∧ r ≠ .x0 then v else rf r'

@[simp] theorem get_x0 (rf : RegFile) : rf.get .x0 = 0 := rfl

@[simp] theorem get_set_self (rf : RegFile) (r : Reg) (v : Word)
    (hr : r ≠ .x0) : (rf.set r v).get r = v := by
  simp [get, set, hr]

@[simp] theorem get_set_ne (rf : RegFile) (r r' : Reg) (v : Word)
    (h : r' ≠ r) : (rf.set r v).get r' = rf.get r' := by
  by_cases h0 : r' = .x0 <;> simp [get, set, h, h0]

@[simp] theorem set_x0 (rf : RegFile) (v : Word) : rf.set .x0 v = rf := by
  funext r'
  simp [set]

end RegFile

end SAsm
end EvmAsm.Rv64
