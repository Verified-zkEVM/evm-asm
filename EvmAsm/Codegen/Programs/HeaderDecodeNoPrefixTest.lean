/-
  EvmAsm.Codegen.Programs.HeaderDecodeNoPrefixTest

  **Why the `notlist` gate cannot be discharged inside the header decoders.**

  `rlp_walk_next`'s available contract is `.conditional` on the walked item's
  RLP prefix byte being `< 0xc0` — a byte string, not a LIST.  Both routines
  that `validate_header_rlp_pair` calls inherit that gate, and #12776 recorded
  the finding that neither can discharge it.  That finding lived only in issue
  prose; this module makes it a kernel-checked property of the two programs, so
  it survives the retirement of the walk (#12843, architecture A) and cannot
  drift away from the code it describes.

  The claim is *structural*, not "unproved-so-far": the gate is a property of
  the caller's input buffer, and no rearrangement of either routine's proof can
  witness it, because neither routine ever tests the byte.

  * `header_extended_decode_arity_check` performs **no sub-word load at all**
    (`arity_check_has_no_subword_load`).  All nine of its loads are `LD`.  It
    cannot isolate a prefix byte, so it cannot test one.

  * `header_extended_decode` does contain two byte loads, but both are the
    `LBU`/`SB` pair inside the shared 32-byte hash copy loop.  Both write `x6`
    (`subword_loads_write_x6`), and `x6` is never an operand of a conditional
    branch or an indirect jump (`never_branches_on_x6`).  The byte it reads
    is copied out, never compared.

  Note the second bullet is *not* the claim #12776 originally recorded.  That
  comment said "no `lbu` anywhere before a call", which is false as stated:
  there are two, at program indices 22 and 48, and both precede later
  `rlp_walk_next` call sites.  The claim that survives is the dataflow one —
  the byte is loaded and stored, and reaches no branch — and it is stronger,
  because it holds regardless of where in the routine the loads sit.

  Both statements are decided over the concrete `Program` literals, so they
  re-check whenever the emitter changes.  See `prefixTestingControl` at the
  bottom for the negative control: the codebase's actual prefix-testing idiom
  fails both predicates, which is what makes passing them evidence.
-/

import EvmAsm.Codegen.Programs.HeaderDecode
import EvmAsm.Rv64.SAsm.Sym
import EvmAsm.Rv64.RLP.Phase1

set_option maxRecDepth 8000

namespace EvmAsm.Codegen
namespace HeaderDecodeNoPrefixTest

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm (loadSem)

/-- The registers a conditional branch or an indirect jump *tests*.  A value
    that appears in no such list cannot influence control flow directly.

    This match is **exhaustive over the ISA**, which is what makes the theorems
    below say what they appear to say: `Instr` has exactly six conditional
    branches (`BEQ`/`BNE`/`BLT`/`BGE`/`BLTU`/`BGEU`) and one register-indirect
    jump (`JALR`); `JAL`'s only register operand is its link destination, and
    there are no compressed branch forms.  So a register absent from every
    `branchTests` list in a program influences that program's control flow
    nowhere. -/
def branchTests : Instr → List Reg
  | .BEQ a b _  => [a, b]
  | .BNE a b _  => [a, b]
  | .BLT a b _  => [a, b]
  | .BGE a b _  => [a, b]
  | .BLTU a b _ => [a, b]
  | .BGEU a b _ => [a, b]
  | .JALR _ a _ => [a]
  | _           => []

/-- The destination of a *sub-word* load — the only kind of instruction that can
    isolate a single RLP prefix byte out of a buffer.  `none` for everything
    else, including the full 8-byte `LD`, which cannot separate a prefix byte
    from the seven that follow it without further arithmetic. -/
def subwordDest (i : Instr) : Option Reg :=
  (loadSem i).bind fun op => if op.nbytes < 8 then some op.rd else none

/-! ### `header_extended_decode_arity_check`: no sub-word load exists -/

/-- The arity checker performs **no sub-word load at all**: all nine of its
    loads are full 8-byte `LD`, and there is no `LB`/`LBU`/`LH`/`LHU` anywhere
    in its 117 instructions.  It cannot isolate an RLP prefix byte even in
    principle, so `notlist` is not merely undischarged here — it is
    *unestablishable by this routine*, and that is a property of the whole
    instruction stream rather than of one call site's neighbourhood.

    Its `rlp_walk_next_leaf` call site agrees: `mv a0,s2 ; mv a1,s3 ; jal ;
    bnez a1,→fail`, with the only test on the returned status. -/
theorem arity_check_has_no_subword_load :
    ∀ i ∈ headerExtendedDecodeArityCheck_prog, subwordDest i = none := by
  decide

/-! ### `header_extended_decode`: the loaded byte is copied, never tested -/

/-- The decoder's only sub-word loads are the two `LBU` in the shared 32-byte
    hash copy loop, and both write `x6`. -/
theorem subword_loads_write_x6 :
    ∀ i ∈ headerExtendedDecode_prog,
      subwordDest i = none ∨ subwordDest i = some .x6 := by
  decide

/-- `x6` is never an operand of a conditional branch or an indirect jump.

    Together with `subword_loads_write_x6` this says the only byte the decoder
    reads reaches no control-flow decision: it is loaded by `LBU x6, 0(x28)`
    and consumed by the `SB` on the next instruction.  Each of the 19
    `rlp_walk_next` call sites is `mv a0,_ ; mv a1,_ ; jal ; mv _,a0 ;
    bnez a1,→fail` — the only test is on the *returned status*, after the
    fact, so no prefix-byte test exists to establish `notlist` with. -/
theorem never_branches_on_x6 :
    ∀ i ∈ headerExtendedDecode_prog, Reg.x6 ∉ branchTests i := by
  decide

/-! ### Negative control

    Both predicates above must be able to FAIL, or passing them says nothing.
    The control is the codebase's own prefix-testing idiom, not an invention:
    `LBU x5, 0(x13)` (the field-unit load of `Rv64/RLP/FieldUnitDisjoint.lean`)
    followed by the Phase-1 classifier cascade, which branches on `x5`. -/

/-- The real prefix-testing shape: load the byte, then classify it. -/
def prefixTestingControl : Program :=
  (.LBU .x5 .x13 (0 : BitVec 12)) ::
    RLP.rlp_phase1_classifier_prog (44 : BitVec 13) (52 : BitVec 13)
      (60 : BitVec 13) (68 : BitVec 13)

/-- Control: unlike the arity checker, this program *does* perform a sub-word
    load, so `arity_check_loads_are_dwords` is a real constraint. -/
theorem control_has_a_subword_load :
    ¬ (∀ i ∈ prefixTestingControl, subwordDest i = none) := by
  decide

/-- Control: unlike the decoder, this program *does* branch on the register its
    byte load writes, so `never_branches_on_x6` is a real constraint. -/
theorem control_branches_on_the_loaded_register :
    ¬ (∀ i ∈ prefixTestingControl, Reg.x5 ∉ branchTests i) := by
  decide

end HeaderDecodeNoPrefixTest
end EvmAsm.Codegen
