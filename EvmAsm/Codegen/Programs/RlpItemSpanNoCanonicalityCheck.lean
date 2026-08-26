/-
  EvmAsm.Codegen.Programs.RlpItemSpanNoCanonicalityCheck

  **Which of `decode_to_sequence`'s two canonicality checks `rlp_item_span`
  performs** — decided over the emitted program (#10780 item 1).

  The reference performs two checks on a long list header (`ethereum_rlp` 0.1.6,
  `rlp.py`):

  * `:436` — `encoded_sequence[1] == 0`, rejecting a leading-zero length field;
  * `:441` — `len_joined_encodings < 0x38`, rejecting the long form for a length
    the short form could express.

  The answer is **one of each**, and the split is the useful part.

  ## `:436` IS performed — indices 25-27 of the long-list arm

  ```
  25  ADDI x7, x8, 1      -- x7 := item pointer + 1
  26  LBU  x7, 0(x7)      -- read encoded_sequence[1]
  27  BEQ  x7, x0, →fail  -- reject if that byte is zero
  ```

  Reached after the `BLTU x5, 0xf8` at index 19 falls through, i.e. exactly on
  the long-list prefixes where the reference applies it.
  `leadingZeroCheck_is_performed` pins the three instructions.

  ⚠️ #10780's status note, and the first version of this module, claimed this
  check was *unexpressible* by the routine. That was wrong. The error came from
  counting instructions by regex over the Lean source, which gave 53
  instructions and one sub-word load; `rlpItemSpan_prog` actually has **57 and
  two**, the second at index 26 with base `x7`. `#eval` over the program gives
  the truth in one line. Two readers reached the same wrong census by the same
  method, which is why the count is now a theorem (`span_length`) rather than a
  remark.

  ## `:441` is NOT performed

  `spanNeverComparesAgainst0x38` — no instruction materialises `56` as an
  immediate. Inspecting the whole body, there is no computed comparison against
  it either: the only branches are `BGEU` against `x9` (the end pointer),
  `BEQ x22, x18` (the item counter), and the `BEQ x7, x0` above.

  ⚠️ The theorem rules out an **immediate**, not a computed value (a body with
  3 `ADD` and 2 `SUB` could in principle form `56` from other constants). The
  absence of a computed comparison is established by reading, not by this
  theorem.

  ## Scope

  Not a live false-accept: every `rlp_item_span` theorem has domain
  `bs = encode (.list items)`, where both conditions hold by construction, so
  nothing currently claims these inputs are rejected. And under #12843
  architecture A the eager `rlp_recursive_decode` family performs both checks at
  entry (`decodeD_long_bytes_zero` / `decodeD_long_bytes_small`, witnessed by
  #12862), so the remaining `:441` gap closes as a consequence of eager decoding
  rather than by adding a test to a routine on the retirement path.
-/

import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Rv64.SAsm.Sym

set_option maxRecDepth 4000

namespace EvmAsm.Codegen
namespace RlpItemSpanNoCanonicalityCheck

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm (loadSem)

/-- The immediate offset of a sub-word load — the only kind of instruction that
    can isolate one byte of an RLP header. -/
def subwordLoadOffset (i : Instr) : Option (BitVec 12) :=
  (loadSem i).bind fun op => if op.nbytes < 8 then some op.ofs else none

/-- Instruction count, as a theorem rather than a remark — a regex census of the
    source got this wrong (53) and took the sub-word-load count with it. -/
theorem span_length : rlpItemSpan_prog.length = 57 := by decide

/-! ### `rlp.py:436` is performed -/

/-- **The routine reads `encoded_sequence[1]` and rejects a zero there.**

    The three instructions at 25-27 are `ADDI x7, x8, 1` (item pointer plus
    one), `LBU x7, 0(x7)` (load that byte), `BEQ x7, x0` (branch away if it is
    zero) — the reference's leading-zero check, on the long-list arm. -/
theorem leadingZeroCheck_is_performed :
    rlpItemSpan_prog[25]? = some (.ADDI .x7 .x8 (1 : BitVec 12)) ∧
    rlpItemSpan_prog[26]? = some (.LBU .x7 .x7 (0 : BitVec 12)) ∧
    rlpItemSpan_prog[27]? = some (.BEQ .x7 .x0 (0x4c : BitVec 13)) := by
  refine ⟨by decide, by decide, by decide⟩

/-- Both sub-word loads carry immediate offset 0.

    ⚠️ This does NOT say the routine only reads the prefix byte: load 26's base
    is `x7`, computed as `x8 + 1` at index 25. Offset 0 is a property of the
    encoding, not of the effective address — the reason the first version of
    this module drew a false conclusion from it. -/
theorem subwordLoads_have_zero_offset :
    ∀ i ∈ rlpItemSpan_prog,
      subwordLoadOffset i = none ∨ subwordLoadOffset i = some (0 : BitVec 12) := by
  decide

/-- There are exactly two sub-word loads, at indices 15 and 26. -/
theorem subwordLoad_sites :
    (rlpItemSpan_prog.zipIdx.filter (fun p => (subwordLoadOffset p.1).isSome)).map Prod.snd
      = [15, 26] := by
  decide

/-! ### `rlp.py:441` is not performed -/

/-- Registers and immediates an instruction can carry a threshold constant in. -/
def immediateOperand : Instr → Option Word
  | .LI _ v      => some v
  | .ADDI _ _ v  => some (v.signExtend 64)
  | .SLTIU _ _ v => some (v.signExtend 64)
  | _            => none

/-- **`rlp.py:441`'s threshold is never written down.** No instruction
    materialises `56` as an immediate, so the routine does not compare a decoded
    length against the short/long boundary by that route. -/
theorem spanNeverComparesAgainst0x38 :
    ∀ i ∈ rlpItemSpan_prog, immediateOperand i ≠ some (56 : Word) := by
  decide

/-! ### Negative controls

    Both predicates must be able to fail, or passing them says nothing
    (#12857). -/

/-- Control: a program whose sub-word load reads offset 1 fails the offset
    predicate, so `subwordLoads_have_zero_offset` is a real constraint. -/
theorem offsetPredicate_control :
    ¬ (∀ i ∈ [Instr.LBU .x5 .x8 (1 : BitVec 12)],
        subwordLoadOffset i = none ∨
          subwordLoadOffset i = some (0 : BitVec 12)) := by
  decide

/-- Control: a program that DOES materialise the `0x38` threshold fails the
    immediate predicate. -/
theorem shortFormThreshold_control :
    ¬ (∀ i ∈ [Instr.LI .x6 (56 : Word)],
        immediateOperand i ≠ some (56 : Word)) := by
  decide

end RlpItemSpanNoCanonicalityCheck
end EvmAsm.Codegen
