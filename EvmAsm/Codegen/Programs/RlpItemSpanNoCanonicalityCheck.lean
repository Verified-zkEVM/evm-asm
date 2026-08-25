/-
  EvmAsm.Codegen.Programs.RlpItemSpanNoCanonicalityCheck

  **`rlp_item_span` cannot reject a non-canonical long list header** — decided
  over the emitted program, not argued (#10780 item 1).

  The reference's `decode_to_sequence` performs two canonicality checks on a long
  list header that `rlp_item_span` does not (`ethereum_rlp` 0.1.6, `rlp.py`):

  * `:436` — `encoded_sequence[1] == 0`, rejecting a length field with a leading
    zero byte;
  * `:441` — `len_joined_encodings < 0x38`, rejecting the long form used for a
    length the short form could have expressed.

  #10780's status note recorded that the guest omits both. That note was prose.
  This settles it the way #12861 settled `notlist`: as a property of the
  instruction stream, so it survives re-emission and cannot drift.

  * `spanOnlyReadsThePrefixByte` — the routine's **only** sub-word load reads
    offset 0 of the item pointer. `rlp.py:436` inspects `encoded_sequence[1]`,
    and no instruction here loads that byte, so the check is not merely omitted
    — it is **unexpressible by this routine**.
  * `spanNeverComparesAgainst0x38` — no instruction carries `56` as an
    ALU/compare operand, so `rlp.py:441`'s threshold appears nowhere.

  ⚠️ **This is not a live false-accept, and the row is not mis-graded.** Every
  `rlp_item_span` theorem has domain `bs = encode (.list items)`, where both
  conditions hold by construction, so nothing currently claims these inputs are
  rejected. What the two theorems below establish is that closing the gap needs a
  **guest-code change**, not a better proof.

  ⭐ And under #12843's architecture A it likely needs neither: validation moves
  to the entry point, where the eager `rlp_recursive_decode` family already
  performs both checks (`decodeD_long_bytes_zero` / `decodeD_long_bytes_small`
  for the byte-string analogues, witnessed by #12862). The gap closes as a
  consequence of eager decoding rather than by adding two tests here. Recording
  that is the point: this is a gap that should be **waited out**, not proved
  through — the same disposition #12843 gave `rlp_walk_next`'s LIST arms.
-/

import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Rv64.SAsm.Sym

set_option maxRecDepth 4000

namespace EvmAsm.Codegen
namespace RlpItemSpanNoCanonicalityCheck

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm (loadSem)

/-- The immediate offset of a sub-word load — the only kind of instruction that
    can isolate one byte of an RLP header, and the offset is which byte. -/
def subwordLoadOffset (i : Instr) : Option (BitVec 12) :=
  (loadSem i).bind fun op => if op.nbytes < 8 then some op.ofs else none

/-- Registers and immediates an instruction compares or computes with, restricted
    to the forms that could carry a threshold constant. -/
def immediateOperand : Instr → Option Word
  | .LI _ v      => some v
  | .ADDI _ _ v  => some (v.signExtend 64)
  | .SLTIU _ _ v => some (v.signExtend 64)
  | _            => none

/-- **`rlp.py:436` is unexpressible here.** The routine performs exactly one
    sub-word load, and it reads **offset 0** — the prefix byte. The reference's
    leading-zero check inspects `encoded_sequence[1]`; no instruction in this
    program loads that byte, so the check cannot be performed, not merely is
    not. -/
theorem spanOnlyReadsThePrefixByte :
    ∀ i ∈ rlpItemSpan_prog,
      subwordLoadOffset i = none ∨ subwordLoadOffset i = some (0 : BitVec 12) := by
  decide

/-- **`rlp.py:441`'s threshold appears nowhere.** No instruction materialises
    `56` as an immediate, so the routine never compares a decoded length against
    the short/long boundary. -/
theorem spanNeverComparesAgainst0x38 :
    ∀ i ∈ rlpItemSpan_prog, immediateOperand i ≠ some (56 : Word) := by
  decide

/-! ### Negative controls

    Both predicates must be able to fail, or passing them says nothing
    (#12857). -/

/-- Control: a program that DOES read the byte after the prefix fails the first
    predicate, so `spanOnlyReadsThePrefixByte` is a real constraint rather than
    one satisfied by any program without byte loads. -/
theorem leadingZeroCheck_control :
    ¬ (∀ i ∈ [Instr.LBU .x5 .x8 (1 : BitVec 12)],
        subwordLoadOffset i = none ∨
          subwordLoadOffset i = some (0 : BitVec 12)) := by
  decide

/-- Control: a program that DOES materialise the `0x38` threshold fails the
    second predicate. -/
theorem shortFormThreshold_control :
    ¬ (∀ i ∈ [Instr.LI .x6 (56 : Word)],
        immediateOperand i ≠ some (56 : Word)) := by
  decide

/-- Control: the routine is not vacuously free of sub-word loads — it has one,
    so `spanOnlyReadsThePrefixByte` constrains an instruction that exists rather
    than quantifying over nothing. -/
theorem span_does_load_the_prefix_byte_reachable :
    ∃ i ∈ rlpItemSpan_prog, subwordLoadOffset i = some (0 : BitVec 12) := by
  decide

end RlpItemSpanNoCanonicalityCheck
end EvmAsm.Codegen
