/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose2

  Closing composition for the whole-program K137 contract
  `account_is_eip161_empty_spec_within` (`AccountFields.lean`).

  Builds on the three RLP call adapters + prologue + epilogue
  (`AccountIsEip161EmptyClose.lean`) and the three byte-scan loop lemmas
  (`AccountIsEip161EmptyLoop.lean`), composing the field-processing segments,
  the four-way verdict-store block, and the model tie into the top-level
  caller contract.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose

namespace EvmAsm.Codegen.AccountIsEip161EmptySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

/-! ## RLP content-span bound

    From K20's abstract `Success`, the selected field's content window
    `[offset, offset+len)` fits inside the account buffer.  Derived from the
    caller's `hbound` "buffer-fits" precondition (the same honest precondition
    the header callers carry, e.g. `HeaderReceiptsRootSpec.hbound`), fed through
    the last-decode extraction `aieLastDecodeBound`
    (template: `HeaderReceiptsRootSpec.herrLastDecodeBound`). -/

/-- From the final decode of a strict `index`-th item (in a `listLen`-window
    list), extract the last item's raw decode at some offset `off ≤ listLen`. -/
private theorem aieLastDecodeBound {base : Word} {bytes : List (BitVec 8)}
    {endOff : Nat} (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    ∀ {index startOff : Nat} {next len : Word},
      StrictNthItem bytes base (base + BitVec.ofNat 64 endOff)
        index startOff next len →
      startOff ≤ endOff →
      ∃ off, off ≤ endOff ∧ rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
        (base + BitVec.ofNat 64 endOff) next len := by
  intro index startOff next len h
  induction h with
  | zero off n l hi => exact fun hst => ⟨off, hst, hi⟩
  | succ i off n l fn fl hi hrest ih =>
      intro hst
      exact ih (EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_advance
        hi hst hover).2.2

/-- **Content-span bound.**  Given the buffer-fits precondition `hbound`, a
    successful field selection has its content window inside the buffer:
    `offset.toNat + len.toNat ≤ bytes.length`. -/
theorem aieSpanBound (bytes : List (BitVec 8)) (accBase : Word) (listLen index : Nat)
    (offset len : Word)
    (hover : accBase.toNat + listLen + 9 < 2 ^ 64)
    (hbound : ∀ o next len', o ≤ listLen →
      rlpItemDecode bytes o (accBase + BitVec.ofNat 64 o)
        (accBase + BitVec.ofNat 64 listLen) next len' →
      (next - len' - accBase).toNat + len'.toNat ≤ bytes.length)
    (hsucc : Success bytes accBase listLen index offset len) :
    offset.toNat + len.toNat ≤ bytes.length := by
  obtain ⟨cursorOff, endPtr, next, hpay, hnth, hoff⟩ := hsucc
  have hend := hpay.end_eq
  subst hend
  have hcle := hpay.cursor_le
  obtain ⟨off, hoffle, hdec⟩ := aieLastDecodeBound hover hnth hcle
  rw [hoff]
  exact hbound off next len hoffle hdec

#print axioms aieSpanBound

end EvmAsm.Codegen.AccountIsEip161EmptySpec
