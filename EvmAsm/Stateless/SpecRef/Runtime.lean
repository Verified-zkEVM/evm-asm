/-
  EvmAsm.Stateless.SpecRef.Runtime

  Lean functional *reference port* of `execution-specs @ tests-zkevm@v0.4.0`
  `src/ethereum/forks/amsterdam/vm/runtime.py` — the runtime helpers used
  while executing EVM code.  Feeder for bead `evm-asm-4ch8f.49.2`: it is the
  mathematical spec anchor for the dispatcher's jumpdest-bitmap prologue
  (`EvmAsm/Codegen/Dispatch.lean` `emitJumpdestBitmapBuild`) and for the
  JUMP/JUMPI validity tail (`.55`).  Reference model only — no theorems about
  the RV64 guest live here.

  Currently ports the single function `get_valid_jump_destinations`.
-/
import EvmAsm.EL.RLP.Basic

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (Byte)

/-! ## `get_valid_jump_destinations`

Code is a `List Byte` (matching `SpecRef.Crypto`'s `Bytes`, but stated
inline here so this module stays decoupled from the crypto/accel imports —
the JUMP/JUMPI tail `.55` consumes it without pulling ZisK).

The Python analyses the code with a single forward pass over instruction
*boundaries*, starting at `pc = 0`:

* `JUMPDEST` (`0x5b`) → the boundary is a valid jump destination; `pc += 1`.
* `PUSH1..PUSH32` (`0x60..0x7f`) → skip the opcode and its `n = op-0x5f`
  immediate bytes: `pc += (op - 0x60 + 1) + 1`.  A `0x5b` *inside* the
  immediate data is therefore never a boundary and never valid.
* EIP-8024 `DUPN`/`SWAPN` (`0xe6`/`0xe7`) → if the next byte exists and lies in
  the *invalid* immediate range `0x5b..0x7f` the immediate is **not** skipped
  (the byte stays an instruction boundary): `pc += 1`.  Otherwise skip the
  immediate: `pc += 2`.
* EIP-8024 `EXCHANGE` (`0xe8`) → same, with invalid immediate range
  `0x52..0x7f`.
* any other byte → `pc += 1`.  (The Python distinguishes a valid non-listed
  opcode, which advances `pc += 1`, from an invalid byte, whose `ValueError`
  path also advances `pc += 1` before `continue`.  Both advance by exactly one
  and add no destination, so a single "else `+1`" arm faithfully covers both.)

We factor the boundary step into `jdAdvance` (the amount `pc` moves, always
`≥ 1`) and record the visited-and-`0x5b` boundaries in `validJumpDestinations`.
-/

/-- The amount the boundary pointer advances at `pc`, mirroring one iteration
    of `get_valid_jump_destinations`.  Always `≥ 1` (see `jdAdvance_pos`), so
    the analysis terminates and — in the guest — the scan variant `end - pc`
    strictly decreases on every arm. -/
def jdAdvance (code : List Byte) (pc : Nat) : Nat :=
  let op := (code.getD pc 0).toNat
  if op = 0x5b then 1
  else if 0x60 ≤ op ∧ op ≤ 0x7f then (op - 0x60 + 1) + 1
  else if op = 0xe6 ∨ op = 0xe7 then
    (if pc + 1 < code.length
        ∧ 0x5b ≤ (code.getD (pc + 1) 0).toNat ∧ (code.getD (pc + 1) 0).toNat ≤ 0x7f
     then 1 else 2)
  else if op = 0xe8 then
    (if pc + 1 < code.length
        ∧ 0x52 ≤ (code.getD (pc + 1) 0).toNat ∧ (code.getD (pc + 1) 0).toNat ≤ 0x7f
     then 1 else 2)
  else 1

/-- Every arm of the boundary step advances the pointer by at least one byte.
    This is the per-arm "≥1 advance" fact the jumpdest-scan loop variant
    (`end - pc`) relies on. -/
theorem jdAdvance_pos (code : List Byte) (pc : Nat) : 1 ≤ jdAdvance code pc := by
  simp only [jdAdvance]
  repeat' split
  all_goals omega

/-- Boundary walk with an explicit `fuel` budget.  Because every step advances
    `pc` by `≥ 1`, `fuel = code.length` suffices to reach the end (see
    `validJumpDestinations`). -/
def validJDaux (code : List Byte) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, pc =>
    if pc < code.length then
      let rest := validJDaux code fuel (pc + jdAdvance code pc)
      if (code.getD pc 0).toNat = 0x5b then pc :: rest else rest
    else []

/-- The set of valid jump destinations of `code`, as a list of 0-indexed
    positions (the Python returns a `Set[Uint]`; membership is decidable, so a
    list is an adequate reference model).  Faithful port of
    `get_valid_jump_destinations`. -/
def validJumpDestinations (code : List Byte) : List Nat :=
  validJDaux code code.length 0

/-- Decidable membership view, convenient as a bitmap post
    (`bit idx set ⟺ isValidJumpDest code idx`). -/
def isValidJumpDest (code : List Byte) (idx : Nat) : Bool :=
  idx ∈ validJumpDestinations code

/-! ## Characterization

Every position the walk records is in-bounds and holds the `JUMPDEST` opcode.
This is the load-bearing fact for the JUMP/JUMPI validity tail (`.55`): a
destination that passes the O(1) bitmap test is necessarily a `0x5b` byte at an
instruction boundary — the pushdata/immediate skips are what make it sound. -/
theorem validJDaux_mem (code : List Byte) (fuel pc : Nat) {idx : Nat}
    (h : idx ∈ validJDaux code fuel pc) :
    idx < code.length ∧ (code.getD idx 0).toNat = 0x5b := by
  induction fuel generalizing pc with
  | zero => simp [validJDaux] at h
  | succ f ih =>
    unfold validJDaux at h
    split at h
    · next hlt =>
      simp only at h
      split at h
      · next hjd =>
        rcases List.mem_cons.1 h with rfl | h'
        · exact ⟨hlt, hjd⟩
        · exact ih _ h'
      · exact ih _ h
    · simp at h

/-- A valid jump destination is an in-bounds `JUMPDEST` (`0x5b`) byte. -/
theorem mem_validJumpDestinations (code : List Byte) {idx : Nat}
    (h : idx ∈ validJumpDestinations code) :
    idx < code.length ∧ (code.getD idx 0).toNat = 0x5b :=
  validJDaux_mem code code.length 0 h

end EvmAsm.Stateless.SpecRef
