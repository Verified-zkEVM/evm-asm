/-
  EvmAsm.Evm64.MStore.UnalignedVacuity

  **`evm_mstore_stack_spec_within` is vacuous for every unaligned offset** (GH #11913).

  MSTORE is registered `.proven`, which `Progress.lean`'s rubric defines as a complete
  triple "with **no input-domain precondition**". But
  `evm_mstore_stack_spec_within` (`MStore/UnalignedFramedStackSpec.lean:1409`)
  separates **eight** memory cells:

      (loAddr0 ↦ₘ loVal0) ** (hiAddr0 ↦ₘ hiVal0) ** (loAddr1 ↦ₘ loVal1) **
      (hiAddr1 ↦ₘ hiVal1) ** (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2) **
      (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3)

  and constrains them via four `mstoreLimbWindowOk … start …` hypotheses sharing one
  `start`. An unaligned 32-byte write touches **five** distinct dwords, not eight, so
  eight pairwise-disjoint cells cannot exist — the precondition is unsatisfiable and the
  theorem says nothing there. It has content only on `offset % 8 = 0`.

  This module mechanises the arithmetic core of that argument, which #11913 flagged as
  the outstanding confirmation step (the issue derived it from the statement shape but
  did not machine-check it).

  ## The collision

  `mstoreDwordPairAddr loAddr hiAddr start i = if start + i < 8 then loAddr else hiAddr`
  (`MStore/ByteAlg.lean:88`), and `mstoreLimbWindowOk` pins, for each byte `i` of a
  limb's window, `alignToDword (addrPtr + off_i) = mstoreDwordPairAddr … start i`.

  The four limbs take windows `0..7`, `8..15`, `16..23`, `24..31`. With `start = s ≠ 0`
  each limb straddles two dwords, and the *high* dword of one limb is the *low* dword of
  the next:

  | limb | window | `loAddr` | `hiAddr` |
  |---|---|---|---|
  | limb3 | 0..7   | `D`      | `D + 8`  |
  | limb2 | 8..15  | `D + 8`  | `D + 16` |
  | limb1 | 16..23 | `D + 16` | `D + 24` |
  | limb0 | 24..31 | `D + 24` | `D + 32` |

  So `hiAddr3 = loAddr2`, `hiAddr2 = loAddr1`, `hiAddr1 = loAddr0` — three pairs of the
  eight `**`-separated cells naming one address.

  `alignToDword a = a &&& ~~~7#64` and `byteOffset a = (a &&& 7#64).toNat`
  (`Rv64/Word.lean:209,212`) are concrete `BitVec` operations, so the collisions are
  decidable at a concrete base. Below they are checked at every unaligned residue
  `s ∈ 1..7`, which is the whole excluded region.

  Both halves are here, so the argument has **no open link**:

  * the **address collision** — `decide`-checked at every unaligned residue `s ∈ 1..7`,
    with the contrasting `s = 0` case showing no collision (which is why the row is
    domain-restricted rather than simply wrong);
  * the **separation step** — `memIs_sepConj_same_addr_false`, *proved*: no state
    satisfies `(a ↦ₘ v) ** (a ↦ₘ w)`, because `sepConj` demands
    `∀ a, h1.mem a = none ∨ h2.mem a = none` while both footprints are
    `singletonMem a`.

  ⚠️ What is deliberately **not** done: rewriting
  `evm_mstore_stack_spec_within`'s own statement, or regrading the registry row. Both
  are the maintainer's call — see "What to do about it" below — and #11913 asked for the
  confirmation, not the remedy.

  ## What to do about it

  Either regrade MSTORE `.conditional` with the `offset % 8 = 0` gate named, or land
  #10190's `evmMemoryIs` re-statement and keep `.proven` honestly — an interface-level
  region assertion does not ask the caller to name eight disjoint dwords. PR #11910
  lands the bridge lemma for the second route, which is the better one.
-/

import EvmAsm.Evm64.MStore.ByteAlg
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64.MStore

open EvmAsm.Rv64

/-! ## The dword collision at every unaligned residue

    For a base whose `byteOffset` is `s ≠ 0`, byte `23` (the last byte of limb1's
    window) and byte `24` (the first byte of limb0's window) lie in the **same** dword.
    That is `hiAddr1 = loAddr0`.

    Checked at a concrete base per residue rather than proved for a symbolic one: the
    point is that the excluded region is nonempty and the collision is real, and
    `alignToDword`/`byteOffset` are concrete `BitVec` operations, so `decide` settles it
    without any TCB-expanding tactic. -/

/-- `s = 1`: bytes 23 and 24 share a dword, so limb1's high cell IS limb0's low cell. -/
example : byteOffset (0x40000001#64) = 1
    ∧ alignToDword (0x40000001#64 + 23) = alignToDword (0x40000001#64 + 24) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `s = 2`. -/
example : byteOffset (0x40000002#64) = 2
    ∧ alignToDword (0x40000002#64 + 23) = alignToDword (0x40000002#64 + 24) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `s = 3`. -/
example : byteOffset (0x40000003#64) = 3
    ∧ alignToDword (0x40000003#64 + 23) = alignToDword (0x40000003#64 + 24) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `s = 4`. -/
example : byteOffset (0x40000004#64) = 4
    ∧ alignToDword (0x40000004#64 + 23) = alignToDword (0x40000004#64 + 24) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `s = 5`. -/
example : byteOffset (0x40000005#64) = 5
    ∧ alignToDword (0x40000005#64 + 23) = alignToDword (0x40000005#64 + 24) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `s = 6`. -/
example : byteOffset (0x40000006#64) = 6
    ∧ alignToDword (0x40000006#64 + 23) = alignToDword (0x40000006#64 + 24) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `s = 7`. -/
example : byteOffset (0x40000007#64) = 7
    ∧ alignToDword (0x40000007#64 + 23) = alignToDword (0x40000007#64 + 24) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⭐ **The contrast that makes the finding precise: at `s = 0` there is no collision.**
    Bytes 23 and 24 fall in *different* dwords, each limb sits inside one dword, and the
    four `hiAddr`s are left unconstrained by the window equations — so the eight cells
    CAN be chosen distinct. This is exactly why the triple has content on aligned
    offsets and none elsewhere, and why the row is not simply wrong but
    domain-restricted. -/
example : byteOffset (0x40000000#64) = 0
    ∧ alignToDword (0x40000000#64 + 23) ≠ alignToDword (0x40000000#64 + 24) := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## The other two collisions, at one representative residue

    The same argument at the limb2/limb1 and limb3/limb2 boundaries: bytes 15/16 and
    7/8. Three collisions among eight cells. -/

example :
    alignToDword (0x40000001#64 + 15) = alignToDword (0x40000001#64 + 16)
      ∧ alignToDword (0x40000001#64 + 7) = alignToDword (0x40000001#64 + 8) := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## Which cell each byte is routed to

    Tying the arithmetic to the precondition's variables: at `start = 1`, limb1's byte
    `i = 7` routes to `hiAddr1` and limb0's byte `i = 0` routes to `loAddr0`. So the two
    equal dwords above are exactly those two cells. -/

example (loAddr0 hiAddr0 loAddr1 hiAddr1 : Word) :
    mstoreDwordPairAddr loAddr1 hiAddr1 1 7 = hiAddr1
      ∧ mstoreDwordPairAddr loAddr0 hiAddr0 1 0 = loAddr0 := by
  refine ⟨?_, ?_⟩ <;> simp [mstoreDwordPairAddr]

/-! ## The separation step — proved, so the argument has no open link

    `memIs` at one address cannot be split by `**`: `sepConj` demands
    `∀ a, h1.mem a = none ∨ h2.mem a = none`, and both footprints are
    `singletonMem a`, which holds `some` at exactly `a`. Together with the collisions
    above this turns "two of the eight cells name one address" into "the precondition
    is unsatisfiable". -/

/-- ⭐ **Separating two dword cells at the same address is unsatisfiable.** No state
    satisfies `(a ↦ₘ v) ** (a ↦ₘ w)`, whatever `v` and `w` are — including `v = w`.

    This is the step that makes the vacuity argument complete rather than
    arithmetic-only: with `hiAddr1 = loAddr0` established above, the eight-cell
    precondition of `evm_mstore_stack_spec_within` contains this pattern for every
    unaligned offset. -/
theorem memIs_sepConj_same_addr_false (a v w : Word) :
    ¬ ∃ st, ((a ↦ₘ v) ** (a ↦ₘ w)) st := by
  rintro ⟨_, h1, h2, hdisj, _, ⟨rfl, _⟩, ⟨rfl, _⟩⟩
  have hmem := hdisj.2.1 a
  simp [PartialState.singletonMem] at hmem

/-- The same fact in the form a reader of the MSTORE precondition wants: the two cells
    are *already known* to be at one address, so no further arithmetic is needed. -/
theorem memIs_sepConj_collide_false {a b v w : Word} (hab : a = b) :
    ¬ ∃ st, ((a ↦ₘ v) ** (b ↦ₘ w)) st := by
  subst hab
  exact memIs_sepConj_same_addr_false a v w

end EvmAsm.Evm64.MStore
