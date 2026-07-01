/-
  EvmAsm.Rv64.SAsm.Flatten

  Flattening structured SAsm statements to plain instruction lists.  All
  branch and jump offsets are synthesized from statement sizes; the emitted
  `Program` plugs into the existing codegen pipeline and its `CodeReq` is a
  single `CodeReq.ofProg` per function (no manual disjointness proofs).

  Layouts (docs/sasm-design.md §3.7), all sizes in instructions:

    block _ is        is                                     is.length
    ite c t e         B¬c → Lelse · t · J → Lend · e         t.size+e.size+2
    when c b          B¬c → Lend  · b                        b.size+1
    while c n _ b     Lhdr: B¬c → Lend · b · J → Lhdr        b.size+2
    call _ callee     JAL x1, (callee − pc)                  1
    assert _ _        (nothing)                              0

  Offset-range side-conditions are collected by the decidable `offsetsOk`
  well-formedness check; the VC generator (M3) re-emits them as labeled VCs
  that `decide` closes.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SAsm.Ast

namespace EvmAsm.Rv64
namespace SAsm
namespace Stmt

/-- Byte distance of `n` instructions, as a branch offset (13-bit). -/
def brOfs (n : Nat) : BitVec 13 := BitVec.ofNat 13 (4 * n)

/-- Byte distance of `n` instructions forward, as a jump offset (21-bit). -/
def jFwd (n : Nat) : BitVec 21 := BitVec.ofNat 21 (4 * n)

/-- Byte distance of `n` instructions backward, as a jump offset (21-bit),
    in two's complement (`0 < 4*n ≤ 2^20` for a valid backward branch). -/
def jBack (n : Nat) : BitVec 21 := BitVec.ofNat 21 (2 ^ 21 - 4 * n)

/-- Flatten a statement placed at address `addr` to machine instructions.
    `addr` is only consulted by `call` (to compute the pc-relative JAL
    offset); everything else is position-independent. -/
def flatten (addr : Word) : Stmt → List Instr
  | block _ is =>
      is
  | seq a b =>
      a.flatten addr ++ b.flatten (addr + BitVec.ofNat 64 (4 * a.size))
  | ite _ c t e =>
      c.neg.toInstr (brOfs (t.size + 2))
        :: (t.flatten (addr + 4)
            ++ .JAL .x0 (jFwd (e.size + 1))
            :: e.flatten (addr + BitVec.ofNat 64 (4 * (t.size + 2))))
  | when _ c b =>
      c.neg.toInstr (brOfs (b.size + 1)) :: b.flatten (addr + 4)
  | assert _ _ =>
      []
  | «while» _ c _ _ b =>
      c.neg.toInstr (brOfs (b.size + 2))
        :: (b.flatten (addr + 4) ++ [.JAL .x0 (jBack (b.size + 1))])
  | call _ f =>
      [.JAL .x1 (BitVec.setWidth 21 (f.entry - addr))]

/-- The flattened code of a statement occupies exactly `size` slots. -/
theorem flatten_length (s : Stmt) (addr : Word) :
    (s.flatten addr).length = s.size := by
  induction s generalizing addr with
  | block _ is => rfl
  | seq a b iha ihb =>
      simp [flatten, size, iha, ihb]
  | ite _ c t e iht ihe =>
      simp [flatten, size, iht, ihe]; omega
  | «when» _ c b ihb =>
      simp [flatten, size, ihb]
  | assert _ _ => rfl
  | «while» _ c fuel inv b ihb =>
      simp [flatten, size, ihb]
  | call _ callee => rfl

/-- Decidable well-formedness: every synthesized offset fits its immediate
    field, and every branch condition reads only exposed registers (or x0).

    Ranges: conditional branches carry a signed 13-bit byte offset (positive
    forward targets need `4*n < 2^12`); jumps carry a signed 21-bit byte
    offset (`4*n < 2^20` forward, `4*n ≤ 2^20` backward). -/
def offsetsOk : Stmt → Bool
  | block _ _ => true
  | seq a b => a.offsetsOk && b.offsetsOk
  | ite _ c t e =>
      c.wf && decide (4 * (t.size + 2) < 2^12)
           && decide (4 * (e.size + 1) < 2^20)
           && t.offsetsOk && e.offsetsOk
  | when _ c b =>
      c.wf && decide (4 * (b.size + 1) < 2^12) && b.offsetsOk
  | assert _ _ => true
  | «while» _ c _ _ b =>
      c.wf && decide (4 * (b.size + 2) < 2^12)
           && decide (4 * (b.size + 1) ≤ 2^20)
           && b.offsetsOk
  | call _ _ => true

/-- Address-aware side conditions of the call sites of a statement placed at
    `addr`: each `jal` offset round-trips through its 21-bit immediate, the
    return address is aligned, and the callee's code does not sit on the
    call instruction itself.  Decidable for concrete layouts (`decide`),
    `bv_omega` for relative ones. -/
def callsOk : Stmt → Word → Prop
  | block _ _, _ => True
  | seq a b, addr =>
      a.callsOk addr ∧ b.callsOk (addr + BitVec.ofNat 64 (4 * a.size))
  | ite _ _ t e, addr =>
      t.callsOk (addr + 4) ∧ e.callsOk (addr + BitVec.ofNat 64 (4 * (t.size + 2)))
  | when _ _ b, addr => b.callsOk (addr + 4)
  | assert _ _, _ => True
  | «while» _ _ _ _ b, addr => b.callsOk (addr + 4)
  | call _ f, addr =>
      addr + signExtend21 (BitVec.setWidth 21 (f.entry - addr)) = f.entry
      ∧ ((addr + 4) &&& ~~~(1 : Word)) = addr + 4
      ∧ f.code addr = none

end Stmt
end SAsm
end EvmAsm.Rv64
