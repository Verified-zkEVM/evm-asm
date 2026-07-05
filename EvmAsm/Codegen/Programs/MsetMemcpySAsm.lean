/-
  EvmAsm.Codegen.Programs.MsetMemcpySAsm

  Verified SAsm port of `mset_memcpy` (bead evm-asm-4ch8f.12.1): copy `len`
  bytes forward from `src` (a1) to `dst` (a0).

  `msetMemcpy_prog` (MptSet.lean) has the **same loop body and register roles**
  as `sg_memcpy` (x10=dst, x11=src, x12=len; `LBU x5,(x11); SB (x10),x5;
  x10++; x11++; x12--`), and the same net effect `dst = src[0..len)`.  It
  differs only in loop *shape*: `mset_memcpy` is a **pre-guarded do-while**
  (a top `BEQ x12,x0` that runs once as the entry guard, then the body, then a
  bottom `BNE x12,x0` back-edge to the body, then a separate `ret`), whereas a
  structured `.«while»` is a top-tested loop (guard, body, `JAL` back to the
  guard).  Both execute the body exactly `len` times — semantically identical.

  This module therefore **reuses the verified generic core** of
  `EvmAsm.Codegen.SgMemcpySAsm` (`sgMemcpyFn`/`sgMemcpyFn_spec`,
  `dst = src.take len`, src/dst-disjoint precondition) wholesale.

  Byte-identity: NOT claimed.  The structured flatten and `msetMemcpy_prog`
  agree on the entry `BEQ` guard (offset 28) and all five body instructions,
  but diverge at the back-edge — the structured loop emits a single
  `JAL x0 -24` (to the guard) where `msetMemcpy_prog` emits `BNE x12 x0 -20`
  (to the body) followed by an explicit `JALR` return.  The explicit structured
  flatten is pinned below (and `msetMemcpy_prog.length` recorded) with the
  divergence documented; the functional spec is not weakened.  Spec-only module
  (no emitted-code change) — no EEST A/B.
-/

import EvmAsm.Codegen.Programs.SgMemcpySAsm
import EvmAsm.Codegen.Programs.MptSet

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace MsetMemcpySAsm

open SgMemcpySAsm

/-- `mset_memcpy` as a verified SAsm `Fn`: identical to the `sg_memcpy` core
    (same body, registers, and net effect). -/
def msetMemcpyFn (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) : Fn :=
  sgMemcpyFn src dst len bs orig

-- The structured `.«while»` flatten (7 instrs): agrees with `msetMemcpy_prog`
-- on the entry guard (`BEQ x12 x0 28`) and the five body instructions, but the
-- back-edge is a single `JAL x0 -24` (to the guard) where the emitted routine
-- uses `BNE x12 x0 -20` (do-while back-edge to the body) + a separate `JALR`.
#guard (sgMemcpyBody 0 0 0 [] []).flatten 0 =
  [.BEQ .x12 .x0 (28 : BitVec 13),
   .LBU .x5 .x11 0, .SB .x10 .x5 0, .ADDI .x10 .x10 1, .ADDI .x11 .x11 1,
   .ADDI .x12 .x12 (-1 : BitVec 12),
   .JAL .x0 (-24 : BitVec 21)]
-- For reference, the emitted routine (`msetMemcpy_prog`, 8 instrs incl. ret):
--   BEQ x12 x0 28, LBU x5 x11 0, SB x10 x5 0, ADDI x10 x10 1, ADDI x11 x11 1,
--   ADDI x12 x12 -1, BNE x12 x0 -20, JALR x0 x1 0
#guard msetMemcpy_prog.length = 8

/-- `mset_memcpy` correctness: `dst = src[0..len)`, with the src (read-only) and
    dst (writable, disjoint) regions well-formed.  Reuses the generic forward-
    copy proof. -/
theorem msetMemcpyFn_spec (src dst : Word) (len : Nat) (bs orig : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, len⟩) (base : Word) :
    (msetMemcpyFn src dst len bs orig).Spec base :=
  sgMemcpyFn_spec src dst len bs orig hwf hrww base

end MsetMemcpySAsm

end EvmAsm.Codegen
