/-
  EvmAsm.Codegen.Programs.BhrRevLeBeSAsm

  Verified SAsm port of `bhr_rev_le_be` (bead evm-asm-4ch8f.12.5): reverse the
  first `len` little-endian bytes of `src` (a0) into big-endian order at `dst`
  (a2), `len` in a1.

  `bhrRevLeBe_prog` (BlockHeaderSszToRlp.lean) is **byte-identical** to
  `swrRevLeBe_prog` (SszWithdrawal.lean) — the same 11-instruction leaf emitted
  under two labels.  This module therefore reuses the verified generic
  `swrRevLeBeFn`/`swrRevLeBeFn_spec` (EvmAsm.Codegen.SwrRevLeBeSAsm) wholesale,
  and additionally kernel-pins byte-identity of the shared structured body to
  *this* routine's emitted program (`bhrRevLeBe_prog`), witnessing that the two
  labels denote the same code.

  Contract (see SwrRevLeBeSAsm for the full proof): `dst = (src[0..len)).reverse`
  over a read-only src region and a writable dst region that the precondition
  requires to be disjoint (reverse-copy into a separate buffer).  Spec-only
  module (no emitted-code change) — no EEST A/B required.
-/

import EvmAsm.Codegen.Programs.SwrRevLeBeSAsm
import EvmAsm.Codegen.Programs.BlockHeaderSszToRlp

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace BhrRevLeBeSAsm

open SwrRevLeBeSAsm

/-- `bhr_rev_le_be` as a verified SAsm `Fn`: identical to the `swr_rev_le_be`
    core (the two are the same emitted routine). -/
def bhrRevLeBeFn (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) : Fn :=
  swrRevLeBeFn src dst len bs orig

-- Byte-identity of the shared structured body to *this* routine's emitted
-- program: `bhrRevLeBe_prog = swrRevLeBe_prog` (same code, two labels).
#guard (swrRevLeBeBody 0 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0]
  = bhrRevLeBe_prog

/-- `bhr_rev_le_be` correctness: `dst = (src[0..len)).reverse`, with the src
    (read-only) and dst (writable, disjoint) regions well-formed.  Reuses the
    generic reverse proof. -/
theorem bhrRevLeBeFn_spec (src dst : Word) (len : Nat) (bs orig : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, len⟩) (base : Word) :
    (bhrRevLeBeFn src dst len bs orig).Spec base :=
  swrRevLeBeFn_spec src dst len bs orig hwf hrww base

end BhrRevLeBeSAsm

end EvmAsm.Codegen
