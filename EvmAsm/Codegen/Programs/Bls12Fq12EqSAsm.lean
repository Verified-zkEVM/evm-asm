/-
  EvmAsm.Codegen.Programs.Bls12Fq12EqSAsm

  SAsm port of `blq_eq` (bead evm-asm-4ch8f.58.3.25): compare two 576-byte
  (72-dword) BLS12-381 FQ12 buffers at `a0`/`a1`, returning `a0 = 1` iff they are
  byte-identical.  Byte-transparent: the verified body IS the emitted
  `blqEq_prog` (`#guard`/`rfl`), an instantiation of the reusable dual-read
  dword equality scan (`DualReadScan.scan_spec`) at `ctr = t0`, `tA = t1`,
  `tB = t2`, `pA = a0`, `pB = a1`, `N = 72` — the genuine post is real
  byte-list equality via the per-dword ⇔ byte-list bridge.
-/

import EvmAsm.Codegen.Programs.Bls12Fq12
import EvmAsm.Rv64.SAsm.DualReadScan

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace Bls12Fq12EqSAsm

-- Address anchor (semantic constant: 72 dwords = 576 bytes of FQ12).
#guard GuestAddrs.blq_eq = 0x80034864

/-- The `blq_eq` body: the dual-read dword equality scan over 72 slots. -/
def blqEqBody (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Stmt :=
  DualReadScan.scanBody .x5 .x6 .x7 .x10 .x11 ptr1 ptr2 bs1 bs2 72

-- Byte-identity to the emitted `blq_eq` program (byte-transparent port).
#guard (blqEqBody 0 0 [] []).flatten 0 = blqEq_prog
#guard (blqEqBody 0 0 [] []).flatten 0x80034864 = blqEq_prog
#guard (blqEqBody 0 0 [] []).retOffsetsOk

/-- Kernel-checked byte tie at the `#guard`-tied address. -/
theorem blqEqBody_flatten_eq (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) :
    (blqEqBody ptr1 ptr2 bs1 bs2).flatten (0x80034864 : Word) = blqEq_prog := rfl

/-- **`blq_eq`, whole-routine, at its linked address.**  Genuine post:
    `a0 = 1` iff the two 576-byte FQ12 buffers are byte-equal. -/
theorem blqEq_spec (ptr1 ptr2 ret : Word) (bs1 bs2 : List (BitVec 8))
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hwf1 : Region.wf ⟨ptr1, bs1⟩) (hwf2 : Region.wf ⟨ptr2, bs2⟩)
    (hlen1 : bs1.length = 576) (hlen2 : bs2.length = 576) :
    cpsTripleWithin (blqEqBody ptr1 ptr2 bs1 bs2).steps
      (0x80034864 : Word) ret
      (CodeReq.ofProg (0x80034864 : Word) blqEq_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM (Region.mk ptr1 bs1) RwRegion.empty
        (DualReadScan.scanPre .x10 .x11 ptr1 ptr2 bs1 bs2 72))
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM (Region.mk ptr1 bs1) RwRegion.empty
        (DualReadScan.scanPost ptr2 bs1 bs2)) := by
  have h := DualReadScan.scan_spec (ctr := .x5) (tA := .x6) (tB := .x7)
    (pA := .x10) (pB := .x11) (ptrA := ptr1) (ptrB := ptr2)
    (bsA := bs1) (bsB := bs2) (N := 72)
    (0x80034864 : Word) ret
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    halign hwf1 hwf2 (by omega) (by omega)
  rw [show (DualReadScan.scanBody .x5 .x6 .x7 .x10 .x11 ptr1 ptr2 bs1 bs2
      72).flatten (0x80034864 : Word) = blqEq_prog from rfl] at h
  exact h

#print axioms blqEq_spec

end Bls12Fq12EqSAsm
end EvmAsm.Codegen
