/-
  EvmAsm.Codegen.Programs.Bn254Fp2EqSAsm

  SAsm port of `bnp_fp2_eq` (bead evm-asm-4ch8f.58.3.26): compare two
  64-byte (8-dword) BN254 Fp2 buffers at `a0`/`a1`, returning `a0 = 1` iff
  they are byte-identical. Byte-transparent: the verified body IS the emitted
  `bnpFp2Eq_prog` (`#guard`/`rfl`), an instantiation of the reusable
  dual-read dword equality scan (`DualReadScan.scan_spec`) at `N = 8`.
-/

import EvmAsm.Codegen.Programs.Bn254Fp2
import EvmAsm.Rv64.SAsm.DualReadScan

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace Bn254Fp2EqSAsm

-- Address anchor (semantic constant: 8 dwords = 64 bytes of Fp2).
#guard GuestAddrs.bnp_fp2_eq = 0x800308bc

/-- The `bnp_fp2_eq` body: the dual-read dword equality scan over 8 slots. -/
def bnpFp2EqBody (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Stmt :=
  DualReadScan.scanBody .x5 .x6 .x7 .x10 .x11 ptr1 ptr2 bs1 bs2 8

-- Byte-identity to the emitted `bnp_fp2_eq` program (byte-transparent port).
#guard (bnpFp2EqBody 0 0 [] []).flatten 0 = bnpFp2Eq_prog
#guard (bnpFp2EqBody 0 0 [] []).flatten 0x800308bc = bnpFp2Eq_prog
#guard (bnpFp2EqBody 0 0 [] []).retOffsetsOk

/-- Kernel-checked byte tie at the `#guard`-tied address. -/
theorem bnpFp2EqBody_flatten_eq (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) :
    (bnpFp2EqBody ptr1 ptr2 bs1 bs2).flatten (0x800308bc : Word) = bnpFp2Eq_prog := rfl

/-- **`bnp_fp2_eq`, whole-routine, at its linked address.** Genuine post:
    `a0 = 1` iff the two 64-byte Fp2 buffers are byte-equal. -/
theorem bnpFp2Eq_spec (ptr1 ptr2 ret : Word) (bs1 bs2 : List (BitVec 8))
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hwf1 : Region.wf ⟨ptr1, bs1⟩) (hwf2 : Region.wf ⟨ptr2, bs2⟩)
    (hlen1 : bs1.length = 64) (hlen2 : bs2.length = 64) :
    cpsTripleWithin (bnpFp2EqBody ptr1 ptr2 bs1 bs2).steps
      (0x800308bc : Word) ret
      (CodeReq.ofProg (0x800308bc : Word) bnpFp2Eq_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM (Region.mk ptr1 bs1) RwRegion.empty
        (DualReadScan.scanPre .x10 .x11 ptr1 ptr2 bs1 bs2 8))
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM (Region.mk ptr1 bs1) RwRegion.empty
        (DualReadScan.scanPost ptr2 bs1 bs2)) := by
  have h := DualReadScan.scan_spec (ctr := .x5) (tA := .x6) (tB := .x7)
    (pA := .x10) (pB := .x11) (ptrA := ptr1) (ptrB := ptr2)
    (bsA := bs1) (bsB := bs2) (N := 8)
    (0x800308bc : Word) ret
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    halign hwf1 hwf2 (by omega) (by omega)
  rw [show (DualReadScan.scanBody .x5 .x6 .x7 .x10 .x11 ptr1 ptr2 bs1 bs2
      8).flatten (0x800308bc : Word) = bnpFp2Eq_prog from rfl] at h
  exact h

#print axioms bnpFp2Eq_spec

end Bn254Fp2EqSAsm
end EvmAsm.Codegen
