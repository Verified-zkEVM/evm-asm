/-
  EvmAsm.Evm64.Terminating.ReturnHaltResolved

  **RETURN's `la` reconstruction hypotheses, retired** (bead evm-asm-85699,
  acceptance (b)).

  `evm_return_halt_spec_within` and `evm_return_stack_spec_within` carry
  the linker `la`s (`evm_halt_flag`, `.Ldispatch_resume`,
  `system_call_mode`, `evm_memory` ×2) as ASSUMED hypotheses
  (`hla1`/`hla2`/`hlaSCM`/`hlaMem`/`hlaMem2`) of the form

  ```
    pc + ((hi.zeroExtend 32) <<< 12).signExtend 64 + signExtend12 lo = sym
  ```

  This module restates both specs with the immediates COMPUTED by the `la`
  resolution model (`laHi`/`laLo`, `EvmAsm/Rv64/LaResolve.lean`) and the
  former hypotheses PROVEN by `la_resolve`.  What remains per `la` is only
  `laInRange pc sym` — representability of the displacement, a decidable
  fact of the linked layout (a few MB in practice) — instead of the full
  materialization arithmetic.  This removes the `la`-reconstruction
  residual from the RETURN `.conditional` spec (the byte-check now only
  has to confirm the ELF's immediates equal `laHi`/`laLo`, which is what
  an assembler computes anyway); the spec's OTHER residuals (reachable
  precondition, memory-gas preBody branch) are untouched.
-/

import EvmAsm.Evm64.Terminating.ReturnSpec
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Evm64.Terminating

open EvmAsm.Rv64

/-- **The RETURN/REVERT halt core with the `la`s resolved**: immediates
    computed by `laHi`/`laLo`; the former `hla2`/`hla1` are `la_resolve`
    facts.  Only displacement representability remains per `la`. -/
theorem evm_return_halt_spec_resolved (hbase flag resume v5 v6 v1 f0 : Word)
    (hr2 : laInRange (hbase + 4) flag)
    (hr1 : laInRange (hbase + 16) resume) :
    cpsTripleWithin 7 hbase (resume &&& ~~~1)
      (CodeReq.ofProg hbase (evm_return_halt
        (laHi (hbase + 4) flag) (laLo (hbase + 4) flag)
        (laHi (hbase + 16) resume) (laLo (hbase + 16) resume)))
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ v1) ** (flag ↦ₘ f0))
      ((.x5 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ flag) ** (.x1 ↦ᵣ resume) **
        (flag ↦ₘ (2 : Word))) :=
  evm_return_halt_spec_within
    (laHi (hbase + 4) flag) (laLo (hbase + 4) flag)
    (laHi (hbase + 16) resume) (laLo (hbase + 16) resume)
    hbase flag resume v5 v6 v1 f0
    (la_resolve (hbase + 4) flag hr2)
    (la_resolve (hbase + 16) resume hr1)

/-- **The full RETURN tail with all five `la`s resolved**
    (`system_call_mode`, `evm_memory` ×2, `evm_halt_flag`,
    `.Ldispatch_resume`): the `hlaSCM`/`hlaMem`/`hlaMem2`/`hla2`/`hla1`
    reconstruction hypotheses of `evm_return_stack_spec_within` are now
    `la_resolve` facts; per `la` only `laInRange` (decidable
    representability) remains.  All other hypotheses/residuals of the
    `.conditional` spec are unchanged. -/
theorem evm_return_stack_spec_resolved
    {hiLen : BitVec 20} {loLen : BitVec 12} {hiRd : BitVec 20} {loRd : BitVec 12}
    (hbase p scmAddr evmMemBase flag resume : Word)
    (off size x1o x5o x6o x14o x15o x16o x17o x19o x21o x22o x23o f0 : Word)
    (descInit memBytes : List (BitVec 8))
    (hDescLen : descInit.length = 256)
    (hSrcAlign : evmMemBase.toNat % 8 = 0)
    (hSrcOver : evmMemBase.toNat + memBytes.length < 2 ^ 64)
    (hSrcValid : ∀ k, k < memBytes.length →
      isValidByteAccess (evmMemBase + BitVec.ofNat 64 k) = true)
    (hOff : off.toNat + (returnClamp size).toNat ≤ memBytes.length)
    (hOff32 : off.toNat + (returnClamp32 size).toNat ≤ memBytes.length)
    (hrSCM : laInRange (hbase + 8) scmAddr)
    (hrMem : laInRange (hbase + 160) evmMemBase)
    (hrMem2 : laInRange (hbase + 208) evmMemBase)
    (hr2 : laInRange (hbase + 276 + 4) flag)
    (hr1 : laInRange (hbase + 276 + 16) resume) :
    cpsTripleWithin (154 + 7 * (returnClamp size).toNat + 7 * (returnClamp32 size).toNat)
      hbase (resume &&& ~~~1)
      (CodeReq.ofProg hbase (returnTailProg
        (laHi (hbase + 8) scmAddr) (laLo (hbase + 8) scmAddr)
        hiLen loLen hiRd loRd
        (laHi (hbase + 160) evmMemBase) (laLo (hbase + 160) evmMemBase)
        (laHi (hbase + 208) evmMemBase) (laLo (hbase + 208) evmMemBase)
        (laHi (hbase + 276 + 4) flag) (laLo (hbase + 276 + 4) flag)
        (laHi (hbase + 276 + 16) resume) (laLo (hbase + 276 + 16) resume)))
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5o) **
        ((.x6 : Reg) ↦ᵣ x6o) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ x14o) **
        ((.x15 : Reg) ↦ᵣ x15o) ** ((.x16 : Reg) ↦ᵣ x16o) ** ((.x17 : Reg) ↦ᵣ x17o) **
        ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o) **
        ((.x23 : Reg) ↦ᵣ x23o) ** ((p + signExtend12 0) ↦ₘ off) **
        ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)) **
        (flag ↦ₘ f0) ** bytesRegion returnDescBase descInit **
        bytesRegion evmMemBase memBytes)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ resume) ** ((.x5 : Reg) ↦ᵣ (2 : Word)) **
        ((.x6 : Reg) ↦ᵣ flag) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
        ((.x15 : Reg) ↦ᵣ size) ** ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ (1 : Word)) **
        ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (returnClamp32 size).toNat)) **
        ((.x21 : Reg) ↦ᵣ (32 : Word)) ** ((.x22 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x23 **
        ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
        ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)) ** (flag ↦ₘ (2 : Word)) **
        bytesRegion returnDescBase
          (setBytes
            (copyIntoRegion
              (copyIntoRegion
                (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
                  (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
              memBytes 0 off.toNat (returnClamp32 size).toNat) 32 (dwordBytes (1 : Word))) **
        bytesRegion evmMemBase memBytes) :=
  evm_return_stack_spec_within
    (hiSCM := laHi (hbase + 8) scmAddr) (loSCM := laLo (hbase + 8) scmAddr)
    (hiLen := hiLen) (loLen := loLen) (hiRd := hiRd) (loRd := loRd)
    (hiMem := laHi (hbase + 160) evmMemBase) (loMem := laLo (hbase + 160) evmMemBase)
    (hiMem2 := laHi (hbase + 208) evmMemBase) (loMem2 := laLo (hbase + 208) evmMemBase)
    (hi2 := laHi (hbase + 276 + 4) flag) (lo2 := laLo (hbase + 276 + 4) flag)
    (hi1 := laHi (hbase + 276 + 16) resume) (lo1 := laLo (hbase + 276 + 16) resume)
    hbase p scmAddr evmMemBase flag resume
    off size x1o x5o x6o x14o x15o x16o x17o x19o x21o x22o x23o f0
    descInit memBytes hDescLen hSrcAlign hSrcOver hSrcValid hOff hOff32
    (la_resolve (hbase + 8) scmAddr hrSCM)
    (la_resolve (hbase + 160) evmMemBase hrMem)
    (la_resolve (hbase + 208) evmMemBase hrMem2)
    (la_resolve (hbase + 276 + 4) flag hr2)
    (la_resolve (hbase + 276 + 16) resume hr1)

#print axioms evm_return_halt_spec_resolved
#print axioms evm_return_stack_spec_resolved

end EvmAsm.Evm64.Terminating
