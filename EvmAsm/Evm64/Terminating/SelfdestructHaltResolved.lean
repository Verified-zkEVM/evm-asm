/-
  EvmAsm.Evm64.Terminating.SelfdestructHaltResolved

  **SELFDESTRUCT's `la` reconstruction hypotheses, retired.**

  `evm_selfdestruct_stack_spec_within` (`SelfdestructSpec.lean`) carries the two
  linker `la`s (`evm_halt_flag`, `.dispatch_resume`) as ASSUMED reconstruction
  hypotheses `hla2`/`hla1` of the form

  ```
    pc + ((hi.zeroExtend 32) <<< 12).signExtend 64 + signExtend12 lo = sym
  ```

  This module restates the spec with the immediates COMPUTED by the `la`
  resolution model (`laHi`/`laLo`, `EvmAsm/Rv64/LaResolve.lean`, PR #10059) and
  the former hypotheses PROVEN by `la_resolve`. What remains per `la` is only
  `laInRange pc sym` — displacement representability, a decidable fact of the
  linked layout — instead of the full materialization arithmetic. Direct clone
  of `evm_return_halt_spec_resolved` (`ReturnHaltResolved.lean`), routing code 4.

  Kernel-checkable throughout (classical-3 only).
-/

import EvmAsm.Evm64.Terminating.SelfdestructSpec
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Evm64.Terminating

open EvmAsm.Rv64

/-- **The SELFDESTRUCT halt tail with the two `la`s resolved**: immediates
    computed by `laHi`/`laLo`; the former `hla2`/`hla1` are `la_resolve` facts.
    Only displacement representability (`laInRange`) remains per `la`. Direct
    STOP/RETURN clone with routing code 4 (`.exit_selfdestruct`). -/
theorem evm_selfdestruct_stack_spec_resolved (hbase flag resume v5 v6 v1 f0 : Word)
    (hr2 : laInRange (hbase + 4) flag)
    (hr1 : laInRange (hbase + 16) resume) :
    cpsTripleWithin 7 hbase (resume &&& ~~~1)
      (CodeReq.ofProg hbase (evm_selfdestruct
        (laHi (hbase + 4) flag) (laLo (hbase + 4) flag)
        (laHi (hbase + 16) resume) (laLo (hbase + 16) resume)))
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ v1) ** (flag ↦ₘ f0))
      ((.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ flag) ** (.x1 ↦ᵣ resume) **
        (flag ↦ₘ (4 : Word))) :=
  evm_selfdestruct_stack_spec_within
    (laHi (hbase + 4) flag) (laLo (hbase + 4) flag)
    (laHi (hbase + 16) resume) (laLo (hbase + 16) resume)
    hbase flag resume v5 v6 v1 f0
    (la_resolve (hbase + 4) flag hr2)
    (la_resolve (hbase + 16) resume hr1)


end EvmAsm.Evm64.Terminating
