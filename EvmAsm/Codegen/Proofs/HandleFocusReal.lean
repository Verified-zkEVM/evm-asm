/-
  EvmAsm.Codegen.Proofs.HandleFocusReal

  `FnHandleS.focus` (bead evm-asm-4ch8f.49.1, `Rv64/SAsm/HandleFocus.lean`)
  applied to the REAL `.10.1` dispatch handles (`HandlerHandles*.lean`), not a
  re-stated toy — the reviewer's tie-in check.

  Each `.10.1` handle is `evmAddHandle base ·`, `evmSubHandle base ·`, … : a
  family `Word → FnHandleS` sharing one code placement (`entry = base`,
  `code = cleanRetHandlerCode base <op> 1`, `nSteps`, `region = Region.empty`)
  and differing only in its window base (`rw = ⟨sp, 64⟩`) and its
  snapshot-parameterized `pre`/`post`.  That is exactly the shape
  `FnHandleS.focus` consumes: every field hypothesis holds by `rfl`, so the
  minimal `⟨sp, 64⟩` handles embed into a fixed arena with the operative
  window carried by the register `x12` — the composition bead `.49.d` needs at
  the dispatch site.
-/

import EvmAsm.Rv64.SAsm.HandleFocus
import EvmAsm.Codegen.Proofs.HandlerHandles
import EvmAsm.Codegen.Proofs.HandlerHandlesBinary

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

/-- The real `.10.1` ADD handle, focused into a fixed frame arena: `rw = arena`
    (fixed, so `callRegS`'s `h.rw = caller.rw` holds), window at the per-call
    `x12`.  All `FnHandleS.focus` field hypotheses discharge by `rfl` — the
    embedding is usable by the real minimal-window handles verbatim. -/
def focusedEvmAdd (base : Word) (arena : RwRegion) : FnHandleS :=
  FnHandleS.focus (evmAddHandle base) arena 64 base
    (cleanRetHandlerCode base EvmAsm.Evm64.evm_add 1) 32 Region.empty
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (by decide)

/-- The same for SUB — the family shape is uniform across the `.10.1`
    arithmetic/logic handles, so `focus` applies to each by `rfl`. -/
def focusedEvmSub (base : Word) (arena : RwRegion) : FnHandleS :=
  FnHandleS.focus (evmSubHandle base) arena 64 base
    (cleanRetHandlerCode base EvmAsm.Evm64.evm_sub 1) 32 Region.empty
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (by decide)

-- The focused handle presents the arena as its (fixed) writable region and
-- keeps the family's code entry — the two facts `callRegS` reconciles.
example (base : Word) (arena : RwRegion) :
    (focusedEvmAdd base arena).rw = arena := rfl
example (base : Word) (arena : RwRegion) :
    (focusedEvmAdd base arena).entry = base := rfl
example (base : Word) (arena : RwRegion) :
    (focusedEvmAdd base arena).code = cleanRetHandlerCode base EvmAsm.Evm64.evm_add 1 :=
  rfl

end EvmAsm.Codegen.Proofs
