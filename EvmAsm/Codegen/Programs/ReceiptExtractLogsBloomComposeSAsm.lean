import EvmAsm.Codegen.Programs.ReceiptExtractLogsBloomSAsm

namespace EvmAsm.Codegen.ReceiptExtractLogsBloomSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

theorem copyLoopTail
    (src dst : Word) (srcBytes outBytes : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf)
    (hrww : RwRegion.wf ⟨dst, 256⟩)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin (copyLoopNoAbiFn src dst srcBytes outBytes).body.steps
      (B + 112) (B + 140) code
      (asrtM (copyLoopNoAbiFn src dst srcBytes outBytes).region
        (copyLoopNoAbiFn src dst srcBytes outBytes).rw
        (copyLoopNoAbiFn src dst srcBytes outBytes).pre ** F)
      (asrtM (copyLoopNoAbiFn src dst srcBytes outBytes).region
        (copyLoopNoAbiFn src dst srcBytes outBytes).rw
        (copyLoopNoAbiFn src dst srcBytes outBytes).post ** F) := by
  have h := copyLoopNoAbiFn_code_spec src dst srcBytes outBytes hwf hrww
  have hF' := cpsTripleWithin_frameR F hF h
  simpa [copyLoopNoAbiFn] using hF'

end EvmAsm.Codegen.ReceiptExtractLogsBloomSAsm
