module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem fullDivN3ScratchNoX1_pcFree (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    (fullDivN3ScratchNoX1 bltu_1 bltu_0 sp base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0).pcFree := by
  delta fullDivN3ScratchNoX1
  pcFree

instance pcFreeInst_fullDivN3ScratchNoX1 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (fullDivN3ScratchNoX1 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0) :=
  ⟨fullDivN3ScratchNoX1_pcFree bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0⟩

theorem fullDivN3FrameNoX1_pcFree (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    (fullDivN3FrameNoX1 bltu_1 bltu_0 sp base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0).pcFree := by
  delta fullDivN3FrameNoX1
  pcFree

instance pcFreeInst_fullDivN3FrameNoX1 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (fullDivN3FrameNoX1 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0) :=
  ⟨fullDivN3FrameNoX1_pcFree bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0⟩

theorem fullDivN3UnifiedPostNoX1_pcFree (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    (fullDivN3UnifiedPostNoX1 bltu_1 bltu_0 sp base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0).pcFree := by
  delta fullDivN3UnifiedPostNoX1
  pcFree

instance pcFreeInst_fullDivN3UnifiedPostNoX1 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (fullDivN3UnifiedPostNoX1 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0) :=
  ⟨fullDivN3UnifiedPostNoX1_pcFree bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0⟩

end EvmAsm.Evm64
