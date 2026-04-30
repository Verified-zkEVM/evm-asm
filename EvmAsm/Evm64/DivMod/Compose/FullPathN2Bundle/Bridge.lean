/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Bridge

  Public bridge from the n=2 unified loop postcondition to the bundled denorm
  precondition and preserved frame.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.BridgeFalse
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.BridgeTrue

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem preloopN2UnifiedPost_to_fullDivN2DenormPre_frame
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (h : PartialState)
    (hp :
      preloopN2UnifiedPost bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0 h) :
    (fullDivN2DenormPre bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2Frame bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratch_un0) h := by
  cases bltu_2 <;> cases bltu_1 <;> cases bltu_0
  · exact preloopN2UnifiedPost_to_fullDivN2DenormPre_frame_FFF
      sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h hp
  · exact preloopN2UnifiedPost_to_fullDivN2DenormPre_frame_FFT
      sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h hp
  · exact preloopN2UnifiedPost_to_fullDivN2DenormPre_frame_FTF
      sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h hp
  · exact preloopN2UnifiedPost_to_fullDivN2DenormPre_frame_FTT
      sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h hp
  · exact preloopN2UnifiedPost_to_fullDivN2DenormPre_frame_TFF
      sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h hp
  · exact preloopN2UnifiedPost_to_fullDivN2DenormPre_frame_TFT
      sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h hp
  · exact preloopN2UnifiedPost_to_fullDivN2DenormPre_frame_TTF
      sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h hp
  · exact preloopN2UnifiedPost_to_fullDivN2DenormPre_frame_TTT
      sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h hp

end EvmAsm.Evm64
