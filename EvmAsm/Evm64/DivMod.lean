import EvmAsm.Evm64.DivMod.NormDefs
-- SpecCall covers Spec → Compose + FullPathN4 + FullPathN4Beq + ModFullPathN4
-- + EvmWordArith + ModFullPathN4Shift0 + FullPathN4Shift0.
-- Shift0Dispatcher → Shift0AddbackMod → SpecCall transitively.
-- FullPathN1LoopUnified transitively covers FullPathN1Loop + FullPathN3Loop,
-- which pull in LoopUnifiedN{1,2,3} + LoopComposeN3 + FullPathN{1,2,3}
-- + FullPathN4Loop → LoopIterN4 → LoopBodyN4 → LoopBody → Compose +
-- LoopDefs + EvmWordArith.DivN4Overestimate. FullPathN2Full covers
-- FullPathN2LoopUnified + FullPathN2Cases + FullPath.
import EvmAsm.Evm64.DivMod.Shift0Dispatcher
import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Full
