import EvmAsm.Evm64.DivMod.NormDefs
-- AddrNormSmokeTests pins canonical shapes from docs/263-addr-norm-inventory.md
-- so silent gaps in @[divmod_addr] coverage become CI failures (issue #263).
import EvmAsm.Evm64.DivMod.AddrNormSmokeTests
-- Spec is the public stack-spec surface and re-exports the split Spec/*
-- modules. It also covers Compose + FullPathN4 + FullPathN4Beq +
-- ModFullPathN4 + EvmWordArith + ModFullPathN4Shift0 + FullPathN4Shift0.
import EvmAsm.Evm64.DivMod.Spec
-- Shift0Dispatcher → Shift0AddbackMod → SpecCall transitively.
-- FullPathN1LoopUnified transitively covers FullPathN1Loop + FullPathN3Loop,
-- which pull in LoopUnifiedN{1,2,3} + LoopComposeN3 + FullPathN{1,2,3}
-- + FullPathN4Loop → LoopIterN4 → LoopBodyN4 → LoopBody → Compose +
-- LoopDefs + EvmWordArith.DivN4Overestimate. ModFullPathN{1,2,3}LoopUnified
-- cover the MOD n=1/n=2/n=3 wrappers. FullPathN2Bundle carries shared N2
-- irreducible intermediates for later full-wrapper refactors. FullPathN2Full
-- covers FullPathN2LoopUnified + FullPathN2Cases + FullPath.
-- SpecCallV4 transitively covers SpecCallAddbackBeq (+ AlgDefs, AlgEuclideans)
-- and LoopDefs.IterV4InvariantsPhase2 (→ IterV4Invariants). The leaf
-- NumericalTests / NumericalTestsV4 files are imported explicitly so the
-- unimported-file check (#1209/#1440) sees them reachable from the umbrella.
import EvmAsm.Evm64.DivMod.Shift0Dispatcher
import EvmAsm.Evm64.DivMod.Compose.SharedLoopPost
import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN2LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN3LoopUnified
import EvmAsm.Evm64.DivMod.Compose.Dispatcher
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Full
import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified
import EvmAsm.Evm64.DivMod.SpecCallV4
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.NumericalTests
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.NumericalTestsV4
