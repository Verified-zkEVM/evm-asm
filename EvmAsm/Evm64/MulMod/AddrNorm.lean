/-
  EvmAsm.Evm64.MulMod.AddrNorm

  Address-normalization simp set for MULMOD composition proofs.

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0). The
  `@[mulmod_addr, grind =]`-tagged atomic facts will be added once the
  Compose layer (`MulMod/Compose/...`) starts emitting concrete address
  arithmetic. For now this file just imports the shared `Rv64.AddrNorm`
  base and the attribute declaration so downstream files can already
  open the namespace.
-/

module

public import EvmAsm.Rv64.AddrNorm
public import EvmAsm.Evm64.MulMod.AddrNormAttr

public section

namespace EvmAsm.Evm64.MulMod.AddrNorm

open EvmAsm.Rv64

end EvmAsm.Evm64.MulMod.AddrNorm
