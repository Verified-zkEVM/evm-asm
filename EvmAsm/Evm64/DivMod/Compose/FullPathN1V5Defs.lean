/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Defs

  v5 n=1 schoolbook digit functions, mirroring `fullDivN1R3/R2/R1/R0/C3`
  (`FullPathN1LoopUnified.lean`) but running each per-digit iteration over the
  v5 capped trial quotient (`iterN1V5` / `div128Quot_v5`) instead of v4
  `iterN1` / `div128Quot`.

  Required because v4 `div128Quot` is inexact even in the n=1 call regime
  (`ceV4Div128Call_div128Quot_ne_floor`), whereas `div128Quot_v5 = floor`
  (`div128Quot_v5_eq_q_true`) — so the v5 schoolbook discharges the n=1
  carry-zero from shape alone (via `fullDivN1NormV_limb0_ge_pow63_of_shape`
  + the call-regime `U_top < V0'`), sidestepping the false-universal
  `Carry2NzAll`. Bead evm-asm-wbc4i.9.1.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
public import EvmAsm.Evm64.DivMod.LoopDefs.IterV5

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 n=1 first schoolbook digit (top window). -/
@[irreducible]
def fullDivN1R3V5 (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  iterN1V5 bltu_3 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)

/-- v5 n=1 second schoolbook digit. -/
@[irreducible]
def fullDivN1R2V5 (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3V5 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  iterN1V5 bltu_2 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.1 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1

/-- v5 n=1 third schoolbook digit. -/
@[irreducible]
def fullDivN1R1V5 (bltu_3 bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r2 := fullDivN1R2V5 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  iterN1V5 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

/-- v5 n=1 fourth schoolbook digit. -/
@[irreducible]
def fullDivN1R0V5 (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r1 := fullDivN1R1V5 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  iterN1V5 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

/-- v5 n=1 final-digit mulsub top borrow (uses the v5 capped trial on the
    call path). -/
@[irreducible]
def fullDivN1C3V5 (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r1 := fullDivN1R1V5 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  if bltu_0 then
    (mulsubN4 (div128Quot_v5 r1.2.1 u.1 v.1)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  else
    (mulsubN4 (signExtend12 4095 : Word)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2

end EvmAsm.Evm64
