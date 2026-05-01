/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Scratch

  One-step irreducible scratch-state transitions for n=2 full-path wrappers.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Base

namespace EvmAsm.Evm64

open EvmAsm.Rv64

def N2ScratchState : Type :=
  Word × Word × Word × Word

@[irreducible]
def n2ScratchRet (s : N2ScratchState) : Word :=
  s.1

@[irreducible]
def n2ScratchD (s : N2ScratchState) : Word :=
  s.2.1

@[irreducible]
def n2ScratchDLo (s : N2ScratchState) : Word :=
  s.2.2.1

@[irreducible]
def n2ScratchUn0 (s : N2ScratchState) : Word :=
  s.2.2.2

@[irreducible]
def fullDivN2Scratch2 (bltu_2 : Bool) (base v1 u2 retMem dMem dloMem scratch_un0 : Word) :
    N2ScratchState :=
  if bltu_2 then
    (base + div128CallRetOff, v1, div128DLo v1, div128Un0 u2)
  else
    (retMem, dMem, dloMem, scratch_un0)

@[irreducible]
def fullDivN2Scratch1 (bltu_2 bltu_1 : Bool)
    (base v1 u2 r2_hi retMem dMem dloMem scratch_un0 : Word) :
    N2ScratchState :=
  let s2 := fullDivN2Scratch2 bltu_2 base v1 u2 retMem dMem dloMem scratch_un0
  if bltu_1 then
    (base + div128CallRetOff, v1, div128DLo v1, div128Un0 r2_hi)
  else
    s2

@[irreducible]
def fullDivN2Scratch0 (bltu_2 bltu_1 bltu_0 : Bool)
    (base v1 u2 r2_hi r1_hi retMem dMem dloMem scratch_un0 : Word) :
    N2ScratchState :=
  let s1 := fullDivN2Scratch1 bltu_2 bltu_1 base v1 u2 r2_hi retMem dMem dloMem scratch_un0
  if bltu_0 then
    (base + div128CallRetOff, v1, div128DLo v1, div128Un0 r1_hi)
  else
    s1

theorem n2ScratchRet_unfold (s : N2ScratchState) :
    n2ScratchRet s = s.1 := by
  delta n2ScratchRet
  rfl

theorem n2ScratchD_unfold (s : N2ScratchState) :
    n2ScratchD s = s.2.1 := by
  delta n2ScratchD
  rfl

theorem n2ScratchDLo_unfold (s : N2ScratchState) :
    n2ScratchDLo s = s.2.2.1 := by
  delta n2ScratchDLo
  rfl

theorem n2ScratchUn0_unfold (s : N2ScratchState) :
    n2ScratchUn0 s = s.2.2.2 := by
  delta n2ScratchUn0
  rfl

theorem fullDivN2Scratch2_true (base v1 u2 retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Scratch2 true base v1 u2 retMem dMem dloMem scratch_un0 =
      (base + div128CallRetOff, v1, div128DLo v1, div128Un0 u2) := by
  delta fullDivN2Scratch2
  rfl

theorem fullDivN2Scratch2_false (base v1 u2 retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Scratch2 false base v1 u2 retMem dMem dloMem scratch_un0 =
      (retMem, dMem, dloMem, scratch_un0) := by
  delta fullDivN2Scratch2
  rfl

theorem fullDivN2Scratch1_true (bltu_2 : Bool)
    (base v1 u2 r2_hi retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Scratch1 bltu_2 true base v1 u2 r2_hi retMem dMem dloMem scratch_un0 =
      (base + div128CallRetOff, v1, div128DLo v1, div128Un0 r2_hi) := by
  delta fullDivN2Scratch1
  rfl

theorem fullDivN2Scratch1_false (bltu_2 : Bool)
    (base v1 u2 r2_hi retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Scratch1 bltu_2 false base v1 u2 r2_hi retMem dMem dloMem scratch_un0 =
      fullDivN2Scratch2 bltu_2 base v1 u2 retMem dMem dloMem scratch_un0 := by
  delta fullDivN2Scratch1
  rfl

theorem fullDivN2Scratch0_true (bltu_2 bltu_1 : Bool)
    (base v1 u2 r2_hi r1_hi retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Scratch0 bltu_2 bltu_1 true base v1 u2 r2_hi r1_hi
        retMem dMem dloMem scratch_un0 =
      (base + div128CallRetOff, v1, div128DLo v1, div128Un0 r1_hi) := by
  delta fullDivN2Scratch0
  rfl

theorem fullDivN2Scratch0_false (bltu_2 bltu_1 : Bool)
    (base v1 u2 r2_hi r1_hi retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Scratch0 bltu_2 bltu_1 false base v1 u2 r2_hi r1_hi
        retMem dMem dloMem scratch_un0 =
      fullDivN2Scratch1 bltu_2 bltu_1 base v1 u2 r2_hi retMem dMem dloMem scratch_un0 := by
  delta fullDivN2Scratch0
  rfl

end EvmAsm.Evm64
