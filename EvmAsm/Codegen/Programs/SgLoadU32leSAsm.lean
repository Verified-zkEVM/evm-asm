/-
  EvmAsm.Codegen.Programs.SgLoadU32leSAsm

  Verified SAsm port of `sg_load_u32le` (bead evm-asm-4ch8f.12.3): read a
  little-endian u32 byte-wise from the pointer in `a0` and return it in `a0`.

  Source asm (leaf, string-emitted inline in StatelessGuestEpilogue.lean):

      sg_load_u32le:
        lbu t0, 0(a0)
        lbu t1, 1(a0); slli t1, t1, 8;  or t0, t0, t1
        lbu t1, 2(a0); slli t1, t1, 16; or t0, t0, t1
        lbu t1, 3(a0); slli t1, t1, 24; or t0, t0, t1
        mv a0, t0
        ret

  **Why byte-wise reads**: the callers walk the SSZ outer offset table whose
  base is `0x40000012` (unaligned); a single `LWU` at such an address fails
  the RV64 model's word-alignment gate and traps (bead `evm-asm-4ch8f.7`).
  Assembling the u32 from four `LBU`s is legal at any address.

  Leaf (`t0`/`t1` = `x5`/`x6` scratch, result in `a0`, `ra` return).  The
  spec is the single functional equation `a0 = leU32 bs 0` over the byte
  region at the pointer.  This module is spec-only (no emitted-code change),
  so no EEST A/B is required.
-/

import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace SgLoadU32leSAsm

/-- Byte `i` of the region, as a word. -/
def leByte (bs : List (BitVec 8)) (i : Nat) : Word :=
  (bs.getD i 0).zeroExtend 64

/-- Little-endian u32 at byte index `i`. -/
def leU32 (bs : List (BitVec 8)) (i : Nat) : Word :=
  leByte bs i ||| leByte bs (i + 1) <<< 8
    ||| leByte bs (i + 2) <<< 16 ||| leByte bs (i + 3) <<< 24

/-- The straight-line instruction sequence: four `LBU`s shifted/`OR`ed into
    `t0` (`x5`), then `mv a0, t0`. -/
def sgLoadU32leInstrs : List Instr :=
  [ .LBU .x5 .x10 0,
    .LBU .x6 .x10 1, .SLLI .x6 .x6 8,  .OR .x5 .x5 .x6,
    .LBU .x6 .x10 2, .SLLI .x6 .x6 16, .OR .x5 .x5 .x6,
    .LBU .x6 .x10 3, .SLLI .x6 .x6 24, .OR .x5 .x5 .x6,
    .MV .x10 .x5 ]

/-- The straight-line body.  Matches the emitted asm sans its `ret`. -/
def sgLoadU32leBody : Stmt := .block "read" sgLoadU32leInstrs

/-- Verified port of `sg_load_u32le`: `a0 := leU32 (bytes at a0) 0`. -/
def sgLoadU32leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "sgLoadU32le"
  region := ⟨p, bs⟩
  pre := fun rf _ _ => rf.get .x10 = p ∧ 4 ≤ bs.length
  post := fun rf _ _ => rf.get .x10 = leU32 bs 0
  body := sgLoadU32leBody

/-- The emitted drop-in replacement (position-independent: no branches). -/
def sgLoadU32le_verified : Program :=
  sgLoadU32leBody.flatten 0

#guard (sgLoadU32le_verified : List Instr).length = 11
#guard sgLoadU32leBody.flatten 0 = sgLoadU32leBody.flatten 0x80000000

/-- The complete verified routine, including its leaf `ret`.  This is the
    program consumed by `StatelessGuestEpilogue` so the emitted guest and the
    proved body cannot drift independently. -/
def sgLoadU32le_prog : Program :=
  sgLoadU32leBody.flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]

/-- Kernel correspondence between the structured body and emitted routine. -/
theorem sgLoadU32le_body_eq_prog :
    sgLoadU32leBody.flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]
      = sgLoadU32le_prog := by
  rfl

#guard sgLoadU32le_prog.length = 12

/-- Engine lemma (own heartbeat budget): stepping the four byte loads leaves
    `a0` holding the little-endian u32 assembled from `reg`'s first 4 bytes. -/
private theorem sgLoadU32le_engine (reg : Region) (rwb : Word) (rf : RegFile)
    (hx10 : rf.get .x10 = reg.base) :
    (execBlock reg rwb rf [] sgLoadU32leInstrs).1.get .x10 = leU32 reg.bytes 0 := by
  have e0 : (rf.get .x10 + signExtend12 (0 : BitVec 12) - reg.base).toNat = 0 := by
    rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
  have e1 : (rf.get .x10 + signExtend12 (1 : BitVec 12) - reg.base).toNat = 1 := by
    rw [hx10, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
  have e2 : (rf.get .x10 + signExtend12 (2 : BitVec 12) - reg.base).toNat = 2 := by
    rw [hx10, show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide]; bv_omega
  have e3 : (rf.get .x10 + signExtend12 (3 : BitVec 12) - reg.base).toNat = 3 := by
    rw [hx10, show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide]; bv_omega
  simp only [sgLoadU32leInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil,
    aluSem, loadSem, RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]
  simp only [Region.byteAt, e0, e1, e2, e3]
  rfl

theorem sgLoadU32leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (sgLoadU32leFn p bs).Spec base := by
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case sgLoadU32le.read.mem =>
    rintro rf ws A hws ⟨hx10, hlen⟩
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    have e0 : (rf.get .x10 + signExtend12 (0 : BitVec 12) - p).toNat = 0 := by
      rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
    have e1 : (rf.get .x10 + signExtend12 (1 : BitVec 12) - p).toNat = 1 := by
      rw [hx10, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
    have e2 : (rf.get .x10 + signExtend12 (2 : BitVec 12) - p).toNat = 2 := by
      rw [hx10, show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide]; bv_omega
    have e3 : (rf.get .x10 + signExtend12 (3 : BitVec 12) - p).toNat = 3 := by
      rw [hx10, show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide]; bv_omega
    simp only [execInstrRF_nil, aluSem, loadSem, storeSem, blockVCs, Region.loadOk,
      RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, sgLoadU32leFn, sgLoadU32leInstrs, inRw, List.length_nil,
      Nat.le_zero, e0, e1, e2, e3]
    refine ⟨⟨Nat.one_dvd _, by omega⟩, ⟨Nat.one_dvd _, by omega⟩, trivial, trivial,
      ⟨Nat.one_dvd _, by omega⟩, trivial, trivial, ⟨Nat.one_dvd _, by omega⟩,
      trivial, trivial, trivial, trivial⟩
  case sgLoadU32le.post =>
    intro rf' ws' A' h
    obtain ⟨rf₀, ws₀, hws₀, ⟨hx10, _⟩, rfl, rfl⟩ := h
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    show RegFile.get _ .x10 = leU32 bs 0
    exact sgLoadU32le_engine (sgLoadU32leFn p bs).region
      (sgLoadU32leFn p bs).rw.base rf₀ hx10


end SgLoadU32leSAsm

end EvmAsm.Codegen
