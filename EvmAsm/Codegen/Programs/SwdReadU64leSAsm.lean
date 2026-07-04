/-
  EvmAsm.Codegen.Programs.SwdReadU64leSAsm

  Verified SAsm port of `swd_read_u64le` (bead evm-asm-4ch8f.12.6): read a
  little-endian u64 byte-wise from the pointer in `a0` and return it in `a0`.

  **Why byte-wise reads**: the callers read `block_number`/`timestamp` u64
  fields at unaligned offsets of the SSZ `ExecutionPayload` (SSZ base is
  `0x40000012`, payload at `+60`, fields at `+404`/`+428`).  A single `LD`
  at such an address fails the RV64 model's dword-alignment gate and traps
  (bead `evm-asm-4ch8f.7`).  The routine therefore assembles the u64 from
  eight `LBU`s, which the machine permits at any address.

  This is a leaf (`t0`/`t1` = `x5`/`x6` scratch, result in `a0`, `ra`
  return).  The spec is the single functional equation
  `a0 = leU64 bs 0` over the byte region at the pointer.

  Correspondence: `swdReadU64leBody.flatten 0 ++ [ret] = swdReadU64le_prog`
  is pinned below by `decide` (`swd_read_u64le_body_eq_prog`); the
  `_prog`↔emitted-string identity is `swdReadU64leFunction_eq_prog` in
  SystemWrites.lean.
-/

import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.SystemWrites

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace SwdReadU64leSAsm

/-- Byte `i` of the region, as a word. -/
def leByte (bs : List (BitVec 8)) (i : Nat) : Word :=
  (bs.getD i 0).zeroExtend 64

/-- Little-endian u64 at byte index `i`. -/
def leU64 (bs : List (BitVec 8)) (i : Nat) : Word :=
  leByte bs i ||| leByte bs (i + 1) <<< 8
    ||| leByte bs (i + 2) <<< 16 ||| leByte bs (i + 3) <<< 24
    ||| leByte bs (i + 4) <<< 32 ||| leByte bs (i + 5) <<< 40
    ||| leByte bs (i + 6) <<< 48 ||| leByte bs (i + 7) <<< 56

/-- The straight-line instruction sequence: eight `LBU`s shifted/`OR`ed into
    `t0` (`x5`), then `mv a0, t0`. -/
def swdReadU64leInstrs : List Instr :=
  [ .LBU .x5 .x10 0,
    .LBU .x6 .x10 1, .SLLI .x6 .x6 8,  .OR .x5 .x5 .x6,
    .LBU .x6 .x10 2, .SLLI .x6 .x6 16, .OR .x5 .x5 .x6,
    .LBU .x6 .x10 3, .SLLI .x6 .x6 24, .OR .x5 .x5 .x6,
    .LBU .x6 .x10 4, .SLLI .x6 .x6 32, .OR .x5 .x5 .x6,
    .LBU .x6 .x10 5, .SLLI .x6 .x6 40, .OR .x5 .x5 .x6,
    .LBU .x6 .x10 6, .SLLI .x6 .x6 48, .OR .x5 .x5 .x6,
    .LBU .x6 .x10 7, .SLLI .x6 .x6 56, .OR .x5 .x5 .x6,
    .MV .x10 .x5 ]

/-- The straight-line body.  Matches `swdReadU64le_prog` sans its `ret`. -/
def swdReadU64leBody : Stmt := .block "read" swdReadU64leInstrs

/-- Verified port of `swd_read_u64le`: `a0 := leU64 (bytes at a0) 0`. -/
def swdReadU64leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "swdReadU64le"
  region := ⟨p, bs⟩
  pre := fun rf _ _ => rf.get .x10 = p ∧ 8 ≤ bs.length
  post := fun rf _ _ => rf.get .x10 = leU64 bs 0
  body := swdReadU64leBody

/-- The emitted drop-in replacement (position-independent: no branches). -/
def swdReadU64le_verified : Program :=
  swdReadU64leBody.flatten 0

#guard (swdReadU64le_verified : List Instr).length = 23
#guard swdReadU64leBody.flatten 0 = swdReadU64leBody.flatten 0x80000000
#guard swdReadU64leBody.flatten 0 ++ [Instr.JALR .x0 .x1 0] = swdReadU64le_prog

/-- Engine lemma (own heartbeat budget): stepping the eight byte loads leaves
    `a0` holding the little-endian u64 assembled from `reg`'s first 8 bytes. -/
private theorem swdReadU64le_engine (reg : Region) (rwb : Word) (rf : RegFile)
    (hx10 : rf.get .x10 = reg.base) :
    (execBlock reg rwb rf [] swdReadU64leInstrs).1.get .x10 = leU64 reg.bytes 0 := by
  have e0 : (rf.get .x10 + signExtend12 (0 : BitVec 12) - reg.base).toNat = 0 := by
    rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
  have e1 : (rf.get .x10 + signExtend12 (1 : BitVec 12) - reg.base).toNat = 1 := by
    rw [hx10, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
  have e2 : (rf.get .x10 + signExtend12 (2 : BitVec 12) - reg.base).toNat = 2 := by
    rw [hx10, show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide]; bv_omega
  have e3 : (rf.get .x10 + signExtend12 (3 : BitVec 12) - reg.base).toNat = 3 := by
    rw [hx10, show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide]; bv_omega
  have e4 : (rf.get .x10 + signExtend12 (4 : BitVec 12) - reg.base).toNat = 4 := by
    rw [hx10, show signExtend12 (4 : BitVec 12) = (4 : Word) from by decide]; bv_omega
  have e5 : (rf.get .x10 + signExtend12 (5 : BitVec 12) - reg.base).toNat = 5 := by
    rw [hx10, show signExtend12 (5 : BitVec 12) = (5 : Word) from by decide]; bv_omega
  have e6 : (rf.get .x10 + signExtend12 (6 : BitVec 12) - reg.base).toNat = 6 := by
    rw [hx10, show signExtend12 (6 : BitVec 12) = (6 : Word) from by decide]; bv_omega
  have e7 : (rf.get .x10 + signExtend12 (7 : BitVec 12) - reg.base).toNat = 7 := by
    rw [hx10, show signExtend12 (7 : BitVec 12) = (7 : Word) from by decide]; bv_omega
  simp only [swdReadU64leInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil,
    aluSem, loadSem, RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]
  simp only [Region.byteAt, e0, e1, e2, e3, e4, e5, e6, e7]
  rfl

theorem swdReadU64leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (swdReadU64leFn p bs).Spec base := by
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case swdReadU64le.read.mem =>
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
    have e4 : (rf.get .x10 + signExtend12 (4 : BitVec 12) - p).toNat = 4 := by
      rw [hx10, show signExtend12 (4 : BitVec 12) = (4 : Word) from by decide]; bv_omega
    have e5 : (rf.get .x10 + signExtend12 (5 : BitVec 12) - p).toNat = 5 := by
      rw [hx10, show signExtend12 (5 : BitVec 12) = (5 : Word) from by decide]; bv_omega
    have e6 : (rf.get .x10 + signExtend12 (6 : BitVec 12) - p).toNat = 6 := by
      rw [hx10, show signExtend12 (6 : BitVec 12) = (6 : Word) from by decide]; bv_omega
    have e7 : (rf.get .x10 + signExtend12 (7 : BitVec 12) - p).toNat = 7 := by
      rw [hx10, show signExtend12 (7 : BitVec 12) = (7 : Word) from by decide]; bv_omega
    simp only [execInstrRF_nil, aluSem, loadSem,
      storeSem, blockVCs, Region.loadOk, RegFile.get_set_self, RegFile.get_set_ne,
      ne_eq, reduceCtorEq, not_false_eq_true, swdReadU64leFn, swdReadU64leInstrs,
      inRw, List.length_nil, Nat.le_zero, e0, e1, e2, e3, e4, e5, e6, e7]
    refine ⟨⟨Nat.one_dvd _, by omega⟩, ⟨Nat.one_dvd _, by omega⟩, trivial, trivial,
      ⟨Nat.one_dvd _, by omega⟩, trivial, trivial, ⟨Nat.one_dvd _, by omega⟩, trivial, trivial,
      ⟨Nat.one_dvd _, by omega⟩, trivial, trivial, ⟨Nat.one_dvd _, by omega⟩, trivial, trivial,
      ⟨Nat.one_dvd _, by omega⟩, trivial, trivial, ⟨Nat.one_dvd _, by omega⟩, trivial, trivial, trivial, trivial⟩
  case swdReadU64le.post =>
    intro rf' ws' A' h
    obtain ⟨rf₀, ws₀, hws₀, ⟨hx10, _⟩, rfl, rfl⟩ := h
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    show RegFile.get _ .x10 = leU64 bs 0
    exact swdReadU64le_engine (swdReadU64leFn p bs).region
      (swdReadU64leFn p bs).rw.base rf₀ hx10

end SwdReadU64leSAsm

end EvmAsm.Codegen
