/-
  EvmAsm.Stateless.SSZ.Decode.ActiveForkSAsm

  A verified SAsm port of `read_active_fork` (Program.lean): read the
  `active_fork` offset (u32) at `chain_config + 8` and load the u64 fork
  index it points to.

  **Why byte-wise reads**: the chain-config section sits at
  `INPUT_BASE + 18 + offset` with a 4-aligned host offset, so the original
  `LWU x14, x13, 8` reads at an address `≡ 2 (mod 4)` and the `LD` reads at
  a host-data-dependent address; both fail the Lean RV64 model's alignment
  gates (beads `evm-asm-iwzun`), exactly like `read_chain_id`.  The port
  assembles both values from one-byte loads (ChainIdSAsm.lean recipe).

  Interface (matching the original + the `readChainIdFn` post):
    pre:  a3 = chain-config address (`0x40000012 + leU32 bs 26`), ghost
          bounds putting the offset u32 and the fork u64 inside the buffer
    post: a2 = fork index, a3 preserved.  Clobbers t0, a2, a4.
-/

import EvmAsm.Stateless.SSZ.Decode.ChainIdSAsm

namespace EvmAsm.Stateless.SSZ.Decode

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

/-- The structured body of the verified `read_active_fork` (ghost-free, so
    it flattens to a concrete `Program`). -/
def readActiveForkBody : Stmt :=
    .block "offset32" [
      .LBU .x14 .x13 8,
      .LBU .x5 .x13 9,  .SLLI .x5 .x5 8,  .OR .x14 .x14 .x5,
      .LBU .x5 .x13 10, .SLLI .x5 .x5 16, .OR .x14 .x14 .x5,
      .LBU .x5 .x13 11, .SLLI .x5 .x5 24, .OR .x14 .x14 .x5,
      .ADD .x14 .x13 .x14] ;;;
    .block "fork64" [
      .LBU .x12 .x14 0,
      .LBU .x5 .x14 1, .SLLI .x5 .x5 8,  .OR .x12 .x12 .x5,
      .LBU .x5 .x14 2, .SLLI .x5 .x5 16, .OR .x12 .x12 .x5,
      .LBU .x5 .x14 3, .SLLI .x5 .x5 24, .OR .x12 .x12 .x5,
      .LBU .x5 .x14 4, .SLLI .x5 .x5 32, .OR .x12 .x12 .x5,
      .LBU .x5 .x14 5, .SLLI .x5 .x5 40, .OR .x12 .x12 .x5,
      .LBU .x5 .x14 6, .SLLI .x5 .x5 48, .OR .x12 .x12 .x5,
      .LBU .x5 .x14 7, .SLLI .x5 .x5 56, .OR .x12 .x12 .x5]

/-- Verified port of `read_active_fork`: with `a3` holding the chain-config
    address (as `read_chain_id` leaves it), `a2 := the u64 fork index` at
    `chain_config + (u32 at chain_config+8)`, read byte-wise from the
    (ghost) input buffer `bs` at `INPUT_BASE`.  `a3` is preserved.
    Clobbers t0, a2, a4 — the original's interface plus `t0`. -/
def readActiveForkFn (bs : List (BitVec 8)) : Fn where
  name := "readActiveFork"
  region := ⟨0x40000000, bs⟩
  pre := fun rf _ _ =>
    rf.get .x13 = (0x40000012 : Word) + leU32 bs 26 ∧
    26 + (leU32 bs 26).toNat + 4 ≤ bs.length ∧
    18 + (leU32 bs 26).toNat
      + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 8 ≤ bs.length
  post := fun rf _ _ =>
    rf.get .x12 = leU64 bs (18 + (leU32 bs 26).toNat
      + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat) ∧
    rf.get .x13 = (0x40000012 : Word) + leU32 bs 26
  body := readActiveForkBody

/-- The emitted drop-in replacement for `read_active_fork`
    (position-independent: no calls, all branches structured). -/
def read_active_fork_verified : Program :=
  readActiveForkBody.flatten 0

#guard (read_active_fork_verified : List Instr).length = 33
#guard readActiveForkBody.flatten 0 = readActiveForkBody.flatten 0x80000000

theorem readActiveForkFn_spec (bs : List (BitVec 8))
    (hlen : bs.length ≤ 0x2000) (base : Word) :
    (readActiveForkFn bs).Spec base := by
  have hoff32 := leU32_toNat_lt bs 26
  have hoff32' := leU32_toNat_lt bs (26 + (leU32 bs 26).toNat)
  vcgen
  case region =>
    exact ⟨inputRegion_wf bs hlen, RwRegion.empty_wf⟩
  case readActiveFork.offset32.mem =>
    rintro rf ws A hws ⟨hx13, hb1, hb2⟩
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    simp only [execInstrRF_nil, aluSem, loadSem,
      storeSem, blockVCs, Region.loadOk, RegFile.get_set_self,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp only [hx13,
      show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
      show signExtend12 (9 : BitVec 12) = (9 : Word) from by decide,
      show signExtend12 (10 : BitVec 12) = (10 : Word) from by decide,
      show signExtend12 (11 : BitVec 12) = (11 : Word) from by decide,
      show (readActiveForkFn bs).region.base = (0x40000000 : Word) from rfl,
      show (readActiveForkFn bs).region.bytes = bs from rfl,
      show ((0x40000012 : Word) + leU32 bs 26 + 8
          - 0x40000000).toNat = 26 + (leU32 bs 26).toNat from by bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + 9
          - 0x40000000).toNat = 26 + (leU32 bs 26).toNat + 1 from by bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + 10
          - 0x40000000).toNat = 26 + (leU32 bs 26).toNat + 2 from by bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + 11
          - 0x40000000).toNat = 26 + (leU32 bs 26).toNat + 3 from by bv_omega]
    and_intros <;> first
      | trivial
      | omega
  case readActiveFork.fork64.mem =>
    rintro rf ws A hws ⟨rf₀, ws₀, hws₀, ⟨hx13, hb1, hb2⟩, rfl, rfl⟩
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
      storeSem, blockVCs, Region.loadOk, RegFile.get_set_self,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    have hbyteAt : ∀ a : Word,
        (readActiveForkFn bs).region.byteAt a
          = bs.getD (a - 0x40000000).toNat 0 := fun _ => rfl
    simp only [hbyteAt, hx13,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide,
      show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide,
      show signExtend12 (4 : BitVec 12) = (4 : Word) from by decide,
      show signExtend12 (5 : BitVec 12) = (5 : Word) from by decide,
      show signExtend12 (6 : BitVec 12) = (6 : Word) from by decide,
      show signExtend12 (7 : BitVec 12) = (7 : Word) from by decide,
      show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
      show signExtend12 (9 : BitVec 12) = (9 : Word) from by decide,
      show signExtend12 (10 : BitVec 12) = (10 : Word) from by decide,
      show signExtend12 (11 : BitVec 12) = (11 : Word) from by decide,
      show (readActiveForkFn bs).region.base = (0x40000000 : Word) from rfl,
      show (readActiveForkFn bs).region.bytes = bs from rfl,
      show ((0x40000012 : Word) + leU32 bs 26 + 8
          - 0x40000000).toNat = 26 + (leU32 bs 26).toNat from by bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + 9
          - 0x40000000).toNat = 26 + (leU32 bs 26).toNat + 1 from by bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + 10
          - 0x40000000).toNat = 26 + (leU32 bs 26).toNat + 2 from by bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + 11
          - 0x40000000).toNat = 26 + (leU32 bs 26).toNat + 3 from by bv_omega]
    rw [show BitVec.zeroExtend 64 (bs.getD (26 + (leU32 bs 26).toNat) 0)
        ||| BitVec.zeroExtend 64 (bs.getD (26 + (leU32 bs 26).toNat + 1) 0)
            <<< BitVec.toNat (8 : BitVec 6)
        ||| BitVec.zeroExtend 64 (bs.getD (26 + (leU32 bs 26).toNat + 2) 0)
            <<< BitVec.toNat (16 : BitVec 6)
        ||| BitVec.zeroExtend 64 (bs.getD (26 + (leU32 bs 26).toNat + 3) 0)
            <<< BitVec.toNat (24 : BitVec 6)
        = leU32 bs (26 + (leU32 bs 26).toNat) from rfl]
    simp only [
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 0 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 1 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 1 from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 2 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 2 from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 3 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 3 from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 4 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 4 from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 5 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 5 from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 6 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 6 from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 7 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 7 from by
        bv_omega]
    and_intros <;> first
      | trivial
      | omega
  case readActiveFork.post =>
    intro rf' ws' A' h
    show rf'.get .x12 = leU64 bs (18 + (leU32 bs 26).toNat
        + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat) ∧
      rf'.get .x13 = (0x40000012 : Word) + leU32 bs 26
    obtain ⟨rf₁, ws₁, hws₁, ⟨rf₀, ws₀, hws₀, ⟨hx13, hb1, hb2⟩, rfl, rfl⟩, rfl, rfl⟩ := h
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
      RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true]
    have hbyteAt : ∀ a : Word,
        (readActiveForkFn bs).region.byteAt a
          = bs.getD (a - 0x40000000).toNat 0 := fun _ => rfl
    simp only [hbyteAt, hx13,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide,
      show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide,
      show signExtend12 (4 : BitVec 12) = (4 : Word) from by decide,
      show signExtend12 (5 : BitVec 12) = (5 : Word) from by decide,
      show signExtend12 (6 : BitVec 12) = (6 : Word) from by decide,
      show signExtend12 (7 : BitVec 12) = (7 : Word) from by decide,
      show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
      show signExtend12 (9 : BitVec 12) = (9 : Word) from by decide,
      show signExtend12 (10 : BitVec 12) = (10 : Word) from by decide,
      show signExtend12 (11 : BitVec 12) = (11 : Word) from by decide,
      show ((0x40000012 : Word) + leU32 bs 26 + 8
          - 0x40000000).toNat = 26 + (leU32 bs 26).toNat from by bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + 9
          - 0x40000000).toNat = 26 + (leU32 bs 26).toNat + 1 from by bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + 10
          - 0x40000000).toNat = 26 + (leU32 bs 26).toNat + 2 from by bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + 11
          - 0x40000000).toNat = 26 + (leU32 bs 26).toNat + 3 from by bv_omega]
    rw [show BitVec.zeroExtend 64 (bs.getD (26 + (leU32 bs 26).toNat) 0)
        ||| BitVec.zeroExtend 64 (bs.getD (26 + (leU32 bs 26).toNat + 1) 0)
            <<< BitVec.toNat (8 : BitVec 6)
        ||| BitVec.zeroExtend 64 (bs.getD (26 + (leU32 bs 26).toNat + 2) 0)
            <<< BitVec.toNat (16 : BitVec 6)
        ||| BitVec.zeroExtend 64 (bs.getD (26 + (leU32 bs 26).toNat + 3) 0)
            <<< BitVec.toNat (24 : BitVec 6)
        = leU32 bs (26 + (leU32 bs 26).toNat) from rfl]
    simp only [
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 0 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 1 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 1 from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 2 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 2 from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 3 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 3 from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 4 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 4 from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 5 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 5 from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 6 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 6 from by
        bv_omega,
      show ((0x40000012 : Word) + leU32 bs 26 + leU32 bs (26 + (leU32 bs 26).toNat)
          + 7 - 0x40000000).toNat
        = 18 + (leU32 bs 26).toNat
          + (leU32 bs (26 + (leU32 bs 26).toNat)).toNat + 7 from by
        bv_omega]
    exact ⟨rfl, trivial⟩

end EvmAsm.Stateless.SSZ.Decode
