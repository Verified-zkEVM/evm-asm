/-
  EvmAsm.Stateless.SSZ.Decode.ChainIdSAsm

  A verified SAsm port of `read_chain_id` (Program.lean): walk the
  `SszStatelessInput` outer offset table and load `chain_config.chain_id`.

  **Why byte-wise reads**: the original routine does `LWU x13, x12, 8` with
  `x12 = INPUT_BASE + 18`, i.e. at address `0x4000001A ≡ 2 (mod 4)`, and an
  `LD` at a host-data-dependent address.  Under the Lean RV64 model both
  accesses fail their alignment gates (`isValidMemAccess` /
  `isValidDwordAccess`) and `step` traps — see beads `evm-asm-iwzun`.  The
  SSZ container sits at `+18` from the dword-aligned input base, so *no*
  u32 of the offset table is 4-aligned.  The verified port therefore
  assembles the u32 offset and the u64 chain-id from one-byte loads, which
  the machine permits at any address.

  The ghost precondition carries exactly the assumption the unverified
  routine makes implicitly: the host-supplied `chain_config` offset points
  inside the input buffer.
-/

import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Stateless.SSZ.Decode

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

-- ============================================================================
-- Little-endian ghost values (shaped to match the block engine's output)
-- ============================================================================

/-- Byte `i` of the buffer, as a word. -/
def leByte (bs : List (BitVec 8)) (i : Nat) : Word :=
  (bs.getD i 0).zeroExtend 64

/-- Little-endian u32 at byte index `i`, as a word. -/
def leU32 (bs : List (BitVec 8)) (i : Nat) : Word :=
  leByte bs i ||| leByte bs (i + 1) <<< 8
    ||| leByte bs (i + 2) <<< 16 ||| leByte bs (i + 3) <<< 24

/-- Little-endian u64 at byte index `i`. -/
def leU64 (bs : List (BitVec 8)) (i : Nat) : Word :=
  leByte bs i ||| leByte bs (i + 1) <<< 8
    ||| leByte bs (i + 2) <<< 16 ||| leByte bs (i + 3) <<< 24
    ||| leByte bs (i + 4) <<< 32 ||| leByte bs (i + 5) <<< 40
    ||| leByte bs (i + 6) <<< 48 ||| leByte bs (i + 7) <<< 56

theorem leByte_toNat_lt (bs : List (BitVec 8)) (i : Nat) :
    (leByte bs i).toNat < 2 ^ 8 := by
  unfold leByte
  rw [show BitVec.zeroExtend 64 (bs.getD i 0)
      = BitVec.setWidth 64 (bs.getD i 0) from rfl,
    BitVec.toNat_setWidth]
  have := (bs.getD i 0).isLt
  omega

theorem leU32_toNat_lt (bs : List (BitVec 8)) (i : Nat) :
    (leU32 bs i).toNat < 2 ^ 32 := by
  have hsh : ∀ j k : Nat, k + 8 ≤ 32 →
      ((leByte bs j) <<< k).toNat < 2 ^ 32 := by
    intro j k hk
    rw [BitVec.toNat_shiftLeft]
    have := leByte_toNat_lt bs j
    have h1 : (leByte bs j).toNat <<< k < 2 ^ 32 := by
      rw [Nat.shiftLeft_eq]
      calc (leByte bs j).toNat * 2 ^ k
          < 2 ^ 8 * 2 ^ k :=
            mul_lt_mul_of_pos_right this (Nat.pow_pos (by omega))
        _ ≤ 2 ^ 32 := by
            rw [← Nat.pow_add]
            exact Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h1
  unfold leU32
  simp only [BitVec.toNat_or]
  have h0 := leByte_toNat_lt bs i
  have h1 := hsh (i + 1) 8 (by omega)
  have h2 := hsh (i + 2) 16 (by omega)
  have h3 := hsh (i + 3) 24 (by omega)
  have := Nat.or_lt_two_pow
    (Nat.or_lt_two_pow
      (Nat.or_lt_two_pow (by omega : (leByte bs i).toNat < 2 ^ 32) h1) h2) h3
  exact this

-- ============================================================================
-- The port
-- ============================================================================

/-- The structured body of the verified `read_chain_id` (ghost-free, so it
    flattens to a concrete `Program`). -/
def readChainIdBody : Stmt :=
    .block "setup" [.LI .x11 0x40000000, .ADDI .x12 .x11 18] ;;;
    .block "offset32" [
      .LBU .x13 .x12 8,
      .LBU .x5 .x12 9,  .SLLI .x5 .x5 8,  .OR .x13 .x13 .x5,
      .LBU .x5 .x12 10, .SLLI .x5 .x5 16, .OR .x13 .x13 .x5,
      .LBU .x5 .x12 11, .SLLI .x5 .x5 24, .OR .x13 .x13 .x5,
      .ADD .x13 .x12 .x13] ;;;
    .block "chainid" [
      .LBU .x10 .x13 0,
      .LBU .x5 .x13 1, .SLLI .x5 .x5 8,  .OR .x10 .x10 .x5,
      .LBU .x5 .x13 2, .SLLI .x5 .x5 16, .OR .x10 .x10 .x5,
      .LBU .x5 .x13 3, .SLLI .x5 .x5 24, .OR .x10 .x10 .x5,
      .LBU .x5 .x13 4, .SLLI .x5 .x5 32, .OR .x10 .x10 .x5,
      .LBU .x5 .x13 5, .SLLI .x5 .x5 40, .OR .x10 .x10 .x5,
      .LBU .x5 .x13 6, .SLLI .x5 .x5 48, .OR .x10 .x10 .x5,
      .LBU .x5 .x13 7, .SLLI .x5 .x5 56, .OR .x10 .x10 .x5]

/-- Verified port of `read_chain_id`: `a0 := chain_config.chain_id`, read
    byte-wise from the (ghost) input buffer `bs` at `INPUT_BASE`; `a3` is
    left holding the chain-config section address (the interface
    `read_active_fork` documents).  Clobbers t0, a1–a3 — the original's
    interface plus `t0`. -/
def readChainIdFn (bs : List (BitVec 8)) : Fn where
  name := "readChainId"
  region := ⟨0x40000000, bs⟩
  pre := fun _ _ =>
    30 ≤ bs.length ∧ 18 + (leU32 bs 26).toNat + 8 ≤ bs.length
  post := fun rf _ =>
    rf.get .x10 = leU64 bs (18 + (leU32 bs 26).toNat) ∧
    rf.get .x13 = (0x40000012 : Word) + leU32 bs 26
  body := readChainIdBody

/-- The emitted drop-in replacement for `read_chain_id`
    (position-independent: no calls, all branches structured). -/
def read_chain_id_verified : Program :=
  readChainIdBody.flatten 0

#guard (read_chain_id_verified : List Instr).length = 35
#guard readChainIdBody.flatten 0 = readChainIdBody.flatten 0x80000000

/-- The input buffer forms a well-formed SAsm region (dword-aligned base in
    the machine's input zone). -/
theorem inputRegion_wf (bs : List (BitVec 8)) (hlen : bs.length ≤ 0x2000) :
    (Region.mk (0x40000000 : Word) bs).wf := by
  have hb : (0x40000000 : Word).toNat = 0x40000000 := by decide
  refine ⟨?_, ?_, ?_⟩
  · show (0x40000000 : Word).toNat % 8 = 0
    omega
  · show (0x40000000 : Word).toNat + bs.length < 2 ^ 64
    omega
  · intro k hk
    have hk' : k < bs.length := hk
    show isValidMemAddr ((0x40000000 : Word) + BitVec.ofNat 64 k) = true
    simp only [isValidMemAddr, INPUT_MEM_START, INPUT_MEM_END, MEM_START,
      MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat, hb]
    omega

theorem readChainIdFn_spec (bs : List (BitVec 8))
    (hlen : bs.length ≤ 0x2000) (base : Word) :
    (readChainIdFn bs).Spec base := by
  vcgen
  case region =>
    exact ⟨inputRegion_wf bs hlen, RwRegion.empty_wf⟩
  case readChainId.offset32.mem =>
    rintro rf ws hws ⟨rf₀, ws₀, hws₀, ⟨hlen30, hoff⟩, rfl, rfl⟩
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
      storeSem, blockVCs, Region.loadOk]
    simp [RegFile.get_set_self, RegFile.get_set_ne]
    have hbb : (readChainIdFn bs).region.base.toNat = 0x40000000 := by
      rw [show (readChainIdFn bs).region.base = (0x40000000 : Word) from rfl]
      decide
    have hll : (readChainIdFn bs).region.bytes.length = bs.length := rfl
    have h18 : (signExtend12 (18#12)).toNat = 18 := by decide
    have h8 : (signExtend12 (8#12)).toNat = 8 := by decide
    have h9 : (signExtend12 (9#12)).toNat = 9 := by decide
    have h10 : (signExtend12 (10#12)).toNat = 10 := by decide
    have h11 : (signExtend12 (11#12)).toNat = 11 := by decide
    omega
  case readChainId.chainid.mem =>
    rintro rf ws hws ⟨rf₁, ws₁, hws₁, ⟨rf₀, ws₀, hws₀, ⟨hlen30, hoff⟩, rfl, rfl⟩, rfl, rfl⟩
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
      storeSem, blockVCs, Region.loadOk, RegFile.get_set_self, RegFile.get_set_ne,
      ne_eq, reduceCtorEq, not_false_eq_true]
    have hbyteAt : ∀ a : Word,
        (readChainIdFn bs).region.byteAt a
          = bs.getD (a - 0x40000000).toNat 0 := fun _ => rfl
    simp only [hbyteAt,
      show signExtend12 (18 : BitVec 12) = (18 : Word) from by decide,
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
      show ((1073741824 : Word) + 18 + 8 - 0x40000000).toNat = 26 from by decide,
      show ((1073741824 : Word) + 18 + 9 - 0x40000000).toNat = 27 from by decide,
      show ((1073741824 : Word) + 18 + 10 - 0x40000000).toNat = 28 from by decide,
      show ((1073741824 : Word) + 18 + 11 - 0x40000000).toNat = 29 from by decide,
      show (readChainIdFn bs).region.base = (0x40000000 : Word) from rfl,
      show (readChainIdFn bs).region.bytes = bs from rfl]
    rw [show BitVec.zeroExtend 64 (bs.getD 26 0)
        ||| BitVec.zeroExtend 64 (bs.getD 27 0) <<< BitVec.toNat (8 : BitVec 6)
        ||| BitVec.zeroExtend 64 (bs.getD 28 0) <<< BitVec.toNat (16 : BitVec 6)
        ||| BitVec.zeroExtend 64 (bs.getD 29 0) <<< BitVec.toNat (24 : BitVec 6)
        = leU32 bs 26 from rfl]
    have hoff32 := leU32_toNat_lt bs 26
    and_intros <;> first
      | trivial
      | omega
      | bv_omega
  case readChainId.post =>
    intro rf' ws' h
    show rf'.get .x10 = leU64 bs (18 + (leU32 bs 26).toNat) ∧
      rf'.get .x13 = (0x40000012 : Word) + leU32 bs 26
    obtain ⟨rf₂, ws₂, hws₂, ⟨rf₁, ws₁, hws₁, ⟨rf₀, ws₀, hws₀, ⟨hlen30, hoff⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩ := h
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
      RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true]
    have hbyteAt : ∀ a : Word,
        (readChainIdFn bs).region.byteAt a
          = bs.getD (a - 0x40000000).toNat 0 := fun _ => rfl
    simp only [hbyteAt,
      show signExtend12 (18 : BitVec 12) = (18 : Word) from by decide,
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
      show ((1073741824 : Word) + 18 + 8 - 0x40000000).toNat = 26 from by decide,
      show ((1073741824 : Word) + 18 + 9 - 0x40000000).toNat = 27 from by decide,
      show ((1073741824 : Word) + 18 + 10 - 0x40000000).toNat = 28 from by decide,
      show ((1073741824 : Word) + 18 + 11 - 0x40000000).toNat = 29 from by decide]
    rw [show BitVec.zeroExtend 64 (bs.getD 26 0)
        ||| BitVec.zeroExtend 64 (bs.getD 27 0) <<< BitVec.toNat (8 : BitVec 6)
        ||| BitVec.zeroExtend 64 (bs.getD 28 0) <<< BitVec.toNat (16 : BitVec 6)
        ||| BitVec.zeroExtend 64 (bs.getD 29 0) <<< BitVec.toNat (24 : BitVec 6)
        = leU32 bs 26 from rfl]
    have hoff32 := leU32_toNat_lt bs 26
    rw [show ((1073741824 : Word) + 18 + leU32 bs 26 + 0 - 0x40000000).toNat
          = 18 + (leU32 bs 26).toNat from by bv_omega,
      show ((1073741824 : Word) + 18 + leU32 bs 26 + 1 - 0x40000000).toNat
          = 18 + (leU32 bs 26).toNat + 1 from by bv_omega,
      show ((1073741824 : Word) + 18 + leU32 bs 26 + 2 - 0x40000000).toNat
          = 18 + (leU32 bs 26).toNat + 2 from by bv_omega,
      show ((1073741824 : Word) + 18 + leU32 bs 26 + 3 - 0x40000000).toNat
          = 18 + (leU32 bs 26).toNat + 3 from by bv_omega,
      show ((1073741824 : Word) + 18 + leU32 bs 26 + 4 - 0x40000000).toNat
          = 18 + (leU32 bs 26).toNat + 4 from by bv_omega,
      show ((1073741824 : Word) + 18 + leU32 bs 26 + 5 - 0x40000000).toNat
          = 18 + (leU32 bs 26).toNat + 5 from by bv_omega,
      show ((1073741824 : Word) + 18 + leU32 bs 26 + 6 - 0x40000000).toNat
          = 18 + (leU32 bs 26).toNat + 6 from by bv_omega,
      show ((1073741824 : Word) + 18 + leU32 bs 26 + 7 - 0x40000000).toNat
          = 18 + (leU32 bs 26).toNat + 7 from by bv_omega]
    refine ⟨rfl, ?_⟩
    rw [show (1073741824 : Word) + 18 = (0x40000012 : Word) from by decide]

end EvmAsm.Stateless.SSZ.Decode
