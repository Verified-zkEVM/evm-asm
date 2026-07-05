/-
  EvmAsm.Evm64.StateAssertions

  Separation-logic assertion for the EVM interpreter memory region.

  ## Layout faithfulness (what this describes)

  The RISC-V guest keeps the current frame's EVM memory as a flat byte
  buffer at `EVM_MEMORY_AREA = 0xa0b70000` inside ziskemu's writable RAM
  zone (`EvmAsm/Stateless/MemoryLayout.lean`, working-RAM anchor table).
  The region is **statically allocated at 16 MiB per frame**: the block
  gas limit (~200 Mgas) bounds how far EVM memory can ever expand
  (quadratic memory-expansion gas makes even a single frame's memory far
  smaller than 16 MiB), so the guest never grows or relocates the buffer.
  `EVM_MEMORY_CAPACITY` below is that static allocation, and
  `evmMemoryIs` is parametrized by it.

  The MLOAD/MSTORE/MSTORE8 guest routines (`EvmAsm/Evm64/MLoad/*`,
  `MStore/*`, `MStore8/*`) access this buffer with byte loads/stores
  (`LBU`/`SB`) at `memBase + offset + c`; at the separation-logic level
  each 8-byte-aligned group of bytes is one RV64 dword cell (`↦ₘ`,
  little-endian `packBytes`), exactly the `bytesRegion` representation
  from `EvmAsm/Rv64/MemRegion.lean`. `evmMemoryIs` is `bytesRegion`
  over the whole allocation, so the proven opcode specs (which frame
  against raw dword cells) can be restated against it by *peeling* the
  touched dword window — see `evmMemoryIs_peel_word` /
  `evmMemoryIs_peel_window64` and
  `EvmAsm/Evm64/MLoad/MemoryRegionStackSpec.lean` (the reframed MLOAD
  stack spec, which proves this assertion is the guest's real memory).

  ## Zero-extended tail

  EVM memory reads beyond the current high-water mark return zero. The
  guest gets this for free: ziskemu's RAM is zero-initialized and the
  region is written only by the memory opcodes, so the not-yet-written
  tail of the 16 MiB allocation holds zero bytes. `evmMemoryIs` models
  the *full* allocation (`contents.length = capacity` is part of the
  assertion); the freshly-initialized state is `evmMemoryInit`, whose
  contents are all zeros, and a partially-written state is
  `live ++ List.replicate (capacity - live.length) 0`.
-/

import EvmAsm.Rv64.MemRegion
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-! ## Static capacity of the EVM memory region

The per-frame EVM memory allocation. 16 MiB, per the working-RAM anchor
table in `EvmAsm/Stateless/MemoryLayout.lean` (`EVM_MEMORY_AREA` row):
the ~200 Mgas block gas limit and the quadratic memory-expansion cost
bound any frame's EVM memory well below this, so the guest allocates a
fixed 16 MiB slab and never grows it. -/
def EVM_MEMORY_CAPACITY : Nat := 0x1000000

/-! ## The assertion -/

/-- `evmMemoryIs base capacity contents` — ownership of the guest's EVM
    memory buffer: the byte list `contents` stored little-endian-per-dword
    from `base` (`bytesRegion`), together with the pure fact that the
    buffer covers the full static allocation (`contents.length =
    capacity`). Instantiate `base := Stateless.EVM_MEMORY_AREA` and
    `capacity := EVM_MEMORY_CAPACITY` for the real guest region; the
    parameters keep the peel/framing lemmas usable for any statically
    allocated byte buffer. -/
def evmMemoryIs (base : Word) (capacity : Nat) (contents : List (BitVec 8)) : Assertion :=
  fun ps => contents.length = capacity ∧ bytesRegion base contents ps

/-- The freshly-initialized EVM memory region: all `capacity` bytes zero
    (ziskemu zero-initializes RAM, so this is the state at frame entry). -/
def evmMemoryInit (base : Word) (capacity : Nat) : Assertion :=
  evmMemoryIs base capacity (List.replicate capacity 0)

/-- The RV64 dword cell value holding bytes `[k, k+8)` of a byte list
    (zero-padded past the end, matching `packBytes`). -/
def dwordAt (bs : List (BitVec 8)) (k : Nat) : Word :=
  packBytes ((bs.drop k).take 8)

theorem evmMemoryIs_unfold {base : Word} {capacity : Nat} {contents : List (BitVec 8)} :
    evmMemoryIs base capacity contents =
      fun ps => contents.length = capacity ∧ bytesRegion base contents ps := rfl

/-- With the length side condition in hand, `evmMemoryIs` *is* the raw
    `bytesRegion` — the bridge to all `MemRegion` machinery. -/
theorem evmMemoryIs_eq_bytesRegion {base : Word} {capacity : Nat}
    {contents : List (BitVec 8)} (hlen : contents.length = capacity) :
    evmMemoryIs base capacity contents = bytesRegion base contents := by
  funext ps
  exact propext ⟨fun h => h.2, fun h => ⟨hlen, h⟩⟩

/-- `evmMemoryIs` pins the buffer length to the declared capacity: a
    satisfying state certifies `contents.length = capacity`. -/
theorem evmMemoryIs_length {base : Word} {capacity : Nat}
    {contents : List (BitVec 8)} {ps : PartialState}
    (h : evmMemoryIs base capacity contents ps) :
    contents.length = capacity := h.1

theorem evmMemoryInit_eq {base : Word} {capacity : Nat} :
    evmMemoryInit base capacity =
      evmMemoryIs base capacity (List.replicate capacity 0) := rfl

theorem pcFree_evmMemoryIs {base : Word} {capacity : Nat}
    {contents : List (BitVec 8)} :
    (evmMemoryIs base capacity contents).pcFree :=
  fun ps h => bytesRegion_pcFree base contents ps h.2

theorem pcFree_evmMemoryInit {base : Word} {capacity : Nat} :
    (evmMemoryInit base capacity).pcFree := pcFree_evmMemoryIs

instance (base : Word) (capacity : Nat) (contents : List (BitVec 8)) :
    Assertion.PCFree (evmMemoryIs base capacity contents) :=
  ⟨pcFree_evmMemoryIs⟩

instance (base : Word) (capacity : Nat) : Assertion.PCFree (evmMemoryInit base capacity) :=
  ⟨pcFree_evmMemoryInit⟩

/-- Contents-side congruence. -/
theorem evmMemoryIs_congr {base : Word} {capacity : Nat}
    {bs bs' : List (BitVec 8)} (h : bs = bs') :
    evmMemoryIs base capacity bs = evmMemoryIs base capacity bs' :=
  congrArg (evmMemoryIs base capacity) h

/-! ## Address arithmetic helpers -/

/-- Fold two `ofNat` offsets from the same base into one. Pure wrap-around
    BitVec arithmetic — no overflow side conditions. -/
theorem add_ofNat_add_ofNat (b : Word) (i j : Nat) :
    (b + BitVec.ofNat 64 i) + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Specialization: stepping a based offset by one dword. -/
theorem add_ofNat_add_eight (b : Word) (i : Nat) :
    (b + BitVec.ofNat 64 i) + 8 = b + BitVec.ofNat 64 (i + 8) := by
  rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl]
  exact add_ofNat_add_ofNat b i 8

/-! ## Region split and dword-window peel

The lemmas the memory opcodes need: split `bytesRegion` at a dword
boundary, and peel the dword cells covering one 32-byte EVM word (or the
64-byte window the proven MLOAD/MSTORE stack specs frame against). All
are *equalities* of assertions, so they rewrite in both pre and post
(peel to consume, `rw [←]` to fold back). -/

/-- Chunk-count split of `bytesRegionAux`: the first `m1` dwords cover
    `bs.take (8 * m1)`, the remainder continues at `base + 8 * m1`. -/
theorem bytesRegionAux_append (m1 m2 : Nat) (base : Word) (bs : List (BitVec 8)) :
    bytesRegionAux base (m1 + m2) bs =
      (bytesRegionAux base m1 (bs.take (8 * m1)) **
       bytesRegionAux (base + BitVec.ofNat 64 (8 * m1)) m2 (bs.drop (8 * m1))) := by
  induction m1 generalizing base bs with
  | zero =>
    simp only [Nat.zero_add, Nat.mul_zero, List.take_zero, List.drop_zero]
    rw [show bytesRegionAux base 0 ([] : List (BitVec 8)) = empAssertion from rfl,
        sepConj_emp_left']
    rw [show (BitVec.ofNat 64 0 : Word) = 0 from rfl,
        show base + (0 : Word) = base from by bv_omega]
  | succ k ih =>
    rw [show k + 1 + m2 = (k + m2) + 1 from by omega]
    rw [show bytesRegionAux base ((k + m2) + 1) bs =
        ((base ↦ₘ packBytes (bs.take 8)) **
         bytesRegionAux (base + 8) (k + m2) (bs.drop 8)) from rfl]
    rw [ih (base + 8) (bs.drop 8)]
    rw [show bytesRegionAux base (k + 1) (bs.take (8 * (k + 1))) =
        ((base ↦ₘ packBytes ((bs.take (8 * (k + 1))).take 8)) **
         bytesRegionAux (base + 8) k ((bs.take (8 * (k + 1))).drop 8)) from rfl]
    have htt : (bs.take (8 * (k + 1))).take 8 = bs.take 8 := by
      rw [List.take_take]
      congr 1
    have hdt : (bs.take (8 * (k + 1))).drop 8 = (bs.drop 8).take (8 * k) := by
      rw [List.drop_take]
      congr 1
    have hdd : (bs.drop 8).drop (8 * k) = bs.drop (8 * (k + 1)) := by
      rw [List.drop_drop]
      congr 1
      omega
    have haddr : (base + 8) + BitVec.ofNat 64 (8 * k) = base + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      have h8 : (8 : Word).toNat = 8 := by decide
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h8]
      omega
    rw [htt, hdt, hdd, haddr, sepConj_assoc']

/-- Split a byte region at a dword-aligned byte position `n`. -/
theorem bytesRegion_split (base : Word) (bs : List (BitVec 8)) (n : Nat)
    (h8 : n % 8 = 0) (hn : n ≤ bs.length) :
    bytesRegion base bs =
      (bytesRegion base (bs.take n) **
       bytesRegion (base + BitVec.ofNat 64 n) (bs.drop n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 8 * m := ⟨n / 8, by omega⟩
  show bytesRegionAux base ((bs.length + 7) / 8) bs = _
  have hchunks : (bs.length + 7) / 8 = m + ((bs.drop (8 * m)).length + 7) / 8 := by
    rw [List.length_drop]
    omega
  rw [hchunks, bytesRegionAux_append m _ base bs]
  congr 1
  show bytesRegionAux base m (bs.take (8 * m)) =
    bytesRegionAux base (((bs.take (8 * m)).length + 7) / 8) (bs.take (8 * m))
  congr 1
  rw [List.length_take]
  omega

/-- Peel the leading dword cell off a `take`-windowed region and step the
    window forward one dword. Building block for the word/window peels. -/
theorem bytesRegion_take_chunk (b : Word) (bs : List (BitVec 8)) (k n : Nat)
    (hk : k < bs.length) (hn : 8 ≤ n) :
    bytesRegion b ((bs.drop k).take n) =
      ((b ↦ₘ dwordAt bs k) **
       bytesRegion (b + 8) ((bs.drop (k + 8)).take (n - 8))) := by
  have hne : (bs.drop k).take n ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_take, List.length_drop, List.length_nil] at this
    omega
  rw [bytesRegion_eq_cons _ _ hne]
  have htt : ((bs.drop k).take n).take 8 = (bs.drop k).take 8 := by
    rw [List.take_take]
    congr 1
    omega
  have hdt : ((bs.drop k).take n).drop 8 = (bs.drop (k + 8)).take (n - 8) := by
    rw [List.drop_take, List.drop_drop]
  rw [htt, hdt]
  rfl

/-- **Peel a 32-byte EVM word at dword-aligned offset `k`.** The four
    dword cells covering bytes `[k, k+32)` come out of `evmMemoryIs` as
    raw `↦ₘ` atoms (the shape the MLOAD/MSTORE limb specs consume), with
    the untouched front and tail staying `bytesRegion`s. Being an
    equality, `rw [←]` folds an unchanged (or value-updated) window back. -/
theorem evmMemoryIs_peel_word (base : Word) (capacity k : Nat) (bs : List (BitVec 8))
    (hlen : bs.length = capacity) (hk8 : k % 8 = 0) (hin : k + 32 ≤ bs.length) :
    evmMemoryIs base capacity bs =
      (bytesRegion base (bs.take k) **
       ((base + BitVec.ofNat 64 k) ↦ₘ dwordAt bs k) **
       ((base + BitVec.ofNat 64 (k + 8)) ↦ₘ dwordAt bs (k + 8)) **
       ((base + BitVec.ofNat 64 (k + 16)) ↦ₘ dwordAt bs (k + 16)) **
       ((base + BitVec.ofNat 64 (k + 24)) ↦ₘ dwordAt bs (k + 24)) **
       bytesRegion (base + BitVec.ofNat 64 (k + 32)) (bs.drop (k + 32))) := by
  rw [evmMemoryIs_eq_bytesRegion hlen,
      bytesRegion_split base bs k hk8 (by omega)]
  have hsplit2 : bytesRegion (base + BitVec.ofNat 64 k) (bs.drop k) =
      (bytesRegion (base + BitVec.ofNat 64 k) ((bs.drop k).take 32) **
       bytesRegion (base + BitVec.ofNat 64 (k + 32)) (bs.drop (k + 32))) := by
    rw [bytesRegion_split (base + BitVec.ofNat 64 k) (bs.drop k) 32 (by omega)
        (by rw [List.length_drop]; omega)]
    rw [add_ofNat_add_ofNat, List.drop_drop]
  rw [hsplit2]
  rw [bytesRegion_take_chunk _ bs k 32 (by omega) (by omega),
      add_ofNat_add_eight,
      show (32 : Nat) - 8 = 24 from rfl,
      bytesRegion_take_chunk _ bs (k + 8) 24 (by omega) (by omega),
      add_ofNat_add_eight,
      show (24 : Nat) - 8 = 16 from rfl,
      bytesRegion_take_chunk _ bs (k + 8 + 8) 16 (by omega) (by omega),
      add_ofNat_add_eight,
      show (16 : Nat) - 8 = 8 from rfl,
      bytesRegion_take_chunk _ bs (k + 8 + 8 + 8) 8 (by omega) (by omega)]
  rw [show k + 8 + 8 = k + 16 from by omega, show k + 8 + 8 + 8 = k + 24 from by omega]
  simp only [Nat.sub_self, List.take_zero, bytesRegion_nil, sepConj_emp_right']
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

/-- **Peel the 64-byte dword window at dword-aligned offset `k`** — eight
    consecutive dword cells. This is the exact memory footprint of the
    proven aligned MLOAD/MSTORE stack specs
    (`evm_mload_stack_spec_within` / `evm_mstore_stack_spec_within`):
    four lo/hi dword pairs, of which the four lo cells cover the accessed
    32-byte word `[k, k+32)` and the four hi cells `[k+32, k+64)` are the
    windows' scratch dwords (owned but unread when the access is
    dword-aligned). -/
theorem evmMemoryIs_peel_window64 (base : Word) (capacity k : Nat) (bs : List (BitVec 8))
    (hlen : bs.length = capacity) (hk8 : k % 8 = 0) (hin : k + 64 ≤ bs.length) :
    evmMemoryIs base capacity bs =
      (bytesRegion base (bs.take k) **
       ((base + BitVec.ofNat 64 k) ↦ₘ dwordAt bs k) **
       ((base + BitVec.ofNat 64 (k + 8)) ↦ₘ dwordAt bs (k + 8)) **
       ((base + BitVec.ofNat 64 (k + 16)) ↦ₘ dwordAt bs (k + 16)) **
       ((base + BitVec.ofNat 64 (k + 24)) ↦ₘ dwordAt bs (k + 24)) **
       ((base + BitVec.ofNat 64 (k + 32)) ↦ₘ dwordAt bs (k + 32)) **
       ((base + BitVec.ofNat 64 (k + 40)) ↦ₘ dwordAt bs (k + 40)) **
       ((base + BitVec.ofNat 64 (k + 48)) ↦ₘ dwordAt bs (k + 48)) **
       ((base + BitVec.ofNat 64 (k + 56)) ↦ₘ dwordAt bs (k + 56)) **
       bytesRegion (base + BitVec.ofNat 64 (k + 64)) (bs.drop (k + 64))) := by
  rw [evmMemoryIs_eq_bytesRegion hlen,
      bytesRegion_split base bs k hk8 (by omega)]
  have hsplit2 : bytesRegion (base + BitVec.ofNat 64 k) (bs.drop k) =
      (bytesRegion (base + BitVec.ofNat 64 k) ((bs.drop k).take 64) **
       bytesRegion (base + BitVec.ofNat 64 (k + 64)) (bs.drop (k + 64))) := by
    rw [bytesRegion_split (base + BitVec.ofNat 64 k) (bs.drop k) 64 (by omega)
        (by rw [List.length_drop]; omega)]
    rw [add_ofNat_add_ofNat, List.drop_drop]
  rw [hsplit2]
  rw [bytesRegion_take_chunk _ bs k 64 (by omega) (by omega),
      add_ofNat_add_eight,
      show (64 : Nat) - 8 = 56 from rfl,
      bytesRegion_take_chunk _ bs (k + 8) 56 (by omega) (by omega),
      add_ofNat_add_eight,
      show (56 : Nat) - 8 = 48 from rfl,
      bytesRegion_take_chunk _ bs (k + 8 + 8) 48 (by omega) (by omega),
      add_ofNat_add_eight,
      show (48 : Nat) - 8 = 40 from rfl,
      bytesRegion_take_chunk _ bs (k + 8 + 8 + 8) 40 (by omega) (by omega),
      add_ofNat_add_eight,
      show (40 : Nat) - 8 = 32 from rfl,
      bytesRegion_take_chunk _ bs (k + 8 + 8 + 8 + 8) 32 (by omega) (by omega),
      add_ofNat_add_eight,
      show (32 : Nat) - 8 = 24 from rfl,
      bytesRegion_take_chunk _ bs (k + 8 + 8 + 8 + 8 + 8) 24 (by omega) (by omega),
      add_ofNat_add_eight,
      show (24 : Nat) - 8 = 16 from rfl,
      bytesRegion_take_chunk _ bs (k + 8 + 8 + 8 + 8 + 8 + 8) 16 (by omega) (by omega),
      add_ofNat_add_eight,
      show (16 : Nat) - 8 = 8 from rfl,
      bytesRegion_take_chunk _ bs (k + 8 + 8 + 8 + 8 + 8 + 8 + 8) 8 (by omega) (by omega)]
  rw [show k + 8 + 8 = k + 16 from by omega,
      show k + 8 + 8 + 8 = k + 24 from by omega,
      show k + 8 + 8 + 8 + 8 = k + 32 from by omega,
      show k + 8 + 8 + 8 + 8 + 8 = k + 40 from by omega,
      show k + 8 + 8 + 8 + 8 + 8 + 8 = k + 48 from by omega,
      show k + 8 + 8 + 8 + 8 + 8 + 8 + 8 = k + 56 from by omega]
  simp only [Nat.sub_self, List.take_zero, bytesRegion_nil, sepConj_emp_right']
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc', sepConj_assoc',
      sepConj_assoc', sepConj_assoc', sepConj_assoc']

/-! ## Region placement facts

Validity and disjointness of the concrete `EVM_MEMORY_AREA` allocation
against the rest of the working-RAM anchor map
(`EvmAsm/Stateless/MemoryLayout.lean`). These discharge the
`isValidByteAccess` side conditions of the byte-level opcode specs and
document that the 16 MiB slab does not alias its neighbours
(`EVM_VALUE_STACK` below, `KECCAK_SCRATCH` above). -/

theorem EVM_MEMORY_AREA_toNat : Stateless.EVM_MEMORY_AREA.toNat = 0xa0b70000 := rfl

theorem EVM_MEMORY_AREA_aligned : Stateless.EVM_MEMORY_AREA.toNat % 8 = 0 := by decide

/-- Every byte of the 16 MiB EVM memory slab is a valid guest address:
    `0xa0b70000 + k` with `k < 0x1000000` sits inside ziskemu's writable
    RAM zone `RAM_MEM_START .. RAM_MEM_END` (`0xa0000000 .. 0xc0000000`). -/
theorem isValidMemAddr_evmMemoryArea {k : Nat} (hk : k < EVM_MEMORY_CAPACITY) :
    isValidMemAddr (Stateless.EVM_MEMORY_AREA + BitVec.ofNat 64 k) = true := by
  have hcap : EVM_MEMORY_CAPACITY = 0x1000000 := rfl
  have htoNat : (Stateless.EVM_MEMORY_AREA + BitVec.ofNat 64 k).toNat = 0xa0b70000 + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, EVM_MEMORY_AREA_toNat]
    omega
  simp only [isValidMemAddr_eq, htoNat, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  right
  constructor
  · show RAM_MEM_START ≤ 0xa0b70000 + k
    have : RAM_MEM_START = 0xa0000000 := rfl
    omega
  · show 0xa0b70000 + k ≤ RAM_MEM_END
    have : RAM_MEM_END = 0xc0000000 := rfl
    omega

/-- The EVM memory slab is disjoint from the EVM value stack below it
    (`EVM_VALUE_STACK = 0xa0a70000`, 1 MiB): no address aliases. -/
theorem evmMemoryArea_disjoint_valueStack {i j : Nat}
    (hi : i < EVM_MEMORY_CAPACITY) (hj : j < 0x100000) :
    Stateless.EVM_MEMORY_AREA + BitVec.ofNat 64 i ≠
      Stateless.EVM_VALUE_STACK + BitVec.ofNat 64 j := by
  intro h
  have hcap : EVM_MEMORY_CAPACITY = 0x1000000 := rfl
  have hmem : (Stateless.EVM_MEMORY_AREA + BitVec.ofNat 64 i).toNat = 0xa0b70000 + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, EVM_MEMORY_AREA_toNat]
    omega
  have hstk : (Stateless.EVM_VALUE_STACK + BitVec.ofNat 64 j).toNat = 0xa0a70000 + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
        show Stateless.EVM_VALUE_STACK.toNat = 0xa0a70000 from rfl]
    omega
  have := congrArg BitVec.toNat h
  rw [hmem, hstk] at this
  omega

/-- The EVM memory slab is disjoint from the Keccak scratch buffer above
    it (`KECCAK_SCRATCH = 0xa1b70000`, 64 KiB): the slab ends exactly at
    the scratch base. -/
theorem evmMemoryArea_disjoint_keccakScratch {i j : Nat}
    (hi : i < EVM_MEMORY_CAPACITY) (hj : j < 0x10000) :
    Stateless.EVM_MEMORY_AREA + BitVec.ofNat 64 i ≠
      Stateless.KECCAK_SCRATCH + BitVec.ofNat 64 j := by
  intro h
  have hcap : EVM_MEMORY_CAPACITY = 0x1000000 := rfl
  have hmem : (Stateless.EVM_MEMORY_AREA + BitVec.ofNat 64 i).toNat = 0xa0b70000 + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, EVM_MEMORY_AREA_toNat]
    omega
  have hscr : (Stateless.KECCAK_SCRATCH + BitVec.ofNat 64 j).toNat = 0xa1b70000 + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
        show Stateless.KECCAK_SCRATCH.toNat = 0xa1b70000 from rfl]
    omega
  have := congrArg BitVec.toNat h
  rw [hmem, hscr] at this
  omega

end EvmAsm.Evm64
