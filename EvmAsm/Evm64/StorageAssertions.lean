/-
  EvmAsm.Evm64.StorageAssertions

  Separation-logic assertions for the guest's storage data structures —
  the append-only storage exec-logs SLOAD/SSTORE (and TLOAD/TSTORE)
  actually read and write.

  ## Layout faithfulness (what this describes)

  Derived from `EvmAsm/Codegen/Programs/Storage.lean` (M24 "Option A"
  handlers), the authoritative layout:

  * Two logs live in `STATE_TRACKER_AREA` (`0xa0630000`, 4 MiB —
    `EvmAsm/Stateless/MemoryLayout.lean`): the persistent storage log at
    `0xa0630000` (SLOAD/SSTORE) and the transient log at `0xa0830000`
    (EIP-1153 TLOAD/TSTORE).
  * Each entry is **128 bytes, 8-byte aligned**:
    `+0..32 addrHash` (the executing frame's `env.ADDRESS` — per-contract
    keying), `+32..64 slotKey`, `+64..96 original` (pre-tx value),
    `+96..128 current` (latest committed value). The three value fields
    are 32-byte words in EVM-stack byte order — 4 little-endian u64
    limbs, low limb first — i.e. exactly the existing `evmWordIs`
    convention (`EvmAsm/Evm64/Stack.lean`); `addrHash` is compared
    dword-wise in the same shape.
  * Entry `i` sits at `base + i * 128`; SSTORE **always appends** at
    `base + logLength * 128` (the guest computes it as
    `slli x16, x15, 7`, `Storage.lean:421`), never mutating prior
    entries — REVERT is a log-length truncation.
  * Log lengths are u64 cells in the env block
    (`EvmAsm/Evm64/Environment/Layout.lean`): `env+448`
    (`persistentLogLengthOff`), `env+456` (checkpoint), `env+464`
    (`transientLogLengthOff`).

  ## Static sizing (the capacity parameter)

  The persistent log arena is **statically capped at 16384 entries**
  (`Storage.lean:381`, `Dispatch.lean:2242`; `Codegen/RegionMap.lean:155`
  records the live extent `0xa0630000..0xa0830000` = 2 MiB = 16384 × 128).
  The block gas limit bounds how many SSTOREs (≥ 100 gas each) a tx can
  ever perform, so the fixed arena never overflows in valid executions;
  the guest still guards the cap at runtime. `STORAGE_LOG_CAPACITY`
  carries that constant; the placement lemmas below are stated for any
  in-capacity index.

  ## `committedStorageIs`

  The cross-transaction committed-storage table
  (`Codegen/Programs/CommittedStorageSnapshot.lean` /
  `CommittedStorageLookup.lean`, params in `BlockVerdictParams.lean:105`)
  uses the **same 128-byte entry shape** (with `addrHash` holding the
  zero-padded 20-byte tx recipient instead of the frame address), so its
  assertion is the same log predicate at a different base/capacity
  (`bvMtxCommittedEntryBytes = 128`, chunk capacity 512).

  Like the account routines, the storage handlers are inline-asm codegen
  programs with no functional `cpsTripleWithin` specs yet; this module
  fixes the assertion vocabulary those specs (and the SLOAD/SSTORE
  opcode triples) will be stated in, and ships the split/append lemmas
  the lookup (scan-from-end) and append paths need.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Evm64.Environment.Layout
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-! ## Constants (cited from the guest) -/

/-- Bytes per storage-log entry (`Storage.lean` entry format). -/
def STORAGE_LOG_ENTRY_BYTES : Nat := 128

/-- Static entry capacity of the persistent log arena
    (`Storage.lean:381`, `Dispatch.lean:2242`): 16384 × 128 B = 2 MiB,
    the live extent `0xa0630000..0xa0830000` recorded in
    `Codegen/RegionMap.lean`. -/
def STORAGE_LOG_CAPACITY : Nat := 16384

/-- Base of the persistent storage log — the bottom of
    `STATE_TRACKER_AREA`. -/
def PERSISTENT_STORAGE_LOG_BASE : Word := Stateless.STATE_TRACKER_AREA

/-- Base of the transient (EIP-1153) storage log (`Storage.lean:10-12`). -/
def TRANSIENT_STORAGE_LOG_BASE : Word := 0xa0830000

-- The persistent arena ends exactly at the transient base.
#guard STORAGE_LOG_CAPACITY * STORAGE_LOG_ENTRY_BYTES = 0x200000
#guard PERSISTENT_STORAGE_LOG_BASE + BitVec.ofNat 64 0x200000 =
  TRANSIENT_STORAGE_LOG_BASE

/-! ## The entry and the assertions -/

/-- One 128-byte storage-log entry (`Storage.lean:14-22`): the four
    32-byte fields in their on-arena order. All four are stored as 4
    little-endian u64 limbs (the `evmWordIs` shape); `addrHash` holds
    the executing frame's `env.ADDRESS` (20-byte address zero-extended),
    `slotKey` the EVM stack key, `original` the slot's pre-tx value,
    `current` the latest committed value. -/
structure StorageLogEntry where
  addrHash : EvmWord
  slotKey : EvmWord
  original : EvmWord
  current : EvmWord

/-- `storageSlotIs addr e` — ownership of one 128-byte storage-log entry
    at `addr`: the four 32-byte fields at `+0/+32/+64/+96`. -/
def storageSlotIs (addr : Word) (e : StorageLogEntry) : Assertion :=
  evmWordIs addr e.addrHash **
  evmWordIs (addr + 32) e.slotKey **
  evmWordIs (addr + 64) e.original **
  evmWordIs (addr + 96) e.current

/-- `storageLogIs base entries` — the append-only storage exec-log:
    entry `i` of `entries` at `base + i * 128`. Mirrors `evmStackIs`'s
    structure with a 128-byte stride. -/
def storageLogIs (base : Word) (entries : List StorageLogEntry) : Assertion :=
  match entries with
  | [] => empAssertion
  | e :: es => storageSlotIs base e ** storageLogIs (base + 128) es

/-- The committed-storage table (`bv_mtx_committed*`) shares the exact
    128-byte entry shape, re-keyed by tx recipient
    (`CommittedStorageSnapshot.lean:29-34`); its assertion is the same
    log predicate at the table's base. -/
def committedStorageIs : Word → List StorageLogEntry → Assertion :=
  storageLogIs

/-- The persistent-log length cell: the u64 at `env + 448`
    (`EvmEnv.persistentLogLengthOff`, `Environment/Layout.lean:99`) holding the
    live entry count. SSTORE increments it; REVERT restores it from the
    checkpoint cell. -/
def storageLogLenIs (env : Word) (n : Nat) : Assertion :=
  (env + BitVec.ofNat 64 EvmEnv.persistentLogLengthOff) ↦ₘ BitVec.ofNat 64 n

/-- The transient-log length cell (`EvmEnv.transientLogLengthOff = 464`). -/
def transientLogLenIs (env : Word) (n : Nat) : Assertion :=
  (env + BitVec.ofNat 64 EvmEnv.transientLogLengthOff) ↦ₘ BitVec.ofNat 64 n

/-! ## Unfolds, pcFree, congruence -/

theorem storageSlotIs_unfold {addr : Word} {e : StorageLogEntry} :
    storageSlotIs addr e =
      (evmWordIs addr e.addrHash **
       evmWordIs (addr + 32) e.slotKey **
       evmWordIs (addr + 64) e.original **
       evmWordIs (addr + 96) e.current) := rfl

theorem storageLogIs_nil {base : Word} :
    storageLogIs base [] = empAssertion := rfl

theorem storageLogIs_cons {base : Word} {e : StorageLogEntry}
    {es : List StorageLogEntry} :
    storageLogIs base (e :: es) =
      (storageSlotIs base e ** storageLogIs (base + 128) es) := rfl

theorem pcFree_storageSlotIs {addr : Word} {e : StorageLogEntry} :
    (storageSlotIs addr e).pcFree :=
  pcFree_sepConj pcFree_evmWordIs
    (pcFree_sepConj pcFree_evmWordIs
      (pcFree_sepConj pcFree_evmWordIs pcFree_evmWordIs))

theorem pcFree_storageLogIs {base : Word} {entries : List StorageLogEntry} :
    (storageLogIs base entries).pcFree := by
  induction entries generalizing base with
  | nil => exact pcFree_emp
  | cons _ _ ih => exact pcFree_sepConj pcFree_storageSlotIs ih

theorem pcFree_storageLogLenIs {env : Word} {n : Nat} :
    (storageLogLenIs env n).pcFree := pcFree_memIs

theorem pcFree_transientLogLenIs {env : Word} {n : Nat} :
    (transientLogLenIs env n).pcFree := pcFree_memIs

instance (addr : Word) (e : StorageLogEntry) :
    Assertion.PCFree (storageSlotIs addr e) := ⟨pcFree_storageSlotIs⟩

instance (base : Word) (entries : List StorageLogEntry) :
    Assertion.PCFree (storageLogIs base entries) := ⟨pcFree_storageLogIs⟩

instance (env : Word) (n : Nat) : Assertion.PCFree (storageLogLenIs env n) :=
  ⟨pcFree_storageLogLenIs⟩

instance (env : Word) (n : Nat) : Assertion.PCFree (transientLogLenIs env n) :=
  ⟨pcFree_transientLogLenIs⟩

theorem storageLogIs_congr {base : Word} {xs ys : List StorageLogEntry}
    (h : xs = ys) : storageLogIs base xs = storageLogIs base ys :=
  congrArg (storageLogIs base) h

/-! ## Append / snoc / split — the lemmas SLOAD/SSTORE need -/

/-- Concatenation: a log of `xs ++ ys` splits at the 128-byte stride.
    Mirrors `evmStackIs_append`. -/
theorem storageLogIs_append (base : Word) (xs ys : List StorageLogEntry) :
    storageLogIs base (xs ++ ys) =
      (storageLogIs base xs **
       storageLogIs (base + BitVec.ofNat 64 (xs.length * 128)) ys) := by
  induction xs generalizing base with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_mul,
               storageLogIs_nil, sepConj_emp_left']
    rw [show (BitVec.ofNat 64 0 : Word) = 0 from rfl]
    rw [show base + (0 : Word) = base from by bv_omega]
  | cons e es ih =>
    have hshift : base + (128 : Word) + BitVec.ofNat 64 (es.length * 128) =
        base + BitVec.ofNat 64 ((es.length + 1) * 128) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    simp only [List.cons_append, storageLogIs_cons, List.length_cons]
    rw [ih (base + 128), hshift, sepConj_assoc']

/-- **The SSTORE append shape**: extending the log by one entry places it
    at `base + length * 128` — exactly the address the guest computes
    (`slli x16, x15, 7` over the live length counter,
    `Storage.lean:421`). -/
theorem storageLogIs_snoc {base : Word} {xs : List StorageLogEntry}
    {e : StorageLogEntry} :
    storageLogIs base (xs ++ [e]) =
      (storageLogIs base xs **
       storageSlotIs (base + BitVec.ofNat 64 (xs.length * 128)) e) := by
  rw [storageLogIs_append]
  congr 1
  rw [storageLogIs_cons, storageLogIs_nil, sepConj_emp_right']

/-- **The SLOAD lookup shape**: isolate entry `i` (0-indexed) of the log,
    framing the entries before and after it. The scan-from-end handler
    reads the isolated entry's `slotKey`/`addrHash` for the match and its
    `current` for the result. Mirrors `evmStackIs_split_at`. -/
theorem storageLogIs_split_at (base : Word) (entries : List StorageLogEntry)
    (i : Nat) (hi : i < entries.length) :
    storageLogIs base entries =
      (storageLogIs base (entries.take i) **
       storageSlotIs (base + BitVec.ofNat 64 (i * 128)) (entries[i]'hi) **
       storageLogIs (base + BitVec.ofNat 64 ((i + 1) * 128))
         (entries.drop (i + 1))) := by
  induction i generalizing base entries with
  | zero =>
    cases entries with
    | nil => simp at hi
    | cons e es =>
      simp only [Nat.zero_mul, List.take_zero, List.drop_succ_cons,
                 List.drop_zero, List.getElem_cons_zero, storageLogIs_cons,
                 storageLogIs_nil, sepConj_emp_left', BitVec.add_zero]
      congr 1
  | succ k ih =>
    cases entries with
    | nil => simp at hi
    | cons e es =>
      have hk' : k < es.length := by simp at hi; omega
      have a1 : base + (128 : Word) + BitVec.ofNat 64 (k * 128) =
          base + BitVec.ofNat 64 ((k + 1) * 128) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      have a2 : base + (128 : Word) + BitVec.ofNat 64 ((k + 1) * 128) =
          base + BitVec.ofNat 64 ((k + 2) * 128) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rw [storageLogIs_cons, ih (base + 128) es hk', a1, a2]
      simp only [List.take_succ_cons, List.drop_succ_cons,
                 List.getElem_cons_succ]
      simp only [storageLogIs_cons, sepConj_assoc']

/-! ## Placement facts (the concrete arenas) -/

theorem STATE_TRACKER_AREA_toNat :
    Stateless.STATE_TRACKER_AREA.toNat = 0xa0630000 := rfl

/-- Every byte of the 4 MiB state-tracker area (both logs) is a valid
    guest address inside ziskemu's writable RAM zone. -/
theorem isValidMemAddr_stateTrackerArea {k : Nat} (hk : k < 0x400000) :
    isValidMemAddr (Stateless.STATE_TRACKER_AREA + BitVec.ofNat 64 k) = true := by
  have htoNat : (Stateless.STATE_TRACKER_AREA + BitVec.ofNat 64 k).toNat =
      0xa0630000 + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, STATE_TRACKER_AREA_toNat]
    omega
  simp only [isValidMemAddr_eq, htoNat, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  right
  constructor
  · show RAM_MEM_START ≤ 0xa0630000 + k
    have : RAM_MEM_START = 0xa0000000 := rfl
    omega
  · show 0xa0630000 + k ≤ RAM_MEM_END
    have : RAM_MEM_END = 0xc0000000 := rfl
    omega

/-- In-capacity persistent-log entries never alias the transient log:
    entry `i < 16384` occupies `[i*128, i*128+128) ⊂ [0, 2 MiB)`, and the
    transient log starts exactly at the 2 MiB mark. -/
theorem persistentLog_disjoint_transientLog {i b j : Nat}
    (hi : i < STORAGE_LOG_CAPACITY) (hb : b < STORAGE_LOG_ENTRY_BYTES)
    (hj : j < 0x200000) :
    PERSISTENT_STORAGE_LOG_BASE + BitVec.ofNat 64 (i * 128 + b) ≠
      TRANSIENT_STORAGE_LOG_BASE + BitVec.ofNat 64 j := by
  intro h
  have hcap : STORAGE_LOG_CAPACITY = 16384 := rfl
  have hentry : STORAGE_LOG_ENTRY_BYTES = 128 := rfl
  have hp : (PERSISTENT_STORAGE_LOG_BASE + BitVec.ofNat 64 (i * 128 + b)).toNat =
      0xa0630000 + (i * 128 + b) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
        show PERSISTENT_STORAGE_LOG_BASE.toNat = 0xa0630000 from rfl]
    omega
  have ht : (TRANSIENT_STORAGE_LOG_BASE + BitVec.ofNat 64 j).toNat =
      0xa0830000 + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
        show TRANSIENT_STORAGE_LOG_BASE.toNat = 0xa0830000 from rfl]
    omega
  have := congrArg BitVec.toNat h
  rw [hp, ht] at this
  omega

/-! ## Consuming the assertion (worked example)

The SLOAD scan isolates one entry and reads its fields; the split lemma
produces exactly the `evmWordIs` atoms the existing word-load machinery
consumes, and folds back unchanged (`rw [←]`). -/

example (base : Word) (e0 e1 e2 : StorageLogEntry) :
    storageLogIs base [e0, e1, e2] =
      (storageLogIs base [e0] **
       (evmWordIs (base + BitVec.ofNat 64 128) e1.addrHash **
        evmWordIs (base + BitVec.ofNat 64 128 + 32) e1.slotKey **
        evmWordIs (base + BitVec.ofNat 64 128 + 64) e1.original **
        evmWordIs (base + BitVec.ofNat 64 128 + 96) e1.current) **
       storageLogIs (base + BitVec.ofNat 64 256) [e2]) := by
  rw [storageLogIs_split_at base [e0, e1, e2] 1 (by simp)]
  rfl

-- Entry 16383 (the last in-capacity entry) still ends inside the arena.
#guard (STORAGE_LOG_CAPACITY - 1) * STORAGE_LOG_ENTRY_BYTES +
  STORAGE_LOG_ENTRY_BYTES = 0x200000

end EvmAsm.Evm64
