/-
  EvmAsm.Evm64.StorageAssertions (transient storage assertions)

  Separation-logic assertions for the live EIP-1153 transient storage log.

  The transient log lives at `0xa0830000`.  Each entry is 128 bytes and
  contains four 32-byte EVM words: the executing address, slot key, original
  value, and current value.  The transient log length is the u64 cell at
  `env+464` (`transientLogLengthOff`).

  The historical append-only persistent storage-log assertions were retired;
  keeping this module focused on the EIP-1153 log prevents the old proof
  vocabulary from being mistaken for a live guest data structure.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Evm64.Environment.Layout

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Base of the transient (EIP-1153) storage log (`Storage.lean:10-12`). -/
def TRANSIENT_STORAGE_LOG_BASE : Word := 0xa0830000

/-! ## The entry and the assertions -/

/-- One 128-byte storage-log entry (`Storage.lean:14-22`). -/
structure StorageLogEntry where
  addrHash : EvmWord
  slotKey : EvmWord
  original : EvmWord
  current : EvmWord

/-- Ownership of one 128-byte storage-log entry at `addr`. -/
def storageSlotIs (addr : Word) (e : StorageLogEntry) : Assertion :=
  evmWordIs addr e.addrHash **
  evmWordIs (addr + 32) e.slotKey **
  evmWordIs (addr + 64) e.original **
  evmWordIs (addr + 96) e.current

/-- The EIP-1153 transient-storage log assertion. -/
def transientLogIs (base : Word) (entries : List StorageLogEntry) : Assertion :=
  match entries with
  | [] => empAssertion
  | e :: es => storageSlotIs base e ** transientLogIs (base + 128) es

/-- The transient-log length cell (`EvmEnv.transientLogLengthOff = 464`). -/
def transientLogLenIs (env : Word) (n : Nat) : Assertion :=
  (env + BitVec.ofNat 64 EvmEnv.transientLogLengthOff) ↦ₘ BitVec.ofNat 64 n

/-! ## Unfolds, pcFree, and congruence -/

theorem storageSlotIs_unfold {addr : Word} {e : StorageLogEntry} :
    storageSlotIs addr e =
      (evmWordIs addr e.addrHash **
       evmWordIs (addr + 32) e.slotKey **
       evmWordIs (addr + 64) e.original **
       evmWordIs (addr + 96) e.current) := rfl

theorem transientLogIs_nil {base : Word} :
    transientLogIs base [] = empAssertion := rfl

theorem transientLogIs_cons {base : Word} {e : StorageLogEntry}
    {es : List StorageLogEntry} :
    transientLogIs base (e :: es) =
      (storageSlotIs base e ** transientLogIs (base + 128) es) := rfl

theorem pcFree_storageSlotIs {addr : Word} {e : StorageLogEntry} :
    (storageSlotIs addr e).pcFree :=
  pcFree_sepConj pcFree_evmWordIs
    (pcFree_sepConj pcFree_evmWordIs
      (pcFree_sepConj pcFree_evmWordIs pcFree_evmWordIs))

theorem pcFree_transientLogIs {base : Word} {entries : List StorageLogEntry} :
    (transientLogIs base entries).pcFree := by
  induction entries generalizing base with
  | nil => exact pcFree_emp
  | cons _ _ ih => exact pcFree_sepConj pcFree_storageSlotIs ih

theorem pcFree_transientLogLenIs {env : Word} {n : Nat} :
    (transientLogLenIs env n).pcFree := pcFree_memIs

instance (addr : Word) (e : StorageLogEntry) :
    Assertion.PCFree (storageSlotIs addr e) := ⟨pcFree_storageSlotIs⟩

instance (base : Word) (entries : List StorageLogEntry) :
    Assertion.PCFree (transientLogIs base entries) := ⟨pcFree_transientLogIs⟩

instance (env : Word) (n : Nat) : Assertion.PCFree (transientLogLenIs env n) :=
  ⟨pcFree_transientLogLenIs⟩

theorem transientLogIs_congr {base : Word} {xs ys : List StorageLogEntry}
    (h : xs = ys) : transientLogIs base xs = transientLogIs base ys :=
  congrArg (transientLogIs base) h

/-! ## Append / snoc -/

/-- Concatenation of transient-log assertions at the 128-byte stride. -/
theorem transientLogIs_append (base : Word) (xs ys : List StorageLogEntry) :
    transientLogIs base (xs ++ ys) =
      (transientLogIs base xs **
       transientLogIs (base + BitVec.ofNat 64 (xs.length * 128)) ys) := by
  induction xs generalizing base with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_mul,
      transientLogIs_nil, sepConj_emp_left']
    rw [show (BitVec.ofNat 64 0 : Word) = 0 from rfl]
    rw [show base + (0 : Word) = base from by bv_omega]
  | cons x xs ih =>
    have hshift : base + (128 : Word) + BitVec.ofNat 64 (xs.length * 128) =
        base + BitVec.ofNat 64 ((xs.length + 1) * 128) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    simp only [List.cons_append, transientLogIs_cons, List.length_cons]
    rw [ih (base + 128), hshift, sepConj_assoc']

/-- Extending the transient log places the new entry at `base + length * 128`. -/
theorem transientLogIs_snoc {base : Word} {xs : List StorageLogEntry}
    {e : StorageLogEntry} :
    transientLogIs base (xs ++ [e]) =
      (transientLogIs base xs **
       storageSlotIs (base + BitVec.ofNat 64 (xs.length * 128)) e) := by
  rw [transientLogIs_append]
  congr 1
  rw [transientLogIs_cons, transientLogIs_nil, sepConj_emp_right']

end EvmAsm.Evm64
