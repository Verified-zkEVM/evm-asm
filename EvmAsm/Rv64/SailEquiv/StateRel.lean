/-
  EvmAsm.Rv64.SailEquiv.StateRel

  Abstraction relation between the simplified Rv64 MachineState
  and the SAIL-generated RISC-V formal spec state.
-/

import EvmAsm.Rv64.Basic
import Out

open Out.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Type abbreviations
-- ============================================================================

/-- The SAIL machine state type. -/
abbrev SailState := PreSail.SequentialState RegisterType trivialChoiceSource

-- ============================================================================
-- Register mapping: Rv64.Reg → regidx (5-bit index)
-- ============================================================================

/-- Map Rv64.Reg to the SAIL 5-bit register index. -/
def regToRegidx : Reg → regidx
  | .x0  => regidx.Regidx 0
  | .x1  => regidx.Regidx 1
  | .x2  => regidx.Regidx 2
  | .x3  => regidx.Regidx 3
  | .x4  => regidx.Regidx 4
  | .x5  => regidx.Regidx 5
  | .x6  => regidx.Regidx 6
  | .x7  => regidx.Regidx 7
  | .x8  => regidx.Regidx 8
  | .x9  => regidx.Regidx 9
  | .x10 => regidx.Regidx 10
  | .x11 => regidx.Regidx 11
  | .x12 => regidx.Regidx 12
  | .x13 => regidx.Regidx 13
  | .x14 => regidx.Regidx 14
  | .x15 => regidx.Regidx 15
  | .x16 => regidx.Regidx 16
  | .x17 => regidx.Regidx 17
  | .x18 => regidx.Regidx 18
  | .x19 => regidx.Regidx 19
  | .x20 => regidx.Regidx 20
  | .x21 => regidx.Regidx 21
  | .x22 => regidx.Regidx 22
  | .x23 => regidx.Regidx 23
  | .x24 => regidx.Regidx 24
  | .x25 => regidx.Regidx 25
  | .x26 => regidx.Regidx 26
  | .x27 => regidx.Regidx 27
  | .x28 => regidx.Regidx 28
  | .x29 => regidx.Regidx 29
  | .x30 => regidx.Regidx 30
  | .x31 => regidx.Regidx 31

-- ============================================================================
-- Register mapping: Rv64.Reg → Register (SAIL state key, for non-x0)
-- ============================================================================

/-- Map an Rv64 non-x0 register to its SAIL Register key.
    x0 has no entry in the state (hardwired zero). -/
def regToSailReg : Reg → Option Register
  | .x0  => none
  | .x1  => some Register.x1
  | .x2  => some Register.x2
  | .x3  => some Register.x3
  | .x4  => some Register.x4
  | .x5  => some Register.x5
  | .x6  => some Register.x6
  | .x7  => some Register.x7
  | .x8  => some Register.x8
  | .x9  => some Register.x9
  | .x10 => some Register.x10
  | .x11 => some Register.x11
  | .x12 => some Register.x12
  | .x13 => some Register.x13
  | .x14 => some Register.x14
  | .x15 => some Register.x15
  | .x16 => some Register.x16
  | .x17 => some Register.x17
  | .x18 => some Register.x18
  | .x19 => some Register.x19
  | .x20 => some Register.x20
  | .x21 => some Register.x21
  | .x22 => some Register.x22
  | .x23 => some Register.x23
  | .x24 => some Register.x24
  | .x25 => some Register.x25
  | .x26 => some Register.x26
  | .x27 => some Register.x27
  | .x28 => some Register.x28
  | .x29 => some Register.x29
  | .x30 => some Register.x30
  | .x31 => some Register.x31

/-- Pure register lookup: read an integer register value from SAIL state.
    Returns 0 for x0, or looks up in the ExtDHashMap for others.
    Each case is concrete so Lean knows RegisterType Register.xN = BitVec 64. -/
noncomputable def sailRegVal (s : SailState) (r : Reg) : Option (BitVec 64) :=
  match r with
  | .x0  => some 0#64  -- x0 is hardwired zero
  | .x1  => s.regs.get? Register.x1
  | .x2  => s.regs.get? Register.x2
  | .x3  => s.regs.get? Register.x3
  | .x4  => s.regs.get? Register.x4
  | .x5  => s.regs.get? Register.x5
  | .x6  => s.regs.get? Register.x6
  | .x7  => s.regs.get? Register.x7
  | .x8  => s.regs.get? Register.x8
  | .x9  => s.regs.get? Register.x9
  | .x10 => s.regs.get? Register.x10
  | .x11 => s.regs.get? Register.x11
  | .x12 => s.regs.get? Register.x12
  | .x13 => s.regs.get? Register.x13
  | .x14 => s.regs.get? Register.x14
  | .x15 => s.regs.get? Register.x15
  | .x16 => s.regs.get? Register.x16
  | .x17 => s.regs.get? Register.x17
  | .x18 => s.regs.get? Register.x18
  | .x19 => s.regs.get? Register.x19
  | .x20 => s.regs.get? Register.x20
  | .x21 => s.regs.get? Register.x21
  | .x22 => s.regs.get? Register.x22
  | .x23 => s.regs.get? Register.x23
  | .x24 => s.regs.get? Register.x24
  | .x25 => s.regs.get? Register.x25
  | .x26 => s.regs.get? Register.x26
  | .x27 => s.regs.get? Register.x27
  | .x28 => s.regs.get? Register.x28
  | .x29 => s.regs.get? Register.x29
  | .x30 => s.regs.get? Register.x30
  | .x31 => s.regs.get? Register.x31

-- ============================================================================
-- Running SAIL computations
-- ============================================================================

/-- Run a SAIL monadic computation, returning the result and final state (or none on error). -/
noncomputable def runSail (m : SailM α) (s : SailState) : Option (α × SailState) :=
  match m s with
  | .ok v s' => some (v, s')
  | .error _ _ => none

-- ============================================================================
-- Memory reconstruction: SAIL byte-addressed → Rv64 doubleword-addressed
-- ============================================================================

/-- Reconstruct a 64-bit doubleword from 8 consecutive bytes in SAIL memory (little-endian). -/
def reconstructDword (mem : Std.ExtHashMap Nat (BitVec 8)) (addr : Nat) : BitVec 64 :=
  let b0 := (mem.getD addr 0).zeroExtend 64
  let b1 := (mem.getD (addr + 1) 0).zeroExtend 64
  let b2 := (mem.getD (addr + 2) 0).zeroExtend 64
  let b3 := (mem.getD (addr + 3) 0).zeroExtend 64
  let b4 := (mem.getD (addr + 4) 0).zeroExtend 64
  let b5 := (mem.getD (addr + 5) 0).zeroExtend 64
  let b6 := (mem.getD (addr + 6) 0).zeroExtend 64
  let b7 := (mem.getD (addr + 7) 0).zeroExtend 64
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
  (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

-- ============================================================================
-- Post-write SAIL state
-- ============================================================================

/-- The SAIL state after a `wX_bits`-style write to register `rd`.  For `x0`
    the state is unchanged (writes to x0 are no-ops); for any other register
    the corresponding entry is replaced via `insert`.  Concrete per-case so
    Lean can reduce `sailStateWithReg sSail .xN v` to the specific shape
    without further unfolding. -/
def sailStateWithReg (sSail : SailState) (rd : Reg) (v : BitVec 64) : SailState :=
  match rd with
  | .x0  => sSail
  | .x1  => { sSail with regs := sSail.regs.insert Register.x1  v }
  | .x2  => { sSail with regs := sSail.regs.insert Register.x2  v }
  | .x3  => { sSail with regs := sSail.regs.insert Register.x3  v }
  | .x4  => { sSail with regs := sSail.regs.insert Register.x4  v }
  | .x5  => { sSail with regs := sSail.regs.insert Register.x5  v }
  | .x6  => { sSail with regs := sSail.regs.insert Register.x6  v }
  | .x7  => { sSail with regs := sSail.regs.insert Register.x7  v }
  | .x8  => { sSail with regs := sSail.regs.insert Register.x8  v }
  | .x9  => { sSail with regs := sSail.regs.insert Register.x9  v }
  | .x10 => { sSail with regs := sSail.regs.insert Register.x10 v }
  | .x11 => { sSail with regs := sSail.regs.insert Register.x11 v }
  | .x12 => { sSail with regs := sSail.regs.insert Register.x12 v }
  | .x13 => { sSail with regs := sSail.regs.insert Register.x13 v }
  | .x14 => { sSail with regs := sSail.regs.insert Register.x14 v }
  | .x15 => { sSail with regs := sSail.regs.insert Register.x15 v }
  | .x16 => { sSail with regs := sSail.regs.insert Register.x16 v }
  | .x17 => { sSail with regs := sSail.regs.insert Register.x17 v }
  | .x18 => { sSail with regs := sSail.regs.insert Register.x18 v }
  | .x19 => { sSail with regs := sSail.regs.insert Register.x19 v }
  | .x20 => { sSail with regs := sSail.regs.insert Register.x20 v }
  | .x21 => { sSail with regs := sSail.regs.insert Register.x21 v }
  | .x22 => { sSail with regs := sSail.regs.insert Register.x22 v }
  | .x23 => { sSail with regs := sSail.regs.insert Register.x23 v }
  | .x24 => { sSail with regs := sSail.regs.insert Register.x24 v }
  | .x25 => { sSail with regs := sSail.regs.insert Register.x25 v }
  | .x26 => { sSail with regs := sSail.regs.insert Register.x26 v }
  | .x27 => { sSail with regs := sSail.regs.insert Register.x27 v }
  | .x28 => { sSail with regs := sSail.regs.insert Register.x28 v }
  | .x29 => { sSail with regs := sSail.regs.insert Register.x29 v }
  | .x30 => { sSail with regs := sSail.regs.insert Register.x30 v }
  | .x31 => { sSail with regs := sSail.regs.insert Register.x31 v }

/-- Writes don't touch memory. -/
@[simp] theorem sailStateWithReg_mem (sSail : SailState) (rd : Reg) (v : BitVec 64) :
    (sailStateWithReg sSail rd v).mem = sSail.mem := by
  cases rd <;> rfl

/-- An integer-register write doesn't touch `nextPC` (distinct key from every `xN`). -/
@[simp] theorem sailStateWithReg_get?_nextPC (sSail : SailState) (rd : Reg) (v : BitVec 64) :
    (sailStateWithReg sSail rd v).regs.get? Register.nextPC = sSail.regs.get? Register.nextPC := by
  cases rd <;> simp [sailStateWithReg, Std.ExtDHashMap.get?_insert]

/-- An integer-register write doesn't touch `PC` (distinct key from every `xN`). -/
@[simp] theorem sailStateWithReg_get?_PC (sSail : SailState) (rd : Reg) (v : BitVec 64) :
    (sailStateWithReg sSail rd v).regs.get? Register.PC = sSail.regs.get? Register.PC := by
  cases rd <;> simp [sailStateWithReg, Std.ExtDHashMap.get?_insert]

/-- A non-x0 write doesn't touch memory on the Rv64 side either. -/
@[simp] theorem MachineState_setReg_getMem (sRv : MachineState) (rd : Reg) (v : Word) (a : Word) :
    (sRv.setReg rd v).getMem a = sRv.getMem a := by
  cases rd <;> rfl

@[simp] theorem MachineState_setReg_mem (sRv : MachineState) (rd : Reg) (v : Word) :
    (sRv.setReg rd v).mem = sRv.mem := by
  cases rd <;> rfl

-- ============================================================================
-- State abstraction relation (no PC — proved separately at step level)
-- ============================================================================

/-- The abstraction relation between Rv64.MachineState and SAIL state.
    Asserts register and memory agreement only. -/
structure StateRel (sRv : MachineState) (sSail : SailState) : Prop where
  /-- Registers agree on all 32 integer registers. -/
  reg_agree : ∀ (r : Reg), sailRegVal sSail r = some (sRv.getReg r)
  /-- Memory agrees on **8-aligned doublewords**: the SAIL bytes at `a` reconstruct
      to the Rv64 doubleword `getMem a`.

      Restricted to 8-aligned `a` because Rv64 `mem` is dword-granular (a store is a
      single-point `setMem`), so the unrestricted ∀-byte form (overlapping 8-byte
      windows at every offset) cannot be preserved by a store — the byte write would
      change the windows at the seven preceding offsets, which the dword-granular
      `mem` does not track. Distinct 8-aligned dwords are disjoint, so an 8-aligned
      store *does* preserve this form. -/
  mem_agree : ∀ (a : BitVec 64), a.toNat % 8 = 0 →
    reconstructDword sSail.mem a.toNat = sRv.getMem a

/-- Inserting the `PC` register preserves `StateRel`: `PC` is not in the tracked
    integer-register set (`sailRegVal` reads only `x0`..`x31`), and a register
    insert doesn't touch memory. Mirrors the `nextPC` version used for branches. -/
theorem stateRel_PC_insert {sRv : MachineState} {sSail : SailState}
    (hrel : StateRel sRv sSail) (v : BitVec 64) :
    StateRel sRv { sSail with regs := sSail.regs.insert Register.PC v } :=
  ⟨fun r => by
    have ha := hrel.reg_agree r
    cases r <;> simpa [sailRegVal, Std.ExtDHashMap.get?_insert] using ha,
   fun a ha => hrel.mem_agree a ha⟩

/-- PC-aware abstraction relation: `StateRel` (registers + memory) plus agreement
    of the committed `PC`.  This is the step-stable relation that holds at each
    fetch boundary.  It is kept separate from `StateRel` because `execute_*` does
    not commit `PC` (it writes `nextPC`); only `tick_pc` commits `PC := nextPC`,
    so `PC` agreement is re-established once per `execute_* ; tick_pc` step. -/
structure StateRelPC (sRv : MachineState) (sSail : SailState) : Prop extends
    StateRel sRv sSail where
  /-- The committed program counter agrees. -/
  pc_agree : sSail.regs.get? Register.PC = some sRv.pc

-- ============================================================================
-- Byte-presence predicates
-- ============================================================================

/-- **Byte-presence over a half-open address range.** Every byte address `a` with
    `lo ≤ a < hi` has an entry in the SAIL byte memory `mem`.  This is the shape
    of the run-level memory invariant: SAIL loads fail (`.error`) on absent bytes,
    so establishing this over the guest's mapped region is what lets a load lemma
    supply its `hm0 … hm7` byte hypotheses. -/
def MemPresent (lo hi : Nat) (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ a : Nat, lo ≤ a → a < hi → (mem.get? a).isSome

/-- **Byte-presence for a single `w`-wide access at `a`.** The `w` bytes
    `a, a+1, …, a+w-1` all have entries in `mem`.  This is the per-access form
    consumed by the `vmem_read`/`vmem_write` reduction lemmas. -/
def BytesPresent (mem : Std.ExtHashMap Nat (BitVec 8)) (a w : Nat) : Prop :=
  ∀ k : Nat, k < w → (mem.get? (a + k)).isSome

/-- A range-level presence fact specialises to an access-level one whenever the
    access `[a, a+w)` sits inside the range `[lo, hi)`. -/
theorem MemPresent.bytesPresent {lo hi a w : Nat} {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : MemPresent lo hi mem) (hlo : lo ≤ a) (hhi : a + w ≤ hi) : BytesPresent mem a w :=
  fun k hk => h (a + k) (by omega) (by omega)

/-- Byte-presence is monotone under insertion: adding a byte never removes one. -/
theorem MemPresent.insert {lo hi : Nat} {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : MemPresent lo hi mem) (k : Nat) (v : BitVec 8) :
    MemPresent lo hi (mem.insert k v) := by
  intro a hlo hhi
  by_cases hk : k = a
  · subst hk; simp
  · simpa [Std.ExtHashMap.getElem?_insert, hk] using h a hlo hhi

-- ============================================================================
-- Platform frame: what a user-mode instruction step leaves untouched
-- ============================================================================

/-- **Platform frame between two SAIL states.** Records that `s'` agrees with `s`
    on every platform-configuration register that the address-translation /
    access-check pipeline consults (privilege, `mstatus`, `mseccfg`, the PMP
    config and address arrays, the PMA region table, `misa`, and the HTIF base),
    and that the byte memory only ever *grew*.

    This is the piece that per-instruction equivalence lemmas must **export**:
    their post-state lives behind an `∃ sSail'`, so without an explicit frame
    conjunct no downstream client can re-establish `BareModeInv` or `MemPresent`
    at the post-state.  With it, both transport mechanically. -/
structure PlatformFrame (s s' : SailState) : Prop where
  /-- Current privilege level is unchanged. -/
  priv_eq    : s'.regs.get? Register.cur_privilege = s.regs.get? Register.cur_privilege
  /-- `mstatus` (hence `MPRV`) is unchanged. -/
  mstatus_eq : s'.regs.get? Register.mstatus       = s.regs.get? Register.mstatus
  /-- `mseccfg` (hence the pointer-masking mode `PMM`) is unchanged. -/
  mseccfg_eq : s'.regs.get? Register.mseccfg       = s.regs.get? Register.mseccfg
  /-- The PMP configuration array is unchanged. -/
  pmpcfg_eq  : s'.regs.get? Register.pmpcfg_n      = s.regs.get? Register.pmpcfg_n
  /-- The PMP address array is unchanged. -/
  pmpaddr_eq : s'.regs.get? Register.pmpaddr_n     = s.regs.get? Register.pmpaddr_n
  /-- The PMA region table is unchanged. -/
  pma_eq     : s'.regs.get? Register.pma_regions   = s.regs.get? Register.pma_regions
  /-- `misa` (the ISA-extension mask) is unchanged. -/
  misa_eq    : s'.regs.get? Register.misa          = s.regs.get? Register.misa
  /-- The HTIF `tohost` base address is unchanged. -/
  htif_eq    : s'.regs.get? Register.htif_tohost_base = s.regs.get? Register.htif_tohost_base
  /-- Byte memory only grows: any address present before is still present after. -/
  mem_mono   : ∀ n : Nat, (s.mem.get? n).isSome → (s'.mem.get? n).isSome

/-- The platform frame is reflexive. -/
theorem PlatformFrame.refl (s : SailState) : PlatformFrame s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => h⟩

/-- The platform frame is transitive, so multi-step frames compose. -/
theorem PlatformFrame.trans {s₁ s₂ s₃ : SailState}
    (h₁ : PlatformFrame s₁ s₂) (h₂ : PlatformFrame s₂ s₃) : PlatformFrame s₁ s₃ :=
  ⟨h₂.priv_eq.trans h₁.priv_eq,
   h₂.mstatus_eq.trans h₁.mstatus_eq,
   h₂.mseccfg_eq.trans h₁.mseccfg_eq,
   h₂.pmpcfg_eq.trans h₁.pmpcfg_eq,
   h₂.pmpaddr_eq.trans h₁.pmpaddr_eq,
   h₂.pma_eq.trans h₁.pma_eq,
   h₂.misa_eq.trans h₁.misa_eq,
   h₂.htif_eq.trans h₁.htif_eq,
   fun n hn => h₂.mem_mono n (h₁.mem_mono n hn)⟩

/-- Writing an integer register preserves the platform frame: every `xN` key is
    distinct from every platform register, and `x0` writes are the identity. -/
theorem platformFrame_sailStateWithReg (s : SailState) (rd : Reg) (v : BitVec 64) :
    PlatformFrame s (sailStateWithReg s rd v) := by
  constructor <;>
    (first
      | (intro n hn; cases rd <;> simpa [sailStateWithReg] using hn)
      | (cases rd <;> simp [sailStateWithReg, Std.ExtDHashMap.get?_insert]))

/-- Committing `PC` preserves the platform frame. -/
theorem platformFrame_insert_PC (s : SailState) (v : BitVec 64) :
    PlatformFrame s { s with regs := s.regs.insert Register.PC v } := by
  constructor <;>
    (first
      | (intro n hn; simpa using hn)
      | simp [Std.ExtDHashMap.get?_insert])

/-- Writing `nextPC` preserves the platform frame. -/
theorem platformFrame_insert_nextPC (s : SailState) (v : BitVec 64) :
    PlatformFrame s { s with regs := s.regs.insert Register.nextPC v } := by
  constructor <;>
    (first
      | (intro n hn; simpa using hn)
      | simp [Std.ExtDHashMap.get?_insert])

/-- Writing a memory byte preserves the platform frame: no register moves, and
    memory only grows. -/
theorem platformFrame_insert_mem (s : SailState) (k : Nat) (v : BitVec 8) :
    PlatformFrame s { s with mem := s.mem.insert k v } := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro n hn
  by_cases hk : k = n
  · subst hk; simp
  · simpa [Std.ExtHashMap.getElem?_insert, hk] using hn

/-- Range byte-presence transports along a platform frame (memory only grows). -/
theorem MemPresent.of_frame {lo hi : Nat} {s s' : SailState}
    (fr : PlatformFrame s s') (h : MemPresent lo hi s.mem) : MemPresent lo hi s'.mem :=
  fun a hlo hhi => fr.mem_mono a (h a hlo hhi)

end EvmAsm.Rv64.SailEquiv
