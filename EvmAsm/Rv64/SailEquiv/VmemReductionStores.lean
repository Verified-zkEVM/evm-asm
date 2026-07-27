/-
  EvmAsm.Rv64.SailEquiv.VmemReductionStores

  Unconditional per-instruction equivalence for the four stores `SD / SW / SH / SB`.
  (Historically these discharged the vacuous `h_exec` stubs the deferred `MemProofs`
  lemmas carried; no stubs remain anywhere.)  Built on the store-side
  write chain in `VmemWriteReduction.lean` (`writeBytes → … → vmem_write`), plus the
  `StateRel.mem_agree` rebuild bridges below — the genuinely new semantic content of the
  store tier:

  * **The written dword.**  After `writeBytes`, the Sail byte map holds the little-endian
    slices of the stored value at `[addr, addr+w)`; `reconstructDword` at the (8-aligned)
    containing dword recovers exactly the toy model's post-store cell — the full value for
    `SD`, or `replaceWord32/Halfword/Byte` of the old cell for the sub-dword stores.
  * **Disjoint dwords.**  The inserts stay inside one aligned dword, so every *other*
    8-aligned dword reconstructs unchanged (`reconstructDword_congr`) and `mem_agree`
    transports from the pre-state.

  Unlike loads, stores need **no byte-presence hypotheses** (`writeByte` is `mem.insert`,
  which never fails).
-/

import EvmAsm.Rv64.SailEquiv.VmemWriteReduction
import EvmAsm.Rv64.SailEquiv.VmemReductionLoads
import EvmAsm.Rv64.SailEquiv.MemReduce

open Out
open Out.Functions
open Sail
open PreSail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- getD over the write chain (per width)
-- ============================================================================

/-- Byte `i` of the width-8 write chain at `a` is the `i`-th little-endian slice. -/
theorem getD_writeChain8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec (8*8))
    (i : Nat) (hi : i < 8) :
    ((((((((mem.insert a (v.extractLsb' 0 8)).insert (a+1) (v.extractLsb' 8 8)).insert
      (a+2) (v.extractLsb' 16 8)).insert (a+3) (v.extractLsb' 24 8)).insert
      (a+4) (v.extractLsb' 32 8)).insert (a+5) (v.extractLsb' 40 8)).insert
      (a+6) (v.extractLsb' 48 8)).insert (a+7) (v.extractLsb' 56 8)).getD (a + i) 0
      = v.extractLsb' (8 * i) 8 := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Nat.add_zero, Std.ExtHashMap.getD_insert]
    rw [if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp),
        if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos (by simp)]
  · simp only [Std.ExtHashMap.getD_insert]
    rw [if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp),
        if_neg (by simp), if_neg (by simp), if_pos (by simp)]
  · simp only [Std.ExtHashMap.getD_insert]
    rw [if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp),
        if_neg (by simp), if_pos (by simp)]
  · simp only [Std.ExtHashMap.getD_insert]
    rw [if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp),
        if_pos (by simp)]
  · simp only [Std.ExtHashMap.getD_insert]
    rw [if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos (by simp)]
  · simp only [Std.ExtHashMap.getD_insert]
    rw [if_neg (by simp), if_neg (by simp), if_pos (by simp)]
  · simp only [Std.ExtHashMap.getD_insert]
    rw [if_neg (by simp), if_pos (by simp)]
  · simp only [Std.ExtHashMap.getD_insert]
    rw [if_pos (by simp)]

/-- Bytes outside `[a, a+8)` are untouched by the width-8 write chain. -/
theorem getD_writeChain8_out (mem : Std.ExtHashMap Nat (BitVec 8)) (a x : Nat)
    (v : BitVec (8*8)) (hout : x < a ∨ a + 8 ≤ x) :
    ((((((((mem.insert a (v.extractLsb' 0 8)).insert (a+1) (v.extractLsb' 8 8)).insert
      (a+2) (v.extractLsb' 16 8)).insert (a+3) (v.extractLsb' 24 8)).insert
      (a+4) (v.extractLsb' 32 8)).insert (a+5) (v.extractLsb' 40 8)).insert
      (a+6) (v.extractLsb' 48 8)).insert (a+7) (v.extractLsb' 56 8)).getD x 0
      = mem.getD x 0 := by
  simp only [Std.ExtHashMap.getD_insert]
  rw [if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp; omega),
      if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp; omega),
      if_neg (by simp; omega), if_neg (by simp; omega)]

-- ============================================================================
-- The little-endian slices are the bytes of the value
-- ============================================================================

/-- The `i`-th little-endian slice `extractLsb' (8 * i) 8` is `extractByte · i`. -/
theorem extractLsb'_eq_extractByte (v : BitVec 64) (i : Nat) :
    v.extractLsb' (8 * i) 8 = extractByte v i := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', extractByte, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj, decide_true, Bool.true_and]
  rw [Nat.mul_comm 8 i]

-- ============================================================================
-- reconstructDword over the write chain (width 8)
-- ============================================================================

/-- **Written-dword bridge (width 8).**  `reconstructDword` at the written address
    recovers the stored value. -/
theorem reconstructDword_writeChain8_self (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (v : BitVec (8*8)) :
    reconstructDword
      ((((((((mem.insert a (v.extractLsb' 0 8)).insert (a+1) (v.extractLsb' 8 8)).insert
        (a+2) (v.extractLsb' 16 8)).insert (a+3) (v.extractLsb' 24 8)).insert
        (a+4) (v.extractLsb' 32 8)).insert (a+5) (v.extractLsb' 40 8)).insert
        (a+6) (v.extractLsb' 48 8)).insert (a+7) (v.extractLsb' 56 8)) a = v := by
  apply reconstructDword_of_bytes
  intro i hi
  rw [getD_writeChain8 mem a v i hi, extractLsb'_eq_extractByte]

/-- **Disjoint-dword bridge (width 8).**  Any dword disjoint from the written range
    reconstructs unchanged. -/
theorem reconstructDword_writeChain8_disjoint (mem : Std.ExtHashMap Nat (BitVec 8))
    (a x : Nat) (v : BitVec (8*8)) (hdis : x + 8 ≤ a ∨ a + 8 ≤ x) :
    reconstructDword
      ((((((((mem.insert a (v.extractLsb' 0 8)).insert (a+1) (v.extractLsb' 8 8)).insert
        (a+2) (v.extractLsb' 16 8)).insert (a+3) (v.extractLsb' 24 8)).insert
        (a+4) (v.extractLsb' 32 8)).insert (a+5) (v.extractLsb' 40 8)).insert
        (a+6) (v.extractLsb' 48 8)).insert (a+7) (v.extractLsb' 56 8)) x
      = reconstructDword mem x := by
  apply reconstructDword_congr
  intro i hi
  exact getD_writeChain8_out mem a (x + i) v (by omega)

-- ============================================================================
-- SD capstone
-- ============================================================================

/-- **`sd_sail_equiv` discharged — unconditional doubleword-store equivalence.** Given
    the abstraction relation, a bare-mode machine, and that the access is 8-aligned, in a
    writable PMA region, and off the writable MMIO ranges, the SAIL `execute_STORE`
    (width 8) succeeds with `RETIRE_SUCCESS` and the resulting state is `StateRel`-related
    to the toy model's `SD`. No `h_exec` assumption, and — unlike the loads — no
    byte-presence hypotheses (`writeByte` never fails). -/
theorem sd_sail_equiv (sRv : MachineState) (sSail : SailState)
    (rs1 rs2 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (h_valign : is_aligned_vaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = true)
    (h_match : matching_pma_region bm.regions
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = some region)
    (h_write : region.attributes.writable = true)
    (h_palign : is_aligned_paddr
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = true)
    (hclint : (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
      = .ok false sSail)
    (hsig : (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
      = .ok false sSail)
    (hhtif : (within_htif_writable
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
      = .ok false sSail) :
    ∃ sSail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 8) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SD rs1 rs2 offset)) sSail' ∧
      sSail'.regs.get? Register.nextPC = sSail.regs.get? Register.nextPC := by
  have soff : sign_extend (m := 64) offset = signExtend12 offset := by
    unfold sign_extend signExtend12 Sail.BitVec.signExtend; rfl
  have h_rs1 : (rX_bits (regToRegidx rs1)) sSail = .ok (sRv.getReg rs1) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs1)
  have h_rs2 : (rX_bits (regToRegidx rs2)) sSail = .ok (sRv.getReg rs2) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs2)
  -- the post-write Sail state: the eight little-endian slices of the stored value
  set addr := sRv.getReg rs1 + signExtend12 offset with haddr_def
  set v : BitVec (8*8) := sRv.getReg rs2 with hv_def
  set sSail' : SailState := { sSail with mem :=
      ((((((((sSail.mem.insert addr.toNat (v.extractLsb' 0 8)).insert
        (addr.toNat+1) (v.extractLsb' 8 8)).insert
        (addr.toNat+2) (v.extractLsb' 16 8)).insert (addr.toNat+3) (v.extractLsb' 24 8)).insert
        (addr.toNat+4) (v.extractLsb' 32 8)).insert (addr.toNat+5) (v.extractLsb' 40 8)).insert
        (addr.toNat+6) (v.extractLsb' 48 8)).insert (addr.toNat+7) (v.extractLsb' 56 8)) }
    with hs'_def
  have hwrite : (writeBytes addr.toNat v : SailM Bool) sSail = .ok true sSail' :=
    writeBytes8_raw sSail addr.toNat v
  have hvwa := vmem_write_addr_store_core 8 (virtaddr.Virtaddr addr) sSail sSail'
    bm.mst v bm.cfgs bm.pmpaddrs bm.regions region (Or.inr (Or.inr (Or.inr rfl)))
    h_valign bm.h_priv bm.h_mst bm.h_mprv bm.h_cfg bm.h_pmpaddr bm.h_off bm.h_reg
    (by simpa using h_match) h_write (by simpa using h_palign)
    (by simpa using hclint) (by simpa using hsig) (by simpa using hhtif)
    (by simpa using hwrite)
  have hvw := vmem_write_store_N 8 (regToRegidx rs1) (signExtend12 offset) (sRv.getReg rs1)
    sSail sSail' v bm h_rs1 (by simpa using hvwa)
  have halign8 : addr.toNat % 8 = 0 := is_aligned_vaddr_toNat addr 8 h_valign
  refine ⟨sSail', ?_, ?_, ?_⟩
  · -- SAIL execution succeeds with RETIRE_SUCCESS
    unfold execute_STORE
    simp +decide only [soff, runSail_bind, runSail_pure, PreSail.assert, if_true]
    rw [show runSail (rX_bits (regToRegidx rs2)) sSail = some (v, sSail) from by
      simp only [runSail, h_rs2]]
    simp +decide only []
    rw [show (((8 : Nat) *i 8) -i 1).toNat = 63 from by decide]
    rw [show runSail (vmem_write (regToRegidx rs1) (signExtend12 offset) 8
          (BitVec.setWidth (8*8) (Sail.BitVec.extractLsb v 63 0))
          (MemoryAccessType.Store mem_payload.Data) false false false) sSail
        = some (Result.Ok true, sSail') from by
      rw [show Sail.BitVec.extractLsb v 63 0 = v from extractLsb_full64 v, BitVec.setWidth_eq]
      simp only [runSail, hvw]]
    simp only [runSail_pure]
  · -- abstraction relation for the post-store state
    refine ⟨fun r => ?_, fun a' ha' => ?_⟩
    · -- registers: neither side writes any register
      have h := hrel.reg_agree r
      cases r <;>
        simp [sailRegVal, hs'_def, execInstrBr, MachineState.setPC, MachineState.setMem,
          MachineState.getReg] at h ⊢ <;> exact h
    · -- memory: written dword = stored value; other aligned dwords unchanged
      rcases eq_or_ne a' addr with rfl | hne
      · -- the written dword: `reconstructDword` over the insert chain recovers the value
        have hrw : (execInstrBr sRv (.SD rs1 rs2 offset)).getMem addr = sRv.getReg rs2 := by
          simp only [execInstrBr, ← haddr_def, MachineState.getMem_setPC,
            MachineState.getMem_setMem_eq]
        rw [hrw]
        exact reconstructDword_writeChain8_self sSail.mem addr.toNat v
      · -- disjoint aligned dwords: the inserts stay inside [addr, addr+8)
        have hnat : a'.toNat ≠ addr.toNat := fun h => hne (BitVec.toNat_inj.mp h)
        have hdis : a'.toNat + 8 ≤ addr.toNat ∨ addr.toNat + 8 ≤ a'.toNat := by omega
        have hrw : (execInstrBr sRv (.SD rs1 rs2 offset)).getMem a' = sRv.getMem a' := by
          simp only [execInstrBr, ← haddr_def, MachineState.getMem_setPC,
            MachineState.getMem_setMem_ne hne]
        rw [hrw, ← hrel.mem_agree a' ha']
        exact reconstructDword_writeChain8_disjoint sSail.mem addr.toNat a'.toNat v hdis
  · simp [hs'_def]

-- ============================================================================
-- Width-4 chain (SW): getD, read-modify-write bridge, disjointness
-- ============================================================================

/-- Byte `i` of the width-4 write chain at `a` is the `i`-th little-endian slice. -/
theorem getD_writeChain4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec (8*4))
    (i : Nat) (hi : i < 4) :
    ((((mem.insert a (v.extractLsb' 0 8)).insert (a+1) (v.extractLsb' 8 8)).insert
      (a+2) (v.extractLsb' 16 8)).insert (a+3) (v.extractLsb' 24 8)).getD (a + i) 0
      = v.extractLsb' (8 * i) 8 := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  · simp only [Nat.add_zero, Std.ExtHashMap.getD_insert]
    rw [if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos (by simp)]
  · simp only [Std.ExtHashMap.getD_insert]
    rw [if_neg (by simp), if_neg (by simp), if_pos (by simp)]
  · simp only [Std.ExtHashMap.getD_insert]
    rw [if_neg (by simp), if_pos (by simp)]
  · simp only [Std.ExtHashMap.getD_insert]
    rw [if_pos (by simp)]

/-- Bytes outside `[a, a+4)` are untouched by the width-4 write chain. -/
theorem getD_writeChain4_out (mem : Std.ExtHashMap Nat (BitVec 8)) (a x : Nat)
    (v : BitVec (8*4)) (hout : x < a ∨ a + 4 ≤ x) :
    ((((mem.insert a (v.extractLsb' 0 8)).insert (a+1) (v.extractLsb' 8 8)).insert
      (a+2) (v.extractLsb' 16 8)).insert (a+3) (v.extractLsb' 24 8)).getD x 0
      = mem.getD x 0 := by
  simp only [Std.ExtHashMap.getD_insert]
  rw [if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp; omega),
      if_neg (by simp; omega)]

/-- **Read-modify-write bridge (width 4).**  Reconstructing the containing dword after a
    4-byte store at word-position `pos` is `replaceWord32` of the old dword. -/
theorem reconstructDword_writeChain4_replace (mem : Std.ExtHashMap Nat (BitVec 8))
    (b pos : Nat) (v : BitVec (8*4)) (_hpos : pos < 2) :
    reconstructDword
      ((((mem.insert (b + pos*4) (v.extractLsb' 0 8)).insert
        (b + pos*4 + 1) (v.extractLsb' 8 8)).insert
        (b + pos*4 + 2) (v.extractLsb' 16 8)).insert
        (b + pos*4 + 3) (v.extractLsb' 24 8)) b
      = replaceWord32 (reconstructDword mem b) pos v := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have hp64 : p < 64 := hp
  have hold := reconstructDword_getLsbD mem b p hp64
  rw [reconstructDword_getLsbD _ b p hp64]
  simp only [replaceWord32, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth,
    show (0xFFFFFFFF#64) = (BitVec.allOnes 32).setWidth 64 from by decide,
    BitVec.getLsbD_allOnes, hp64, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge p (pos*32) with hlo | hlo
  · -- below the window: byte untouched, mask bit clear
    rw [getD_writeChain4_out mem (b + pos*4) (b + p/8) v (Or.inl (by omega)), ← hold]
    simp only [show decide (p < pos*32) = true from by simp [hlo],
      Bool.not_true, Bool.false_and, Bool.not_false, Bool.and_true, Bool.or_false]
  rcases Nat.lt_or_ge p (pos*32 + 32) with hin | hhi
  · -- inside the window: the fresh byte, mask bit set
    rw [show b + p/8 = (b + pos*4) + (p/8 - pos*4) from by omega,
        getD_writeChain4 mem (b + pos*4) v (p/8 - pos*4) (by omega)]
    simp only [BitVec.getLsbD_extractLsb', show p % 8 < 8 from by omega, decide_true,
      Bool.true_and, show decide (p < pos*32) = false from by simp; omega,
      Bool.not_false,
      show p - pos*32 < 32 from by omega, show p - pos*32 < 64 from by omega,
      decide_true, Bool.true_and, Bool.and_true, Bool.not_true, Bool.and_false,
      Bool.false_or]
    rw [show 8 * (p/8 - pos*4) + p % 8 = p - pos*32 from by omega]
  · -- above the window: byte untouched, mask bit clear (allOnes exhausted)
    rw [getD_writeChain4_out mem (b + pos*4) (b + p/8) v (Or.inr (by omega)), ← hold]
    simp only [show decide (p < pos*32) = false from by simp; omega, Bool.not_false,
      show decide (p - pos*32 < 32) = false from by simp; omega,
      Bool.and_false, Bool.not_false, Bool.and_true, Bool.or_false,
      BitVec.getLsbD_of_ge v (p - pos*32) (by omega)]

/-- Dwords disjoint from the 4-byte write range reconstruct unchanged. -/
theorem reconstructDword_writeChain4_disjoint (mem : Std.ExtHashMap Nat (BitVec 8))
    (c x : Nat) (v : BitVec (8*4)) (hdis : x + 8 ≤ c ∨ c + 4 ≤ x) :
    reconstructDword
      ((((mem.insert c (v.extractLsb' 0 8)).insert (c+1) (v.extractLsb' 8 8)).insert
        (c+2) (v.extractLsb' 16 8)).insert (c+3) (v.extractLsb' 24 8)) x
      = reconstructDword mem x := by
  apply reconstructDword_congr
  intro i hi
  exact getD_writeChain4_out mem c (x + i) v (by omega)

/-- The width-4 store's data slice (`setWidth (8*4) ∘ extractLsb · 31 0`) is `truncate 32`. -/
theorem extractLsb_data32 (x : BitVec 64) :
    BitVec.setWidth (8*4) (Sail.BitVec.extractLsb x 31 0) = x.truncate 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.truncate_eq_setWidth,
    show i < 32 from hi]

/-- **`sw_sail_equiv` discharged — unconditional word-store equivalence.** The toy `SW`
    is a read-modify-write of the containing dword (`setWord32` = `replaceWord32` at the
    aligned base); the Sail side inserts the four byte slices. The `mem_agree` rebuild
    compares at the aligned base via the read-modify-write bridge. -/
theorem sw_sail_equiv (sRv : MachineState) (sSail : SailState)
    (rs1 rs2 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (h_valign : is_aligned_vaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = true)
    (h_match : matching_pma_region bm.regions
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = some region)
    (h_write : region.attributes.writable = true)
    (h_palign : is_aligned_paddr
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = true)
    (hclint : (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
      = .ok false sSail)
    (hsig : (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
      = .ok false sSail)
    (hhtif : (within_htif_writable
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
      = .ok false sSail) :
    ∃ sSail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 4) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SW rs1 rs2 offset)) sSail' ∧
      sSail'.regs.get? Register.nextPC = sSail.regs.get? Register.nextPC := by
  have soff : sign_extend (m := 64) offset = signExtend12 offset := by
    unfold sign_extend signExtend12 Sail.BitVec.signExtend; rfl
  have h_rs1 : (rX_bits (regToRegidx rs1)) sSail = .ok (sRv.getReg rs1) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs1)
  have h_rs2 : (rX_bits (regToRegidx rs2)) sSail = .ok (sRv.getReg rs2) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs2)
  set addr := sRv.getReg rs1 + signExtend12 offset with haddr_def
  set v : BitVec (8*4) := (sRv.getReg rs2).truncate 32 with hv_def
  set sSail' : SailState := { sSail with mem :=
      ((((sSail.mem.insert addr.toNat (v.extractLsb' 0 8)).insert
        (addr.toNat+1) (v.extractLsb' 8 8)).insert
        (addr.toNat+2) (v.extractLsb' 16 8)).insert
        (addr.toNat+3) (v.extractLsb' 24 8)) }
    with hs'_def
  have hwrite : (writeBytes addr.toNat v : SailM Bool) sSail = .ok true sSail' :=
    writeBytes4_raw sSail addr.toNat v
  have hvwa := vmem_write_addr_store_core 4 (virtaddr.Virtaddr addr) sSail sSail'
    bm.mst v bm.cfgs bm.pmpaddrs bm.regions region (Or.inr (Or.inr (Or.inl rfl)))
    h_valign bm.h_priv bm.h_mst bm.h_mprv bm.h_cfg bm.h_pmpaddr bm.h_off bm.h_reg
    (by simpa using h_match) h_write (by simpa using h_palign)
    (by simpa using hclint) (by simpa using hsig) (by simpa using hhtif)
    (by simpa using hwrite)
  have hvw := vmem_write_store_N 4 (regToRegidx rs1) (signExtend12 offset) (sRv.getReg rs1)
    sSail sSail' v bm h_rs1 (by simpa using hvwa)
  have halign4 : addr.toNat % 4 = 0 := is_aligned_vaddr_toNat addr 4 h_valign
  have hdecomp : (alignToDword addr).toNat + (byteOffset addr / 4) * 4 = addr.toNat :=
    alignToDword_offset_eq addr 4 (Or.inr (Or.inr rfl)) halign4
  have hposlt : byteOffset addr / 4 < 2 := by
    have := byteOffset_lt_8 (addr := addr); omega
  refine ⟨sSail', ?_, ?_, ?_⟩
  · -- SAIL execution succeeds with RETIRE_SUCCESS
    unfold execute_STORE
    simp +decide only [soff, runSail_bind, runSail_pure, PreSail.assert, if_true]
    rw [show runSail (rX_bits (regToRegidx rs2)) sSail = some (sRv.getReg rs2, sSail) from by
      simp only [runSail, h_rs2]]
    simp +decide only []
    rw [show (((4 : Nat) *i 8) -i 1).toNat = 31 from by decide]
    rw [show runSail (vmem_write (regToRegidx rs1) (signExtend12 offset) 4
          (BitVec.setWidth (8*4) (Sail.BitVec.extractLsb (sRv.getReg rs2) 31 0))
          (MemoryAccessType.Store mem_payload.Data) false false false) sSail
        = some (Result.Ok true, sSail') from by
      rw [show BitVec.setWidth (8*4) (Sail.BitVec.extractLsb (sRv.getReg rs2) 31 0) = v
        from extractLsb_data32 (sRv.getReg rs2)]
      simp only [runSail, hvw]]
    simp only [runSail_pure]
  · -- abstraction relation for the post-store state
    refine ⟨fun r => ?_, fun a' ha' => ?_⟩
    · -- registers: neither side writes any register
      have h := hrel.reg_agree r
      cases r <;>
        simp [sailRegVal, hs'_def, execInstrBr, MachineState.setPC, MachineState.setWord32,
          MachineState.setMem, MachineState.getReg] at h ⊢ <;> exact h
    · -- memory: containing dword = read-modify-write; other aligned dwords unchanged
      rcases eq_or_ne a' (alignToDword addr) with rfl | hne
      · -- the containing dword
        have hrw : (execInstrBr sRv (.SW rs1 rs2 offset)).getMem (alignToDword addr)
            = replaceWord32 (sRv.getMem (alignToDword addr)) (byteOffset addr / 4) v := by
          simp only [execInstrBr, ← haddr_def, MachineState.setWord32,
            MachineState.getMem_setPC, MachineState.getMem_setMem_eq]
          rfl
        rw [hrw, ← hrel.mem_agree (alignToDword addr) (alignToDword_toNat_mod8 addr)]
        have hbridge := reconstructDword_writeChain4_replace sSail.mem
          (alignToDword addr).toNat (byteOffset addr / 4) v hposlt
        rw [hdecomp] at hbridge
        exact hbridge
      · -- disjoint aligned dwords: the four inserts stay inside the containing dword
        have hnat : a'.toNat ≠ (alignToDword addr).toNat :=
          fun h => hne (BitVec.toNat_inj.mp h)
        have hb8 := alignToDword_toNat_mod8 addr
        have hdis : a'.toNat + 8 ≤ addr.toNat ∨ addr.toNat + 4 ≤ a'.toNat := by omega
        have hrw : (execInstrBr sRv (.SW rs1 rs2 offset)).getMem a' = sRv.getMem a' := by
          simp only [execInstrBr, ← haddr_def, MachineState.setWord32,
            MachineState.getMem_setPC, MachineState.getMem_setMem_ne hne]
        rw [hrw, ← hrel.mem_agree a' ha']
        exact reconstructDword_writeChain4_disjoint sSail.mem addr.toNat a'.toNat v hdis
  · simp [hs'_def]

-- ============================================================================
-- Width-2 chain (SH)
-- ============================================================================

/-- Byte `i` of the width-2 write chain at `a` is the `i`-th little-endian slice. -/
theorem getD_writeChain2 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec (8*2))
    (i : Nat) (hi : i < 2) :
    ((mem.insert a (v.extractLsb' 0 8)).insert (a+1) (v.extractLsb' 8 8)).getD (a + i) 0
      = v.extractLsb' (8 * i) 8 := by
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simp only [Nat.add_zero, Std.ExtHashMap.getD_insert]
    rw [if_neg (by simp), if_pos (by simp)]
  · simp only [Std.ExtHashMap.getD_insert]
    rw [if_pos (by simp)]

/-- Bytes outside `[a, a+2)` are untouched by the width-2 write chain. -/
theorem getD_writeChain2_out (mem : Std.ExtHashMap Nat (BitVec 8)) (a x : Nat)
    (v : BitVec (8*2)) (hout : x < a ∨ a + 2 ≤ x) :
    ((mem.insert a (v.extractLsb' 0 8)).insert (a+1) (v.extractLsb' 8 8)).getD x 0
      = mem.getD x 0 := by
  simp only [Std.ExtHashMap.getD_insert]
  rw [if_neg (by simp; omega), if_neg (by simp; omega)]

/-- **Read-modify-write bridge (width 2).** -/
theorem reconstructDword_writeChain2_replace (mem : Std.ExtHashMap Nat (BitVec 8))
    (b pos : Nat) (v : BitVec (8*2)) (_hpos : pos < 4) :
    reconstructDword
      ((mem.insert (b + pos*2) (v.extractLsb' 0 8)).insert
        (b + pos*2 + 1) (v.extractLsb' 8 8)) b
      = replaceHalfword (reconstructDword mem b) pos v := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have hp64 : p < 64 := hp
  have hold := reconstructDword_getLsbD mem b p hp64
  rw [reconstructDword_getLsbD _ b p hp64]
  simp only [replaceHalfword, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth,
    show (0xFFFF#64) = (BitVec.allOnes 16).setWidth 64 from by decide,
    BitVec.getLsbD_allOnes, hp64, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge p (pos*16) with hlo | hlo
  · rw [getD_writeChain2_out mem (b + pos*2) (b + p/8) v (Or.inl (by omega)), ← hold]
    simp only [show decide (p < pos*16) = true from by simp [hlo],
      Bool.not_true, Bool.false_and, Bool.not_false, Bool.and_true, Bool.or_false]
  rcases Nat.lt_or_ge p (pos*16 + 16) with hin | hhi
  · rw [show b + p/8 = (b + pos*2) + (p/8 - pos*2) from by omega,
        getD_writeChain2 mem (b + pos*2) v (p/8 - pos*2) (by omega)]
    simp only [BitVec.getLsbD_extractLsb', show p % 8 < 8 from by omega, decide_true,
      Bool.true_and, show decide (p < pos*16) = false from by simp; omega,
      Bool.not_false,
      show p - pos*16 < 16 from by omega, show p - pos*16 < 64 from by omega,
      decide_true, Bool.true_and, Bool.and_true, Bool.not_true, Bool.and_false,
      Bool.false_or]
    rw [show 8 * (p/8 - pos*2) + p % 8 = p - pos*16 from by omega]
  · rw [getD_writeChain2_out mem (b + pos*2) (b + p/8) v (Or.inr (by omega)), ← hold]
    simp only [show decide (p < pos*16) = false from by simp; omega, Bool.not_false,
      show decide (p - pos*16 < 16) = false from by simp; omega,
      Bool.and_false, Bool.not_false, Bool.and_true, Bool.or_false,
      BitVec.getLsbD_of_ge v (p - pos*16) (by omega)]

/-- Dwords disjoint from the 2-byte write range reconstruct unchanged. -/
theorem reconstructDword_writeChain2_disjoint (mem : Std.ExtHashMap Nat (BitVec 8))
    (c x : Nat) (v : BitVec (8*2)) (hdis : x + 8 ≤ c ∨ c + 2 ≤ x) :
    reconstructDword
      ((mem.insert c (v.extractLsb' 0 8)).insert (c+1) (v.extractLsb' 8 8)) x
      = reconstructDword mem x := by
  apply reconstructDword_congr
  intro i hi
  exact getD_writeChain2_out mem c (x + i) v (by omega)

/-- The width-2 store's data slice is `truncate 16`. -/
theorem extractLsb_data16 (x : BitVec 64) :
    BitVec.setWidth (8*2) (Sail.BitVec.extractLsb x 15 0) = x.truncate 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.truncate_eq_setWidth,
    show i < 16 from hi]

-- ============================================================================
-- Width-1 chain (SB)
-- ============================================================================

/-- The single inserted byte of the width-1 write chain. -/
theorem getD_writeChain1 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec (8*1))
    (i : Nat) (hi : i < 1) :
    (mem.insert a (v.extractLsb' 0 8)).getD (a + i) 0 = v.extractLsb' (8 * i) 8 := by
  rcases (show i = 0 by omega) with rfl
  simp only [Nat.add_zero, Std.ExtHashMap.getD_insert]
  rw [if_pos (by simp)]

/-- Bytes other than `a` are untouched by the width-1 write chain. -/
theorem getD_writeChain1_out (mem : Std.ExtHashMap Nat (BitVec 8)) (a x : Nat)
    (v : BitVec (8*1)) (hout : x < a ∨ a + 1 ≤ x) :
    (mem.insert a (v.extractLsb' 0 8)).getD x 0 = mem.getD x 0 := by
  simp only [Std.ExtHashMap.getD_insert]
  rw [if_neg (by simp; omega)]

/-- **Read-modify-write bridge (width 1).** -/
theorem reconstructDword_writeChain1_replace (mem : Std.ExtHashMap Nat (BitVec 8))
    (b pos : Nat) (v : BitVec (8*1)) (_hpos : pos < 8) :
    reconstructDword (mem.insert (b + pos*1) (v.extractLsb' 0 8)) b
      = replaceByte (reconstructDword mem b) pos v := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have hp64 : p < 64 := hp
  have hold := reconstructDword_getLsbD mem b p hp64
  rw [reconstructDword_getLsbD _ b p hp64]
  simp only [replaceByte, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth,
    show (0xFF#64) = (BitVec.allOnes 8).setWidth 64 from by decide,
    BitVec.getLsbD_allOnes, hp64, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge p (pos*8) with hlo | hlo
  · rw [getD_writeChain1_out mem (b + pos*1) (b + p/8) v (Or.inl (by omega)), ← hold]
    simp only [show decide (p < pos*8) = true from by simp [hlo],
      Bool.not_true, Bool.false_and, Bool.not_false, Bool.and_true, Bool.or_false]
  rcases Nat.lt_or_ge p (pos*8 + 8) with hin | hhi
  · rw [show b + p/8 = (b + pos*1) + (p/8 - pos*1) from by omega,
        getD_writeChain1 mem (b + pos*1) v (p/8 - pos*1) (by omega)]
    simp only [BitVec.getLsbD_extractLsb', show p % 8 < 8 from by omega, decide_true,
      Bool.true_and, show decide (p < pos*8) = false from by simp; omega,
      Bool.not_false,
      show p - pos*8 < 8 from by omega, show p - pos*8 < 64 from by omega,
      decide_true, Bool.true_and, Bool.and_true, Bool.not_true, Bool.and_false,
      Bool.false_or]
    rw [show 8 * (p/8 - pos*1) + p % 8 = p - pos*8 from by omega]
  · rw [getD_writeChain1_out mem (b + pos*1) (b + p/8) v (Or.inr (by omega)), ← hold]
    simp only [show decide (p < pos*8) = false from by simp; omega, Bool.not_false,
      show decide (p - pos*8 < 8) = false from by simp; omega,
      Bool.and_false, Bool.not_false, Bool.and_true, Bool.or_false,
      BitVec.getLsbD_of_ge v (p - pos*8) (by omega)]

/-- Dwords disjoint from the written byte reconstruct unchanged. -/
theorem reconstructDword_writeChain1_disjoint (mem : Std.ExtHashMap Nat (BitVec 8))
    (c x : Nat) (v : BitVec (8*1)) (hdis : x + 8 ≤ c ∨ c + 1 ≤ x) :
    reconstructDword (mem.insert c (v.extractLsb' 0 8)) x = reconstructDword mem x := by
  apply reconstructDword_congr
  intro i hi
  exact getD_writeChain1_out mem c (x + i) v (by omega)

/-- The width-1 store's data slice is `truncate 8`. -/
theorem extractLsb_data8 (x : BitVec 64) :
    BitVec.setWidth (8*1) (Sail.BitVec.extractLsb x 7 0) = x.truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.truncate_eq_setWidth,
    show i < 8 from hi]

/-- **`sh_sail_equiv` discharged — unconditional halfword-store equivalence.** -/
theorem sh_sail_equiv (sRv : MachineState) (sSail : SailState)
    (rs1 rs2 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (h_valign : is_aligned_vaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = true)
    (h_match : matching_pma_region bm.regions
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = some region)
    (h_write : region.attributes.writable = true)
    (h_palign : is_aligned_paddr
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = true)
    (hclint : (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
      = .ok false sSail)
    (hsig : (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
      = .ok false sSail)
    (hhtif : (within_htif_writable
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
      = .ok false sSail) :
    ∃ sSail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 2) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SH rs1 rs2 offset)) sSail' ∧
      sSail'.regs.get? Register.nextPC = sSail.regs.get? Register.nextPC := by
  have soff : sign_extend (m := 64) offset = signExtend12 offset := by
    unfold sign_extend signExtend12 Sail.BitVec.signExtend; rfl
  have h_rs1 : (rX_bits (regToRegidx rs1)) sSail = .ok (sRv.getReg rs1) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs1)
  have h_rs2 : (rX_bits (regToRegidx rs2)) sSail = .ok (sRv.getReg rs2) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs2)
  set addr := sRv.getReg rs1 + signExtend12 offset with haddr_def
  set v : BitVec (8*2) := (sRv.getReg rs2).truncate 16 with hv_def
  set sSail' : SailState := { sSail with mem :=
      ((sSail.mem.insert addr.toNat (v.extractLsb' 0 8)).insert
        (addr.toNat+1) (v.extractLsb' 8 8)) }
    with hs'_def
  have hwrite : (writeBytes addr.toNat v : SailM Bool) sSail = .ok true sSail' :=
    writeBytes2_raw sSail addr.toNat v
  have hvwa := vmem_write_addr_store_core 2 (virtaddr.Virtaddr addr) sSail sSail'
    bm.mst v bm.cfgs bm.pmpaddrs bm.regions region (Or.inr (Or.inl rfl))
    h_valign bm.h_priv bm.h_mst bm.h_mprv bm.h_cfg bm.h_pmpaddr bm.h_off bm.h_reg
    (by simpa using h_match) h_write (by simpa using h_palign)
    (by simpa using hclint) (by simpa using hsig) (by simpa using hhtif)
    (by simpa using hwrite)
  have hvw := vmem_write_store_N 2 (regToRegidx rs1) (signExtend12 offset) (sRv.getReg rs1)
    sSail sSail' v bm h_rs1 (by simpa using hvwa)
  have halign2 : addr.toNat % 2 = 0 := is_aligned_vaddr_toNat addr 2 h_valign
  have hdecomp : (alignToDword addr).toNat + (byteOffset addr / 2) * 2 = addr.toNat :=
    alignToDword_offset_eq addr 2 (Or.inr (Or.inl rfl)) halign2
  have hposlt : byteOffset addr / 2 < 4 := by
    have := byteOffset_lt_8 (addr := addr); omega
  refine ⟨sSail', ?_, ?_, ?_⟩
  · unfold execute_STORE
    simp +decide only [soff, runSail_bind, runSail_pure, PreSail.assert, if_true]
    rw [show runSail (rX_bits (regToRegidx rs2)) sSail = some (sRv.getReg rs2, sSail) from by
      simp only [runSail, h_rs2]]
    simp +decide only []
    rw [show (((2 : Nat) *i 8) -i 1).toNat = 15 from by decide]
    rw [show runSail (vmem_write (regToRegidx rs1) (signExtend12 offset) 2
          (BitVec.setWidth (8*2) (Sail.BitVec.extractLsb (sRv.getReg rs2) 15 0))
          (MemoryAccessType.Store mem_payload.Data) false false false) sSail
        = some (Result.Ok true, sSail') from by
      rw [show BitVec.setWidth (8*2) (Sail.BitVec.extractLsb (sRv.getReg rs2) 15 0) = v
        from extractLsb_data16 (sRv.getReg rs2)]
      simp only [runSail, hvw]]
    simp only [runSail_pure]
  · refine ⟨fun r => ?_, fun a' ha' => ?_⟩
    · have h := hrel.reg_agree r
      cases r <;>
        simp [sailRegVal, hs'_def, execInstrBr, MachineState.setPC,
          MachineState.setHalfword, MachineState.setMem, MachineState.getReg] at h ⊢ <;>
        exact h
    · rcases eq_or_ne a' (alignToDword addr) with rfl | hne
      · have hrw : (execInstrBr sRv (.SH rs1 rs2 offset)).getMem (alignToDword addr)
            = replaceHalfword (sRv.getMem (alignToDword addr)) (byteOffset addr / 2) v := by
          simp only [execInstrBr, ← haddr_def, MachineState.setHalfword,
            MachineState.getMem_setPC, MachineState.getMem_setMem_eq]
          rfl
        rw [hrw, ← hrel.mem_agree (alignToDword addr) (alignToDword_toNat_mod8 addr)]
        have hbridge := reconstructDword_writeChain2_replace sSail.mem
          (alignToDword addr).toNat (byteOffset addr / 2) v hposlt
        rw [hdecomp] at hbridge
        exact hbridge
      · have hnat : a'.toNat ≠ (alignToDword addr).toNat :=
          fun h => hne (BitVec.toNat_inj.mp h)
        have hb8 := alignToDword_toNat_mod8 addr
        have hdis : a'.toNat + 8 ≤ addr.toNat ∨ addr.toNat + 2 ≤ a'.toNat := by omega
        have hrw : (execInstrBr sRv (.SH rs1 rs2 offset)).getMem a' = sRv.getMem a' := by
          simp only [execInstrBr, ← haddr_def, MachineState.setHalfword,
            MachineState.getMem_setPC, MachineState.getMem_setMem_ne hne]
        rw [hrw, ← hrel.mem_agree a' ha']
        exact reconstructDword_writeChain2_disjoint sSail.mem addr.toNat a'.toNat v hdis
  · simp [hs'_def]

/-- **`sb_sail_equiv` discharged — unconditional byte-store equivalence.** The byte
    position inside the containing dword is `byteOffset addr` directly (no rounding). -/
theorem sb_sail_equiv (sRv : MachineState) (sSail : SailState)
    (rs1 rs2 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (h_valign : is_aligned_vaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = true)
    (h_match : matching_pma_region bm.regions
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = some region)
    (h_write : region.attributes.writable = true)
    (h_palign : is_aligned_paddr
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = true)
    (hclint : (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
      = .ok false sSail)
    (hsig : (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
      = .ok false sSail)
    (hhtif : (within_htif_writable
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
      = .ok false sSail) :
    ∃ sSail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 1) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SB rs1 rs2 offset)) sSail' ∧
      sSail'.regs.get? Register.nextPC = sSail.regs.get? Register.nextPC := by
  have soff : sign_extend (m := 64) offset = signExtend12 offset := by
    unfold sign_extend signExtend12 Sail.BitVec.signExtend; rfl
  have h_rs1 : (rX_bits (regToRegidx rs1)) sSail = .ok (sRv.getReg rs1) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs1)
  have h_rs2 : (rX_bits (regToRegidx rs2)) sSail = .ok (sRv.getReg rs2) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs2)
  set addr := sRv.getReg rs1 + signExtend12 offset with haddr_def
  set v : BitVec (8*1) := (sRv.getReg rs2).truncate 8 with hv_def
  set sSail' : SailState := { sSail with mem := sSail.mem.insert addr.toNat (v.extractLsb' 0 8) }
    with hs'_def
  have hwrite : (writeBytes addr.toNat v : SailM Bool) sSail = .ok true sSail' :=
    writeBytes1_raw sSail addr.toNat v
  have hvwa := vmem_write_addr_store_core 1 (virtaddr.Virtaddr addr) sSail sSail'
    bm.mst v bm.cfgs bm.pmpaddrs bm.regions region (Or.inl rfl)
    h_valign bm.h_priv bm.h_mst bm.h_mprv bm.h_cfg bm.h_pmpaddr bm.h_off bm.h_reg
    (by simpa using h_match) h_write (by simpa using h_palign)
    (by simpa using hclint) (by simpa using hsig) (by simpa using hhtif)
    (by simpa using hwrite)
  have hvw := vmem_write_store_N 1 (regToRegidx rs1) (signExtend12 offset) (sRv.getReg rs1)
    sSail sSail' v bm h_rs1 (by simpa using hvwa)
  have hdecomp : (alignToDword addr).toNat + byteOffset addr * 1 = addr.toNat := by
    have := alignToDword_add_byteOffset_toNat addr; omega
  have hposlt : byteOffset addr < 8 := byteOffset_lt_8
  refine ⟨sSail', ?_, ?_, ?_⟩
  · unfold execute_STORE
    simp +decide only [soff, runSail_bind, runSail_pure, PreSail.assert, if_true]
    rw [show runSail (rX_bits (regToRegidx rs2)) sSail = some (sRv.getReg rs2, sSail) from by
      simp only [runSail, h_rs2]]
    simp +decide only []
    rw [show (((1 : Nat) *i 8) -i 1).toNat = 7 from by decide]
    rw [show runSail (vmem_write (regToRegidx rs1) (signExtend12 offset) 1
          (BitVec.setWidth (8*1) (Sail.BitVec.extractLsb (sRv.getReg rs2) 7 0))
          (MemoryAccessType.Store mem_payload.Data) false false false) sSail
        = some (Result.Ok true, sSail') from by
      rw [show BitVec.setWidth (8*1) (Sail.BitVec.extractLsb (sRv.getReg rs2) 7 0) = v
        from extractLsb_data8 (sRv.getReg rs2)]
      simp only [runSail, hvw]]
    simp only [runSail_pure]
  · refine ⟨fun r => ?_, fun a' ha' => ?_⟩
    · have h := hrel.reg_agree r
      cases r <;>
        simp [sailRegVal, hs'_def, execInstrBr, MachineState.setPC,
          MachineState.setByte, MachineState.setMem, MachineState.getReg] at h ⊢ <;>
        exact h
    · rcases eq_or_ne a' (alignToDword addr) with rfl | hne
      · have hrw : (execInstrBr sRv (.SB rs1 rs2 offset)).getMem (alignToDword addr)
            = replaceByte (sRv.getMem (alignToDword addr)) (byteOffset addr) v := by
          simp only [execInstrBr, ← haddr_def, MachineState.setByte,
            MachineState.getMem_setPC, MachineState.getMem_setMem_eq]
          rfl
        rw [hrw, ← hrel.mem_agree (alignToDword addr) (alignToDword_toNat_mod8 addr)]
        have hbridge := reconstructDword_writeChain1_replace sSail.mem
          (alignToDword addr).toNat (byteOffset addr) v hposlt
        rw [hdecomp] at hbridge
        exact hbridge
      · have hnat : a'.toNat ≠ (alignToDword addr).toNat :=
          fun h => hne (BitVec.toNat_inj.mp h)
        have hb8 := alignToDword_toNat_mod8 addr
        have hdis : a'.toNat + 8 ≤ addr.toNat ∨ addr.toNat + 1 ≤ a'.toNat := by omega
        have hrw : (execInstrBr sRv (.SB rs1 rs2 offset)).getMem a' = sRv.getMem a' := by
          simp only [execInstrBr, ← haddr_def, MachineState.setByte,
            MachineState.getMem_setPC, MachineState.getMem_setMem_ne hne]
        rw [hrw, ← hrel.mem_agree a' ha']
        exact reconstructDword_writeChain1_disjoint sSail.mem addr.toNat a'.toNat v hdis
  · simp [hs'_def]

end EvmAsm.Rv64.SailEquiv
