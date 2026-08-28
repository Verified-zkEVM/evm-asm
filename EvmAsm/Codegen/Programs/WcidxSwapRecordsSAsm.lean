/-
  EvmAsm.Codegen.Programs.WcidxSwapRecordsSAsm

  Proof-first (DCode) port of the DEPLOYED `wcidx_swap_records` (and its
  token-identical twin `widx_swap_records`): swap two 48-byte index
  records held in one writable arena, byte-identically to the emitted
  routine (docs/sasm-deriv.md).

  Why this exists: the flat swap triple (`widx_swap_records_spec`,
  `Proofs/MptWitnessIndexSpec.lean`) historically covered a
  register-allocation VARIANT (x6 loop counter where the image uses
  x31); #12990 reconciled it onto the image's allocation, so it now
  transfers here too (`wcidxSwapRecords_prog_eq`,
  `Proofs/WitnessCodeLookupSpec.lean`).  This port proves the deployed
  register allocation independently — and, unlike the flat triple (which required
  the two records to be distinct), it is UNIFIED: the leading
  `beq a0, a1` equal-pointer skip is the `when`'s pure skip path, so the
  postcondition covers `pa = pb` as well.

  Byte shape: `beq a0,a1 → ret` over (`li t6, 6`; a 6-trip dword-swap
  `while`) — exactly `when (bne a0 a1) { block; dwhile }`.
-/

import EvmAsm.Rv64.SAsm.Deriv
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Codegen.Programs.WitnessCodeLookup

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

namespace WcidxSwapRecordsSAsm

/-! ## The swap model -/

/-- The 8-byte chunk of `l` at byte offset `p`. -/
def chunk (l : List (BitVec 8)) (p : Nat) : List (BitVec 8) :=
  (l.drop p).take 8

theorem length_chunk (l : List (BitVec 8)) (p : Nat) (h : p + 8 ≤ l.length) :
    (chunk l p).length = 8 := by
  simp only [chunk, List.length_take, List.length_drop]
  omega

/-- After `k` trips: the first `k` dwords of the two records exchanged,
    everything else original.  The recursion IS the loop step. -/
def swapK (orig : List (BitVec 8)) (oa ob : Nat) : Nat → List (BitVec 8)
  | 0 => orig
  | k + 1 =>
      setBytes
        (setBytes (swapK orig oa ob k) (oa + 8 * k) (chunk orig (ob + 8 * k)))
        (ob + 8 * k) (chunk orig (oa + 8 * k))

@[simp] theorem length_swapK (orig : List (BitVec 8)) (oa ob k : Nat) :
    (swapK orig oa ob k).length = orig.length := by
  induction k with
  | zero => rfl
  | succ k ih => simp [swapK, ih]

/-- A chunk beyond a spliced window is untouched. -/
theorem chunk_setBytes_disjoint (l ns : List (BitVec 8)) (p q : Nat)
    (h : p + ns.length ≤ q ∨ q + 8 ≤ p) :
    chunk (setBytes l p ns) q = chunk l q := by
  rcases h with h | h
  · unfold chunk
    rw [setBytes_drop_of_le _ _ _ _ h]
  · unfold chunk
    rw [setBytes_drop_of_ge _ _ _ _ (by omega),
      setBytes_take_of_ge _ _ _ _ (by omega)]

/-- The record layout: `oa`/`ob` are byte offsets of two 48-byte records
    in the arena — either the same record or fully disjoint. -/
def recLayout (len oa ob : Nat) : Prop :=
  8 ∣ oa ∧ 8 ∣ ob ∧ oa + 48 ≤ len ∧ ob + 48 ≤ len ∧
  (oa = ob ∨ oa + 48 ≤ ob ∨ ob + 48 ≤ oa)

/-- Chunks at any not-yet-swapped dword (trip index ≥ k) are still the
    original bytes: every write of the first `k` trips ends strictly
    below it in its own record and is disjoint from (or below) it in the
    other record. -/
theorem chunk_swapK (orig : List (BitVec 8)) (oa ob k m : Nat) (q : Nat)
    (hlay : recLayout orig.length oa ob) (hm : k ≤ m) (hm6 : m < 6)
    (hq : q = oa + 8 * m ∨ q = ob + 8 * m) :
    chunk (swapK orig oa ob k) q = chunk orig q := by
  obtain ⟨-, -, hoa, hob, hdisj⟩ := hlay
  induction k with
  | zero => rfl
  | succ k ih =>
      show chunk (setBytes (setBytes (swapK orig oa ob k) (oa + 8 * k)
        (chunk orig (ob + 8 * k))) (ob + 8 * k)
        (chunk orig (oa + 8 * k))) q = chunk orig q
      have hca : (chunk orig (oa + 8 * k)).length = 8 :=
        length_chunk _ _ (by omega)
      have hcb : (chunk orig (ob + 8 * k)).length = 8 :=
        length_chunk _ _ (by omega)
      rw [chunk_setBytes_disjoint _ _ _ _ (by
          rw [hca]
          rcases hq with rfl | rfl <;> rcases hdisj with h | h | h <;> omega),
        chunk_setBytes_disjoint _ _ _ _ (by
          rw [hcb]
          rcases hq with rfl | rfl <;> rcases hdisj with h | h | h <;> omega)]
      exact ih (by omega)

/-- Writing a list's own bytes back is the identity. -/
theorem setBytes_chunk_self (bs : List (BitVec 8)) (p n : Nat)
    (h : p + n ≤ bs.length) :
    setBytes bs p ((bs.drop p).take n) = bs := by
  induction n generalizing bs p with
  | zero => rfl
  | succ n ih =>
      have hp : p < bs.length := by omega
      rw [List.drop_eq_getElem_cons hp, List.take_succ_cons, setBytes_cons,
        List.set_getElem_self]
      have hd : (bs[p] :: bs.drop (p + 1)).tail = bs.drop (p + 1) := rfl
      rw [show bs.drop (p + 1) = ((bs.drop p).drop 1) from by
        rw [List.drop_drop, Nat.add_comm]]
      rw [List.drop_eq_getElem_cons hp]
      show setBytes bs (p + 1) ((bs.drop (p + 1)).take n) = bs
      exact ih bs (p + 1) (by omega)

/-- Swapping a record with itself is the identity. -/
theorem swapK_self (orig : List (BitVec 8)) (oa k : Nat)
    (hk : k ≤ 6) (hlen : oa + 48 ≤ orig.length) :
    swapK orig oa oa k = orig := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show setBytes (setBytes (swapK orig oa oa k) (oa + 8 * k)
        (chunk orig (oa + 8 * k))) (oa + 8 * k)
        (chunk orig (oa + 8 * k)) = orig
      rw [ih (by omega)]
      rw [show chunk orig (oa + 8 * k)
          = (orig.drop (oa + 8 * k)).take 8 from rfl,
        setBytes_chunk_self orig (oa + 8 * k) 8 (by omega),
        setBytes_chunk_self orig (oa + 8 * k) 8 (by omega)]

/-! ## The routine's pieces -/

/-- The 6-trip dword-swap body. -/
def wsrStepBlock : List Instr :=
  [ .LD .x5 .x10 0,
    .LD .x6 .x11 0,
    .SD .x10 .x6 0,
    .SD .x11 .x5 0,
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x11 .x11 (8 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12) ]

/-- Register file after one swap trip (given the two loaded dwords). -/
def wsrStepRf (rf : RegFile) (va vb : Word) : RegFile :=
  let r1 := rf.set .x5 va
  let r2 := r1.set .x6 vb
  let r3 := r2.set .x10 (r2.get .x10 + signExtend12 (8 : BitVec 12))
  let r4 := r3.set .x11 (r3.get .x11 + signExtend12 (8 : BitVec 12))
  r4.set .x31 (r4.get .x31 + signExtend12 (-1 : BitVec 12))

theorem wsrStepRf_get_x10 (rf : RegFile) (va vb : Word) :
    (wsrStepRf rf va vb).get .x10
      = rf.get .x10 + signExtend12 (8 : BitVec 12) := by
  unfold wsrStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x31),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x11),
    RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]

theorem wsrStepRf_get_x11 (rf : RegFile) (va vb : Word) :
    (wsrStepRf rf va vb).get .x11
      = rf.get .x11 + signExtend12 (8 : BitVec 12) := by
  unfold wsrStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x31),
    RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]

theorem wsrStepRf_get_x31 (rf : RegFile) (va vb : Word) :
    (wsrStepRf rf va vb).get .x31
      = rf.get .x31 + signExtend12 (-1 : BitVec 12) := by
  unfold wsrStepRf
  rw [RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x31 ≠ .x11),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x31 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x31 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x31 ≠ .x5)]

/-! ## The step engine -/

section Engine

variable (base : Word) (ro : Region)

/-- Address of the current dword of a record, as a window index. -/
theorem wsr_haddr (m : Nat) (rf : RegFile) (r : Reg)
    (hx : rf.get r = base + BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) (hnw : base.toNat + m < 2 ^ 64) :
    ((rf.get r + signExtend12 (0 : BitVec 12)) - base).toNat = m := by
  rw [hx, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  have h1 : (BitVec.ofNat 64 m).toNat = m := by
    rw [BitVec.toNat_ofNat]; omega
  bv_omega

/-- Engine: one trip loads the two current dwords, cross-stores them,
    and advances the cursors. -/
theorem wsr_step_engine (oa ob k : Nat) (orig : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8))
    (hx10 : rf.get .x10 = base + BitVec.ofNat 64 (oa + 8 * k))
    (hx11 : rf.get .x11 = base + BitVec.ofNat 64 (ob + 8 * k))
    (hlay : recLayout orig.length oa ob) (hk : k < 6)
    (hnw : base.toNat + orig.length < 2 ^ 64)
    (hws : ws = swapK orig oa ob k) :
    execBlock ro base rf ws wsrStepBlock
      = (wsrStepRf rf (packBytes (chunk orig (oa + 8 * k)))
          (packBytes (chunk orig (ob + 8 * k))),
         swapK orig oa ob (k + 1)) := by
  obtain ⟨hda, hdb, hoa, hob, hdisj⟩ := hlay
  have hlen : ws.length = orig.length := by rw [hws, length_swapK]
  have hA : ((rf.get .x10 + signExtend12 (0 : BitVec 12)) - base).toNat
      = oa + 8 * k :=
    wsr_haddr base _ rf .x10 hx10 (by omega) (by omega)
  have hsliceA : packBytes ((ws.drop (oa + 8 * k)).take 8)
      = packBytes (chunk orig (oa + 8 * k)) := by
    rw [hws]
    rw [show ((swapK orig oa ob k).drop (oa + 8 * k)).take 8
        = chunk (swapK orig oa ob k) (oa + 8 * k) from rfl,
      chunk_swapK orig oa ob k k _ ⟨hda, hdb, hoa, hob, hdisj⟩
        (Nat.le_refl k) hk (Or.inl rfl)]
  rw [show wsrStepBlock =
      [.LD .x5 .x10 0, .LD .x6 .x11 0, .SD .x10 .x6 0, .SD .x11 .x5 0,
       .ADDI .x10 .x10 (8 : BitVec 12), .ADDI .x11 .x11 (8 : BitVec 12),
       .ADDI .x31 .x31 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons, execInstrRF_ld_dword ro base rf ws .x5 .x10 0
    (oa + 8 * k) (packBytes (chunk orig (oa + 8 * k))) hA
    (by omega) hsliceA]
  dsimp only
  set rf1 := rf.set .x5 (packBytes (chunk orig (oa + 8 * k))) with hrf1
  have hx11' : rf1.get .x11 = base + BitVec.ofNat 64 (ob + 8 * k) := by
    rw [hrf1, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
  have hB : ((rf1.get .x11 + signExtend12 (0 : BitVec 12)) - base).toNat
      = ob + 8 * k :=
    wsr_haddr base _ rf1 .x11 hx11' (by omega) (by omega)
  have hsliceB : packBytes ((ws.drop (ob + 8 * k)).take 8)
      = packBytes (chunk orig (ob + 8 * k)) := by
    rw [hws]
    rw [show ((swapK orig oa ob k).drop (ob + 8 * k)).take 8
        = chunk (swapK orig oa ob k) (ob + 8 * k) from rfl,
      chunk_swapK orig oa ob k k _ ⟨hda, hdb, hoa, hob, hdisj⟩
        (Nat.le_refl k) hk (Or.inr rfl)]
  rw [execBlock_cons, execInstrRF_ld_dword ro base rf1 ws .x6 .x11 0
    (ob + 8 * k) (packBytes (chunk orig (ob + 8 * k))) hB
    (by omega) hsliceB]
  dsimp only
  set rf2 := rf1.set .x6 (packBytes (chunk orig (ob + 8 * k))) with hrf2
  have hx10'' : rf2.get .x10 = base + BitVec.ofNat 64 (oa + 8 * k) := by
    rw [hrf2, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6), hrf1,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
  have hA2 : ((rf2.get .x10 + signExtend12 (0 : BitVec 12)) - base).toNat
      = oa + 8 * k :=
    wsr_haddr base _ rf2 .x10 hx10'' (by omega) (by omega)
  rw [execBlock_cons, execInstrRF_sd_dword ro base rf2 ws .x10 .x6 0
    (oa + 8 * k) hA2]
  have hv6 : rf2.get .x6 = packBytes (chunk orig (ob + 8 * k)) := by
    rw [hrf2, RegFile.get_set_self _ _ _ (by decide)]
  rw [hv6, dwordBytes_packBytes _ (length_chunk _ _ (by omega))]
  set ws1 := setBytes ws (oa + 8 * k) (chunk orig (ob + 8 * k)) with hws1
  have hx11'' : rf2.get .x11 = base + BitVec.ofNat 64 (ob + 8 * k) := by
    rw [hrf2, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6), hx11']
  have hB2 : ((rf2.get .x11 + signExtend12 (0 : BitVec 12)) - base).toNat
      = ob + 8 * k :=
    wsr_haddr base _ rf2 .x11 hx11'' (by omega) (by omega)
  rw [execBlock_cons, execInstrRF_sd_dword ro base rf2 ws1 .x11 .x5 0
    (ob + 8 * k) hB2]
  have hv5 : rf2.get .x5 = packBytes (chunk orig (oa + 8 * k)) := by
    rw [hrf2, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6), hrf1,
      RegFile.get_set_self _ _ _ (by decide)]
  rw [hv5, dwordBytes_packBytes _ (length_chunk _ _ (by omega))]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  rw [hws1, hws]
  rfl

end Engine

/-! ## The derivation -/

section Deriv

variable (base : Word) (orig : List (BitVec 8)) (oa ob : Nat)

/-- Static facts. -/
def wsrStatic : Prop :=
  recLayout orig.length oa ob ∧ base.toNat + orig.length < 2 ^ 64

/-- Loop invariant. -/
def wsrInv (k : Nat) : Reach :=
  fun rf ws A =>
    rf.get .x10 = base + BitVec.ofNat 64 (oa + 8 * k) ∧
    rf.get .x11 = base + BitVec.ofNat 64 (ob + 8 * k) ∧
    rf.get .x31 = BitVec.ofNat 64 (6 - k) ∧ k ≤ 6 ∧
    wsrStatic base orig oa ob ∧
    ws = swapK orig oa ob k ∧ A = empAssertion

local infix:36 " ⤳ " => DCode Region.empty (RwRegion.mk base orig.length)

/-- Proof-first record swap, unified over the equal-pointer case: the
    leading `beq a0, a1` skip is the `when`'s pure skip path (a swap of a
    record with itself is the identity, `swapK_self`). -/
def wsrDeriv :
    (fun rf ws A => rf.get .x10 = base + BitVec.ofNat 64 oa ∧
      rf.get .x11 = base + BitVec.ofNat 64 ob ∧
      ws = orig ∧ wsrStatic base orig oa ob ∧ A = empAssertion)
      ⤳ (fun _ ws A => ws = swapK orig oa ob 6 ∧ A = empAssertion) :=
  DCode.when "swap" (.bne .x10 .x11)
    (calc (fun rf ws A => (rf.get .x10 = base + BitVec.ofNat 64 oa ∧
          rf.get .x11 = base + BitVec.ofNat 64 ob ∧
          ws = orig ∧ wsrStatic base orig oa ob ∧ A = empAssertion)
          ∧ (Cond.bne .x10 .x11).holds rf : Reach)
      _ ⤳ (fun rf ws A => wsrInv base orig oa ob 0 rf ws A : Reach) :=
        DCode.block "count" [.LI .x31 (6 : Word)] (by decide)
          (fun h => absurd h (by decide))
          (by
            rintro rf ws A _ ⟨⟨h10, h11, hws, hst, hA⟩, -⟩
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
              wsrInv]
            refine ⟨?_, ?_, ?_, by omega, hst, by rw [hws]; rfl, hA⟩
            · rw [RegFile.get_set_ne _ _ _ _ (by decide), h10]
              bv_omega
            · rw [RegFile.get_set_ne _ _ _ _ (by decide), h11]
              bv_omega
            · rw [RegFile.get_set_self _ _ _ (by decide)]
              decide)
      _ ⤳ (fun rf ws A => (∃ k, k ≤ 6 ∧ wsrInv base orig oa ob k rf ws A)
            ∧ ¬ (Cond.bne .x31 .x0).holds rf : Reach) :=
        DCode.dwhile "loop" (.bne .x31 .x0) 6 (wsrInv base orig oa ob)
          (fun _ _ _ h => h)
          (fun k =>
            DCode.block "step" wsrStepBlock (by decide)
              (by
                intro _ rf ws A hwslen hpre
                obtain ⟨hk, ⟨h10, h11, h31, hk6,
                  ⟨⟨hda, hdb, hoa, hob, hdisj⟩, hnw⟩, hws, hA⟩, -⟩ := hpre
                have hlen : ws.length = orig.length := by
                  rw [hws, length_swapK]
                have hA1 : ((rf.get .x10 + signExtend12 (0 : BitVec 12))
                    - base).toNat = oa + 8 * k :=
                  wsr_haddr base (oa + 8 * k) rf .x10 h10
                    (by omega) (by omega)
                show blockVCs Region.empty base rf ws wsrStepBlock
                rw [show wsrStepBlock =
                    [.LD .x5 .x10 0, .LD .x6 .x11 0, .SD .x10 .x6 0,
                     .SD .x11 .x5 0, .ADDI .x10 .x10 (8 : BitVec 12),
                     .ADDI .x11 .x11 (8 : BitVec 12),
                     .ADDI .x31 .x31 (-1 : BitVec 12)] from rfl]
                refine ⟨?_, ?_⟩
                · -- first LD routes into the window, aligned and in range
                  simp only [loadSem]
                  rw [if_pos (show inRw base ws
                      (rf.get .x10 + signExtend12 (0 : BitVec 12)) 8 from by
                    unfold inRw
                    rw [hA1]
                    omega)]
                  unfold Region.loadOk
                  rw [show ((rf.get .x10 + signExtend12 (0 : BitVec 12))
                      - (Region.mk base ws).base).toNat = oa + 8 * k
                      from hA1]
                  show 8 ∣ (oa + 8 * k) ∧ oa + 8 * k + 8 ≤ ws.length
                  exact ⟨by omega, by omega⟩
                · rw [execInstrRF_ld_dword Region.empty base rf ws .x5 .x10 0
                    (oa + 8 * k) (packBytes ((ws.drop (oa + 8 * k)).take 8))
                    hA1 (by omega) rfl]
                  have hx11' : (rf.set .x5
                      (packBytes ((ws.drop (oa + 8 * k)).take 8))).get .x11
                      = base + BitVec.ofNat 64 (ob + 8 * k) := by
                    rw [RegFile.get_set_ne _ _ _ _
                      (by decide : Reg.x11 ≠ .x5), h11]
                  have hB1 : (((rf.set .x5
                      (packBytes ((ws.drop (oa + 8 * k)).take 8))).get .x11
                      + signExtend12 (0 : BitVec 12)) - base).toNat
                      = ob + 8 * k :=
                    wsr_haddr base (ob + 8 * k) _ .x11 hx11'
                      (by omega) (by omega)
                  refine ⟨?_, ?_⟩
                  · simp only [loadSem]
                    rw [if_pos (show inRw base ws _ 8 from by
                      unfold inRw
                      rw [hB1]
                      omega)]
                    unfold Region.loadOk
                    rw [show (_ - (Region.mk base ws).base).toNat
                        = ob + 8 * k from hB1]
                    show 8 ∣ (ob + 8 * k) ∧ ob + 8 * k + 8 ≤ ws.length
                    exact ⟨by omega, by omega⟩
                  · rw [execInstrRF_ld_dword Region.empty base _ ws .x6 .x11 0
                      (ob + 8 * k)
                      (packBytes ((ws.drop (ob + 8 * k)).take 8))
                      hB1 (by omega) rfl]
                    have hx10'' : ((rf.set .x5
                        (packBytes ((ws.drop (oa + 8 * k)).take 8))).set .x6
                        (packBytes ((ws.drop (ob + 8 * k)).take 8))).get .x10
                        = base + BitVec.ofNat 64 (oa + 8 * k) := by
                      rw [RegFile.get_set_ne _ _ _ _
                          (by decide : Reg.x10 ≠ .x6),
                        RegFile.get_set_ne _ _ _ _
                          (by decide : Reg.x10 ≠ .x5), h10]
                    have hA2 : ((((rf.set .x5
                        (packBytes ((ws.drop (oa + 8 * k)).take 8))).set .x6
                        (packBytes ((ws.drop (ob + 8 * k)).take 8))).get .x10
                        + signExtend12 (0 : BitVec 12)) - base).toNat
                        = oa + 8 * k :=
                      wsr_haddr base (oa + 8 * k) _ .x10 hx10''
                        (by omega) (by omega)
                    refine ⟨⟨?_, ?_⟩, ?_⟩
                    · dsimp only
                      unfold inRw
                      rw [hA2]
                      omega
                    · dsimp only
                      rw [hA2]
                      omega
                    · rw [execInstrRF_sd_dword Region.empty base _ ws
                        .x10 .x6 0 (oa + 8 * k) hA2]
                      have hx11'' : ((rf.set .x5
                          (packBytes ((ws.drop (oa + 8 * k)).take 8))).set
                          .x6 (packBytes ((ws.drop (ob + 8 * k)).take 8))).get
                          .x11 = base + BitVec.ofNat 64 (ob + 8 * k) := by
                        rw [RegFile.get_set_ne _ _ _ _
                            (by decide : Reg.x11 ≠ .x6), hx11']
                      have hB2 : ((((rf.set .x5
                          (packBytes ((ws.drop (oa + 8 * k)).take 8))).set
                          .x6 (packBytes ((ws.drop (ob + 8 * k)).take 8))).get
                          .x11 + signExtend12 (0 : BitVec 12))
                          - base).toNat = ob + 8 * k :=
                        wsr_haddr base (ob + 8 * k) _ .x11 hx11''
                          (by omega) (by omega)
                      refine ⟨⟨?_, ?_⟩, trivial, trivial, trivial, trivial⟩
                      · dsimp only
                        unfold inRw
                        rw [hB2, length_setBytes]
                        omega
                      · dsimp only
                        rw [hB2]
                        omega)
              (by
                rintro rf ws A hwslen ⟨hk, ⟨h10, h11, h31, hk6, hst,
                  hws, hA⟩, -⟩
                obtain ⟨⟨hda, hdb, hoa, hob, hdisj⟩, hnw⟩ := hst
                rw [wsr_step_engine base Region.empty oa ob k orig rf ws
                  h10 h11 ⟨hda, hdb, hoa, hob, hdisj⟩ hk hnw hws]
                refine ⟨?_, ?_, ?_, by omega,
                  ⟨⟨hda, hdb, hoa, hob, hdisj⟩, hnw⟩, rfl, hA⟩
                · rw [wsrStepRf_get_x10, h10,
                    show signExtend12 (8 : BitVec 12) = (8 : Word) from
                      by decide]
                  have h1 : (BitVec.ofNat 64 (oa + 8 * k)).toNat
                      = oa + 8 * k := by rw [BitVec.toNat_ofNat]; omega
                  have h2 : (BitVec.ofNat 64 (oa + 8 * (k + 1))).toNat
                      = oa + 8 * (k + 1) := by
                    rw [BitVec.toNat_ofNat]; omega
                  bv_omega
                · rw [wsrStepRf_get_x11, h11,
                    show signExtend12 (8 : BitVec 12) = (8 : Word) from
                      by decide]
                  have h1 : (BitVec.ofNat 64 (ob + 8 * k)).toNat
                      = ob + 8 * k := by rw [BitVec.toNat_ofNat]; omega
                  have h2 : (BitVec.ofNat 64 (ob + 8 * (k + 1))).toNat
                      = ob + 8 * (k + 1) := by
                    rw [BitVec.toNat_ofNat]; omega
                  bv_omega
                · rw [wsrStepRf_get_x31, h31,
                    show signExtend12 (-1 : BitVec 12) = (-1 : Word) from
                      by decide]
                  have h1 : (BitVec.ofNat 64 (6 - k)).toNat = 6 - k := by
                    rw [BitVec.toNat_ofNat]; omega
                  have h2 : (BitVec.ofNat 64 (6 - (k + 1))).toNat
                      = 6 - (k + 1) := by rw [BitVec.toNat_ofNat]; omega
                  bv_omega))
          (fun rf ws A h => by
            obtain ⟨-, -, h31, -⟩ := h
            simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not]
            rw [h31]
            decide)
      _ ⤳ (fun _ ws A => ws = swapK orig oa ob 6 ∧ A = empAssertion
            : Reach) :=
        DCode.pure "done"
          (by
            rintro rf ws A ⟨⟨k, hk6, -, -, h31, -, -, hws, hA⟩, hc⟩
            simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hc
            have hk : k = 6 := by
              rw [h31] at hc
              have := congrArg BitVec.toNat hc
              rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl]
                at this
              omega
            subst hk
            exact ⟨hws, hA⟩))
    (by
      rintro rf ws A ⟨h10, h11, hws, ⟨⟨hda, hdb, hoa, hob, hdisj⟩, hnw⟩, hA⟩
        hc
      simp only [Cond.holds, ne_eq, not_not] at hc
      rw [h10, h11] at hc
      have hoab : oa = ob := by
        have := congrArg BitVec.toNat hc
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
          BitVec.toNat_ofNat] at this
        omega
      subst hoab
      refine ⟨?_, hA⟩
      rw [hws, swapK_self orig oa 6 (by omega) hoa])

/-! ## The generated function, spec, and code -/

/-- The generated SAsm function. -/
def wsrFn : Fn := (wsrDeriv base orig oa ob).fn "wcidx_swap_records"

/-- Machine-level correctness at any base: from the ABI precondition (two
    record pointers into the arena, layout facts), the arena ends as
    `swapK … 6` — the two 48-byte records exchanged; for `pa = pb` the
    postcondition degenerates to the identity (`swapK_self`). -/
theorem wsrFn_spec (hrw : RwRegion.wf ⟨base, orig.length⟩) (b0 : Word) :
    (wsrFn base orig oa ob).Spec b0 :=
  DCode.fn_spec "wcidx_swap_records" (wsrDeriv base orig oa ob) b0
    Region.empty_wf hrw

end Deriv

/-- The generated code with the return epilogue. -/
def wcidxSwapRecordsGen_prog : Program :=
  (wsrFn 0 [] 0 0).programRet 0

/-- `Program` is a def alias, opaque to instance search. -/
instance : BEq Program := inferInstanceAs (BEq (List Instr))

-- Byte-identity with the DEPLOYED program (and hence, via the drift
-- theorems in `WitnessCodeLookup.lean` / `MptWitnessIndex.lean`, with the
-- emitted `wcidx_swap_records` and `widx_swap_records` text).
#guard (wcidxSwapRecordsGen_prog : List Instr)
    == (Codegen.wcidxSwapRecords_prog : List Instr)

#guard wcidxSwapRecordsGen_prog.length = 12

-- The code does not depend on the ghost arguments (sampled).
#guard ((wsrFn 3 [0, 1] 8 16).programRet 0 : List Instr)
    == (wcidxSwapRecordsGen_prog : List Instr)

end WcidxSwapRecordsSAsm

end EvmAsm.Codegen

