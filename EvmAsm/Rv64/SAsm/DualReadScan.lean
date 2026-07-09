/-
  EvmAsm.Rv64.SAsm.DualReadScan

  The reusable **dual-read dword equality scan** (bead evm-asm-4ch8f.58.3.25.1).

  Three pieces, each independently consumable:

  1. **Focused dword-read primitives** — from a region at `base`, an `LD` at
     `base + 8·i` is in-region (`Region.loadOk_slot`) and yields dword slot
     `i` (`Region.dwordAt_slot`); a region suffix stays well-formed
     (`Region.wf_dropSuffix`), so an advancing cursor can be focused via
     `readAt` with a `take`/`drop` split of the ambient `bytesRegion`.

  2. **The per-dword ⇔ byte-list bridge** — `bytes_eq_of_dwordSlots_eq`:
     if the two `8·N`-byte lists agree on every dword slot they are EQUAL
     byte lists (via `extractByte_packBytes`); the converse is `congrArg`.
     This is what makes an equality-scan post genuine byte equality rather
     than dangling per-slot facts.

  3. **The scan itself** — `scanBody`, register-agnostic (`ctr`/`tA`/`tB`/
     `pA`/`pB` are parameters, constrained only to be exposed and pairwise
     distinct): a bottom-tested `retWhileBreak` countdown loop that reads
     dword `i` from BOTH buffers through advancing cursors (buffer A is the
     primary read-only region, buffer B a `readAt`-focused suffix of the
     ambient), breaks to a `0`-returning tail on the first mismatch, and
     falls out to a `1`-returning tail after `N` matches.  `scan_spec`
     concludes the genuine post `a0 = (if bsA = bsB then 1 else 0)`.

  Consumers: `bnq_eq` (`Bn254Fq12EqSAsm`, N = 48) and `blq_eq`
  (`Bls12Fq12EqSAsm`, N = 72) instantiate the registers/size and inherit the
  byte-tie `#guard`s; `bloom_eq`'s all-`readAt` accumulate-compare shape can
  reuse pieces 1–2 (its single-exit XOR/OR loop is not this scan).
-/

import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.HandleWiden

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

-- ============================================================================
-- §1  Dword slots and the per-dword ⇔ byte-list bridge
-- ============================================================================

/-- Dword slot `i` of a byte list: the little-endian pack of bytes
    `8·i … 8·i+7`.  This is exactly what an `LD` at offset `8·i` from the
    list's base reads (`Region.dwordAt_slot`). -/
def dwordSlot (bs : List (BitVec 8)) (i : Nat) : Word :=
  packBytes ((bs.drop (8 * i)).take 8)

/-- Equal byte lists have equal dword slots (the trivial direction). -/
theorem dwordSlot_congr {bs1 bs2 : List (BitVec 8)} (h : bs1 = bs2) (i : Nat) :
    dwordSlot bs1 i = dwordSlot bs2 i := by rw [h]

/-- **The bridge**: two `8·N`-byte lists that agree on every dword slot are
    equal.  Together with `dwordSlot_congr` this closes
    "all `N` dwords equal ⇔ the two byte lists are equal". -/
theorem bytes_eq_of_dwordSlots_eq (N : Nat) (bs1 bs2 : List (BitVec 8))
    (h1 : bs1.length = 8 * N) (h2 : bs2.length = 8 * N)
    (h : ∀ i, i < N → dwordSlot bs1 i = dwordSlot bs2 i) :
    bs1 = bs2 := by
  apply List.ext_getElem (by omega)
  intro j hj1 hj2
  have hiN : j / 8 < N := by omega
  have hr8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
  have hslot := h (j / 8) hiN
  unfold dwordSlot at hslot
  have hlt1 : j % 8 < ((bs1.drop (8 * (j / 8))).take 8).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have hlt2 : j % 8 < ((bs2.drop (8 * (j / 8))).take 8).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have e1 := extractByte_packBytes ((bs1.drop (8 * (j / 8))).take 8) (j % 8) hr8
    hlt1
  have e2 := extractByte_packBytes ((bs2.drop (8 * (j / 8))).take 8) (j % 8) hr8
    hlt2
  rw [hslot] at e1
  have hb : ((bs1.drop (8 * (j / 8))).take 8)[j % 8]'hlt1
      = ((bs2.drop (8 * (j / 8))).take 8)[j % 8]'hlt2 := by
    rw [← e1, ← e2]
  have hg1 : ((bs1.drop (8 * (j / 8))).take 8)[j % 8]'hlt1
      = bs1[8 * (j / 8) + j % 8]'(by omega) := by
    rw [List.getElem_take, List.getElem_drop]
  have hg2 : ((bs2.drop (8 * (j / 8))).take 8)[j % 8]'hlt2
      = bs2[8 * (j / 8) + j % 8]'(by omega) := by
    rw [List.getElem_take, List.getElem_drop]
  have hj8 : 8 * (j / 8) + j % 8 = j := by omega
  rw [hg1, hg2] at hb
  simp only [hj8] at hb
  exact hb

-- ============================================================================
-- §2  Focused dword-read primitives
-- ============================================================================

/-- An 8-byte load at `base + 8·i` is in-region whenever slot `i` fits. -/
theorem Region.loadOk_slot (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hfit : 8 * i + 8 ≤ bs.length) (hlen : bs.length < 2 ^ 64) :
    Region.loadOk ⟨base, bs⟩ (base + BitVec.ofNat 64 (8 * i)) 8 := by
  unfold Region.loadOk
  dsimp only
  have hcancel : base + BitVec.ofNat 64 (8 * i) - base = BitVec.ofNat 64 (8 * i) := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  rw [hcancel]
  simp only [BitVec.toNat_ofNat]
  have hmod : 8 * i % 2 ^ 64 = 8 * i := Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  exact ⟨⟨i, rfl⟩, by omega⟩

/-- The dword an `LD` reads at `base + 8·i` is dword slot `i`. -/
theorem Region.dwordAt_slot (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hlt : 8 * i < 2 ^ 64) :
    Region.dwordAt ⟨base, bs⟩ (base + BitVec.ofNat 64 (8 * i)) = dwordSlot bs i := by
  unfold Region.dwordAt dwordSlot
  dsimp only
  have hcancel : base + BitVec.ofNat 64 (8 * i) - base = BitVec.ofNat 64 (8 * i) := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  rw [hcancel]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hlt]

/-- A dword-aligned suffix of a well-formed region is well-formed: this is
    what keeps an advancing `readAt` cursor focusable. -/
theorem Region.wf_dropSuffix (base : Word) (bs : List (BitVec 8)) (k : Nat)
    (hwf : Region.wf ⟨base, bs⟩) (h8 : k % 8 = 0) (hk : k ≤ bs.length) :
    Region.wf ⟨base + BitVec.ofNat 64 k, bs.drop k⟩ := by
  unfold Region.wf at hwf ⊢
  dsimp only at hwf ⊢
  obtain ⟨halign, hbound, hvalid⟩ := hwf
  have htoNat : (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hklt : k < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hklt]
    omega
  refine ⟨by omega, ?_, ?_⟩
  · simp only [List.length_drop]
    omega
  · intro j hj
    simp only [List.length_drop] at hj
    have haddr : base + BitVec.ofNat 64 k + BitVec.ofNat 64 j
        = base + BitVec.ofNat 64 (k + j) := by
      rw [BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [haddr]
    exact hvalid (k + j) (by omega)

/-- Exposed registers are never the hardwired zero (needed to read a value
    back after `RegFile.set` on a symbolic exposed register). -/
theorem Reg.ne_x0_of_isExposed : ∀ r : Reg, Reg.isExposed r = true → r ≠ .x0 := by
  intro r h hr
  subst hr
  exact absurd h (by decide)

-- ============================================================================
-- §3  The register-agnostic dual-read equality scan
-- ============================================================================

namespace DualReadScan

open EvmAsm.Rv64.SAsm.Stmt

/-- Loop invariant after `i` matched slots: the counter holds `N - i`, both
    cursors sit at slot `i`, the first `i` slots agree, and the ambient is
    exactly buffer B. -/
def scanInv (ctr pA pB : Reg) (ptrA ptrB : Word) (bsA bsB : List (BitVec 8))
    (N : Nat) : Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ A =>
    rf.get ctr = BitVec.ofNat 64 (N - i) ∧
    rf.get pA = ptrA + BitVec.ofNat 64 (8 * i) ∧
    rf.get pB = ptrB + BitVec.ofNat 64 (8 * i) ∧
    i ≤ N ∧
    (∀ j, j < i → dwordSlot bsA j = dwordSlot bsB j) ∧
    A = bytesRegion ptrB bsB

/-- Focus relation for buffer B: the cursor `pB` sits at slot `i`, the
    focused window is the suffix from there, the remainder the prefix. -/
def scanFocus (pB : Reg) (ptrB : Word) (bsB : List (BitVec 8)) (N : Nat) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rest =>
    ∃ i, i < N ∧ rf.get pB = ptrB + BitVec.ofNat 64 (8 * i)
      ∧ rob = bsB.drop (8 * i) ∧ rest = bytesRegion ptrB (bsB.take (8 * i))

/-- The dual-read equality scan, register-agnostic.  Byte-for-byte the shape
    of the emitted `bnq_eq`/`blq_eq`:

    ```
          li   ctr, N
    hdr:  beq  ctr, x0, +eq_tail
          ld   tA, 0(pA)
          ld   tB, 0(pB)
          bne  tA, tB, +ne_tail
          addi pA, pA, 8
          addi pB, pB, 8
          addi ctr, ctr, -1
          jal  x0, hdr
    eq:   li   a0, 1 ; ret
    ne:   li   a0, 0 ; ret
    ``` -/
def scanBody (ctr tA tB pA pB : Reg) (ptrA ptrB : Word)
    (bsA bsB : List (BitVec 8)) (N : Nat) : Stmt :=
  .block "init" [.LI ctr (BitVec.ofNat 64 N)] ;;;
  .retWhileBreak "scan" (.bne ctr .x0) N (scanInv ctr pA pB ptrA ptrB bsA bsB N)
    (.block "ldA" [.LD tA pA (0 : BitVec 12)] ;;;
     .readAt "ldB" pB (scanFocus pB ptrB bsB N) [.LD tB pB (0 : BitVec 12)])
    (.bne tA tB)
    (.block "adv" [.ADDI pA pA (8 : BitVec 12), .ADDI pB pB (8 : BitVec 12),
      .ADDI ctr ctr (-1 : BitVec 12)])
    (.block "eq" [.LI .x10 (1 : Word)] ;;; .ret "ret_eq")
    (.block "ne" [.LI .x10 (0 : Word)] ;;; .ret "ret_ne")

/-- Entry: cursors at the buffer bases, both buffers `8·N` bytes, ambient =
    buffer B (buffer A is the primary read-only region). -/
def scanPre (pA pB : Reg) (ptrA ptrB : Word) (bsA bsB : List (BitVec 8))
    (N : Nat) : Reach :=
  fun rf _ A =>
    rf.get pA = ptrA ∧ rf.get pB = ptrB ∧
    bsA.length = 8 * N ∧ bsB.length = 8 * N ∧
    A = bytesRegion ptrB bsB

/-- Exit: the genuine equality verdict — `a0 = 1` iff the two byte lists are
    EQUAL (not per-slot residue), ambient restored. -/
def scanPost (ptrB : Word) (bsA bsB : List (BitVec 8)) : Reach :=
  fun rf _ A =>
    rf.get .x10 = (if bsA = bsB then (1 : Word) else (0 : Word)) ∧
    A = bytesRegion ptrB bsB

section Scan

-- Word-arithmetic helpers for the countdown counter and advancing cursors.

private theorem cursor_advance (p : Word) (i : Nat) (h : 8 * (i + 1) < 2 ^ 64) :
    p + BitVec.ofNat 64 (8 * i) + signExtend12 (8 : BitVec 12)
      = p + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  rw [show ((8 : Word)).toNat = 8 from rfl]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem counter_dec (N i : Nat) (hi : i < N) (hN : N < 2 ^ 64) :
    BitVec.ofNat 64 (N - i) + signExtend12 (-1 : BitVec 12)
      = BitVec.ofNat 64 (N - (i + 1)) := by
  have hsem : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  rw [hsem]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  rw [show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem lt_of_ctr_ne (N i : Nat) (hle : i ≤ N) (hN : N < 2 ^ 64)
    (h : BitVec.ofNat 64 (N - i) ≠ (0 : Word)) : i < N := by
  by_contra hge
  have hiN : i = N := by omega
  subst hiN
  simp at h

private theorem eq_of_ctr_zero (N i : Nat) (hle : i ≤ N) (hN : N < 2 ^ 64)
    (h : BitVec.ofNat 64 (N - i) = (0 : Word)) : i = N := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat] at this
  rw [show ((0 : Word)).toNat = 0 from rfl] at this
  omega

/-- The ambient split at cursor position `i`: buffer B is the focused suffix
    times the already-scanned prefix. -/
private theorem focus_split (ptrB : Word) (bsB : List (BitVec 8)) (i : Nat)
    (h : 8 * i ≤ bsB.length) :
    bytesRegion ptrB bsB
      = (bytesRegion (ptrB + BitVec.ofNat 64 (8 * i)) (bsB.drop (8 * i))
          ** bytesRegion ptrB (bsB.take (8 * i))) := by
  conv_lhs => rw [← List.take_append_drop (8 * i) bsB]
  rw [bytesRegion_append _ _ _ (by rw [List.length_take]; exact ⟨i, by omega⟩)]
  rw [List.length_take, Nat.min_eq_left h]
  exact sepConj_comm' _ _

/-- The dword an `LD` at immediate `0` reads from a focused region based at
    the cursor itself (`ofs` generic so the rewrite matches any encoding of
    the zero literal). -/
private theorem dwordAt_self (b : Word) (rob : List (BitVec 8)) (ofs : BitVec 12)
    (h0 : signExtend12 ofs = (0#64 : Word)) :
    Region.dwordAt ⟨b, rob⟩ (b + signExtend12 ofs)
      = packBytes (rob.take 8) := by
  unfold Region.dwordAt
  dsimp only
  have hb : b + (0#64 : Word) - b = (0#64 : Word) := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  rw [h0, hb]
  rw [show ((0#64 : Word)).toNat = 0 from rfl, List.drop_zero]

/-- Slot-`i` dword read through a zero-immediate cursor. -/
private theorem dwordAt_slot_ofs (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (ofs : BitVec 12) (h0 : signExtend12 ofs = (0#64 : Word))
    (hlt : 8 * i < 2 ^ 64) :
    Region.dwordAt ⟨base, bs⟩ (base + BitVec.ofNat 64 (8 * i) + signExtend12 ofs)
      = dwordSlot bs i := by
  rw [h0, show base + BitVec.ofNat 64 (8 * i) + (0#64 : Word)
    = base + BitVec.ofNat 64 (8 * i) from by simp]
  exact Region.dwordAt_slot base bs i hlt

/-- Slot-`i` load side condition through a zero-immediate cursor. -/
private theorem loadOk_slot_ofs (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (ofs : BitVec 12) (h0 : signExtend12 ofs = (0#64 : Word))
    (hfit : 8 * i + 8 ≤ bs.length) (hlen : bs.length < 2 ^ 64) :
    Region.loadOk ⟨base, bs⟩ (base + BitVec.ofNat 64 (8 * i) + signExtend12 ofs) 8 := by
  rw [h0, show base + BitVec.ofNat 64 (8 * i) + (0#64 : Word)
    = base + BitVec.ofNat 64 (8 * i) from by simp]
  exact Region.loadOk_slot base bs i hfit hlen

/-- Base-anchored load side condition (the focused second buffer). -/
private theorem loadOk_base_ofs (b : Word) (rob : List (BitVec 8))
    (ofs : BitVec 12) (h0 : signExtend12 ofs = (0#64 : Word))
    (hlen8 : 8 ≤ rob.length) :
    Region.loadOk ⟨b, rob⟩ (b + signExtend12 ofs) 8 := by
  unfold Region.loadOk
  dsimp only
  have hb : b + (0#64 : Word) - b = (0#64 : Word) := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  rw [h0, hb]
  rw [show ((0#64 : Word)).toNat = 0 from rfl]
  exact ⟨⟨0, rfl⟩, by omega⟩

section ScanProof

variable {ctr tA tB pA pB : Reg}
variable {ptrA ptrB : Word} {bsA bsB : List (BitVec 8)} {N : Nat}

private theorem scan_vcs
    (hEc : Reg.isExposed ctr = true) (hEtA : Reg.isExposed tA = true)
    (hEtB : Reg.isExposed tB = true) (hEpA : Reg.isExposed pA = true)
    (hEpB : Reg.isExposed pB = true)
    (hctA : ctr ≠ tA) (hctB : ctr ≠ tB) (hcpA : ctr ≠ pA) (hcpB : ctr ≠ pB)
    (htAtB : tA ≠ tB) (htApA : tA ≠ pA) (htApB : tA ≠ pB)
    (htBpA : tB ≠ pA) (htBpB : tB ≠ pB) (hpApB : pA ≠ pB)
    (hwfB : Region.wf ⟨ptrB, bsB⟩)
    (hlenA : bsA.length = 8 * N) (hlenB : bsB.length = 8 * N)
    (hNlt : 8 * N < 2 ^ 64) :
    VCs.Hold (Stmt.vcs (Region.mk ptrA bsA) RwRegion.empty
      (scanBody ctr tA tB pA pB ptrA ptrB bsA bsB N) "scan."
      (scanPre pA pB ptrA ptrB bsA bsB N)) := by
  have hcx0 : ctr ≠ .x0 := Reg.ne_x0_of_isExposed ctr hEc
  have htAx0 : tA ≠ .x0 := Reg.ne_x0_of_isExposed tA hEtA
  have htBx0 : tB ≠ .x0 := Reg.ne_x0_of_isExposed tB hEtB
  have hpAx0 : pA ≠ .x0 := Reg.ne_x0_of_isExposed pA hEpA
  have hpBx0 : pB ≠ .x0 := Reg.ne_x0_of_isExposed pB hEpB
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  intro vc hvc
  unfold scanBody at hvc
  simp [Stmt.vcs, Stmt.ret, hasLoad, blockOk, loadSem, storeSem] at hvc
  rcases hvc with hinitOk | hinvInit | hinvStep | hexhausted | hbeforeOk |
    hbeforeMem | hreadOk | hfocus | hreadMem | hafterOk | heqOk | hneOk
  · -- init.ok
    subst vc
    simp [blockOk, instrOk, aluSem, hEc]
  · -- scan.inv_init
    subst vc
    rintro rf ws A ⟨rf₀, ws₀, hws₀, ⟨hpA, hpB, _hlA, _hlB, hA⟩, hrf, hws⟩
    have hws0z : ws₀.length = 0 := by simpa [RwRegion.empty] using hws₀
    obtain rfl := List.eq_nil_of_length_eq_zero hws0z
    subst hrf
    subst hws
    unfold scanInv
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_, ?_, Nat.zero_le _, fun j hj => absurd hj (by omega), hA⟩
    · rw [RegFile.get_set_self _ _ _ hcx0]
      rfl
    · rw [RegFile.get_set_ne _ _ _ _ (Ne.symm hcpA), hpA]
      simp
    · rw [RegFile.get_set_ne _ _ _ _ (Ne.symm hcpB), hpB]
      simp
  · -- scan.inv_step
    subst vc
    rintro i hi rf' ws' A' hsp
    obtain ⟨rfa, wsa, hwsa, ⟨hload, hnbreak⟩, hrf', hws'⟩ := hsp
    obtain ⟨rf1, ws1, A1, robytes, rest, hlenRead, hsp1, _hsat, hro, hrfa,
      _hwsaEq, hAeq⟩ := hload
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, _hg⟩, hrf1, _hws1⟩ := hsp1
    change wsb.length = 0 at hwsb
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hws1len0 : ws1.length = 0 := by simpa [RwRegion.empty] using hlenRead
    obtain rfl := List.eq_nil_of_length_eq_zero hws1len0
    unfold scanInv at hinv
    obtain ⟨hctr, hpA, hpB, hile, hpref, _hA⟩ := hinv
    obtain ⟨i', hi'N, hpB', hrob, hrest⟩ := hro
    -- rf1 = state after `LD tA, 0(pA)`
    have hrf1ctr : rf1.get ctr = rfb.get ctr := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_ne _ _ _ _ hctA]
    have hrf1pA : rf1.get pA = rfb.get pA := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_ne _ _ _ _ (Ne.symm htApA)]
    have hrf1pB : rf1.get pB = rfb.get pB := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_ne _ _ _ _ (Ne.symm htApB)]
    have hrf1tA : rf1.get tA = dwordSlot bsA i := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_self _ _ _ htAx0, hpA]
      exact dwordAt_slot_ofs ptrA bsA i _ (by decide) (by omega)
    -- the focus index agrees with the invariant index
    have hii' : i' = i := by
      have hbase : ptrB + BitVec.ofNat 64 (8 * i') = ptrB + BitVec.ofNat 64 (8 * i) := by
        rw [← hpB']
        rw [hrf1pB, hpB]
      have hcanc := congrArg (fun w => w - ptrB) hbase
      simp only [BitVec.add_comm ptrB, BitVec.add_sub_cancel] at hcanc
      have := congrArg BitVec.toNat hcanc
      simp only [BitVec.toNat_ofNat] at this
      omega
    rw [hii'] at hpB' hrob hrest
    -- rfa = state after the focused `LD tB, 0(pB)`
    have hrfa_tB : rfa.get tB = dwordSlot bsB i := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_self _ _ _ htBx0, dwordAt_self _ _ _ (by decide), hrob]
      rfl
    have hrfa_tA : rfa.get tA = dwordSlot bsA i := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_ne _ _ _ _ htAtB]
      exact hrf1tA
    have hrfa_ctr : rfa.get ctr = rfb.get ctr := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_ne _ _ _ _ hctB]
      exact hrf1ctr
    have hrfa_pA : rfa.get pA = rfb.get pA := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_ne _ _ _ _ (Ne.symm htBpA)]
      exact hrf1pA
    have hrfa_pB : rfa.get pB = rfb.get pB := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_ne _ _ _ _ (Ne.symm htBpB)]
      exact hrf1pB
    -- the break did not fire: slot i agrees
    have heqslot : dwordSlot bsA i = dwordSlot bsB i := by
      have heq : rfa.get tA = rfa.get tB := not_ne_iff.mp hnbreak
      rw [hrfa_tA, hrfa_tB] at heq
      exact heq
    unfold scanInv
    refine ⟨?_, ?_, ?_, by omega, ?_, ?_⟩
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ hcx0,
        RegFile.get_set_ne _ _ _ _ hcpB,
        RegFile.get_set_ne _ _ _ _ hcpA, hrfa_ctr, hctr]
      exact counter_dec N i hi (by omega)
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (Ne.symm hcpA),
        RegFile.get_set_ne _ _ _ _ hpApB,
        RegFile.get_set_self _ _ _ hpAx0, hrfa_pA, hpA]
      exact cursor_advance ptrA i (by omega)
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (Ne.symm hcpB),
        RegFile.get_set_self _ _ _ hpBx0,
        RegFile.get_set_ne _ _ _ _ (Ne.symm hpApB), hrfa_pB, hpB]
      exact cursor_advance ptrB i (by omega)
    · intro j hj
      by_cases hji : j < i
      · exact hpref j hji
      · have hji' : j = i := by omega
        rw [hji']
        exact heqslot
    · rw [hAeq, hrf1pB, hpB, hrob, hrest]
      exact (focus_split ptrB bsB i (by omega)).symm
  · -- scan.exhausted
    subst vc
    rintro rf ws A hinv
    unfold scanInv at hinv
    obtain ⟨hctr, -, -, -, -, -⟩ := hinv
    intro hc
    apply hc
    show rf.get ctr = rf.get .x0
    rw [hctr, Nat.sub_self]
    rfl
  · -- before.ldA.ok
    subst vc
    simp [blockOk, instrOk, aluSem, loadSem, hEtA, hEpA]
  · -- before.ldA.mem
    subst vc
    rintro rf ws A hws i hi hinv _hg
    change ws.length = 0 at hws
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    unfold scanInv at hinv
    obtain ⟨-, hpA, -, -, -, -⟩ := hinv
    simp only [blockVCs, loadSem, storeSem]
    refine ⟨?_, trivial⟩
    rw [if_neg (by simp [inRw])]
    rw [hpA]
    exact loadOk_slot_ofs ptrA bsA i _ (by decide) (by omega) (by omega)
  · -- before.ldB.ok
    subst vc
    simp [blockOk, instrOk, aluSem, loadSem, hEtB, hEpB]
  · -- before.ldB.focus
    subst vc
    rintro rf ws A hsp _hApc hp hhp
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv, _hg⟩, hrf, _hws⟩ := hsp
    change ws₀.length = 0 at hws₀
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    unfold scanInv at hinv
    obtain ⟨-, -, hpB, -, -, hA⟩ := hinv
    have hpB' : rf.get pB = ptrB + BitVec.ofNat 64 (8 * i) := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_ne _ _ _ _ (Ne.symm htApB)]
      exact hpB
    refine ⟨bsB.drop (8 * i), bytesRegion ptrB (bsB.take (8 * i)),
      ⟨i, hi, hpB', rfl, rfl⟩, ?_, bytesRegion_pcFree _ _, ?_⟩
    · rw [hpB']
      rw [hA, focus_split ptrB bsB i (by omega)] at hhp
      exact hhp
    · rw [hpB']
      exact Region.wf_dropSuffix ptrB bsB (8 * i) hwfB (by omega) (by omega)
  · -- before.ldB.mem
    subst vc
    rintro rf ws A robytes rest hws hsp hro _hp _happ
    change ws.length = 0 at hws
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    obtain ⟨i', hi'N, hpB', hrob, -⟩ := hro
    refine ⟨?_, trivial⟩
    simp only [loadSem]
    rw [if_neg (by simp [inRw])]
    exact loadOk_base_ofs _ _ _ (by decide)
      (by rw [hrob]; simp only [List.length_drop]; omega)
  · -- after.ok
    subst vc
    simp [blockOk, instrOk, aluSem, hEpA, hEpB, hEc]
  · -- guardTail.ok
    subst vc
    decide
  · -- breakTail.ok
    subst vc
    decide

private theorem scan_sp_post
    (hEc : Reg.isExposed ctr = true) (hEtA : Reg.isExposed tA = true)
    (hEtB : Reg.isExposed tB = true) (hEpA : Reg.isExposed pA = true)
    (hEpB : Reg.isExposed pB = true)
    (hctA : ctr ≠ tA) (hctB : ctr ≠ tB) (hcpA : ctr ≠ pA) (hcpB : ctr ≠ pB)
    (htAtB : tA ≠ tB) (htApA : tA ≠ pA) (htApB : tA ≠ pB)
    (htBpA : tB ≠ pA) (htBpB : tB ≠ pB) (hpApB : pA ≠ pB)
    (hlenA : bsA.length = 8 * N) (hlenB : bsB.length = 8 * N)
    (hNlt : 8 * N < 2 ^ 64) :
    ∀ rf ws A,
      Stmt.sp (Region.mk ptrA bsA) RwRegion.empty
        (scanBody ctr tA tB pA pB ptrA ptrB bsA bsB N)
        (scanPre pA pB ptrA ptrB bsA bsB N) rf ws A →
      scanPost ptrB bsA bsB rf ws A := by
  have htAx0 : tA ≠ .x0 := Reg.ne_x0_of_isExposed tA hEtA
  have htBx0 : tB ≠ .x0 := Reg.ne_x0_of_isExposed tB hEtB
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  intro rf ws A hsp
  unfold scanBody at hsp
  simp only [Stmt.sp, Stmt.ret] at hsp
  rcases hsp with heq | hne
  · -- fell out of the loop: all N slots matched
    obtain ⟨rft, wst, hwst, hreach, hrf, _hws⟩ := heq
    obtain ⟨⟨i, hile, hinv⟩, hng⟩ := hreach
    unfold scanInv at hinv
    obtain ⟨hctr, -, -, hiN, hpref, hA⟩ := hinv
    have hiEq : i = N := by
      have hz : rft.get ctr = (0 : Word) := by
        by_contra hc
        exact hng (by
          show rft.get ctr ≠ rft.get .x0
          simpa using hc)
      rw [hctr] at hz
      exact eq_of_ctr_zero N i hiN (by omega) hz
    rw [hiEq] at hpref
    have hEq : bsA = bsB :=
      bytes_eq_of_dwordSlots_eq N bsA bsB hlenA hlenB
        (fun j hj => hpref j hj)
    unfold scanPost
    obtain rfl := List.eq_nil_of_length_eq_zero hwst
    refine ⟨?_, hA⟩
    rw [hrf]
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    rw [RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
    rw [if_pos hEq]
  · -- broke: slot i differs, so the lists differ
    obtain ⟨rft, wst, hwst, hreach, hrf, _hws⟩ := hne
    obtain ⟨⟨i, hi, hbb⟩, hbreak⟩ := hreach
    obtain ⟨rf1, ws1, A1, robytes, rest, hlenRead, hsp1, _hsat, hro, hrft,
      _hwstEq, hAeq⟩ := hbb
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, _hg⟩, hrf1, _hws1⟩ := hsp1
    change wsb.length = 0 at hwsb
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hws1len0 : ws1.length = 0 := by simpa [RwRegion.empty] using hlenRead
    obtain rfl := List.eq_nil_of_length_eq_zero hws1len0
    unfold scanInv at hinv
    obtain ⟨-, hpA, hpB, -, -, -⟩ := hinv
    obtain ⟨i', hi'N, hpB', hrob, hrest⟩ := hro
    have hrf1pB : rf1.get pB = rfb.get pB := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_ne _ _ _ _ (Ne.symm htApB)]
    have hrf1tA : rf1.get tA = dwordSlot bsA i := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_self _ _ _ htAx0, hpA]
      exact dwordAt_slot_ofs ptrA bsA i _ (by decide) (by omega)
    have hii' : i' = i := by
      have hbase : ptrB + BitVec.ofNat 64 (8 * i')
          = ptrB + BitVec.ofNat 64 (8 * i) := by
        rw [← hpB']
        rw [hrf1pB, hpB]
      have hcanc := congrArg (fun w => w - ptrB) hbase
      simp only [BitVec.add_comm ptrB, BitVec.add_sub_cancel] at hcanc
      have := congrArg BitVec.toNat hcanc
      simp only [BitVec.toNat_ofNat] at this
      omega
    rw [hii'] at hpB' hrob hrest
    have hrft_tB : rft.get tB = dwordSlot bsB i := by
      rw [hrft]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_self _ _ _ htBx0, dwordAt_self _ _ _ (by decide), hrob]
      rfl
    have hrft_tA : rft.get tA = dwordSlot bsA i := by
      rw [hrft]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
      rw [RegFile.get_set_ne _ _ _ _ htAtB]
      exact hrf1tA
    have hneslot : dwordSlot bsA i ≠ dwordSlot bsB i := by
      have hne' : rft.get tA ≠ rft.get tB := hbreak
      rw [hrft_tA, hrft_tB] at hne'
      exact hne'
    have hNe : bsA ≠ bsB := fun hEq => hneslot (dwordSlot_congr hEq i)
    unfold scanPost
    obtain rfl := List.eq_nil_of_length_eq_zero hwst
    refine ⟨?_, ?_⟩
    · rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
      rw [if_neg hNe]
    · rw [hAeq, hrf1pB, hpB, hrob, hrest]
      exact (focus_split ptrB bsB i (by omega)).symm

/-- **The dual-read dword equality scan, whole-routine.**  Register-agnostic:
    any five distinct exposed registers.  Genuine post: `a0 = 1` iff the two
    `8·N`-byte buffers are byte-equal. -/
theorem scan_spec (base ret : Word)
    (hEc : Reg.isExposed ctr = true) (hEtA : Reg.isExposed tA = true)
    (hEtB : Reg.isExposed tB = true) (hEpA : Reg.isExposed pA = true)
    (hEpB : Reg.isExposed pB = true)
    (hctA : ctr ≠ tA) (hctB : ctr ≠ tB) (hcpA : ctr ≠ pA) (hcpB : ctr ≠ pB)
    (htAtB : tA ≠ tB) (htApA : tA ≠ pA) (htApB : tA ≠ pB)
    (htBpA : tB ≠ pA) (htBpB : tB ≠ pB) (hpApB : pA ≠ pB)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hwfA : Region.wf ⟨ptrA, bsA⟩) (hwfB : Region.wf ⟨ptrB, bsB⟩)
    (hlenA : bsA.length = 8 * N) (hlenB : bsB.length = 8 * N) :
    cpsTripleWithin (scanBody ctr tA tB pA pB ptrA ptrB bsA bsB N).steps base ret
      (CodeReq.ofProg base
        ((scanBody ctr tA tB pA pB ptrA ptrB bsA bsB N).flatten base))
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM (Region.mk ptrA bsA) RwRegion.empty
        (scanPre pA pB ptrA ptrB bsA bsB N))
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM (Region.mk ptrA bsA) RwRegion.empty
        (scanPost ptrB bsA bsB)) := by
  have hNlt : 8 * N < 2 ^ 64 := by
    have h := hwfA
    unfold Region.wf at h
    dsimp only at h
    omega
  have hsound := Stmt.retSound (Region.mk ptrA bsA) RwRegion.empty
    (scanBody ctr tA tB pA pB ptrA ptrB bsA bsB N) base ret "scan."
    (scanPre pA pB ptrA ptrB bsA bsB N)
    hwfA RwRegion.empty_wf
    (by rfl)
    (by
      simp [scanBody, Stmt.ret, Stmt.retOffsetsOk, Stmt.offsetsOk, Cond.wf,
        Cond.regs, Stmt.size, hEc, hEtA, hEtB])
    (by
      rw [show (scanBody ctr tA tB pA pB ptrA ptrB bsA bsB N).size = 13 from rfl]
      norm_num)
    halign (fun _ _ h => h)
    (scan_vcs hEc hEtA hEtB hEpA hEpB hctA hctB hcpA hcpB htAtB htApA htApB
      htBpA htBpB hpApB hwfB hlenA hlenB hNlt)
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (sepConj_mono_right (asrtM_mono (scan_sp_post hEc hEtA hEtB hEpA hEpB
      hctA hctB hcpA hcpB htAtB htApA htApB htBpA htBpB hpApB
      hlenA hlenB hNlt)))
    hsound

#print axioms scan_spec

end ScanProof

end Scan

end DualReadScan

end EvmAsm.Rv64.SAsm
