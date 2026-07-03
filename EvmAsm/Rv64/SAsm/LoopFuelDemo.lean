/-
  EvmAsm.Rv64.SAsm.LoopFuelDemo

  End-to-end demos for data-dependent loop fuel and nested loops at guest
  shape (docs/sasm-design.md §3.10, bead evm-asm-4ch8f.5):

  1. `rlpSkipFn` — a loop whose iteration count is **loaded from the
     read-only region at runtime** (an RLP short-length-style byte).  The
     fuel is the static cap 256; the exit is the runtime compare of the
     counter register against the loaded limit register; the `exhausted`
     VC closes from `i ≤ n` (invariant) plus `n < 256` (the decoded
     value's width bound).

  2. `gridScanFn` — a **nested** loop (outer per-item over a ghost count
     `m`, inner per-byte over 4-byte items) whose inner invariant needs
     the outer index: the outer index lives in `x5`, and the inner
     `whileS` invariant pins `x5` to its **entry snapshot**, which the
     outer `inv_step` correlates with its quantified index after the
     inner loop's `sp` has forgotten everything else.

  3. `capScanFn` — the scaling demo: the count is a **u64 loaded from the
     input**, the fuel is a `Nat` parameter `cap`, and the theorem takes
     `n ≤ cap` as a precondition on the decoded input.  The proof is one
     and the same for `cap = 32`, `1024`, and `100000` (the VCs are O(1)
     in the fuel); the concrete instantiations pin that down.
-/

import EvmAsm.Rv64.SAsm.LoopFuel
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64
namespace SAsm
namespace LoopFuelDemo

open Stmt

-- ============================================================================
-- Demo 1: data-dependent iteration count loaded from the ro region
-- ============================================================================

/-- The count decoded from the input: its first byte (the shape of an RLP
    short length field). -/
def rlpLen (bs : List (BitVec 8)) : Nat := (bs.getD 0 0).toNat

/-- The loop invariant: index below the decoded count, counter/limit
    register ties, and the moving payload pointer. -/
def rlpSkipInv (inBase : Word) (bs : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ _ =>
    i ≤ rlpLen bs
    ∧ rf.get .x5 = BitVec.ofNat 64 i
    ∧ rf.get .x6 = (bs.getD 0 0).zeroExtend 64
    ∧ rf.get .x11 = inBase + 1 + BitVec.ofNat 64 i

/-- Walk an RLP-style payload: load the length byte at `a0`, then touch
    each payload byte, leaving `a1` one past the payload and `t0` the
    count.  The iteration count is runtime data; the fuel is the static
    cap 256 (every byte value is below it). -/
def rlpSkipFn (inBase : Word) (bs : List (BitVec 8)) : Fn where
  name := "rlpSkip"
  region := ⟨inBase, bs⟩
  pre := fun rf _ _ => rf.get .x10 = inBase
  post := fun rf _ _ =>
    rf.get .x11 = inBase + 1 + BitVec.ofNat 64 (rlpLen bs)
    ∧ rf.get .x5 = BitVec.ofNat 64 (rlpLen bs)
  body :=
    .block "len" [.LBU .x6 .x10 0, .LI .x5 0, .ADDI .x11 .x10 1] ;;;
    .«while» "walk" (.bltu .x5 .x6) 256 (rlpSkipInv inBase bs)
      (.block "step" [.LBU .x7 .x11 0, .ADDI .x11 .x11 1, .ADDI .x5 .x5 1])

theorem rlpSkipFn_spec (inBase : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk inBase bs).wf)
    (hfits : 1 + rlpLen bs ≤ bs.length) (base : Word) :
    (rlpSkipFn inBase bs).Spec base := by
  have hb : rlpLen bs < 256 := (bs.getD 0 0).isLt
  have haddr0 : ∀ v : Word,
      ((v + signExtend12 (0 : BitVec 12)) - inBase).toNat
        = (v - inBase).toNat := by
    intro v
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case rlpSkip.len.mem =>
    rintro rf ws A hws hx10
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial, trivial, trivial⟩
    show ((rf.get .x10 + signExtend12 (0 : BitVec 12)) - inBase).toNat + 1
      ≤ bs.length
    rw [haddr0, hx10, show (inBase - inBase).toNat = 0 from by bv_omega]
    simp only [rlpLen] at hfits
    omega
  case rlpSkip.walk.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, hx10, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
    refine ⟨Nat.zero_le _, ?_, ?_, ?_⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
      show ((rlpSkipFn inBase bs).region.byteAt _).zeroExtend 64 = _
      unfold Region.byteAt
      rw [show (rlpSkipFn inBase bs).region.bytes = bs from rfl,
        show (rlpSkipFn inBase bs).region.base = inBase from rfl,
        haddr0, hx10, show (inBase - inBase).toNat = 0 from by bv_omega]
    · rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hx10,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      bv_omega
  case rlpSkip.walk.inv_step =>
    rintro i hi rf' ws' A'
      ⟨rf₀, ws₀, hws₀, ⟨⟨hle, hx5, hx6, hx11⟩, hcond⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    have hin : i < rlpLen bs := by
      rw [Cond.holds_bltu_iff hx5 (by omega), hx6, toNat_zeroExtend_byte]
        at hcond
      exact hcond
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hx5,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
        ofNat_succ]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx6
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hx11,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      bv_omega
  case rlpSkip.walk.exhausted =>
    rintro rf ws A ⟨hle, -, -, -⟩ -
    omega
  case rlpSkip.walk.body.step.mem =>
    rintro rf ws A hws ⟨i, hi, ⟨hle, hx5, hx6, hx11⟩, hcond⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hin : i < rlpLen bs := by
      rw [Cond.holds_bltu_iff hx5 (by omega), hx6, toNat_zeroExtend_byte]
        at hcond
      exact hcond
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial, trivial, trivial⟩
    show ((rf.get .x11 + signExtend12 (0 : BitVec 12)) - inBase).toNat + 1
      ≤ bs.length
    rw [haddr0, hx11,
      show ((inBase + 1 + BitVec.ofNat 64 i) - inBase).toNat = 1 + i from by
        bv_omega]
    omega
  case rlpSkip.post =>
    rintro rf ws A ⟨⟨i, hile, hle, hx5, hx6, hx11⟩, hncond⟩
    have hx6n : (rf.get .x6).toNat = rlpLen bs := by
      rw [hx6, toNat_zeroExtend_byte]
      rfl
    obtain rfl : i = rlpLen bs :=
      index_eq_of_not_bltu hx5 hx6n hle (by omega) hncond
    exact ⟨hx11, hx5⟩

-- ============================================================================
-- Demo 2: nested loops — the inner invariant sees the outer index through
-- the entry snapshot of `whileS`
-- ============================================================================

/-- Outer invariant of the grid scan: `i` items consumed, counter/limit
    ties, the item-width constant in `t3`, and the scan pointer at the
    start of item `i`. -/
def gridInv (inBase : Word) (m : Nat) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ _ =>
    i ≤ m
    ∧ rf.get .x5 = BitVec.ofNat 64 i
    ∧ rf.get .x6 = BitVec.ofNat 64 m
    ∧ rf.get .x28 = 4
    ∧ rf.get .x11 = inBase + BitVec.ofNat 64 (4 * i)

/-- Inner invariant, parameterized by the inner loop's **entry snapshot**
    `rf₀`: the outer state (`x5`, `x6`, `x28`, and the row pointer) is
    pinned to its entry value — this is the fact that survives the inner
    loop and lets the outer `inv_step` re-establish its index ties.  The
    outer index itself is never named: it is `rf₀.get .x5`. -/
def gridInnerInv :
    RegFile → List (BitVec 8) → Assertion → Nat →
      RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf₀ _ _ j rf _ _ =>
    j ≤ 4
    ∧ rf.get .x7 = BitVec.ofNat 64 j
    ∧ rf.get .x5 = rf₀.get .x5
    ∧ rf.get .x6 = rf₀.get .x6
    ∧ rf.get .x28 = rf₀.get .x28
    ∧ rf.get .x11 = rf₀.get .x11 + BitVec.ofNat 64 j

/-- Scan `m` items of 4 bytes each (per-account → per-byte shape): the
    outer loop advances an item counter, the inner loop touches each byte
    of the item through a moving pointer.  Afterwards the pointer sits at
    the end of the grid. -/
def gridScanFn (inBase : Word) (bs : List (BitVec 8)) (m : Nat) : Fn where
  name := "gridScan"
  region := ⟨inBase, bs⟩
  pre := fun rf _ _ => rf.get .x10 = inBase ∧ rf.get .x6 = BitVec.ofNat 64 m
  post := fun rf _ _ => rf.get .x11 = inBase + BitVec.ofNat 64 (4 * m)
  body :=
    .block "oinit" [.LI .x5 0, .MV .x11 .x10, .LI .x28 4] ;;;
    .«while» "outer" (.bltu .x5 .x6) 1024 (gridInv inBase m)
      (.block "iinit" [.LI .x7 0] ;;;
       .«whileS» "inner" (.bltu .x7 .x28) 4 gridInnerInv
         (.block "istep" [.LBU .x29 .x11 0, .ADDI .x11 .x11 1,
           .ADDI .x7 .x7 1]) ;;;
       .block "onext" [.ADDI .x5 .x5 1])

theorem gridScanFn_spec (inBase : Word) (bs : List (BitVec 8)) (m : Nat)
    (hwf : (Region.mk inBase bs).wf) (hm : m ≤ 1024)
    (hlen : 4 * m ≤ bs.length) (base : Word) :
    (gridScanFn inBase bs m).Spec base := by
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case gridScan.outer.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, ⟨hx10, hx6m⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx6m
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hx10]
      bv_omega
  case gridScan.outer.body.inner.inv_init =>
    rintro rf ws A ⟨rf₁, ws₁, hws₁, -, rfl, rfl⟩
    refine ⟨Nat.zero_le _, ?_, rfl, rfl, rfl, ?_⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · bv_omega
  case gridScan.outer.body.inner.inv_step =>
    rintro rf₀ ws₀ A₀ - j hj rf' ws' A'
      ⟨rf₂, ws₂, hws₂, ⟨⟨hj4, hx7, hx5, hx6, hx28, hx11⟩, hcond⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₂
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hx7,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
        ofNat_succ]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx5
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx6
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx28
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hx11,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      bv_omega
  case gridScan.outer.body.inner.exhausted =>
    rintro rf₀ ws₀ A₀
      ⟨rf₁, ws₁, hws₁, ⟨i, hi, ⟨him, h5₁, h6₁, h28₁, h11₁⟩, hcond₁⟩, hrf₀, -⟩
      rf ws A ⟨-, hx7, -, -, hx28, -⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] at hrf₀
    have hx28v : rf.get .x28 = 4 := by
      rw [hx28, hrf₀, RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h28₁
    rw [Cond.holds, hx7, hx28v]
    decide
  case gridScan.outer.body.inner.body.istep.mem =>
    rintro rf ws A hws
      ⟨rf₀, ws₀, A₀,
        ⟨rf₁, ws₁, hws₁, ⟨i, hi, ⟨him, h5₁, h6₁, h28₁, h11₁⟩, hcond₁⟩, hrf₀, -⟩,
        j, hj, ⟨hj4, hx7, hx5, hx6, hx28, hx11⟩, hcond⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] at hrf₀
    have hin : i < m := by
      rw [Cond.holds_bltu_iff h5₁ (by omega), h6₁, toNat_ofNat_lt (by omega)]
        at hcond₁
      exact hcond₁
    have hx11v : rf.get .x11 = inBase + BitVec.ofNat 64 (4 * i)
        + BitVec.ofNat 64 j := by
      rw [hx11, hrf₀, RegFile.get_set_ne _ _ _ _ (by decide), h11₁]
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial, trivial, trivial⟩
    show ((rf.get .x11 + signExtend12 (0 : BitVec 12)) - inBase).toNat + 1
      ≤ bs.length
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, hx11v,
      show ((inBase + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 j + 0)
          - inBase).toNat = 4 * i + j from by bv_omega]
    omega
  case gridScan.outer.inv_step =>
    rintro i hi rf' ws' A'
      ⟨rf₃, ws₃, hws₃,
        ⟨rf₀, ws₀, A₀,
          ⟨rf₁, ws₁, hws₁, ⟨⟨him, h5₁, h6₁, h28₁, h11₁⟩, hcond₁⟩, hrf₀, -⟩,
          ⟨j, hjle, hj4, hx7₃, hx5₃, hx6₃, hx28₃, hx11₃⟩, hncond⟩,
        rfl, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] at hrf₀
    have hin : i < m := by
      rw [Cond.holds_bltu_iff h5₁ (by omega), h6₁, toNat_ofNat_lt (by omega)]
        at hcond₁
      exact hcond₁
    have hx28v : (rf₃.get .x28).toNat = 4 := by
      rw [hx28₃, hrf₀, RegFile.get_set_ne _ _ _ _ (by decide), h28₁]
      rfl
    obtain rfl : j = 4 :=
      index_eq_of_not_bltu hx7₃ hx28v hj4 (by omega) hncond
    have hx5v : rf₃.get .x5 = BitVec.ofNat 64 i := by
      rw [hx5₃, hrf₀, RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h5₁
    have hx11v : rf₃.get .x11 = inBase + BitVec.ofNat 64 (4 * i)
        + BitVec.ofNat 64 4 := by
      rw [hx11₃, hrf₀, RegFile.get_set_ne _ _ _ _ (by decide), h11₁]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · rw [RegFile.get_set_self _ _ _ (by decide), hx5v,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
        ofNat_succ]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      rw [hx6₃, hrf₀, RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h6₁
    · rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      rw [hx28₃, hrf₀, RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h28₁
    · rw [RegFile.get_set_ne _ _ _ _ (by decide), hx11v]
      bv_omega
  case gridScan.outer.exhausted =>
    rintro rf ws A ⟨him, hx5, hx6, -, -⟩
    have hme : m = 1024 := by omega
    rw [Cond.holds, hx5, hx6, hme]
    decide
  case gridScan.post =>
    rintro rf ws A ⟨⟨i, hile, him, hx5, hx6, -, hx11⟩, hncond⟩
    have hx6n : (rf.get .x6).toNat = m := by
      rw [hx6, toNat_ofNat_lt (by omega)]
    obtain rfl : i = m :=
      index_eq_of_not_bltu hx5 hx6n him (by omega) hncond
    exact hx11

-- ============================================================================
-- Demo 3 (scaling): u64 count from the input, fuel = a static cap
-- parameter; one proof for cap = 32 / 1024 / 100000
-- ============================================================================

/-- The u64 count decoded from the first 8 input bytes. -/
def capLenWord (bs : List (BitVec 8)) : Word := packBytes (bs.take 8)

/-- The count as a `Nat`. -/
def capLen (bs : List (BitVec 8)) : Nat := (capLenWord bs).toNat

/-- Invariant of the capped scan (independent of the cap: the cap enters
    only through the `exhausted` VC, via `capLen bs ≤ cap`). -/
def capScanInv (inBase : Word) (bs : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ _ =>
    i ≤ capLen bs
    ∧ rf.get .x5 = BitVec.ofNat 64 i
    ∧ rf.get .x6 = capLenWord bs
    ∧ rf.get .x11 = inBase + 8 + BitVec.ofNat 64 i

/-- Scan `n` items of one byte, where `n` is a u64 **loaded from the
    input at runtime** and `cap` is the static worst-case fuel (the BAL
    item-scan shape: `cap = 100000`).  The verified step budget is
    `O(cap)` and static; the loop exits after the runtime count. -/
def capScanFn (inBase : Word) (bs : List (BitVec 8)) (cap : Nat) : Fn where
  name := "capScan"
  region := ⟨inBase, bs⟩
  pre := fun rf _ _ => rf.get .x10 = inBase
  post := fun rf _ _ =>
    rf.get .x11 = inBase + 8 + BitVec.ofNat 64 (capLen bs)
    ∧ rf.get .x5 = BitVec.ofNat 64 (capLen bs)
  body :=
    .block "len" [.LD .x6 .x10 0, .LI .x5 0, .ADDI .x11 .x10 8] ;;;
    .«while» "walk" (.bltu .x5 .x6) cap (capScanInv inBase bs)
      (.block "step" [.LBU .x7 .x11 0, .ADDI .x11 .x11 1, .ADDI .x5 .x5 1])

/-- The one proof, generic in the cap.  `hcap` is the precondition on the
    decoded input that the `exhausted` VC consumes; nothing else in the
    proof mentions `cap`. -/
theorem capScanFn_spec (inBase : Word) (bs : List (BitVec 8)) (cap : Nat)
    (hwf : (Region.mk inBase bs).wf)
    (hcap : capLen bs ≤ cap)
    (hfits : 8 + capLen bs ≤ bs.length) (base : Word) :
    (capScanFn inBase bs cap).Spec base := by
  have hn64 : capLen bs < 2 ^ 64 := (capLenWord bs).isLt
  have hbslen : bs.length < 2 ^ 64 := by
    have h : inBase.toNat + bs.length < 2 ^ 64 := hwf.2.1
    omega
  have haddr0 : ∀ v : Word,
      ((v + signExtend12 (0 : BitVec 12)) - inBase).toNat
        = (v - inBase).toNat := by
    intro v
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case capScan.len.mem =>
    rintro rf ws A hws hx10
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    simp only [blockVCs, loadSem]
    refine ⟨⟨?_, ?_⟩, trivial, trivial, trivial⟩
    · show (8 : Nat) ∣ ((rf.get .x10 + signExtend12 (0 : BitVec 12))
        - inBase).toNat
      rw [haddr0, hx10, show (inBase - inBase).toNat = 0 from by bv_omega]
      exact dvd_zero 8
    · show ((rf.get .x10 + signExtend12 (0 : BitVec 12)) - inBase).toNat + 8
        ≤ bs.length
      rw [haddr0, hx10, show (inBase - inBase).toNat = 0 from by bv_omega]
      omega
  case capScan.walk.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, hx10, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
    refine ⟨Nat.zero_le _, ?_, ?_, ?_⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
      show (capScanFn inBase bs cap).region.dwordAt _ = _
      unfold Region.dwordAt
      rw [show (capScanFn inBase bs cap).region.bytes = bs from rfl,
        show (capScanFn inBase bs cap).region.base = inBase from rfl,
        haddr0, hx10, show (inBase - inBase).toNat = 0 from by bv_omega,
        List.drop_zero]
      rfl
    · rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hx10,
        show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
  case capScan.walk.inv_step =>
    rintro i hi rf' ws' A'
      ⟨rf₀, ws₀, hws₀, ⟨⟨hle, hx5, hx6, hx11⟩, hcond⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    have hin : i < capLen bs := by
      rw [Cond.holds_bltu_iff hx5 (by omega), hx6] at hcond
      exact hcond
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hx5,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
        ofNat_succ]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx6
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hx11,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      bv_omega
  case capScan.walk.exhausted =>
    rintro rf ws A ⟨hle, hx5, hx6, -⟩
    rw [Cond.holds_bltu_iff hx5 (by omega), hx6]
    show ¬ cap < capLen bs
    omega
  case capScan.walk.body.step.mem =>
    rintro rf ws A hws ⟨i, hi, ⟨hle, hx5, hx6, hx11⟩, hcond⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hin : i < capLen bs := by
      rw [Cond.holds_bltu_iff hx5 (by omega), hx6] at hcond
      exact hcond
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial, trivial, trivial⟩
    show ((rf.get .x11 + signExtend12 (0 : BitVec 12)) - inBase).toNat + 1
      ≤ bs.length
    rw [haddr0, hx11,
      show ((inBase + 8 + BitVec.ofNat 64 i) - inBase).toNat = 8 + i from by
        bv_omega]
    omega
  case capScan.post =>
    rintro rf ws A ⟨⟨i, hile, hle, hx5, hx6, hx11⟩, hncond⟩
    obtain rfl : i = capLen bs :=
      index_eq_of_not_bltu hx5 (by rw [hx6]; rfl) hle (by omega) hncond
    exact ⟨hx11, hx5⟩

/-- Scaling instantiations: the same proof term serves any cap — the VC
    count and every VC's size are O(1) in the fuel.  Elaboration-time
    measurements for the monomorphized variants (the full `vcgen` proof
    re-run at each literal) are in docs/sasm-design.md §3.10. -/
theorem capScanFn_spec_32 (inBase : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk inBase bs).wf) (hcap : capLen bs ≤ 32)
    (hfits : 8 + capLen bs ≤ bs.length) (base : Word) :
    (capScanFn inBase bs 32).Spec base :=
  capScanFn_spec inBase bs 32 hwf hcap hfits base

theorem capScanFn_spec_1024 (inBase : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk inBase bs).wf) (hcap : capLen bs ≤ 1024)
    (hfits : 8 + capLen bs ≤ bs.length) (base : Word) :
    (capScanFn inBase bs 1024).Spec base :=
  capScanFn_spec inBase bs 1024 hwf hcap hfits base

theorem capScanFn_spec_100000 (inBase : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk inBase bs).wf) (hcap : capLen bs ≤ 100000)
    (hfits : 8 + capLen bs ≤ bs.length) (base : Word) :
    (capScanFn inBase bs 100000).Spec base :=
  capScanFn_spec inBase bs 100000 hwf hcap hfits base

end LoopFuelDemo
end SAsm
end EvmAsm.Rv64
