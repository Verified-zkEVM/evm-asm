/-
  EvmAsm.Rv64.SAsm.BytesRegionWindow

  Shared arena/window framing for byte writers whose logical output starts at
  an arbitrary byte offset.  `bytesRegion` owns dwords, so an unaligned
  logical window owns the complete dword envelope containing it; the bytes
  before and after the logical window in the first/last dword are retained in
  the envelope and are therefore preserved by byte stores.

  This is deliberately separate from `RwSubwindow`: that module requires both
  cut points to be dword aligned.  RLP encoders write with SB and can validly
  start at offsets such as 33, so the shared contract must not pretend that
  the logical pointer is aligned merely because its enclosing arena is.
-/

import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SAsm.RwSubwindow

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

/-! ## Envelope arithmetic -/

/-- The first dword boundary at or before a byte offset. -/
def windowDwordStart (off : Nat) : Nat := 8 * (off / 8)

/-- Number of bytes in the dword envelope containing `[off, off + len)`. -/
def windowDwordLen (off len : Nat) : Nat :=
  8 * ((off % 8 + len + 7) / 8)

/-- End of the dword envelope. -/
def windowDwordEnd (off len : Nat) : Nat :=
  windowDwordStart off + windowDwordLen off len

theorem windowDwordStart_le (off : Nat) : windowDwordStart off ≤ off := by
  unfold windowDwordStart
  omega

theorem windowDwordStart_mod8 (off : Nat) : windowDwordStart off % 8 = 0 := by
  unfold windowDwordStart
  omega

theorem windowDwordLen_mod8 (off len : Nat) : windowDwordLen off len % 8 = 0 := by
  unfold windowDwordLen
  omega

theorem windowDwordEnd_eq (off len : Nat) :
    windowDwordEnd off len =
      8 * ((off % 8 + len + 7) / 8 + off / 8) := by
  unfold windowDwordEnd windowDwordStart windowDwordLen
  omega

theorem windowDwordEnd_ge (off len : Nat) :
    off + len ≤ windowDwordEnd off len := by
  unfold windowDwordEnd windowDwordStart windowDwordLen
  have hdecomp : off = 8 * (off / 8) + off % 8 :=
    (Nat.div_add_mod off 8).symm
  have hceil : off % 8 + len ≤ 8 * ((off % 8 + len + 7) / 8) := by
    omega
  omega

theorem windowDwordStart_le_end (off len : Nat) :
    windowDwordStart off ≤ windowDwordEnd off len := by
  unfold windowDwordEnd windowDwordLen
  omega

theorem windowDwordStart_lt_end (off len : Nat) (hlen : 0 < len) :
    windowDwordStart off < windowDwordEnd off len := by
  unfold windowDwordEnd windowDwordLen
  omega

theorem windowDword_envelope_length {ws : List (BitVec 8)} {off len : Nat}
    (hfit : windowDwordEnd off len ≤ ws.length) :
    ((ws.drop (windowDwordStart off)).take (windowDwordLen off len)).length =
      windowDwordLen off len := by
  simp only [List.length_take, List.length_drop]
  apply Nat.min_eq_left
  unfold windowDwordEnd at hfit
  omega

theorem windowDword_base_aligned {B : Word} {off len : Nat}
    (hB : B.toNat % 8 = 0)
    (haddr : B.toNat + windowDwordEnd off len < 2 ^ 64) :
    (B + BitVec.ofNat 64 (windowDwordStart off)).toNat % 8 = 0 := by
  have hs : windowDwordStart off < 2 ^ 64 := by
    have he := windowDwordStart_le_end off len
    omega
  have hsum : B.toNat + windowDwordStart off < 2 ^ 64 := by
    have he := windowDwordStart_le_end off len
    omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hsum]
  rw [Nat.add_mod, hB, windowDwordStart_mod8]

theorem windowDword_addr_add {B : Word} {a b : Nat}
    (hB : B.toNat + a + b < 2 ^ 64) :
    (B + BitVec.ofNat 64 a) + BitVec.ofNat 64 b =
      B + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have ha : a < 2 ^ 64 := by omega
  have hb : b < 2 ^ 64 := by omega
  have hab : a + b < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hab]

/-! ## Window assertions -/

/-- The dword envelope owned by an arbitrary byte-offset window.  The base of
    the resulting `bytesRegion` is aligned even when `B + off` is not. -/
def bytesRegionWindow (B : Word) (ws : List (BitVec 8)) (off len : Nat) : Assertion :=
  bytesRegion
    (B + BitVec.ofNat 64 (windowDwordStart off))
    ((ws.drop (windowDwordStart off)).take (windowDwordLen off len))

/-- The arena outside the dword envelope. -/
def windowRestAny (B : Word) (ws : List (BitVec 8)) (off len : Nat) : Assertion :=
  bytesRegion B (ws.take (windowDwordStart off)) **
    bytesRegion (B + BitVec.ofNat 64 (windowDwordEnd off len))
      (ws.drop (windowDwordEnd off len))

theorem pcFree_bytesRegionWindow (B : Word) (ws : List (BitVec 8))
    (off len : Nat) : (bytesRegionWindow B ws off len).pcFree := by
  exact bytesRegion_pcFree _ _

theorem pcFree_windowRestAny (B : Word) (ws : List (BitVec 8))
    (off len : Nat) : (windowRestAny B ws off len).pcFree := by
  exact pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _)

/-- Focus an arbitrary logical window out of an aligned arena.  The focused
    resource is the complete dword envelope, not the unaligned logical slice;
    this is what makes it separable from the prefix and suffix. -/
theorem bytesRegion_window_focus_any (B : Word) (ws : List (BitVec 8))
    (off len : Nat) (hfit : windowDwordEnd off len ≤ ws.length)
    :
    bytesRegion B ws =
      (bytesRegionWindow B ws off len ** windowRestAny B ws off len) := by
  have hfocus := bytesRegion_window_focus B ws (windowDwordStart off)
    (windowDwordLen off len) hfit (windowDwordStart_mod8 off)
    (windowDwordLen_mod8 off len)
  unfold bytesRegionWindow windowRestAny
  rw [hfocus]
  rfl

/-- Reassemble an arena after replacing an arbitrary-offset window envelope.
    `win'` has the envelope length, so the framed prefix/suffix remain the
    same resources and the replacement is represented by `setBytes`. -/
theorem bytesRegion_window_update_any (B : Word) (ws win' : List (BitVec 8))
    (off len : Nat) (hfit : windowDwordEnd off len ≤ ws.length)
    (hwlen : win'.length = windowDwordLen off len) :
    bytesRegion B (setBytes ws (windowDwordStart off) win') =
      (bytesRegionWindow B (setBytes ws (windowDwordStart off) win') off len **
        windowRestAny B ws off len) := by
  have hsetlen : (setBytes ws (windowDwordStart off) win').length = ws.length :=
    length_setBytes _ _ _
  have hfocus := bytesRegion_window_focus B (setBytes ws (windowDwordStart off) win')
    (windowDwordStart off) (windowDwordLen off len)
    (by rw [hsetlen]; exact hfit) (windowDwordStart_mod8 off)
    (windowDwordLen_mod8 off len)
  unfold windowRest at hfocus
  unfold bytesRegionWindow windowRestAny
  rw [hfocus]
  unfold windowDwordEnd
  rw [setBytes_take_of_ge win' ws (windowDwordStart off) (windowDwordStart off)
      (Nat.le_refl _),
    setBytes_drop_of_le win' ws (windowDwordStart off)
      (windowDwordStart off + windowDwordLen off len) (by omega)]

/-! ## Offset-zero compatibility -/

theorem bytesRegionWindow_zero (B : Word) (ws : List (BitVec 8)) (len : Nat) :
    bytesRegionWindow B ws 0 len = bytesRegion B (ws.take (8 * ((len + 7) / 8))) := by
  unfold bytesRegionWindow windowDwordStart windowDwordLen
  simp

/-! ## Byte access adapters

These adapters deliberately expose the arithmetic obligations instead of
silently assuming them. Concrete users discharge the index/address facts from
their layout; the adapter then lifts the existing aligned-envelope byte lemma
to an unaligned logical pointer. -/

theorem bytesRegionWindow_lbu_within_of_index
    (rd rs1 : Reg) (B vOld base : Word) (ws : List (BitVec 8))
    (off len k : Nat) (hrd : rd ≠ .x0)
    (hbase_align :
      (B + BitVec.ofNat 64 (windowDwordStart off)).toNat % 8 = 0)
    (hidx : k <
      ((ws.drop (windowDwordStart off)).take (windowDwordLen off len)).length)
    (hptr :
      (B + BitVec.ofNat 64 (windowDwordStart off)) + BitVec.ofNat 64 k =
        B + BitVec.ofNat 64 off)
    (hvalid : isValidByteAccess (B + BitVec.ofNat 64 off) = true)
    (hoff : off < ws.length)
    (hover :
      (B + BitVec.ofNat 64 (windowDwordStart off)).toNat + k < 2 ^ 64)
    (hbyte :
      ((ws.drop (windowDwordStart off)).take (windowDwordLen off len))[k]'hidx =
        ws[off]'hoff) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU rd rs1 0))
      ((rs1 ↦ᵣ (B + BitVec.ofNat 64 off)) ** (rd ↦ᵣ vOld) **
        bytesRegionWindow B ws off len)
      ((rs1 ↦ᵣ (B + BitVec.ofNat 64 off)) **
        (rd ↦ᵣ ((ws[off]'hoff).zeroExtend 64)) **
        bytesRegionWindow B ws off len) := by
  have hvalid' : isValidByteAccess
      ((B + BitVec.ofNat 64 (windowDwordStart off)) + BitVec.ofNat 64 k) = true := by
    rw [hptr]
    exact hvalid
  have hreg := bytesRegion_lbu_within rd rs1
    (B + BitVec.ofNat 64 (windowDwordStart off)) vOld base
    ((ws.drop (windowDwordStart off)).take (windowDwordLen off len)) k hrd
    hbase_align hidx hover hvalid'
  rw [hptr, hbyte] at hreg
  exact hreg

theorem bytesRegionWindow_sb_within_of_index
    (rs1 rs2 : Reg) (B vData base : Word) (ws : List (BitVec 8))
    (off len k : Nat)
    (hbase_align :
      (B + BitVec.ofNat 64 (windowDwordStart off)).toNat % 8 = 0)
    (hidx : k <
      ((ws.drop (windowDwordStart off)).take (windowDwordLen off len)).length)
    (hptr :
      (B + BitVec.ofNat 64 (windowDwordStart off)) + BitVec.ofNat 64 k =
        B + BitVec.ofNat 64 off)
    (hvalid : isValidByteAccess (B + BitVec.ofNat 64 off) = true)
    (hover :
      (B + BitVec.ofNat 64 (windowDwordStart off)).toNat + k < 2 ^ 64)
    (hset :
      ((ws.drop (windowDwordStart off)).take (windowDwordLen off len)).set k
          (vData.truncate 8) =
        ((setBytes ws off [vData.truncate 8]).drop (windowDwordStart off)).take
          (windowDwordLen off len)) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SB rs1 rs2 0))
      ((rs1 ↦ᵣ (B + BitVec.ofNat 64 off)) ** (rs2 ↦ᵣ vData) **
        bytesRegionWindow B ws off len)
      ((rs1 ↦ᵣ (B + BitVec.ofNat 64 off)) ** (rs2 ↦ᵣ vData) **
        bytesRegionWindow B (setBytes ws off [vData.truncate 8]) off len) := by
  have hvalid' : isValidByteAccess
      ((B + BitVec.ofNat 64 (windowDwordStart off)) + BitVec.ofNat 64 k) = true := by
    rw [hptr]
    exact hvalid
  have hreg := bytesRegion_sb_within rs1 rs2
    (B + BitVec.ofNat 64 (windowDwordStart off)) vData base
    ((ws.drop (windowDwordStart off)).take (windowDwordLen off len)) k
    hbase_align hidx hover hvalid'
  rw [hptr, hset] at hreg
  simpa [bytesRegionWindow] using hreg

/-! ## Whole-call framing -/

/-- Lift a callee triple whose writable footprint is an arbitrary-offset dword
    envelope to the enclosing arena.  `win'` is the replacement envelope, so
    the logical output pointer may be unaligned while ownership remains
    separable at dword granularity. -/
theorem cpsTripleWithin_rwWindow_any
    {nS : Nat} {e x : Word} {cr : CodeReq}
    {P Q : Assertion} (B : Word) (ws win' : List (BitVec 8))
    (off len : Nat) (hfit : windowDwordEnd off len ≤ ws.length)
    (hwlen : win'.length = windowDwordLen off len)
    (h : cpsTripleWithin nS e x cr
      (P ** bytesRegionWindow B ws off len)
      (Q ** bytesRegionWindow B (setBytes ws (windowDwordStart off) win') off len)) :
    cpsTripleWithin nS e x cr
      (P ** bytesRegion B ws)
      (Q ** bytesRegion B (setBytes ws (windowDwordStart off) win')) := by
  have hF := cpsTripleWithin_frameR (windowRestAny B ws off len)
    (pcFree_windowRestAny B ws off len) h
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hF
  · rw [bytesRegion_window_focus_any B ws off len hfit] at hp
    xperm_hyp hp
  · rw [bytesRegion_window_update_any B ws win' off len hfit hwlen]
    xperm_hyp hq

/-
/-! ## Byte accesses through an arbitrary window -/

theorem window_index_fits {ws : List (BitVec 8)} {off len i : Nat}
    (hfit : windowDwordEnd off len ≤ ws.length) (hi : i < len) :
    off + i < ws.length ∧
      off + i - windowDwordStart off < windowDwordLen off len := by
  have hend := windowDwordEnd_ge off len (by omega)
  unfold windowDwordEnd windowDwordStart windowDwordLen at hend hfit ⊢
  constructor <;> omega

theorem window_getElem {ws : List (BitVec 8)} {off len i : Nat}
    (hfit : windowDwordEnd off len ≤ ws.length) (hi : i < len) :
    ((ws.drop (windowDwordStart off)).take (windowDwordLen off len))[
        off + i - windowDwordStart off]'(by
          have := window_index_fits hfit hi
          exact (windowDword_envelope_length hfit).symm ▸ this.2) =
      ws[off + i]'(window_index_fits hfit hi).1 := by
  simp only [List.getElem_take, List.getElem_drop]
  congr 1
  omega

theorem window_base_byte_addr {B : Word} {off len i : Nat}
    (haddr : B.toNat + windowDwordEnd off len < 2 ^ 64)
    (hi : i < len) :
    (B + BitVec.ofNat 64 (windowDwordStart off)) +
        BitVec.ofNat 64 (off + i - windowDwordStart off) =
      B + BitVec.ofNat 64 (off + i) := by
  have hend := windowDwordEnd_ge off len (by omega)
  have hsum : B.toNat + windowDwordStart off +
      (off + i - windowDwordStart off) < 2 ^ 64 := by
    unfold windowDwordEnd windowDwordStart windowDwordLen at hend haddr ⊢
    omega
  unfold windowDwordStart at hsum ⊢
  rw [windowDword_addr_add hsum]
  congr 1
  omega

theorem bytesRegionWindow_lbu_within (rd rs1 : Reg) (B vOld base : Word)
    (ws : List (BitVec 8)) (off len i : Nat) (hrd : rd ≠ .x0)
    (hfit : windowDwordEnd off len ≤ ws.length)
    (hB : B.toNat % 8 = 0)
    (haddr : B.toNat + windowDwordEnd off len < 2 ^ 64)
    (hi : i < len)
    (hvalid : isValidByteAccess (B + BitVec.ofNat 64 (off + i)) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU rd rs1 0))
      ((rs1 ↦ᵣ (B + BitVec.ofNat 64 (off + i))) ** (rd ↦ᵣ vOld) **
        bytesRegionWindow B ws off len)
      ((rs1 ↦ᵣ (B + BitVec.ofNat 64 (off + i))) **
        (rd ↦ᵣ ((ws[off + i]'(window_index_fits hfit hi).1).zeroExtend 64)) **
        bytesRegionWindow B ws off len) := by
  let start := windowDwordStart off
  let envLen := windowDwordLen off len
  have hidx := window_index_fits hfit hi
  have hbase_align :
      (B + BitVec.ofNat 64 start).toNat % 8 = 0 :=
    windowDword_base_aligned hB haddr
  have hptr := window_base_byte_addr haddr hi
  have hvalid' : isValidByteAccess
      ((B + BitVec.ofNat 64 start) +
        BitVec.ofNat 64 (off + i - start)) = true := by
    rw [hptr]
    exact hvalid
  have hreg := bytesRegion_lbu_within rd rs1
    (B + BitVec.ofNat 64 start) vOld base
    ((ws.drop start).take envLen) (off + i - start) hrd hbase_align
    (by
      rw [windowDword_envelope_length hfit]
      exact hidx.2)
    (by
      have hend := windowDwordEnd_ge off len (by omega)
      unfold windowDwordEnd at haddr
      dsimp [start]
      omega)
    hvalid'
  rw [hptr] at hreg
  rw [window_getElem hfit hi] at hreg
  exact hreg

theorem bytesRegionWindow_sb_within (rs1 rs2 : Reg) (B vData base : Word)
    (ws : List (BitVec 8)) (off len i : Nat)
    (hfit : windowDwordEnd off len ≤ ws.length)
    (hB : B.toNat % 8 = 0)
    (haddr : B.toNat + windowDwordEnd off len < 2 ^ 64)
    (hi : i < len)
    (hvalid : isValidByteAccess (B + BitVec.ofNat 64 (off + i)) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SB rs1 rs2 0))
      ((rs1 ↦ᵣ (B + BitVec.ofNat 64 (off + i))) ** (rs2 ↦ᵣ vData) **
        bytesRegionWindow B ws off len)
      ((rs1 ↦ᵣ (B + BitVec.ofNat 64 (off + i))) ** (rs2 ↦ᵣ vData) **
        bytesRegionWindow B (setBytes ws (off + i) [vData.truncate 8]) off len) := by
  let start := windowDwordStart off
  let envLen := windowDwordLen off len
  have hidx := window_index_fits hfit hi
  have hbase_align :
      (B + BitVec.ofNat 64 start).toNat % 8 = 0 :=
    windowDword_base_aligned hB haddr
  have hptr := window_base_byte_addr haddr hi
  have hvalid' : isValidByteAccess
      ((B + BitVec.ofNat 64 start) +
        BitVec.ofNat 64 (off + i - start)) = true := by
    rw [hptr]
    exact hvalid
  have hreg := bytesRegion_sb_within rs1 rs2
    (B + BitVec.ofNat 64 start) vData base
    ((ws.drop start).take envLen) (off + i - start) hbase_align
    (by
      rw [windowDword_envelope_length hfit]
      exact hidx.2)
    (by
      have hend := windowDwordEnd_ge off len (by omega)
      unfold windowDwordEnd at haddr
      dsimp [start]
      omega)
    hvalid'
  rw [hptr] at hreg
  have hset :
      ((ws.drop start).take envLen).set (off + i - start) (vData.truncate 8) =
        ((setBytes ws (off + i) [vData.truncate 8]).drop start).take envLen := by
    have hsingle : setBytes ws (off + i) [vData.truncate 8] =
        ws.set (off + i) (vData.truncate 8) := by rfl
    rw [hsingle]
    apply List.ext_getElem
    · simp only [List.length_set, List.length_take, List.length_drop]
      exact (windowDword_envelope_length hfit).symm
    intro k hk1 hk2
    simp only [List.getElem_take, List.getElem_drop]
    rw [List.getElem_set]
    by_cases hk : k = off + i - start
    · simp [hk]
    · simp only [if_neg hk]
      rw [List.getElem_set]
      simp only [if_neg]
      omega
  rw [hset] at hreg
  exact hreg
 -/

end EvmAsm.Rv64.SAsm
