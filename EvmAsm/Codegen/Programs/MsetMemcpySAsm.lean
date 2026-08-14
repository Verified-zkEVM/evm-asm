/-
  EvmAsm.Codegen.Programs.MsetMemcpySAsm

  Verified SAsm port of `mset_memcpy` (bead evm-asm-4ch8f.12.1, byte-tie
  follow-up .12.10): copy `len` bytes forward from `src` (a1) to `dst` (a0).

  `msetMemcpy_prog` (MptSet.lean) has the **same loop body and register roles**
  as `sg_memcpy` (x10=dst, x11=src, x12=len; `LBU x5,(x11); SB (x10),x5;
  x10++; x11++; x12--`) and the same net effect `dst = src[0..len)`.

  Unlike a structured top-tested `.«while»` (guard, body, `JAL` back to guard),
  `mset_memcpy` is a **pre-guarded single do-while**: a top `BEQ x12,x0` that
  runs once as the entry guard, then the body, then a bottom `BNE x12,x0`
  back-edge to the body, then a separate `ret`.  This is exactly the shape
  `Stmt.doWhile` (#9818) models — the bottom-test sibling of `«while»` whose
  back-edge *is* the guard branch (no `JAL`).  Wrapping it in `Stmt.when`
  reconstructs the entry `BEQ` skip-the-whole-loop guard.

  This module therefore reuses the verified generic core of
  `EvmAsm.Codegen.SgMemcpySAsm` (`copyWin`/`copyByte`/`copyStepRf`/
  `copy_step_engine`/`sgMemcpyInv`/`sgMemcpyStepBlock`, `dst = src.take len`,
  src/dst-disjoint precondition) and only re-points the loop *shape* at
  `when`+`doWhile`.

  **Byte-identity**: claimed.  The structured `when`+`doWhile` flatten is
  pinned byte-for-byte against the emitted `msetMemcpy_prog` (the load-bearing
  tie — the proof is about the real emitted routine).  This closes the `.12.10`
  byte-tie gap for `mset_memcpy`.  Spec-only module (no emitted-code change) —
  no EEST A/B.
-/

import EvmAsm.Codegen.Programs.SgMemcpySAsm
import EvmAsm.Codegen.Programs.MptSet

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace MsetMemcpySAsm

open SgMemcpySAsm

/-- `doWhile` invariant: `inv i` holds immediately after the (i+1)-th body
    run, i.e. with `i+1` bytes copied — the `sg_memcpy` invariant indexed at
    `i+1`.  `doWhile` always runs the body once before the first guard test, so
    its `inv 0` is the post-first-iteration state (1 byte copied). -/
def msetDoWhileInv (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i => sgMemcpyInv src dst len bs orig (i + 1)

/-- `mset_memcpy` as a structured `when`+`doWhile`.  The `when` reconstructs
    the entry `BEQ x12,x0 → ret` skip guard; the `doWhile` is the bottom-test
    `BNE x12,x0` back-edge.  `fuel = len`: the body runs once via `inv_init`
    then up to `len-1` real step transitions (the final `inv_step` for
    `i = len-1` is vacuous — its `inv (len-1) ∧ guard` antecedent is
    unsatisfiable, since `inv (len-1)` already forces `x12 = 0`); when
    `len = 0` the `when` guard skips the whole loop. -/
def msetDoWhileBody (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) : Stmt :=
  .when "guard" (.bne .x12 .x0)
    (.doWhile "loop" (.bne .x12 .x0) len (msetDoWhileInv src dst len bs orig)
      (.block "copy" sgMemcpyStepBlock))

/-- `mset_memcpy` as a verified SAsm `Fn`: same pre/post as the `sg_memcpy`
    core (same body, registers, net effect), now byte-tied to the emitted
    routine via `when`+`doWhile`. -/
def msetMemcpyFn (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) : Fn where
  name := "msetMemcpy"
  region := ⟨src, bs⟩
  rw := ⟨dst, len⟩
  pre := fun rf ws _ =>
    rf.get .x10 = dst ∧ rf.get .x11 = src ∧ rf.get .x12 = BitVec.ofNat 64 len ∧
    ws = orig ∧ orig.length = len ∧ len ≤ bs.length ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + len < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
  post := fun _ ws _ => ws = bs.take len
  body := msetDoWhileBody src dst len bs orig

def msetMemcpy_verified : Program :=
  (msetDoWhileBody 0 0 0 [] []).flatten 0

-- **Byte-identity pin (the deliverable)**: the structured `when`+`doWhile`
-- flatten is exactly the emitted `msetMemcpy_prog` (8 instrs incl. ret).  The
-- `when` guard emits `BEQ x12 x0 28` (skips the 6-instr `doWhile`); the
-- `doWhile` body emits the 5 copy instrs + `BNE x12 x0 -20` back-edge.
#guard (msetDoWhileBody 0 0 0 [] []).flatten 0 =
  [ .BEQ .x12 .x0 (28 : BitVec 13),
    .LBU .x5 .x11 (0 : BitVec 12),
    .SB .x10 .x5 (0 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x12 .x12 (-1 : BitVec 12),
    .BNE .x12 .x0 (-20 : BitVec 13) ]

#guard (msetDoWhileBody 0 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0]
    = msetMemcpy_prog

-- Position independence: the body has no PC-relative instructions.
#guard (msetDoWhileBody 0 0 0 [] []).flatten 0
    = (msetDoWhileBody 0 0 0 [] []).flatten 0x80000000


/-- Memory obligations of one copy iteration, indexed by the byte being copied
    (`k`): the `LBU` at `src+k` routes to the read-only region (src/dst
    disjoint), the `SB` at `dst+k` hits the writable window. -/
theorem blockVCs_copy (rf : RegFile) (ws : List (BitVec 8)) (k len : Nat)
    (hwslen : ws.length = len)
    (hlb : len ≤ bs.length)
    (hx10 : rf.get .x10 = dst + BitVec.ofNat 64 k)
    (hx11 : rf.get .x11 = src + BitVec.ofNat 64 k)
    (hk : k < len)
    (hsb : src.toNat + len < 2 ^ 64) (hdb : dst.toNat + len < 2 ^ 64)
    (hdj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat) :
    blockVCs ⟨src, bs⟩ dst rf ws sgMemcpyStepBlock := by
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hi2 : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  have hloadaddr : rf.get .x11 + signExtend12 (0 : BitVec 12) = src + BitVec.ofNat 64 k := by
    rw [hx11, hse_0]; simp
  have hnr : ¬ inRw dst ws (rf.get .x11 + signExtend12 (0 : BitVec 12)) 1 := by
    rw [hloadaddr]; unfold inRw; rw [hwslen]
    have hsubd : (src + BitVec.ofNat 64 k - dst).toNat
        = (src.toNat + k + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]; congr 1; omega
    rw [hsubd]; rcases hdj with hd | hd <;> omega
  have hload_ok : (src + BitVec.ofNat 64 k - src).toNat = k := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]; omega
  have hstore : (rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat = k := by
    rw [hx10, hse_0]; bv_omega
  rw [show sgMemcpyStepBlock =
      [.LBU .x5 .x11 (0 : BitVec 12), .SB .x10 .x5 (0 : BitVec 12),
       .ADDI .x10 .x10 (1 : BitVec 12), .ADDI .x11 .x11 (1 : BitVec 12),
       .ADDI .x12 .x12 (-1 : BitVec 12)] from rfl]
  refine ⟨?_, ?_⟩
  · -- LBU obligation: routes to the read-only region, in-range.
    simp only [loadSem]
    rw [if_neg hnr]
    unfold Region.loadOk
    rw [hloadaddr, hload_ok]
    show 1 ∣ k ∧ k + 1 ≤ bs.length
    exact ⟨Nat.one_dvd _, by omega⟩
  · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _ hnr]
    refine ⟨?_, trivial, trivial, trivial, trivial⟩
    · -- SB obligation: hits the writable window, in-range, aligned.
      dsimp only [storeSem]
      refine ⟨?_, ?_⟩
      · unfold inRw
        rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hwslen, hstore]
        omega
      · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hstore]
        exact Nat.one_dvd _

/-- `mset_memcpy` correctness: `dst = src[0..len)`, with the src (read-only)
    and dst (writable, disjoint) regions well-formed.  Reuses the generic
    forward-copy engine/invariant from `SgMemcpySAsm`; only the loop *shape*
    differs (`when`+`doWhile` vs `«while»`). -/
theorem msetMemcpyFn_spec (src dst : Word) (len : Nat) (bs orig : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, len⟩) (base : Word) :
    (msetMemcpyFn src dst len bs orig).Spec base := by
  have hse_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hse_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  have hbase : (msetMemcpyFn src dst len bs orig).rw.base = dst := rfl
  have hreg : (msetMemcpyFn src dst len bs orig).region = ⟨src, bs⟩ := rfl
  have hlen64 : len < 2 ^ 64 := by
    obtain ⟨_, hdl, _⟩ := hrww
    have h : dst.toNat + len < 2 ^ 64 := by simpa using hdl
    omega
  -- Turn a `.bne .x12 .x0` guard fact + the `x12 = ofNat 64 m` tie into `m ≠ 0`.
  have ne_of_guard {rf : RegFile} {m : Nat} (hc : (Cond.bne .x12 .x0).holds rf)
      (hx12 : rf.get .x12 = BitVec.ofNat 64 m) (hm : m < 2 ^ 64) : m ≠ 0 := by
    dsimp only [Cond.holds] at hc
    rw [RegFile.get_x0] at hc
    rw [hx12] at hc
    intro h
    rw [h] at hc
    exact hc (by simp)
  -- Conversely: a `.bne .x12 .x0` *skip* (¬guard) + the tie forces `m = 0`.
  have zero_of_skip {rf : RegFile} {m : Nat} (hnc : ¬ (Cond.bne .x12 .x0).holds rf)
      (hx12 : rf.get .x12 = BitVec.ofNat 64 m) (hm : m < 2 ^ 64) : m = 0 := by
    dsimp only [Cond.holds] at hnc
    have heq : rf.get .x12 = rf.get .x0 := by by_contra h; exact hnc h
    rw [RegFile.get_x0] at heq
    rw [hx12] at heq
    have hT : (BitVec.ofNat 64 m).toNat = m % 2 ^ 64 := BitVec.toNat_ofNat ..
    have h0 : (0 : Word).toNat = 0 := rfl
    have heqz : m % 2 ^ 64 = 0 := by rw [← h0, ← hT, heq]
    omega
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case msetMemcpy.guard.loop.inv_init =>
    -- entry reach = pre ∧ (.bne .x12 .x0).holds; run the copy body once → inv 0.
    rintro rf' ws' A' ⟨rf₀, ws₀, -,
      ⟨⟨hx10, hx11, hx12, hws₀, hol, hlb, hsb, hdb, hdj⟩, hc⟩, rfl, rfl⟩
    have hpos : 0 < len := by
      have hne : len ≠ 0 := ne_of_guard hc hx12 hlen64
      omega
    have hwslen : ws₀.length = len := by rw [hws₀, hol]
    have hz10 : dst + BitVec.ofNat 64 0 = dst := by bv_omega
    have hz11 : src + BitVec.ofNat 64 0 = src := by bv_omega
    have hx10' : rf₀.get .x10 = dst + BitVec.ofNat 64 0 := by rw [hz10]; exact hx10
    have hx11' : rf₀.get .x11 = src + BitVec.ofNat 64 0 := by rw [hz11]; exact hx11
    rw [hbase, hreg,
      copy_step_engine src dst len 0 bs rf₀ ws₀ hx10' hx11' hpos hsb hdb hdj hwslen]
    refine ⟨?_, ?_, ?_, by omega, hlb, hol, hsb, hdb, hdj, ?_⟩
    · rw [copyStepRf_get_x10, hx10, hse_1]
      bv_omega
    · rw [copyStepRf_get_x11, hx11, hse_1]
      bv_omega
    · rw [copyStepRf_get_x12, hx12, hse_m1]
      have h1 : (BitVec.ofNat 64 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (len - 1)).toNat = len - 1 := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hws₀]
      have hstep := copyWin_step bs orig 0 hol hpos
      rw [copyWin_zero] at hstep
      exact hstep
  case msetMemcpy.guard.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨hinv, hc⟩, rfl, rfl⟩
    simp only [msetDoWhileInv] at hinv
    obtain ⟨hx10, hx11, hx12, hile, hlb, hol, hsb, hdb, hdj, hwin⟩ := hinv
    have hbyte : i + 1 < len := by
      have hne : len - (i + 1) ≠ 0 :=
        ne_of_guard hc hx12 (by omega : (len - (i + 1)) < 2 ^ 64)
      omega
    have hwslen : ws₀.length = len := by
      rw [hwin]; exact length_copyWin bs orig (i + 1) hol (by omega)
    rw [hbase, hreg,
      copy_step_engine src dst len (i + 1) bs rf₀ ws₀ hx10 hx11 hbyte hsb hdb hdj hwslen]
    refine ⟨?_, ?_, ?_, by omega, hlb, hol, hsb, hdb, hdj, ?_⟩
    · rw [copyStepRf_get_x10, hx10, hse_1]
      have h1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1 + 1)).toNat = i + 1 + 1 := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [copyStepRf_get_x11, hx11, hse_1]
      have h1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1 + 1)).toNat = i + 1 + 1 := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [copyStepRf_get_x12, hx12, hse_m1]
      have h1 : (BitVec.ofNat 64 (len - (i + 1))).toNat = len - (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (len - (i + 1 + 1))).toNat = len - (i + 1 + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hwin, copyWin_step bs orig (i + 1) hol hbyte]
  case msetMemcpy.guard.loop.exhausted =>
    -- inv fuel = sgMemcpyInv(len+1):  x12 = ofNat(len-(len+1)) = ofNat 0 → ¬guard.
    rintro rf ws A hinv
    simp only [msetDoWhileInv] at hinv
    obtain ⟨-, -, hx12, -, -, -, -, -, -, -⟩ := hinv
    have heq : len - (len + 1) = 0 := by omega
    show ¬ (rf.get .x12 ≠ rf.get .x0)
    rw [RegFile.get_x0, hx12, heq]
    decide
  case msetMemcpy.guard.loop.body.copy.mem =>
    -- body reach = entry (pre ∧ guard) ∨ ∃ i<fuel, inv i ∧ guard.
    rintro rf ws A hwslen hreach
    rcases hreach with
      ⟨⟨hx10, hx11, hx12, -, hol, hlb, hsb, hdb, hdj⟩, hc⟩
    | ⟨i, hi, hinv, hc⟩
    · have hpos : 0 < len := by
        have hne : len ≠ 0 := ne_of_guard hc hx12 hlen64
        omega
      exact blockVCs_copy (src := src) (dst := dst) rf ws 0 len hwslen hlb
        (by rw [hx10]; simp) (by rw [hx11]; simp) hpos hsb hdb hdj
    · simp only [msetDoWhileInv] at hinv
      obtain ⟨hx10, hx11, hx12, hile, hlb, hol, hsb, hdb, hdj, hwin⟩ := hinv
      have hbyte : i + 1 < len := by
        have hne : len - (i + 1) ≠ 0 :=
          ne_of_guard hc hx12 (by omega : (len - (i + 1)) < 2 ^ 64)
        omega
      exact blockVCs_copy (src := src) (dst := dst) rf ws (i + 1) len hwslen hlb
        hx10 hx11 hbyte hsb hdb hdj
  case msetMemcpy.post =>
    -- sp(when c b) = sp(b)(reach∧c) ∨ (reach ∧ ¬c): do-while exit / skip.
    rintro rf ws A (hloop | hskip)
    · obtain ⟨⟨i, hile, hinv⟩, hncond⟩ := hloop
      simp only [msetDoWhileInv] at hinv
      obtain ⟨hx10, hx11, hx12, hjle, hlb, hol, hsb, hdb, hdj, hwin⟩ := hinv
      have hrem : len - (i + 1) = 0 :=
        zero_of_skip hncond hx12 (by omega : (len - (i + 1)) < 2 ^ 64)
      have hi_len : i + 1 = len := by omega
      show ws = bs.take len
      have hol' : orig.length = i + 1 := by rw [hol, ← hi_len]
      have hlb' : i + 1 ≤ bs.length := by rw [hi_len]; exact hlb
      rw [hwin, copyWin_len_eq bs orig (i + 1) hol' hlb', hi_len]
    · obtain ⟨⟨hx10, hx11, hx12, hws, hol, hlb, hsb, hdb, hdj⟩, hnc⟩ := hskip
      have hlen0 : len = 0 := zero_of_skip hnc hx12 hlen64
      show ws = bs.take len
      rw [hws, hlen0]
      have h0 : orig.length = 0 := by rw [hol, hlen0]
      rw [List.eq_nil_of_length_eq_zero h0, List.take_zero]

end MsetMemcpySAsm

end EvmAsm.Codegen
