/-
  EvmAsm.Codegen.Programs.SgMemcpySAsm

  Verified SAsm port of `sg_memcpy` (bead evm-asm-4ch8f.12.2): copy `len` bytes
  forward from `src` (a1) to `dst` (a0).

  Source (string-emitted inline in StatelessGuestEpilogue.lean; no `_prog`):
      sg_memcpy:                 # a0=dst, a1=src, a2=len
      .Lsgmc_loop:
        beqz a2, .Lsgmc_done     # while a2 != 0
        lbu  t0, 0(a1); sb t0, 0(a0)
        addi a0,a0,1; addi a1,a1,1; addi a2,a2,-1
        j    .Lsgmc_loop
      .Lsgmc_done: ret
  Net: for j < len, dst[j] = src[j], i.e. dst = src[0..len).

  Two regions: READ-ONLY ⟨src, bs⟩ (read via LBU) and WRITABLE ⟨dst, len⟩
  (written via SB), combined with the separating `**`.  The block engine's
  `inRw` routing test is arithmetic, so to route each `LBU` to the read-only
  region the precondition states src/dst **disjointness** explicitly (`hdisj`);
  this is the routine's real forward-copy contract (a caller with overlapping
  buffers where `dst > src` would read already-overwritten bytes — unweakened).

  A clean top-tested `.«while»` (guard, body, back-`JAL` to guard); string-
  emitted, so length + position-independence are pinned (no `_prog` to compare).
  Spec-only module (no emitted-code change) — no EEST A/B.

  Generic in (src, dst, len, bs) so bead .12.1 `mset_memcpy` reuses this core.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace SgMemcpySAsm

/-- The `k`-th output byte: source byte at index `k` (forward copy). -/
def copyByte (bs : List (BitVec 8)) (k : Nat) : BitVec 8 :=
  bs.getD k 0

/-- Loop window: first `i` output bytes are the copied prefix, the rest is the
    untouched tail of the original dst buffer. -/
def copyWin (bs orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  (List.range i).map (copyByte bs) ++ orig.drop i

#guard copyWin [10,20,30] [0,0,0] 0 = [0,0,0]
#guard (List.range 3).map (copyByte [10,20,30]) = [10,20,30]

theorem copyWin_zero (bs orig : List (BitVec 8)) : copyWin bs orig 0 = orig := by
  simp [copyWin]

theorem length_copyWin (bs orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = len) (hi : i ≤ len) : (copyWin bs orig i).length = len := by
  simp only [copyWin, List.length_append, List.length_map, List.length_range,
    List.length_drop, h]
  omega

theorem copyWin_step (bs orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = len) (hi : i < len) :
    setBytes (copyWin bs orig i) i [copyByte bs i] = copyWin bs orig (i + 1) := by
  rw [setBytes_singleton]
  have hpre : ((List.range i).map (copyByte bs)).length = i := by simp
  have hdrop : orig.drop i = orig[i] :: orig.drop (i + 1) :=
    List.drop_eq_getElem_cons (by omega)
  simp only [copyWin, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.singleton_append]
  rw [hdrop]
  simp only [hpre, List.set_append_right, Nat.le_refl, Nat.sub_self,
    List.set_cons_zero]

theorem copyWin_len_eq (bs orig : List (BitVec 8)) (len : Nat)
    (h : orig.length = len) (hlen : len ≤ bs.length) :
    copyWin bs orig len = bs.take len := by
  have hnil : orig.drop len = [] := by simp [h]
  simp only [copyWin, hnil, List.append_nil]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take]; omega
  · intro j hj1 hj2
    simp only [List.length_map, List.length_range] at hj1
    simp only [List.getElem_map, List.getElem_range, copyByte, List.getElem_take,
      List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show j < bs.length by omega), Option.getD_some]

def sgMemcpyStepBlock : List Instr :=
  [.LBU .x5 .x11 0,
   .SB .x10 .x5 0,
   .ADDI .x10 .x10 1,
   .ADDI .x11 .x11 1,
   .ADDI .x12 .x12 (-1 : BitVec 12)]

def sgMemcpyInv (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x10 = dst + BitVec.ofNat 64 i ∧
    rf.get .x11 = src + BitVec.ofNat 64 i ∧
    rf.get .x12 = BitVec.ofNat 64 (len - i) ∧
    i ≤ len ∧ len ≤ bs.length ∧ orig.length = len ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + len < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat) ∧
    ws = copyWin bs orig i

def sgMemcpyBody (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) : Stmt :=
  .«while» "loop" (.bne .x12 .x0) len (sgMemcpyInv src dst len bs orig)
    (.block "copy" sgMemcpyStepBlock)

def sgMemcpyFn (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) : Fn where
  name := "sgMemcpy"
  region := ⟨src, bs⟩
  rw := ⟨dst, len⟩
  pre := fun rf ws _ =>
    rf.get .x10 = dst ∧ rf.get .x11 = src ∧ rf.get .x12 = BitVec.ofNat 64 len ∧
    ws = orig ∧ orig.length = len ∧ len ≤ bs.length ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + len < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
  post := fun _ ws _ => ws = bs.take len
  body := sgMemcpyBody src dst len bs orig

def sgMemcpy_verified : Program :=
  (sgMemcpyBody 0 0 0 [] []).flatten 0

#guard (sgMemcpy_verified : List Instr).length = 7
#guard (sgMemcpyBody 0 0 0 [] []).flatten 0 = (sgMemcpyBody 0 0 0 [] []).flatten 0x80000000

/-- The complete verified forward-copy routine, including its leaf `ret`. -/
def sgMemcpy_prog : Program :=
  (sgMemcpyBody 0 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]

/-- Kernel correspondence between the structured loop and emitted routine. -/
theorem sgMemcpy_body_eq_prog :
    (sgMemcpyBody 0 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]
      = sgMemcpy_prog := by
  rfl

#guard sgMemcpy_prog.length = 8

/-- An `LBU` that misses the writable window reads the read-only region. -/
theorem execInstrRF_lbu_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

/-- Register file after one loop body (given the loaded byte `b`). -/
def copyStepRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r1 := rf.set .x5 (b.zeroExtend 64)
  let r2 := r1.set .x10 (r1.get .x10 + signExtend12 (1 : BitVec 12))
  let r3 := r2.set .x11 (r2.get .x11 + signExtend12 (1 : BitVec 12))
  r3.set .x12 (r3.get .x12 + signExtend12 (-1 : BitVec 12))

theorem copyStepRf_get_x10 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x10 = rf.get .x10 + signExtend12 (1 : BitVec 12) := by
  unfold copyStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x12),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x11),
    RegFile.get_set_self _ _ _ (by decide : Reg.x10 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]

theorem copyStepRf_get_x11 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x11 = rf.get .x11 + signExtend12 (1 : BitVec 12) := by
  unfold copyStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x12),
    RegFile.get_set_self _ _ _ (by decide : Reg.x11 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]

theorem copyStepRf_get_x12 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x12 = rf.get .x12 + signExtend12 (-1 : BitVec 12) := by
  unfold copyStepRf
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x12 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x11),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5)]

/-- Engine (own heartbeat budget): one loop body loads `src[i]`, stores it at
    `dst[i]`, and advances both cursors + the counter. -/
theorem copy_step_engine (src dst : Word) (len i : Nat) (bs : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8))
    (hx10 : rf.get .x10 = dst + BitVec.ofNat 64 i)
    (hx11 : rf.get .x11 = src + BitVec.ofNat 64 i)
    (hi : i < len)
    (hsrc : src.toNat + len < 2 ^ 64) (hdst : dst.toNat + len < 2 ^ 64)
    (hdisj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
    (hws : ws.length = len) :
    execBlock ⟨src, bs⟩ dst rf ws sgMemcpyStepBlock
      = (copyStepRf rf (copyByte bs i), setBytes ws i [copyByte bs i]) := by
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hi2 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  -- the load address `src + i` misses the writable window `[dst, dst+len)`
  have hloadaddr : rf.get .x11 + signExtend12 (0 : BitVec 12) = src + BitVec.ofNat 64 i := by
    rw [hx11, hse_0]; simp
  have hnr : ¬ inRw dst ws (rf.get .x11 + signExtend12 (0 : BitVec 12)) 1 := by
    rw [hloadaddr]
    unfold inRw
    rw [hws]
    have hsubd : (src + BitVec.ofNat 64 i - dst).toNat
        = (src.toNat + i + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]; congr 1; omega
    rw [hsubd]
    rcases hdisj with hd | hd <;> omega
  -- the loaded byte equals `src[i]`
  have hval : (Region.byteAt ⟨src, bs⟩ (rf.get .x11 + signExtend12 (0 : BitVec 12)))
      = copyByte bs i := by
    rw [hloadaddr]
    show bs.getD ((src + BitVec.ofNat 64 i - src).toNat) 0 = copyByte bs i
    rw [show (src + BitVec.ofNat 64 i - src).toNat = i by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]; omega]
    rfl
  -- the store address is index `i` of the writable window
  have hstore : (rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
    rw [hx10, hse_0]
    bv_omega
  rw [show sgMemcpyStepBlock =
      [.LBU .x5 .x11 0, .SB .x10 .x5 0, .ADDI .x10 .x10 (1 : BitVec 12),
       .ADDI .x11 .x11 (1 : BitVec 12), .ADDI .x12 .x12 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ _ _ _ hnr]
  dsimp only
  rw [hval]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ i
    (by rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]; exact hstore)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton, truncate_zeroExtend_byte]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold copyStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x11),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5)]
  rw [setBytes_singleton]

theorem sgMemcpyFn_spec (src dst : Word) (len : Nat) (bs orig : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, len⟩) (base : Word) :
    (sgMemcpyFn src dst len bs orig).Spec base := by
  have hse_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hse_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case sgMemcpy.loop.inv_init =>
    rintro rf ws A ⟨hx10, hx11, hx12, rfl, hol, hlb, hsb, hdb, hdj⟩
    refine ⟨?_, ?_, ?_, by omega, hlb, hol, hsb, hdb, hdj, ?_⟩
    · rw [hx10]; simp
    · rw [hx11]; simp
    · rw [hx12]; simp
    · rw [copyWin_zero]
  case sgMemcpy.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -,
      ⟨⟨hx10, hx11, hx12, hile, hlb, hol, hsb, hdb, hdj, hwin⟩, -⟩, rfl, rfl⟩
    have hwslen : ws₀.length = len := by rw [hwin]; exact length_copyWin bs orig i hol (by omega)
    simp only [show (sgMemcpyFn src dst len bs orig).rw.base = dst from rfl,
      show (sgMemcpyFn src dst len bs orig).region = ⟨src, bs⟩ from rfl]
    rw [copy_step_engine src dst len i bs rf₀ ws₀ hx10 hx11 hi hsb hdb hdj hwslen]
    refine ⟨?_, ?_, ?_, by omega, hlb, hol, hsb, hdb, hdj, ?_⟩
    · rw [copyStepRf_get_x10, hx10, hse_1]
      have h1 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [copyStepRf_get_x11, hx11, hse_1]
      have h1 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [copyStepRf_get_x12, hx12, hse_m1]
      have h1 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (len - (i + 1))).toNat = len - (i + 1) := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hwin, copyWin_step bs orig i hol hi]
  case sgMemcpy.loop.exhausted =>
    rintro rf ws A ⟨-, -, hx12, hile, -, -, -, -, -, -⟩
    simp only [Cond.holds, not_not]
    rw [hx12]
    rw [show (BitVec.ofNat 64 (len - len)) = (0 : Word) by rw [show len - len = 0 by omega]; rfl]
    rfl
  case sgMemcpy.loop.body.copy.mem =>
    rintro rf ws A hwslen ⟨i, hi, ⟨hx10, hx11, hx12, hile, hlb, hol, hsb, hdb, hdj, hwin⟩, -⟩
    have hlen0 : ws.length = len := hwslen
    have hbase : (sgMemcpyFn src dst len bs orig).rw.base = dst := rfl
    have hi2 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    have hloadaddr : rf.get .x11 + signExtend12 (0 : BitVec 12) = src + BitVec.ofNat 64 i := by
      rw [hx11, hse_0]; simp
    have hnr : ¬ inRw dst ws (rf.get .x11 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [hloadaddr]
      unfold inRw
      rw [hlen0]
      have hsubd : (src + BitVec.ofNat 64 i - dst).toNat
          = (src.toNat + i + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
        rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]; congr 1; omega
      rw [hsubd]; rcases hdj with hd | hd <;> omega
    have hload_ok : (src + BitVec.ofNat 64 i - src).toNat = i := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]; omega
    have hstore : (rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
      rw [hx10, hse_0]; bv_omega
    rw [show sgMemcpyStepBlock =
        [.LBU .x5 .x11 0, .SB .x10 .x5 0, .ADDI .x10 .x10 (1 : BitVec 12),
         .ADDI .x11 .x11 (1 : BitVec 12), .ADDI .x12 .x12 (-1 : BitVec 12)] from rfl,
      show (sgMemcpyFn src dst len bs orig).region = ⟨src, bs⟩ from rfl, hbase]
    -- LBU obligation (routes to read-only region) ∧ rest
    refine ⟨?_, ?_⟩
    · simp only [loadSem]
      rw [if_neg hnr]
      unfold Region.loadOk
      rw [hloadaddr, hload_ok]
      refine ⟨Nat.one_dvd _, ?_⟩
      show i + 1 ≤ bs.length
      omega
    · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _ hnr]
      -- SB obligation (writable, aligned) ∧ trailing ADDIs (no obligations)
      refine ⟨?_, trivial, trivial, trivial, trivial⟩
      dsimp only [storeSem]
      refine ⟨?_, ?_⟩
      · unfold inRw
        rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hlen0, hstore]
        omega
      · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hstore]
        exact Nat.one_dvd _
  case sgMemcpy.post =>
    rintro rf ws A ⟨⟨i, hile, hx10, hx11, hx12, hle, hlb, hol, hsb, hdb, hdj, hwin⟩, hncond⟩
    have hi_len : i = len := by
      simp only [Cond.holds, not_not] at hncond
      rw [hx12] at hncond
      have hz : rf.get .x0 = 0 := rfl
      rw [hz] at hncond
      have : (BitVec.ofNat 64 (len - i)).toNat = (0 : Word).toNat := by rw [hncond]
      rw [show (0 : Word).toNat = 0 from rfl, BitVec.toNat_ofNat] at this
      omega
    subst hi_len
    show ws = bs.take i
    rw [hwin, copyWin_len_eq bs orig i hol hlb]

#print axioms sgMemcpyFn_spec

end SgMemcpySAsm

end EvmAsm.Codegen
